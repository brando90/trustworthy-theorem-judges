#!/usr/bin/env python3
"""Experiment 28 (Track 4B): Open-weight Qwen3 single-pass logit readout & OOF LoRA (CE vs RPS vs Pearson).

Runs on mercury2 (free local GPUs 0..7 only; never touches busy GPUs 8..9):
  - sanity        : Digit token checks, trailing space check, batch=1 vs left-padded equivalence,
                    two-pass Pearson chain-rule check, and Karpathy sanity controls on Qwen3-4B & Qwen3-8B.
  - logit_4b      : Qwen3-4B-Instruct-2507 single-pass next-token logit readout (max_seq_len=6144) on 175 items.
  - logit_8b      : Qwen3-8B manual 2-GPU split single-pass logit readout (max_seq_len=6144) on 175 items.
  - extract_4b    : Cache layer-32 prefix hidden states (max_seq_len=2560) for Qwen3-4B across 175 items.
  - train_lora_4b : Strictly OOF Top-4-block LoRA (CE, RPS, Pearson) with inner-val RPS HP selection on
                    exp27_split (train+val -> test) and cv5_fold (5 outer folds covering all 50 tasks).
"""
from __future__ import annotations

import argparse
import csv
import glob
import json
import math
import os
import re
import time
from pathlib import Path

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.nn.attention import SDPBackend, sdpa_kernel
from transformers import AutoModelForCausalLM, AutoTokenizer
from transformers.masking_utils import create_causal_mask

HF_MAIN = "/dfs/scratch0/brando9/at1025_hf"
MODEL_REPOS = {
    "qwen3_4b": "Qwen--Qwen3-4B-Instruct-2507",
    "qwen3_8b": "Qwen--Qwen3-8B",
}

LORA_RANK = 8
LORA_ALPHA = 16.0
WEIGHT_DECAY = 0.01
GRAD_CLIP = 1.0
CHUNK_SIZE = 1
BATCH_SIZE = 32
DEFAULT_STEPS = 24
LRS = (1e-4, 4e-4)
CKPT_FRACS = (0.25, 0.50, 0.75, 1.00)
PEARSON_STD_TOL = 1e-6
GRID_NP = np.arange(6, dtype=np.float64)

SYSTEM_PROMPT_QWEN = (
    "You are evaluating formal specification coverage of a candidate Lean 4 formalization compared with a "
    "Python source file and a gold reference Lean 4 file.\n"
    "Rate strictly on the integer scale 0 to 5:\n"
    "5 = Complete coverage (all essential properties, preconditions, postconditions, and types captured)\n"
    "4 = Almost complete (minor edge condition or helper detail missing)\n"
    "3 = Partial / core properties covered, notable specification gaps\n"
    "2 = Weak / superficial or partial types only\n"
    "1 = Mostly vacuous, trivial True/sorry placeholders, or badly off-target\n"
    "0 = Missing, empty, completely wrong/unrelated, or gamed spam.\n"
    "Output only the single integer rating 0, 1, 2, 3, 4, or 5."
)
ASSISTANT_PREFIX = "Specification coverage rating (0-5): "


def resolve_snapshot(model_key: str) -> str:
    repo_dir = MODEL_REPOS[model_key]
    snaps = sorted(glob.glob(f"{HF_MAIN}/hub/models--{repo_dir}/snapshots/*"))
    if not snaps:
        raise FileNotFoundError(f"No snapshot under {HF_MAIN}/hub/models--{repo_dir}")
    return snaps[-1]


def verify_digit_tokens(tok: AutoTokenizer) -> list[int]:
    digit_ids = []
    for d in range(6):
        enc = tok.encode(str(d), add_special_tokens=False)
        assert len(enc) == 1, f"Digit {d} not single-token: {enc}"
        assert tok.decode(enc).strip() == str(d)
        digit_ids.append(int(enc[0]))
    assert len(set(digit_ids)) == 6
    return digit_ids


def strip_lean_proof_bodies(text: str, max_lines: int = 240) -> str:
    """Statement-preserving Lean compaction: keep imports, defs, and theorem statements intact."""
    lines = text.splitlines()
    out: list[str] = []
    in_proof = False
    for line in lines:
        s = line.strip()
        is_top_decl = bool(re.match(
            r"^(import|open|set_option|universe|variable|namespace|end\s|theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom|#|@\[)",
            s,
        ))
        if is_top_decl:
            in_proof = False
        if not in_proof:
            out.append(line)
            if (":= by" in line or s.endswith("by")) and re.match(r"^(private\s+|protected\s+)?(theorem|lemma)\b", s):
                out.append("  sorry -- [proof body omitted for specification-statement comparison]")
                in_proof = True
        if len(out) >= max_lines:
            break
    if len(lines) > len(out):
        out.append("-- [truncated remaining lines]")
    return "\n".join(out)


def render_ids_from_user_prompt(
    tok: AutoTokenizer,
    user_text: str,
    max_seq_len: int,
) -> tuple[list[int], str]:
    msgs = [
        {"role": "system", "content": SYSTEM_PROMPT_QWEN},
        {"role": "user", "content": user_text},
        {"role": "assistant", "content": ASSISTANT_PREFIX},
    ]
    rendered = tok.apply_chat_template(
        msgs, tokenize=False, continue_final_message=True, add_generation_prompt=False, enable_thinking=False
    )
    if not rendered.endswith(" "):
        rendered = rendered + " "
    ids = tok.encode(rendered, add_special_tokens=False)
    if len(ids) > max_seq_len:
        # Preserve head (Python + ref statements) and tail (candidate + instruction)
        head = max_seq_len // 2
        tail = max_seq_len - head
        ids = ids[:head] + ids[-tail:]
    return ids, rendered


def format_artifact_user(row: dict, tok: AutoTokenizer, max_seq_len: int) -> tuple[list[int], bool]:
    raw_user = (
        f"### Python Source ({row['py_name']})\n```python\n{row['py_text']}\n```\n\n"
        f"### Gold Reference Lean ({row['ref_name']})\n```lean\n{row['ref_text']}\n```\n\n"
        f"### Candidate Lean ({row['cand_name']})\n```lean\n{row['cand_text']}\n```\n\n"
        "Rate the candidate Lean specification coverage on 0-5."
    )
    ids, _ = render_ids_from_user_prompt(tok, raw_user, max_seq_len=max_seq_len + 1)
    if len(ids) <= max_seq_len:
        return ids, False

    ref_c = strip_lean_proof_bodies(row["ref_text"], max_lines=220)
    cand_c = strip_lean_proof_bodies(row["cand_text"], max_lines=220)
    comp_user = (
        f"### Python Source ({row['py_name']})\n```python\n{row['py_text']}\n```\n\n"
        f"### Gold Reference Lean ({row['ref_name']})\n```lean\n{ref_c}\n```\n\n"
        f"### Candidate Lean ({row['cand_name']})\n```lean\n{cand_c}\n```\n\n"
        "Rate the candidate Lean specification coverage on 0-5."
    )
    ids2, _ = render_ids_from_user_prompt(tok, comp_user, max_seq_len=max_seq_len)
    return ids2, True


def load_ratings_targets(data_dir: Path) -> dict[str, dict]:
    targets = {}
    for fname in ("human_ratings_old_11-26-2026.csv", "human_ratings_new_11-26-2026.csv"):
        with (data_dir / fname).open() as f:
            for row in csv.DictReader(f):
                vals = [int(x) for x in row["ratings_sorted_0to5_rater_identity_removed"].split()]
                p_emp = np.bincount(vals, minlength=6).astype(np.float64)
                p_emp /= p_emp.sum()
                targets[row["item"]] = {
                    "item": row["item"],
                    "task": row["task"],
                    "set": row["set"],
                    "exp27_split": row["exp27_split"],
                    "cv5_fold": int(row["cv5_fold"]),
                    "ratings": vals,
                    "p_emp": p_emp,
                    "mean_score": float(np.mean(vals)),
                }
    return targets


class LoRALinear(nn.Module):
    """Pure-PyTorch LoRA wrapper with float32 master adapter weights."""

    def __init__(self, base: nn.Linear, rank: int = LORA_RANK, alpha: float = LORA_ALPHA):
        super().__init__()
        self.base = base
        for p in self.base.parameters():
            p.requires_grad_(False)
        self.rank = rank
        self.scale = alpha / rank
        dev = base.weight.device
        self.lora_A = nn.Parameter(torch.empty(rank, base.in_features, dtype=torch.float32, device=dev))
        self.lora_B = nn.Parameter(torch.zeros(base.out_features, rank, dtype=torch.float32, device=dev))
        self.reset_lora(seed=0)

    def reset_lora(self, seed: int = 0) -> None:
        g = torch.Generator(device=self.lora_A.device).manual_seed(seed)
        nn.init.normal_(self.lora_A, mean=0.0, std=0.02, generator=g)
        nn.init.zeros_(self.lora_B)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        out = self.base(x)
        delta = F.linear(F.linear(x.float(), self.lora_A), self.lora_B) * self.scale
        return out + delta.to(out.dtype)


def build_left_padded_inputs(
    seq_list: list[torch.Tensor],
    device: torch.device,
) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor | None]:
    m = len(seq_list)
    dtype = seq_list[0].dtype
    hdim = seq_list[0].shape[-1]
    lengths = [int(t.shape[1]) for t in seq_list]
    L_max = max(lengths)

    h_pad = torch.zeros((m, L_max, hdim), dtype=dtype, device=device)
    valid = torch.zeros((m, L_max), dtype=torch.bool, device=device)
    pos_ids = torch.zeros((m, L_max), dtype=torch.long, device=device)
    for b, (t, L_b) in enumerate(zip(seq_list, lengths)):
        pad = L_max - L_b
        h_pad[b, pad:, :] = t.squeeze(0).to(device)
        valid[b, pad:] = True
        pos_ids[b, pad:] = torch.arange(L_b, dtype=torch.long, device=device)

    if m == 1:
        return h_pad, pos_ids, None

    r = torch.arange(L_max, device=device)[:, None]
    c = torch.arange(L_max, device=device)[None, :]
    allow = (c <= r)[None, :, :] & (valid[:, None, :] | (r == c)[None, :, :])
    cmask = torch.zeros((m, 1, L_max, L_max), dtype=dtype, device=device)
    cmask.masked_fill_(~allow[:, None, :, :], torch.finfo(dtype).min)
    return h_pad, pos_ids, cmask


class TopBlocksLoRAJudge(nn.Module):
    """Top 4 Qwen3 blocks (LoRA on 7 projections/block) + final RMSNorm + 6-digit rating head."""

    def __init__(
        self,
        config,
        top_layers: nn.ModuleList,
        rotary_emb: nn.Module,
        norm: nn.Module,
        digit_weight: torch.Tensor,
        rank: int = LORA_RANK,
        alpha: float = LORA_ALPHA,
    ):
        super().__init__()
        self.config = config
        self.top_layers = top_layers
        self.rotary_emb = rotary_emb
        self.norm = norm
        for p in self.parameters():
            p.requires_grad_(False)

        self.lora_modules: list[LoRALinear] = []
        target_names = ("q_proj", "k_proj", "v_proj", "o_proj", "gate_proj", "up_proj", "down_proj")
        for layer in self.top_layers:
            for sub_name in ("self_attn", "mlp"):
                sub = getattr(layer, sub_name)
                for proj_name in target_names:
                    if hasattr(sub, proj_name):
                        orig = getattr(sub, proj_name)
                        if isinstance(orig, nn.Linear):
                            wrapped = LoRALinear(orig, rank=rank, alpha=alpha)
                            setattr(sub, proj_name, wrapped)
                            self.lora_modules.append(wrapped)

        dev = digit_weight.device
        self.head_weight = nn.Parameter(digit_weight.detach().float().clone().to(dev))
        self.head_bias = nn.Parameter(torch.zeros(6, dtype=torch.float32, device=dev))
        self._init_head_w = self.head_weight.detach().clone()
        self._init_head_b = self.head_bias.detach().clone()

    def reset_trainable(self, seed: int) -> None:
        for idx, mod in enumerate(self.lora_modules):
            mod.reset_lora(seed=seed + idx * 31)
        with torch.no_grad():
            self.head_weight.copy_(self._init_head_w)
            self.head_bias.copy_(self._init_head_b)

    def trainable_parameters(self) -> list[nn.Parameter]:
        params = [self.head_weight, self.head_bias]
        for mod in self.lora_modules:
            params.extend([mod.lora_A, mod.lora_B])
        return params

    def export_state(self) -> dict[str, torch.Tensor]:
        state = {
            "head_weight": self.head_weight.detach().cpu().clone(),
            "head_bias": self.head_bias.detach().cpu().clone(),
        }
        for i, mod in enumerate(self.lora_modules):
            state[f"lora_{i}_A"] = mod.lora_A.detach().cpu().clone()
            state[f"lora_{i}_B"] = mod.lora_B.detach().cpu().clone()
        return state

    def forward_logits_batch(self, seq_list: list[torch.Tensor]) -> torch.Tensor:
        device = self.head_weight.device
        h_in, pos_ids, cmask = build_left_padded_inputs(seq_list, device=device)
        cache_pos = torch.arange(h_in.shape[1], device=device)
        if cmask is None:
            cmask = create_causal_mask(
                config=self.config,
                inputs_embeds=h_in,
                attention_mask=None,
                past_key_values=None,
                position_ids=pos_ids,
            )
        pos_emb = self.rotary_emb(h_in, pos_ids)
        h = h_in
        for layer in self.top_layers:
            out = layer(
                h,
                attention_mask=cmask,
                position_ids=pos_ids,
                past_key_values=None,
                use_cache=False,
                cache_position=cache_pos,
                position_embeddings=pos_emb,
            )
            h = out[0] if isinstance(out, tuple) else out
        h_last = self.norm(h)[:, -1, :].float()
        return F.linear(h_last, self.head_weight, self.head_bias)  # [m, 6]


def forward_prefix(full_model, inp: torch.Tensor, split_layer: int) -> torch.Tensor:
    pos_ids = torch.arange(inp.shape[1], device=inp.device).unsqueeze(0)
    cache_pos = pos_ids[0]
    h = full_model.model.embed_tokens(inp)
    cmask = create_causal_mask(
        config=full_model.config,
        inputs_embeds=h,
        attention_mask=None,
        past_key_values=None,
        position_ids=pos_ids,
    )
    pos_emb = full_model.model.rotary_emb(h, pos_ids)
    for layer in full_model.model.layers[:split_layer]:
        out = layer(
            h,
            attention_mask=cmask,
            position_ids=pos_ids,
            past_key_values=None,
            use_cache=False,
            cache_position=cache_pos,
            position_embeddings=pos_emb,
        )
        h = out[0] if isinstance(out, tuple) else out
    return h


def pearson_loss_and_grad_np(mu: np.ndarray, h: np.ndarray) -> tuple[float | None, np.ndarray | None, bool]:
    if float(np.std(mu)) <= PEARSON_STD_TOL or float(np.std(h)) <= PEARSON_STD_TOL:
        return None, None, True
    a = mu - mu.mean()
    b = h - h.mean()
    na = float(np.linalg.norm(a))
    nb = float(np.linalg.norm(b))
    r = float((a @ b) / (na * nb))
    grad_r = (b / nb - r * a / na) / na
    return -r, -grad_r, False


def rps_np(q: np.ndarray, p_emp: np.ndarray) -> float:
    cq = np.cumsum(q, axis=1)[:, :5]
    cp = np.cumsum(p_emp, axis=1)[:, :5]
    return float(((cq - cp) ** 2 + cp * (1.0 - cp)).mean())


def ce_np(q: np.ndarray, p_emp: np.ndarray) -> float:
    q_s = np.clip(q, 1e-6, 1.0)
    q_s = q_s / q_s.sum(axis=1, keepdims=True)
    return float(-np.sum(np.where(p_emp > 0, p_emp * np.log(q_s), 0.0), axis=1).mean())


def tvd_np(q: np.ndarray, p_emp: np.ndarray) -> float:
    return float(0.5 * np.abs(q - p_emp).sum(axis=1).mean())


def verify_two_pass_chain_rule() -> dict:
    torch.manual_seed(17)
    w = nn.Parameter(torch.randn(6, 16, dtype=torch.float64))
    xs = torch.randn(10, 16, dtype=torch.float64)
    h_np = np.array([0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 5.0, 4.0, 2.5, 1.0], dtype=np.float64)
    grid_t = torch.arange(6, dtype=torch.float64)

    w.grad = None
    mu_t = F.softmax(xs @ w.T, dim=-1) @ grid_t
    a = mu_t - mu_t.mean()
    b = torch.tensor(h_np - h_np.mean(), dtype=torch.float64)
    (-(a @ b) / (torch.norm(a) * torch.norm(b))).backward()
    g_single = w.grad.detach().clone()

    w.grad = None
    with torch.no_grad():
        mu_np = (F.softmax(xs @ w.T, dim=-1) @ grid_t).numpy()
    _, d_mu, undef = pearson_loss_and_grad_np(mu_np, h_np)
    assert not undef and d_mu is not None
    ((torch.tensor(d_mu, dtype=torch.float64) * (F.softmax(xs @ w.T, dim=-1) @ grid_t)).sum()).backward()
    rel_err = float(torch.norm(g_single - w.grad) / (torch.norm(g_single) + 1e-15))
    assert rel_err < 1e-9, f"Two-pass Pearson mismatch: {rel_err}"
    return {"pearson_two_pass_rel_error": rel_err, "passed": True}


@torch.no_grad()
def predict_single_pass_4b(model, tok: AutoTokenizer, digit_ids: list[int], items: list[dict], max_seq_len: int) -> list[dict]:
    device = next(model.parameters()).device
    rows = []
    for i, item in enumerate(items):
        ids, compacted = format_artifact_user(item, tok, max_seq_len=max_seq_len)
        inp = torch.tensor([ids], dtype=torch.long, device=device)
        pos_ids = torch.arange(inp.shape[1], device=device).unsqueeze(0)
        cache_pos = pos_ids[0]
        h = model.model.embed_tokens(inp)
        cmask = create_causal_mask(
            config=model.config, inputs_embeds=h, attention_mask=None, past_key_values=None, position_ids=pos_ids,
        )
        pos_emb = model.model.rotary_emb(h, pos_ids)
        for layer in model.model.layers:
            out = layer(
                h, attention_mask=cmask, position_ids=pos_ids, past_key_values=None,
                use_cache=False, cache_position=cache_pos, position_embeddings=pos_emb,
            )
            h = out[0] if isinstance(out, tuple) else out
        h_last = model.model.norm(h)[:, -1, :]
        logits_full = model.lm_head(h_last)[0].float()
        d_logits = logits_full[digit_ids].cpu().numpy()
        probs = np.exp(d_logits - d_logits.max())
        probs /= probs.sum()
        argmax_d = int(np.argmax(d_logits))
        argmax_global_tok = int(torch.argmax(logits_full).item())
        rows.append({
            "item": item["item"],
            "n_tokens": len(ids),
            "compacted": compacted,
            "digit_logits": [round(float(x), 6) for x in d_logits],
            "probs": [round(float(x), 6) for x in probs],
            "expected_score": round(float(probs @ GRID_NP), 6),
            "argmax_digit": argmax_d,
            "argmax_is_digit": argmax_global_tok in digit_ids,
        })
        if (i + 1) % 35 == 0 or (i + 1) == len(items):
            print(f"[4B logit] {i+1}/{len(items)}", flush=True)
    return rows


@torch.no_grad()
def predict_single_pass_8b_2gpu(model, tok: AutoTokenizer, digit_ids: list[int], items: list[dict], max_seq_len: int) -> list[dict]:
    """Manual exact layer-split forward for Qwen3-8B across cuda:0 (layers 0..17) and cuda:1 (18..35 + norm + head)."""
    dev0 = torch.device("cuda:0")
    dev1 = torch.device("cuda:1")
    split = len(model.model.layers) // 2
    model.model.embed_tokens.to(dev0)
    model.model.rotary_emb.to(dev0)
    for idx, layer in enumerate(model.model.layers):
        layer.to(dev0 if idx < split else dev1)
    model.model.norm.to(dev1)
    model.lm_head.to(dev1)

    rows = []
    for i, item in enumerate(items):
        ids, compacted = format_artifact_user(item, tok, max_seq_len=max_seq_len)
        inp = torch.tensor([ids], dtype=torch.long, device=dev0)
        pos_ids0 = torch.arange(inp.shape[1], device=dev0).unsqueeze(0)
        cache_pos0 = pos_ids0[0]
        h = model.model.embed_tokens(inp)
        cmask0 = create_causal_mask(
            config=model.config, inputs_embeds=h, attention_mask=None, past_key_values=None, position_ids=pos_ids0,
        )
        pos_emb0 = model.model.rotary_emb(h, pos_ids0)
        for layer in model.model.layers[:split]:
            out = layer(
                h, attention_mask=cmask0, position_ids=pos_ids0, past_key_values=None,
                use_cache=False, cache_position=cache_pos0, position_embeddings=pos_emb0,
            )
            h = out[0] if isinstance(out, tuple) else out

        h = h.to(dev1)
        pos_ids1 = pos_ids0.to(dev1)
        cache_pos1 = cache_pos0.to(dev1)
        cmask1 = cmask0.to(dev1) if cmask0 is not None else None
        pos_emb1 = (pos_emb0[0].to(dev1), pos_emb0[1].to(dev1))
        for layer in model.model.layers[split:]:
            out = layer(
                h, attention_mask=cmask1, position_ids=pos_ids1, past_key_values=None,
                use_cache=False, cache_position=cache_pos1, position_embeddings=pos_emb1,
            )
            h = out[0] if isinstance(out, tuple) else out

        h_last = model.model.norm(h)[:, -1, :]
        logits_full = model.lm_head(h_last)[0].float()
        d_logits = logits_full[digit_ids].cpu().numpy()
        probs = np.exp(d_logits - d_logits.max())
        probs /= probs.sum()
        rows.append({
            "item": item["item"],
            "n_tokens": len(ids),
            "compacted": compacted,
            "digit_logits": [round(float(x), 6) for x in d_logits],
            "probs": [round(float(x), 6) for x in probs],
            "expected_score": round(float(probs @ GRID_NP), 6),
            "argmax_digit": int(np.argmax(d_logits)),
            "argmax_is_digit": int(torch.argmax(logits_full).item()) in digit_ids,
        })
        if (i + 1) % 35 == 0 or (i + 1) == len(items):
            print(f"[8B logit] {i+1}/{len(items)}", flush=True)
    return rows


def run_sanity(work_dir: Path, items: list[dict], controls: list[dict]) -> None:
    chain_info = verify_two_pass_chain_rule()
    snap_4b = resolve_snapshot("qwen3_4b")
    tok = AutoTokenizer.from_pretrained(snap_4b, local_files_only=True)
    digit_ids = verify_digit_tokens(tok)
    _, rendered0 = render_ids_from_user_prompt(tok, "hello", 512)
    assert rendered0.endswith(" ")

    # Controls on Qwen3-4B
    m4 = AutoModelForCausalLM.from_pretrained(snap_4b, dtype=torch.bfloat16, local_files_only=True).to("cuda:0").eval()
    ctrl_4b = []
    with torch.no_grad():
        for r in controls:
            ids, _ = render_ids_from_user_prompt(tok, r["user"], 4096)
            inp = torch.tensor([ids], dtype=torch.long, device="cuda:0")
            pos_ids = torch.arange(inp.shape[1], device="cuda:0").unsqueeze(0)
            cache_pos = pos_ids[0]
            h = m4.model.embed_tokens(inp)
            cmask = create_causal_mask(
                config=m4.config, inputs_embeds=h, attention_mask=None, past_key_values=None, position_ids=pos_ids,
            )
            pos_emb = m4.model.rotary_emb(h, pos_ids)
            for layer in m4.model.layers:
                o = layer(h, attention_mask=cmask, position_ids=pos_ids, past_key_values=None,
                          use_cache=False, cache_position=cache_pos, position_embeddings=pos_emb)
                h = o[0] if isinstance(o, tuple) else o
            dl = m4.lm_head(m4.model.norm(h)[:, -1, :])[0, digit_ids].float().cpu().numpy()
            p = np.exp(dl - dl.max()); p /= p.sum()
            ctrl_4b.append({"id": r["id"], "control": r["control"], "E": round(float(p @ GRID_NP), 4), "argmax": int(np.argmax(dl))})

    # Left-padded prefix equivalence test (full model forward vs cached-prefix TopBlocksLoRAJudge under SDPBackend.MATH)
    split_layer = len(m4.model.layers) - 4
    sample_seqs = []
    for row in items[:3]:
        ids, _ = format_artifact_user(row, tok, max_seq_len=1024)
        sample_seqs.append(torch.tensor([ids], dtype=torch.long, device="cuda:0"))
    with torch.no_grad():
        prefixes = [forward_prefix(m4, s, split_layer).detach().cpu() for s in sample_seqs]
    d_w = m4.lm_head.weight[digit_ids]
    top_judge = TopBlocksLoRAJudge(
        m4.config, m4.model.layers[split_layer:], m4.model.rotary_emb, m4.model.norm, d_w
    )
    top_judge.eval()
    with sdpa_kernel(SDPBackend.MATH):
        with torch.no_grad():
            full_logits = []
            for s in sample_seqs:
                out_full = m4(s, use_cache=False).logits[:, -1, digit_ids].float().cpu()
                full_logits.append(out_full)
            full_cat = torch.cat(full_logits, dim=0)
            batched_cat = top_judge.forward_logits_batch(prefixes).cpu()
            step0_diff = float((full_cat - batched_cat).abs().max().item())

    out_obj = {
        "chain_rule": chain_info,
        "digit_ids_4b": digit_ids,
        "trailing_space_ok": rendered0.endswith(" "),
        "step0_full_vs_leftpad_max_diff": step0_diff,
        "controls_qwen3_4b": ctrl_4b,
    }
    (work_dir / "qwen_sanity.json").write_text(json.dumps(out_obj, indent=2))
    print("[SANITY]", json.dumps(out_obj, indent=2), flush=True)


def run_logit_4b(work_dir: Path, items: list[dict], max_seq_len: int) -> None:
    snap = resolve_snapshot("qwen3_4b")
    tok = AutoTokenizer.from_pretrained(snap, local_files_only=True)
    digit_ids = verify_digit_tokens(tok)
    m = AutoModelForCausalLM.from_pretrained(snap, dtype=torch.bfloat16, local_files_only=True).to("cuda:0").eval()
    rows = predict_single_pass_4b(m, tok, digit_ids, items, max_seq_len=max_seq_len)
    (work_dir / f"qwen3_4b_logit_{max_seq_len}.json").write_text(json.dumps(rows, indent=2))
    print(f"[4B logit] Saved {len(rows)} rows", flush=True)


def run_logit_8b(work_dir: Path, items: list[dict], max_seq_len: int) -> None:
    snap = resolve_snapshot("qwen3_8b")
    tok = AutoTokenizer.from_pretrained(snap, local_files_only=True)
    digit_ids = verify_digit_tokens(tok)
    m = AutoModelForCausalLM.from_pretrained(snap, dtype=torch.bfloat16, local_files_only=True).eval()
    rows = predict_single_pass_8b_2gpu(m, tok, digit_ids, items, max_seq_len=max_seq_len)
    (work_dir / f"qwen3_8b_logit_{max_seq_len}.json").write_text(json.dumps(rows, indent=2))
    print(f"[8B logit] Saved {len(rows)} rows", flush=True)


@torch.no_grad()
def run_extract_4b(work_dir: Path, items: list[dict], max_seq_len: int) -> None:
    snap = resolve_snapshot("qwen3_4b")
    tok = AutoTokenizer.from_pretrained(snap, local_files_only=True)
    digit_ids = verify_digit_tokens(tok)
    m = AutoModelForCausalLM.from_pretrained(snap, dtype=torch.bfloat16, local_files_only=True).to("cuda:0").eval()
    split_layer = len(m.model.layers) - 4
    prefixes = {}
    lens = []
    for i, row in enumerate(items):
        ids, _ = format_artifact_user(row, tok, max_seq_len=max_seq_len)
        inp = torch.tensor([ids], dtype=torch.long, device="cuda:0")
        h = forward_prefix(m, inp, split_layer)
        prefixes[row["item"]] = h.detach().cpu()  # [1, L, 2560] bfloat16
        lens.append(len(ids))
        if (i + 1) % 35 == 0 or (i + 1) == len(items):
            print(f"[extract_4b] {i+1}/{len(items)} max_len={max(lens)}", flush=True)
    cache_path = work_dir / f"prefix_4b_{max_seq_len}.pt"
    torch.save({
        "prefixes": prefixes,
        "split_layer": split_layer,
        "digit_ids": digit_ids,
        "lens": lens,
    }, cache_path)
    print(f"[extract_4b] Saved {cache_path} ({cache_path.stat().st_size / 1e9:.2f} GB)", flush=True)


def fit_and_predict_lora(
    judge: TopBlocksLoRAJudge,
    train_seqs: list[torch.Tensor],
    train_p_emp: np.ndarray,
    eval_seqs: list[torch.Tensor],
    objective: str,
    lr: float,
    steps: int,
    eval_steps: list[int],
    seed: int,
) -> dict[int, np.ndarray]:
    """Matched deterministic mini-batch (B=32) gradient-accumulated LoRA training across Flash/Efficient SDPA."""
    judge.reset_trainable(seed=seed)
    judge.train()
    opt = torch.optim.AdamW(judge.trainable_parameters(), lr=lr, weight_decay=WEIGHT_DECAY)
    n_tr = len(train_seqs)
    bsz = min(BATCH_SIZE, n_tr)
    p_t = torch.tensor(train_p_emp, dtype=torch.float64, device=judge.head_weight.device)
    grid_t = torch.arange(6, dtype=torch.float64, device=judge.head_weight.device)
    mean_scores = (train_p_emp * GRID_NP[None, :]).sum(axis=1)
    preds_by_step: dict[int, np.ndarray] = {}

    for step in range(1, steps + 1):
        rng = np.random.default_rng(seed * 1009 + step)
        b_idx = rng.choice(n_tr, size=bsz, replace=False).tolist()
        opt.zero_grad(set_to_none=True)
        if objective == "pearson":
            all_mu = []
            with torch.no_grad():
                for s in range(0, bsz, CHUNK_SIZE):
                    sub = [train_seqs[j] for j in b_idx[s : s + CHUNK_SIZE]]
                    lg = judge.forward_logits_batch(sub).double()
                    all_mu.append((F.softmax(lg, dim=-1) @ grid_t).cpu().numpy())
            mu_np = np.concatenate(all_mu, axis=0)
            _, d_mu, undef = pearson_loss_and_grad_np(mu_np, mean_scores[b_idx])
            if undef or d_mu is None:
                d_mu = np.zeros(bsz, dtype=np.float64)
            d_mu_t = torch.tensor(d_mu, dtype=torch.float64, device=judge.head_weight.device)

        for s in range(0, bsz, CHUNK_SIZE):
            e = min(bsz, s + CHUNK_SIZE)
            sub_ids = b_idx[s:e]
            sub_seqs = [train_seqs[j] for j in sub_ids]
            lg = judge.forward_logits_batch(sub_seqs).double()
            if objective == "ce":
                lsm = F.log_softmax(lg, dim=-1)
                loss_chunk = -(p_t[sub_ids] * lsm).sum(dim=-1).sum() / bsz
            elif objective == "rps":
                probs = F.softmax(lg, dim=-1)
                cq = torch.cumsum(probs, dim=-1)[:, :5]
                cp = torch.cumsum(p_t[sub_ids], dim=-1)[:, :5]
                loss_chunk = ((cq - cp) ** 2).mean(dim=-1).sum() / bsz
            elif objective == "pearson":
                mu = F.softmax(lg, dim=-1) @ grid_t
                loss_chunk = (d_mu_t[s:e] * mu).sum()
            else:
                raise ValueError(objective)
            loss_chunk.backward()

        torch.nn.utils.clip_grad_norm_(judge.trainable_parameters(), GRAD_CLIP)
        opt.step()

        if step in eval_steps:
            judge.eval()
            ev_probs = []
            with torch.no_grad():
                for s in range(0, len(eval_seqs), CHUNK_SIZE):
                    lg = judge.forward_logits_batch(eval_seqs[s : s + CHUNK_SIZE]).double()
                    ev_probs.append(F.softmax(lg, dim=-1).cpu().numpy())
            preds_by_step[step] = np.concatenate(ev_probs, axis=0)
            judge.train()
    return preds_by_step


def run_train_lora_4b(
    work_dir: Path, cache_dir: Path, targets: dict[str, dict], objectives: list[str],
    max_seq_len: int, steps: int, splits_arg: str = "exp27,0,1,2,3,4", tag: str = "",
) -> None:
    snap = resolve_snapshot("qwen3_4b")
    m = AutoModelForCausalLM.from_pretrained(snap, dtype=torch.bfloat16, local_files_only=True)
    cache = torch.load(cache_dir / f"prefix_4b_{max_seq_len}.pt", map_location="cpu", weights_only=False)
    prefixes = cache["prefixes"]
    split_layer = int(cache["split_layer"])
    digit_ids = cache["digit_ids"]
    d_w = m.lm_head.weight[digit_ids].clone()
    judge = TopBlocksLoRAJudge(
        m.config, m.model.layers[split_layer:], m.model.rotary_emb, m.model.norm, d_w
    ).to("cuda:0")
    del m
    torch.cuda.empty_cache()

    wanted_splits = set(splits_arg.split(","))
    eval_steps = sorted({max(4, int(round(steps * f))) for f in CKPT_FRACS})
    items_ordered = sorted(targets.keys())
    all_out = {}

    for obj in objectives:
        t0 = time.time()
        entry: dict = {"exp27_selected_hp": None, "exp27_test_preds": {}, "cv5_fold_hps": [], "cv5_oof_preds": {}}

        if "exp27" in wanted_splits:
            tr_idx = [it for it in items_ordered if targets[it]["exp27_split"] == "train"]
            va_idx = [it for it in items_ordered if targets[it]["exp27_split"] == "val"]
            te_idx = [it for it in items_ordered if targets[it]["exp27_split"] == "test"]
            trva_idx = tr_idx + va_idx

            best_hp = None
            for lr in LRS:
                preds = fit_and_predict_lora(
                    judge, [prefixes[i] for i in tr_idx],
                    np.stack([targets[i]["p_emp"] for i in tr_idx]),
                    [prefixes[i] for i in va_idx],
                    obj, lr, steps, eval_steps, seed=101,
                )
                va_p = np.stack([targets[i]["p_emp"] for i in va_idx])
                for st, q in preds.items():
                    score = rps_np(q, va_p)
                    if best_hp is None or score < best_hp[0]:
                        best_hp = (score, lr, st)
            _, best_lr, best_st = best_hp
            te_preds = fit_and_predict_lora(
                judge, [prefixes[i] for i in trva_idx],
                np.stack([targets[i]["p_emp"] for i in trva_idx]),
                [prefixes[i] for i in te_idx],
                obj, best_lr, best_st, [best_st], seed=202,
            )[best_st]
            for idx_i, it in enumerate(te_idx):
                q = te_preds[idx_i]
                entry["exp27_test_preds"][it] = {"probs": [round(float(x), 6) for x in q], "E": round(float(q @ GRID_NP), 6), "lr": best_lr, "steps": best_st}
            entry["exp27_selected_hp"] = {"lr": best_lr, "steps": best_st, "val_rps": round(best_hp[0], 6)}
            print(f"[LoRA {obj}] exp27 done ({time.time()-t0:.1f}s) hp=({best_lr},{best_st}) val_rps={best_hp[0]:.4f}", flush=True)

        for f in range(5):
            if str(f) not in wanted_splits:
                continue
            tf = time.time()
            in_val_f = (f + 1) % 5
            itr = [it for it in items_ordered if targets[it]["cv5_fold"] not in (f, in_val_f)]
            iva = [it for it in items_ordered if targets[it]["cv5_fold"] == in_val_f]
            otr = [it for it in items_ordered if targets[it]["cv5_fold"] != f]
            ote = [it for it in items_ordered if targets[it]["cv5_fold"] == f]
            f_best = None
            for lr in LRS:
                preds = fit_and_predict_lora(
                    judge, [prefixes[i] for i in itr],
                    np.stack([targets[i]["p_emp"] for i in itr]),
                    [prefixes[i] for i in iva],
                    obj, lr, steps, eval_steps, seed=300 + f,
                )
                iva_p = np.stack([targets[i]["p_emp"] for i in iva])
                for st, q in preds.items():
                    sc = rps_np(q, iva_p)
                    if f_best is None or sc < f_best[0]:
                        f_best = (sc, lr, st)
            _, f_lr, f_st = f_best
            entry["cv5_fold_hps"].append({"fold": f, "inner_val_rps": round(f_best[0], 6), "lr": f_lr, "steps": f_st})
            ote_preds = fit_and_predict_lora(
                judge, [prefixes[i] for i in otr],
                np.stack([targets[i]["p_emp"] for i in otr]),
                [prefixes[i] for i in ote],
                obj, f_lr, f_st, [f_st], seed=400 + f,
            )[f_st]
            for idx_i, it in enumerate(ote):
                q = ote_preds[idx_i]
                entry["cv5_oof_preds"][it] = {"probs": [round(float(x), 6) for x in q], "E": round(float(q @ GRID_NP), 6), "fold": f, "lr": f_lr, "steps": f_st}
            print(f"[LoRA {obj}] cv5 fold={f} done ({time.time()-tf:.1f}s) hp=({f_lr},{f_st}) val_rps={f_best[0]:.4f}", flush=True)

        all_out[obj] = entry

    suffix = f"_{tag}" if tag else ""
    out_path = work_dir / f"qwen3_4b_lora_{'_'.join(objectives)}{suffix}.json"
    out_path.write_text(json.dumps(all_out, indent=2))
    print(f"[LoRA] Saved {out_path} in {time.time()-t0:.1f}s", flush=True)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--work-dir", default="/lfs/mercury2/0/brando9/exp28_ttj")
    ap.add_argument("--cache-dir", default="/tmp/exp28_ttj_cache")
    ap.add_argument("--phase", required=True, choices=["sanity", "logit_4b", "logit_8b", "extract_4b", "train_lora_4b"])
    ap.add_argument("--max-seq-len", type=int, default=6144)
    ap.add_argument("--steps", type=int, default=DEFAULT_STEPS)
    ap.add_argument("--objectives", default="ce,rps,pearson")
    ap.add_argument("--splits", default="exp27,0,1,2,3,4")
    ap.add_argument("--tag", default="")
    args = ap.parse_args()

    work_dir = Path(args.work_dir)
    cache_dir = Path(args.cache_dir)
    cache_dir.mkdir(parents=True, exist_ok=True)
    items = [json.loads(l) for l in (work_dir / "artifacts_all175.jsonl").read_text().splitlines() if l.strip()]
    controls = [json.loads(l) for l in (work_dir / "requests_h4_controls.jsonl").read_text().splitlines() if l.strip()]

    if args.phase == "logit_4b":
        run_logit_4b(work_dir, items, args.max_seq_len)
    elif args.phase == "logit_8b":
        run_logit_8b(work_dir, items, args.max_seq_len)
    elif args.phase == "train_lora_4b":
        targets = load_ratings_targets(work_dir)
        run_train_lora_4b(work_dir, cache_dir, targets, args.objectives.split(","), args.max_seq_len, args.steps, args.splits, args.tag)
    else:
        with sdpa_kernel(SDPBackend.MATH):
            if args.phase == "sanity":
                run_sanity(work_dir, items, controls)
            elif args.phase == "extract_4b":
                run_extract_4b(cache_dir, items, args.max_seq_len)


if __name__ == "__main__":
    main()
