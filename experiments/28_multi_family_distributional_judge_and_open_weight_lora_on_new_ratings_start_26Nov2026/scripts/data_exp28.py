"""Experiment 28: Leak-free data loader assembling human ratings, H4 multi-family predictions,
H2/H3 legacy baselines, open-weight Qwen3 single-pass logit & OOF LoRA predictions, and structural features.
"""
from __future__ import annotations

import csv
import json
from pathlib import Path
import numpy as np
import distlib as dl

EXP28 = Path(__file__).resolve().parents[1]
DATA_DIR = EXP28 / "data_11-26-2026"
RES_DIR = EXP28 / "results"


def _load_h4_jsonl(path: Path) -> dict[str, list[dict]]:
    out: dict[str, list[dict]] = {}
    if not path.exists():
        return out
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        o = json.loads(line)
        if o.get("status") != "ok":
            continue
        it = o["id"].split("#r")[0]
        out.setdefault(it, []).append(o["parsed"])
    return out


def _probs_from_h4_list(plist: list[dict] | None) -> tuple[np.ndarray, float, float]:
    if not plist:
        return np.full(6, 1.0 / 6.0), 2.5, 2.5
    probs = np.mean([np.asarray(p["probs"], dtype=np.float64) for p in plist], axis=0)
    probs = dl.smooth(probs, eps=1e-6)
    e = float(probs @ dl.GRID)
    f = float(np.mean([p["final_score_0_5"] for p in plist]))
    return probs, e, f


def load_bundle(include_test: bool = True, h4_dir: Path = RES_DIR, require_complete: bool = True) -> dict:
    """Load all aligned 175 artifacts (or only non-test 105 artifacts when include_test=False)."""
    rows = []
    for st in ("old", "new"):
        with (DATA_DIR / f"human_ratings_{st}_11-26-2026.csv").open() as f:
            for r in csv.DictReader(f):
                if not include_test and r["exp27_split"] == "test":
                    continue
                rat = [int(x) for x in r["ratings_sorted_0to5_rater_identity_removed"].split()]
                rows.append({
                    "item": r["item"],
                    "task": r["task"],
                    "set": st,
                    "exp27_split": r["exp27_split"],
                    "cv5_fold": int(r["cv5_fold"]),
                    "ratings": rat,
                })
    rows.sort(key=lambda r: r["item"])
    ix = {r["item"]: i for i, r in enumerate(rows)}
    n = len(rows)

    # H2 features
    js = {}
    with (DATA_DIR / "judge_scores_h2_11-26-2026.csv").open() as f:
        for r in csv.DictReader(f):
            if r["item"] in ix:
                js.setdefault((r["item"], r["judge"]), []).append(int(r["score_0to5"]))

    # Edit similarity
    ed = {}
    with (DATA_DIR / "edit_distance_feature_11-26-2026.csv").open() as f:
        for r in csv.DictReader(f):
            ed[r["item"]] = float(r["edit_similarity"])

    # Structural features
    st_feat = {}
    with (DATA_DIR / "structural_features_11-26-2026.csv").open() as f:
        for r in csv.DictReader(f):
            st_feat[r["item"]] = {k: float(v) if k != "item" else v for k, v in r.items()}

    # H3 Astra features (Exp 27)
    h3_map = {}
    with (DATA_DIR / "h3_features_astra_11-26-2026.csv").open() as f:
        for r in csv.DictReader(f):
            probs = dl.smooth(np.array([float(r[f"p{k}"]) for k in range(6)], dtype=np.float64), eps=1e-6)
            h3_map[r["item"]] = {
                "probs": probs,
                "h3_e": float(probs @ dl.GRID),
                "h3_s": float(r["h3_score"]),
            }

    # Track 4A H4 frontier lanes
    h4_lanes = {}
    for lane in ("codex_astra", "agy_argon", "agy_opus"):
        p = h4_dir / f"h4_{lane}_11-26-2026.jsonl"
        h4_lanes[lane] = _load_h4_jsonl(p)

    # Track 4B Qwen3 single-pass logits (loaded from h4_dir when overridden, else RES_DIR)
    qwen_logits = {}
    for key in ("qwen3_4b", "qwen3_8b"):
        qp = h4_dir / f"{key}_logit_6144.json"
        if qp.exists():
            qwen_logits[key] = {o["item"]: o for o in json.loads(qp.read_text())}
        else:
            qwen_logits[key] = {}

    P = np.zeros((n, 6), dtype=np.float64)
    C = np.zeros((n, 6), dtype=np.float64)
    for i, r in enumerate(rows):
        cnt = np.bincount(r["ratings"], minlength=6).astype(np.float64)
        C[i] = cnt
        P[i] = cnt / cnt.sum()

    def _arr_probs(getter):
        return np.stack([getter(r["item"]) for r in rows])

    p_h4_astra = _arr_probs(lambda it: _probs_from_h4_list(h4_lanes["codex_astra"].get(it))[0])
    p_h4_argon = _arr_probs(lambda it: _probs_from_h4_list(h4_lanes["agy_argon"].get(it))[0])
    p_h4_opus = _arr_probs(lambda it: _probs_from_h4_list(h4_lanes["agy_opus"].get(it))[0])

    # Single-pass Qwen3 logits
    def _q_probs(key, it):
        rec = qwen_logits.get(key, {}).get(it)
        if rec is None:
            return np.full(6, 1.0 / 6.0)
        return dl.smooth(np.asarray(rec["probs"], dtype=np.float64), eps=1e-6)

    def _q_onehot(key, it):
        rec = qwen_logits.get(key, {}).get(it)
        if rec is None:
            return np.full(6, 1.0 / 6.0)
        oh = np.zeros(6, dtype=np.float64)
        oh[int(rec["argmax_digit"])] = 1.0
        return dl.smooth(oh, eps=1e-6)

    p_q4b = _arr_probs(lambda it: _q_probs("qwen3_4b", it))
    p_q8b = _arr_probs(lambda it: _q_probs("qwen3_8b", it))
    p_q4b_oh = _arr_probs(lambda it: _q_onehot("qwen3_4b", it))
    p_q8b_oh = _arr_probs(lambda it: _q_onehot("qwen3_8b", it))

    # Scalar & structural features
    h2_astra = np.array([np.mean(js[(r["item"], "H2_astra")]) for r in rows], dtype=np.float64)
    h2_opus = np.array([np.mean(js[(r["item"], "H2_opus")]) for r in rows], dtype=np.float64)
    h3_e = np.array([h3_map[r["item"]]["h3_e"] for r in rows], dtype=np.float64)
    h3_s = np.array([h3_map[r["item"]]["h3_s"] for r in rows], dtype=np.float64)
    p_h3_astra = np.stack([h3_map[r["item"]]["probs"] for r in rows])
    edit = np.array([ed[r["item"]] for r in rows], dtype=np.float64)
    is_new = np.array([1.0 if r["set"] == "new" else 0.0 for r in rows], dtype=np.float64)

    cand_excess = np.array([st_feat[r["item"]]["excess_thm_log"] for r in rows], dtype=np.float64)
    cand_sorry = np.array([st_feat[r["item"]]["cand_sorry_count"] for r in rows], dtype=np.float64)
    ident_jac = np.array([st_feat[r["item"]]["ident_jaccard"] for r in rows], dtype=np.float64)
    stmt_seq_sim = np.array([st_feat[r["item"]]["stmt_seq_sim"] for r in rows], dtype=np.float64)

    e_astra = p_h4_astra @ dl.GRID
    e_argon = p_h4_argon @ dl.GRID
    e_opus = p_h4_opus @ dl.GRID
    e_q4b = p_q4b @ dl.GRID
    e_q8b = p_q8b @ dl.GRID
    e_stack4 = np.column_stack([e_astra, e_argon, e_opus, e_q8b])
    judge_std4 = np.std(e_stack4, axis=1)
    astra_opus_gap = np.abs(e_astra - e_opus)

    # Scalar dictionary for flexible feature-set selection
    feats = {
        "e_astra": e_astra,
        "e_argon": e_argon,
        "e_opus": e_opus,
        "e_q4b": e_q4b,
        "e_q8b": e_q8b,
        "h2_astra": h2_astra,
        "h2_opus": h2_opus,
        "h3_e": h3_e,
        "h3_s": h3_s,
        "edit": edit,
        "excess_thm_log": cand_excess,
        "cand_sorry_count": cand_sorry,
        "ident_jaccard": ident_jac,
        "stmt_seq_sim": stmt_seq_sim,
        "judge_std4": judge_std4,
        "astra_opus_gap": astra_opus_gap,
        "is_new": is_new,
    }
    dists = {
        "h4_astra": p_h4_astra,
        "h4_argon": p_h4_argon,
        "h4_opus": p_h4_opus,
        "h3_astra": p_h3_astra,
        "qwen3_4b": p_q4b,
        "qwen3_8b": p_q8b,
        "qwen3_4b_oh": p_q4b_oh,
        "qwen3_8b_oh": p_q8b_oh,
    }
    has_lanes = {k: sum(1 for r in rows if r["item"] in h4_lanes[k]) for k in h4_lanes}
    has_qwen = {k: sum(1 for r in rows if r["item"] in qwen_logits[k]) for k in qwen_logits}
    if require_complete:
        for k, cnt in has_lanes.items():
            assert cnt == n, f"Incomplete H4 lane {k}: {cnt}/{n}"
        for k, cnt in has_qwen.items():
            assert cnt == n, f"Incomplete Qwen lane {k}: {cnt}/{n}"
    return {
        "rows": rows,
        "n": n,
        "item": np.array([r["item"] for r in rows]),
        "task": np.array([r["task"] for r in rows]),
        "set": np.array([r["set"] for r in rows]),
        "exp27_split": np.array([r["exp27_split"] for r in rows]),
        "cv5_fold": np.array([r["cv5_fold"] for r in rows], dtype=int),
        "is_new": is_new,
        "P": P,
        "C": C,
        "feats": feats,
        "dists": dists,
        "has_lanes": has_lanes,
        "has_qwen": has_qwen,
    }
