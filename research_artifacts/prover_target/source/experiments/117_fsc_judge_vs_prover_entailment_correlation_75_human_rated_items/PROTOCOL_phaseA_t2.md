<!-- TLDR: Locked amendment for experiment 117 phase A tier T2: two cached open provers (Goedel-Prover-V2-8B with 32 new samples, DeepSeek-Prover-V2-7B with 32 samples) on the 20 train-item goals still open after T1, then the same G2 gate; $0 at Vals, no model download. -->
# Folder 117 — PROTOCOL amendment, phase A tier T2 (LOCKED before any T2 output)

**Doc link:** <https://github.com/brando90/veribench/blob/main/experiments/117_fsc_judge_vs_prover_entailment_correlation_75_human_rated_items/PROTOCOL_phaseA_t2.md>

This amendment is written after the T1 result on the 10 train items and before any T2 generation. It changes nothing in [PROTOCOL_phaseA_t1.md](PROTOCOL_phaseA_t1.md) except adding tier T2. That protocol's G2 outcome was decided 10/30 = 0.333, which falls in its "add T2 before going on" band (README step 4). Authorization: Brando's 10-15-2026 go for $0-at-Vals work, relayed by his "Langston cost doc" session. Only models already cached on SNAP are used (no download).

## Scientific question (locked)

Unchanged from [PROTOCOL_phaseA_t1.md](PROTOCOL_phaseA_t1.md).

**Gate G2 after T2**, measured as `(proved + refuted) / 30` statable agent-dependent goals on the same 10 train items:
- **≥ 0.50:** the full phase A may run. It needs a separate locked amendment with its GPU budget.
- **< 0.50:** phase A stops. The write-up says the open-prover tiers decide too few goals at this budget to test the judge on these outputs. The train items are not used again to tune tiers.

## Locked parameters

| Parameter | Value |
|---|---|
| Goals | the 20 statable agent-dependent goals still `unknown` after T1 in `expt_v1/work/g2v2_t1check/results.jsonl`, with the same T1 prompt text (`expt_v1/results/t1_g2/prompts.jsonl`) |
| T2 model A | `Goedel-LM/Goedel-Prover-V2-8B` revision `dfd02e6271a58375dfbf3ece0175277cf6b6a89a`, n = 32, seed 1 (new samples; T1 used seed 0) |
| T2 model B | `deepseek-ai/DeepSeek-Prover-V2-7B` revision `a8d9e14432b2e8dd9df2a4d4e70f1ba9bc8d9b7b`, n = 32, seed 1, same prompt (its documented format matches Goedel's) |
| Sampling, both models | temperature 1.0, top-p 0.95, max 16,384 new tokens, context 32,768, bfloat16, vLLM 0.21.0, one GPU per model, `gpu_memory_utilization` 0.85 |
| Proof extraction and check | unchanged: tactic block after `theorem vb117_goal … := by`, elaborated against the exact goal term (harness v2.1, sha256 `544cc06d93d94e1447db253a9f61abbbdf14bdf45a27a83fd7cc9513d9114997`), kernel check, axiom audit |
| GPU budget | ≤ 6 GPU-hours for T2 on the 10 train items |
| Vals spend | $0 |

## Pass/fail / abort rules

As in [PROTOCOL_phaseA_t1.md](PROTOCOL_phaseA_t1.md). Send `[RUN START]`/`[RUN DONE]` emails.
