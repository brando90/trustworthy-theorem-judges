# Experiment 28 live results ledger: Multi-family distributional judge and open-weight LoRA on updated human ratings

**Doc link:** <https://github.com/brandomiranda/trustworthy-theorem-judges/blob/main/experiments/28_multi_family_distributional_judge_and_open_weight_lora_on_new_ratings_start_26Nov2026/results.md>

**Status:** RUNNING (started 11-26-2026 15:54 PST)
**Last updated:** 11-26-2026 15:55 PST

## Phase Status

| Phase | Status | Scope & Notes |
|---|---|---|
| 1. Live human-rating sync (Exp 09) | DONE | 33 manifest Sheets verified (`250` numeric ratings across 6 raters: 100, 100, 30, 16, 3, 1); `T30` Max Sieb verified `0/100` via Chrome (`5e5d3ff`). |
| 2. Pre-registration & anonymised data freeze | DONE | `PREREG.md`, `data_11-26-2026/` (`175` artifacts, `50` tasks, `445` ratings), `exp27_split` + `cv5_fold`, cached `H2`/`H3` features committed before any new run. |
| 3. Matched input bundle, SHA-256 audit & `H4` controls | DONE | `175/175` SHA-256 input hashes verified (`results/input_hash_audit_11-26-2026.json`), `structural_features_11-26-2026.csv`, zero-demo `H4` (`sys_sha256=d36bc4e1f456`), `20` Karpathy controls. |
| 4A. Multi-family `H4` frontier judge calls (`$0` plans) | IN PROGRESS | Launching Karpathy controls + 175-artifact `H4` runs on `gpt-6-astra` (Codex), `gemini-4-argon-high` (Antigravity), `grok-4.7` (Grok) / `claude-opus-5-5-high` (Antigravity). |
| 4B. `Qwen3-8B` single-pass logit & CE/RPS/Pearson LoRA (`mercury2`) | IN PROGRESS | Preparing `mercury2` free GPUs (`0..7`) for single-pass logit readout + out-of-fold LoRA (`CE`, `RPS`, `Pearson`). |
| 5. Nested CV search, freeze & final evaluation | PENDING | Exp 27 split (inner CV -> freeze -> test once) + 50-task 5-fold nested OOF CV + Priority 2 vs 4 ablations. |
| 6. Reports, Mega Tech Report PDF & 3-stage Mega QA | PENDING | `RESULTS_11-26-2026.md`, `latex/results/28_*.tex`, `mega_tech_report.pdf`, Codex -> `agy` Carbon Orchestrator -> Claude Mega QA. |

**TLDR-end:** [ttj: exp 28 distributional judge] Pre-registering and freezing the 11-26-2026 pooled dataset (`175` artifacts, `50` disjoint tasks, `445` ratings: `195` old + `250` live Exp 09 ratings) before launching multi-family `H4` judge inference and `Qwen3-8B` single-pass logit/LoRA experiments.
