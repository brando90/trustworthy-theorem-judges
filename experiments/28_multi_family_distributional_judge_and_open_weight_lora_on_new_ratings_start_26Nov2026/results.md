# Experiment 28 live results ledger: Multi-family distributional judge and open-weight LoRA on updated human ratings

**Doc link:** <https://github.com/brandomiranda/trustworthy-theorem-judges/blob/main/experiments/28_multi_family_distributional_judge_and_open_weight_lora_on_new_ratings_start_26Nov2026/results.md>

**Status:** COMPLETE — pending Mega QA (11-26-2026 17:25 PST)
**Last updated:** 11-26-2026 17:25 PST

## Phase Status

| Phase | Status | Scope & Notes |
|---|---|---|
| 1. Live human-rating sync (Exp 09) | DONE | 33 manifest Sheets verified (`250` numeric ratings across 6 raters: 100, 100, 30, 16, 3, 1); `T30` verified `0/100` via Chrome (`5e5d3ff`). |
| 2. Pre-registration & anonymised data freeze | DONE | `PREREG.md`, `data_11-26-2026/` (`175` artifacts, `50` tasks, `445` ratings), `exp27_split` + `cv5_fold`, cached `H2`/`H3` features committed before any new run (`0414a74`). |
| 3. Matched input bundle, SHA-256 audit & `H4` controls | DONE | `175/175` SHA-256 input hashes verified (`results/input_hash_audit_11-26-2026.json`), `structural_features_11-26-2026.csv`, zero-demo `H4` (`sys_sha256=d36bc4e1f456`), `20` Karpathy controls (`7855746`). |
| 4A. Multi-family `H4` frontier judge calls (`$0` plans) | DONE | `175/175` valid responses each from `codex_astra` (`gpt-6-astra` high), `agy_argon` (`gemini-4-argon-high`), and `claude-opus-5-5` (`165` `agy` + `10` `claude_opus_cli` + 3 overlap checks), plus 20/20 Karpathy controls (all 4 families) and `k=3` repeats on 15 items (`ICC(1,1) >= 0.9949`). |
| 4B. `Qwen3-4B/8B` single-pass logit & CE/RPS/Pearson LoRA (`mercury2`) | DONE | `175/175` single-pass logit readouts (`Qwen3-4B`, `Qwen3-8B` 2-GPU split, `max_seq_len=6144`), left-pad prob parity `0.00313`, and 6-GPU parallel Top-4-Block LoRA (`CE`, `RPS`, `Pearson`) across `exp27_split` and `cv5_fold` (`b7a1b10`). |
| 5. Nested CV search, freeze & final evaluation | DONE | Non-test inner-CV selected `C7_h4_3fam_uncert` (`RPS=0.0721`) and global `G9_h4_3fam_q8b_global` (`RPS=0.0743`), locked in `FREEZE_11-26-2026.md` (`94c5cd8`), evaluated once: `exp27_split` `RPS 0.0728 vs 0.1088` (**Promising**); 50-task `cv5_fold` OOF `0.0689/0.0707 vs 0.1186` (**Works**, `p < 0.0001`). See [RESULTS_11-26-2026.md](RESULTS_11-26-2026.md). |
| 6. Reports, Mega Tech Report PDF & 3-stage Mega QA | IN PROGRESS | `RESULTS_11-26-2026.md`, `latex/results/28_*.tex`, and `mega_tech_report.pdf` built; running Codex Astra Ultra -> `agy` Carbon High Orchestrator -> Claude Opus 5.5 Mega QA. |

**TLDR-end:** [ttj: exp 28 distributional judge] Multi-family `H4` + `Qwen3-8B` `(M+K)` calibration reaches `RPS = 0.0728 vs 0.1088` on 20 held-out test tasks (`dRPS = -0.0360 [-0.0754, +0.0018]`, **Promising**) and `0.0689` (`0.0707` strict nested) vs `0.1186` across all 50 tasks via 5-fold OOF (`dRPS = -0.0497 [-0.0755, -0.0256], p < 0.0001`, **Works**), while CE strongly outperforms Pearson on both calibrator and `Qwen3-4B` LoRA (`dRPS = -0.0662, p = 0.0002`).
