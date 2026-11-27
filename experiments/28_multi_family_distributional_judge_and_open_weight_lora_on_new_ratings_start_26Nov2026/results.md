# Experiment 28 live results ledger: Multi-family distributional judge and open-weight LoRA on updated human ratings

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/28_multi_family_distributional_judge_and_open_weight_lora_on_new_ratings_start_26Nov2026/results.md>

**Status:** COMPLETE — Mega QA Stages 1–3 reconciled (11-26-2026 18:18 PST)
**Last updated:** 11-26-2026 18:18 PST
**Rule 92 Google Doc:** [Trustworthy judge, 445 old+new human ratings (11-26-2026)](https://docs.google.com/document/d/1Ah4RFGyGyavSLmiPjCLz6lw7B1BYepGEErdhPoizlMM/edit?tab=t.0) (currently Restricted HTTP `401` on anonymous export until owner toggles Anyone-with-link Viewer)

## Phase Status

| Phase | Status | Scope & Notes |
|---|---|---|
| 1. Live human-rating sync (Exp 09) | DONE | 33 manifest Sheets verified (`250` numeric ratings across 6 non-coordinator raters: 100, 100, 30, 16, 3, 1; `74.0%` are `5`s); empty sheets verified `0/100` (`5e5d3ff`). |
| 2. Pre-registration & anonymised data freeze | DONE | `PREREG.md`, `data_11-26-2026/` (`175` artifacts, `50` tasks, `445` ratings), `exp27_split` + `cv5_fold`, cached `H2`/`H3` features committed (`0414a74`). Zero rater names in current files (early `PREREG.md` occurrence scrubbed in `df7f6af`). |
| 3. Matched input bundle, SHA-256 audit & `H4` controls | DONE | `175/175` SHA-256 input hashes verified (`results/input_hash_audit_11-26-2026.json`), `structural_features_11-26-2026.csv`, zero-demo `H4` (`sys_sha256=d36bc4e1f456`), `20` Karpathy controls (`7855746`). |
| 4A. Multi-family `H4` frontier judge calls (`$0` plans) | DONE | `175/175` valid responses each from `codex_astra` (`gpt-6-astra` high), `agy_argon` (`gemini-4-argon-high`), and `claude-opus-5-5` (`165` `agy` + `10` `claude_opus_cli` + 3 overlap checks); `5/5` passed 4 directional control mean bars, `2/5` passed `label_in_prompt r >= 0.99`; `k=3` repeats `ICC(1,1) >= 0.9949`. |
| 4B. `Qwen3-4B/8B` single-pass logit & CE/RPS/Pearson LoRA (`mercury2`) | DONE | `175/175` single-pass logit readouts (`Qwen3-4B`, `Qwen3-8B` 2-GPU split, `max_seq_len=6144`), left-pad prob parity `0.00313`, and 6-GPU parallel Top-4-Block LoRA (`CE`, `RPS`, `Pearson`) (`b7a1b10`; deviations logged in `PREREG.md` Amendment 2; open-weight research ablation under `AGENTS.md` frontier rule disclosure). |
| 5. Nested CV search, freeze & final evaluation | DONE | Non-test inner-CV selected `G9_h4_3fam_q8b_global` (`RPS=0.0743`, PREREG Primary) and `C7_h4_3fam_uncert` (`RPS=0.0721`, Sensitivity), locked in `FREEZE_11-26-2026.md` (`94c5cd8`), reconciled under Amendment 2: `exp27_test` `G9 RPS 0.0729 vs 0.1088` (**Promising**, ties `F8 0.0737`, `F9` `0.0659`/`0.0706` vs `C7 0.0728`); H3-free 50-task `cv5` OOF `nested_winner_global 0.0704` (`0/10,000 >= 0` vs `0.1186`, `-0.0076, p=0.0364` vs `F3`) & post-hoc all-frontier `nested_frontier_global 0.0685` (`p=0.0214` vs `F8`, `p=0.0036` vs `F3`). See [RESULTS_11-26-2026.md](RESULTS_11-26-2026.md). |
| 6. Reports, Mega Tech Report PDF & 3-stage Mega QA | DONE | Stages 1–3 Mega QA (`gpt-6-astra` ultra -> `agy` Orchestrator Carbon -> `claude-opus-5-5` high) completed; Amendment 2 CPU patch resolved all critical/major defects; Rule 92 Google Doc, `RESULTS_11-26-2026.md`, `latex/results/28_*.tex`, and `mega_tech_report.pdf` updated & verified (`8/8` unit tests, `check_project.py`). See [QA_SYNTHESIS_11-26-2026.md](qa_mega_11-26-2026/QA_SYNTHESIS_11-26-2026.md). |

**TLDR-end:** [ttj: exp 28 distributional judge] Reconciled under 3-stage Mega QA (Amendment 2): `exp27_test` registered Global `G9` reaches `RPS=0.0729 vs 0.1088` constant (`-0.0360 [-0.0746, +0.0011]`, **Promising**, tying `F8 0.0737`), while strict H3-free 50-task nested OOF reaches `0.0704` (and post-hoc all-frontier `0.0685`, clearing `const`, H3-free `F3`, and `F8` at `p<=0.0214`); LoRA `CE > Pearson` holds on both splits (`p=0.0002`), while matched `(M+K)` head `CE` beats `Pearson` on `CE`/`TVD` with `dRPS` crossing zero (`p=0.0786`).
