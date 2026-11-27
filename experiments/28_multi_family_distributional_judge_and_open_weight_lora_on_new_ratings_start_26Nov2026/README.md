# Experiment 28: Multi-family distributional judge, open-weight LoRA, and CE vs. Pearson on updated human ratings

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/28_multi_family_distributional_judge_and_open_weight_lora_on_new_ratings_start_26Nov2026/README.md>

**TLDR:** Pre-registered study (`11-26-2026`) reconciled under 3-stage Mega QA (**Amendment 2 post-hoc sensitivity**) evaluating uniform-harness multi-family `H4` zero-demo distributional judges (`gpt-6-astra`, `gemini-4-argon-high`, `claude-opus-5-5`), `Qwen3-4B/8B` single-pass token-logit readouts and out-of-fold LoRA (`CE` vs `RPS` vs `Pearson` on free `mercury2` GPUs), structural code/Lean features, and `(M+K)` logit-pool calibration on the pooled `50`-task / `175`-artifact / `445`-rating VeriBench corpus (`195` old + `250` live Exp 09 ratings). Verdict: **Promising** on the 20-task `exp27_split` held-out test (registered Global `G9` `RPS 0.0729 vs 0.1088` constant, `dRPS=-0.0360 [-0.0746, +0.0011], p=0.0560`, tying Exp 27 `F8` `0.0737`, while Exp 27 set-aware `F9` scores `0.0659`/`0.0706`); across all 50 tasks via clean strict H3-free nested 5-fold OOF (`cv5_fold`), Global `nested_winner_global` reaches `0.0704` (`0/10,000 >= 0` vs `0.1186` constant, MC floor `0.0002`; `-0.0076, p=0.0364` vs H3-free `F3`; `-0.0044 [-0.0098, +0.0012], p=0.1150` vs H3-exposed `F8`), and pure all-frontier `nested_frontier_global` (zero `Qwen3`, zero `H3`, zero `is_new`) reaches `0.0685` (`p=0.0214` vs `F8`, `p=0.0036` vs `F3`). On `Qwen3-4B` LoRA, `CE` beats `Pearson` on both splits (`p=0.0002`); on matched `(M+K)` head selection, `CE` beats `Pearson` on `CE` (`p=0.0014`) and `TVD` (`p=0.0094`) while `cv5` primary `dRPS` crosses zero (`p=0.0786`).

## Links
- Pre-registration, measurement contract & Amendment 2: [PREREG.md](PREREG.md)
- Pre-test freeze & post-freeze audit note: [FREEZE_11-26-2026.md](FREEZE_11-26-2026.md)
- Full results report: [RESULTS_11-26-2026.md](RESULTS_11-26-2026.md)
- Rule 92 Google Doc companion: [Trustworthy judge, 445 old+new human ratings (11-26-2026)](https://docs.google.com/document/d/1Ah4RFGyGyavSLmiPjCLz6lw7B1BYepGEErdhPoizlMM/edit?tab=t.0) (currently Restricted HTTP `401` on anonymous export until owner toggles Anyone-with-link Viewer)
- Mega QA 3-stage synthesis (`gpt-6-astra` ultra, `agy` Orchestrator Carbon, `claude-opus-5-5` high): [qa_mega_11-26-2026/QA_SYNTHESIS_11-26-2026.md](qa_mega_11-26-2026/QA_SYNTHESIS_11-26-2026.md)
- Live run ledger: [results.md](results.md)
- Anonymised frozen data (`11-26-2026`): [data_11-26-2026/](data_11-26-2026/)
- Prior study (Experiment 27, 247 new ratings): [27_build_a_judge_that_beats_the_constant_forecast_on_held_out_tasks_old_new_ratings_start_24Nov2026](../27_build_a_judge_that_beats_the_constant_forecast_on_held_out_tasks_old_new_ratings_start_24Nov2026/RESULTS_11-24-2026.md)
- Sister-repo methodology (`judges-dont-need-psychometrics-or-corr`): Experiments 29 and 36.

## Reproducibility
1. `python3 scripts/build_data_11_26.py` — freeze anonymised human ratings and splits (`195` old + `250` new).
2. `python3 scripts/build_h4_bundle.py` — verify `175/175` SHA-256 input hashes, extract structural features, render zero-demo `H4` prompts and Karpathy sanity controls.
3. Run Track 4A (`scripts/run_h4_frontier.py`) and Track 4B (`scripts/run_qwen_gpu_mercury2.py` on `mercury2`), then `python3 scripts/export_track4_results.py`.
4. `python3 scripts/search_inner_cv.py` -> freeze selection -> `python3 scripts/final_eval_exp28.py` (includes Amendment 2 H3-free nested OOF, pure all-frontier sensitivity, and matched-grid `(M+K)` head comparison).
5. `python3 -m unittest discover -s tests`.
