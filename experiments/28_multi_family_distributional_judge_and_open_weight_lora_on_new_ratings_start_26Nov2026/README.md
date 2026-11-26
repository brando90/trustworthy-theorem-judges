# Experiment 28: Multi-family distributional judge and open-weight LoRA on updated human ratings

**Doc link:** <https://github.com/brandomiranda/trustworthy-theorem-judges/blob/main/experiments/28_multi_family_distributional_judge_and_open_weight_lora_on_new_ratings_start_26Nov2026/README.md>

**TLDR:** Pre-registered study (`11-26-2026`) testing whether uniform-harness multi-family `H4` zero-demo distributional judges, `Qwen3-8B` single-pass token-logit readout + out-of-fold LoRA (`CE` vs `RPS` vs `Pearson` on free `mercury2` GPUs), structural code/Lean features, and `(M+K)` logit-pool proper-loss calibration beat the set-aware constant and Experiment 27's `F8` judge on the pooled `50`-task / `175`-artifact / `445`-rating VeriBench dataset (`195` old + `250` live Exp 09 ratings).

## Links
- Pre-registration & measurement contract: [PREREG.md](PREREG.md)
- Live run ledger: [results.md](results.md)
- Anonymised frozen data (`11-26-2026`): [data_11-26-2026/](data_11-26-2026/)
- Prior study (Experiment 27, 247 new ratings): [27_build_a_judge_that_beats_the_constant_forecast_on_held_out_tasks_old_new_ratings_start_24Nov2026](../27_build_a_judge_that_beats_the_constant_forecast_on_held_out_tasks_old_new_ratings_start_24Nov2026/RESULTS_11-24-2026.md)
- Sister-repo methodology (`judges-dont-need-psychometrics-or-corr`): Experiments 29 and 36.

## Reproducibility
1. `python3 scripts/build_data_11_26.py` — freeze anonymised human ratings and splits (`195` old + `250` new).
2. `python3 scripts/build_h4_bundle.py` — verify `175/175` SHA-256 input hashes, extract structural features, render zero-demo `H4` prompts and Karpathy sanity controls.
3. Run Track 4A (`scripts/run_h4_frontier.py`) and Track 4B (`scripts/run_qwen8b_logit_readout.py`, `scripts/run_qwen8b_lora_cv.py` on `mercury2`).
4. `python3 scripts/search_inner_cv.py` -> freeze selection -> `python3 scripts/final_eval_exp28.py`.
5. `python3 -m unittest discover -s tests`.
