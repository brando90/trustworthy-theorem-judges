# Review the "0.6, 0.8, 0.8" judge correlations using old and new human ratings — 11-24-2026

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/26_how_new_and_old_human_ratings_fix_06_08_08_and_expand_5metric_eval_start_24Nov2026/README.md>

**TLDR:** Documents limitations of the historical `"0.6, 0.8, 0.8"` train/validation/test Spearman correlations and descriptive checks on the `11-24-2026` human-rating sync (`247` numeric ratings over `100` files and `25` tasks in `09_prepare_packets_and_collect_human_ratings_start_28Sep2026`). Reports empirical inter-rater agreement (normalized ranked probability score, `RPS`, `0.0760`), theorem-count baselines, and the `cert-judge` Experiment 39 comparison using `RPS`, cross-entropy (`CE`), and total variation distance (`TVD`). `RPS` and `CE` are proper scoring rules; `TVD` compares distributions. Evaluating frozen judges on the new cohort remains pending; these checks do not establish the causes of the historical correlations or validate a new judge (`$0.00` API spend, CPU-only, no differential testing, not Lean-checked proofs).

**Date:** `11-24-2026`
**As of 11-24-2026:** Retrospective analysis; new-cohort frozen-judge evaluation remains pending (see companion pre-registered pooled evaluation in [25_do_more_human_ratings_improve_judge_evaluation_old_new_pooled_start_24Nov2026](../25_do_more_human_ratings_improve_judge_evaluation_old_new_pooled_start_24Nov2026/PREREG.md); originally numbered 25 before renumbering after upstream commit `3f5a460`).

## Deliverables

- **[RESULTS_old_and_new_06_08_08_and_certjudge_11-24-2026.md](RESULTS_old_and_new_06_08_08_and_certjudge_11-24-2026.md):** Retrospective defense and reviewer Q1 report covering both `trustworthy-theorem-judges` and `cert-judge`, full provenance audit, empirical inter-rater agreement, zero-cost baselines, `10`-vs-`25`-task confidence interval scaling, Simpson's-paradox regime pooling analysis, `cert-judge` Experiment 39/51 bridge, and ready-to-run `evaluate_5metrics.py score-forecasts` command for frozen judges once scored.
- **[results.md](results.md):** Concise experiment lab-log record and summary tables.
- **[results/summary_old_vs_new_11-24-2026.json](results/summary_old_vs_new_11-24-2026.json):** Aggregate metrics JSON with public item identifiers retained only for response-anomaly provenance. The key-name guard rejects designated raw-rating fields; it is not a general privacy validator. No sealed mappings are exported.
- **[results/MEGA_QA_RECEIPT_11-24-2026.json](results/MEGA_QA_RECEIPT_11-24-2026.json):** Three-stage sequential Mega QA audit receipt (`agy` Carbon Orchestrator -> `codex` `gpt-6-astra` `ultra` -> fresh `agy` Carbon Orchestrator) and final deterministic check record.
- **[scripts/analyze_old_and_new_ratings.py](scripts/analyze_old_and_new_ratings.py)** & **[tests/test_analyze_old_and_new_ratings.py](tests/test_analyze_old_and_new_ratings.py):** Reproducible CPU-only analyzer and regression tests.

## Boundary and safety invariants

- **Strict evaluation-only lock:** Never tunes, selects hyperparameters on, or calibrates any judge on `09_prepare_packets_and_collect_human_ratings_start_28Sep2026`.
- **No `sealed/` item-to-agent leakage:** Resolves tasks and files exclusively via `item_id` joins against `Brando_Miranda__native_main_A1.csv` and verifies via `assert_no_private_leak` before writing JSON.
- **Compute constraints:** `$0.00` paid API spend, CPU-only, no Differential Testing (`DT`), not Lean-checked proofs.

## Reproduce (`$0.00`, CPU-only)

```bash
python3 -m unittest discover -v -s experiments/26_how_new_and_old_human_ratings_fix_06_08_08_and_expand_5metric_eval_start_24Nov2026/tests
python3 experiments/26_how_new_and_old_human_ratings_fix_06_08_08_and_expand_5metric_eval_start_24Nov2026/scripts/analyze_old_and_new_ratings.py
```

**TLDR-end:** [trustworthy-theorem-judges: experiments/26_how_new_and_old_human_ratings_fix_06_08_08_and_expand_5metric_eval_start_24Nov2026] Houses the quantitative Q1 defense analysis connecting historical `"0.6, 0.8, 0.8"` correlation failures, live `247`-rating multi-rater Experiment 09 evidence, and `cert-judge` distributional evaluation (`$0.00`, CPU-only).
