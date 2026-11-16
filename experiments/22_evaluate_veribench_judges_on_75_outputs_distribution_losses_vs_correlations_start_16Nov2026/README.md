# Evaluate VeriBench judges on the 5-metric panel (`RPS`, `CE`, `TVD`, `Pearson`, `Spearman`)

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/22_evaluate_veribench_judges_on_75_outputs_distribution_losses_vs_correlations_start_16Nov2026/README.md>

**TLDR:** Explains why proper distributional losses — normalized Ranked Probability Score (`RPS`, primary), Cross-Entropy (`CE`, secondary), and Total Variation Distance (`TVD`, secondary) — replace correlations alone when evaluating formal specification coverage (`FSC`) judges, reports all 5 metrics (`RPS`, `CE`, `TVD`, `Pearson`, `Spearman` plus `Kendall tau-b`, `MAE`, `signed bias`, `ICC(A,1)`, `ICC(C,1)`) across the `"0.6, 0.8, 0.8"` historical selected judge and all 8 cached frontier judges/mixtures (`$0` paid API calls, CPU-only, `no DT`), and provides a reusable evaluator for incoming human ratings in `experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026`.

## Deliverables

- **[EVAL_DOCUMENT_5_METRICS_11-16-2026.md](EVAL_DOCUMENT_5_METRICS_11-16-2026.md):** Standalone methodology and justification document covering all 5 metrics, worked examples from [the correlation-vs-loss brief](https://claude.ai/artifact/Rg2hYLxYMGJAte7jcV7kKV) and [sister repository `judges-dont-need-psychometrics-or-corr`](https://github.com/brando90/judges-dont-need-psychometrics-or-corr), and CLI usage for new ratings.
- **[results.md](results.md):** Full measured results across `train / validation / test / test_ordinary / all_75`, all 8 frontier judges (`H0/H1/H2 Sol/Opus`, `gpt-6-astra`, `gpt-6.1-sol`, `gemini-4-argon`), `method2_pearson` vs `method4_ce`/`method4_rps` mixtures, `MSE` bias/scale/ordering decomposition, and probability-floor sensitivity (`eps=1e-6`, `1e-3`, `Laplace 0.5`).
- **[results/aggregates_5metrics.json](results/aggregates_5metrics.json):** Split-level aggregate JSON (programmatically guarded against exporting any individual human ratings).
- **[scripts/evaluate_5metrics.py](scripts/evaluate_5metrics.py)** & **[tests/test_evaluate_5metrics.py](tests/test_evaluate_5metrics.py):** Deterministic evaluator and synthetic-control unit tests (`5/5` passing).

## Reproduce (`$0` API calls, CPU-only)

```bash
python3 -m unittest discover -s experiments/22_evaluate_veribench_judges_on_75_outputs_distribution_losses_vs_correlations_start_16Nov2026/tests -v
python3 experiments/22_evaluate_veribench_judges_on_75_outputs_distribution_losses_vs_correlations_start_16Nov2026/scripts/evaluate_5metrics.py
```

Requires the private cached dataset at `~/judges-dont-need-psychometrics-or-corr/experiments/02_exp06_ce_vs_pearson_matched_budget_start_09Nov2026/private/historical_exp06/cached_v1/dataset.json` (SHA-256 recorded in `results/aggregates_5metrics.json`), `experiments/21_add_3_frontier_judges_to_pool_pearson_vs_ce_80_20_start_16Nov2026/results/judge_scores.csv`, NumPy `>= 2.2`, and SciPy `>= 1.16`.

**TLDR-end:** [ttj: experiments/22_evaluate_veribench_judges_on_75_outputs_distribution_losses_vs_correlations_start_16Nov2026] Houses the canonical 5-metric evaluation document, CPU-only VeriBench re-evaluations across cached judges/mixtures, and reusable `score-forecasts` tool for incoming ratings.
