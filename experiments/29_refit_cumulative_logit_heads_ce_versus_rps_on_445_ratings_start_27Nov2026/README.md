# Experiment 29: Refit cumulative-logit heads by cross-entropy and by ranked probability score on 445 ratings

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/29_refit_cumulative_logit_heads_ce_versus_rps_on_445_ratings_start_27Nov2026/README.md>

**TLDR:** CPU refit, on the ratings already in the repo (195 old + 250 new), of cumulative-logit heads selected by validation ranked probability score. The pre-registered 20-task primary does **not** clear the bar (its cross-entropy is worse than the set-aware constant). The H3-free 50-task nested head **does**: RPS 0.0684 versus 0.1186, paired \(-0.0502\) \([-0.0726, -0.0290]\). $0. No new model call.

## Links

- Pre-registration, including the sigmoid-clip amendment written before any test score: [PREREG.md](PREREG.md)
- Full report: [results.md](results.md)
- Prior held-out search (247 new ratings, F8 RPS 0.075): [experiment 27](../27_build_a_judge_that_beats_the_constant_forecast_on_held_out_tasks_old_new_ratings_start_24Nov2026/RESULTS_11-24-2026.md)
- Already on main before this run (445 ratings, H4 and open-weight heads): [experiment 28](../28_multi_family_distributional_judge_and_open_weight_lora_on_new_ratings_start_26Nov2026/RESULTS_11-26-2026.md)

## What was compared

Heads are cumulative logits, \(P(r \le k) = \mathrm{sigmoid}((\theta_k - w \cdot x) / T)\), fit by cross-entropy or by ranked probability score, with an L2 penalty and a mixture toward a constant. A log-pool of cached probability vectors was in the same menu. Cohort indicators, cohort-specific heads, and shrinkage toward the set-aware constant were scored and were not eligible to be the primary. Features are cached H2, H3 and H4 scores plus structural counts. Correlation was not a training objective.

The 20-task split is experiment 27's split. It was already scored in experiments 27 and 28. The 50-task folds are experiment 28's folds. H3 is used on the 20-task split and excluded from the 50-task pass.

## Reproducibility

```bash
python3 scripts/build_snapshot.py
python3 -m unittest tests/test_heads_and_join.py
python3 scripts/run_experiment.py --stage select
python3 scripts/run_experiment.py --stage eval
python3 scripts/run_experiment.py --stage nested
```
