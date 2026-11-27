# Rank the next human ratings by judge-ensemble uncertainty, and estimate when the held-out RPS gain would exclude 0

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/30_rank_next_human_ratings_by_judge_ensemble_uncertainty_and_power_curve_for_the_held_out_rps_gain_start_27Nov2026/README.md>

**TLDR:** The next ratings on the 100 new artifacts should avoid items the logged judges already call a five. Extra ratings on the same 20 held-out tasks do not push the ranked probability score interval below 0. A planning extrapolation crosses at 23 tasks. Result dated 11-27-2026. CPU only, $0.

**Date:** 11-27-2026.

## Question

New-set human ratings are 185/250 fives (74.0%). Experiment 27's held-out ranked probability score (RPS) gain is about -0.035 with a task-bootstrap interval that still reaches +0.002. Which unfilled rows should a rater do next, and how many more ratings or tasks would make that upper bound negative?

## Result

[RESULTS.md](RESULTS.md). The priority CSV is [results/next_ratings_priority_top25_11-27-2026.csv](results/next_ratings_priority_top25_11-27-2026.csv). The derivation of the rank score, the RPS, and the reason a task bootstrap does not shrink when more ratings are added to the same tasks is [derivation/active_selection_and_rps_power_11-27-2026.pdf](derivation/active_selection_and_rps_power_11-27-2026.pdf).

The top item is `native-heavy-11-11-2026__item045` (heap sort): H2 Astra expects 3 and H2 Opus expects 5. The top 25 artifacts are 21/61 fives. The bottom 25 are 66/70 fives. Simulated extra ratings through +2,240 on the 20 test tasks leave the median upper bound near +0.002. The planning extrapolation reaches an upper bound below 0 at 23 tasks. That extrapolation is not a certification.

## Run

```bash
python3 scripts/run_analysis.py
```

Inputs are the frozen tables in experiments 25, 27, 28 and 29. No model call. Predictions are in [PREREG.md](PREREG.md), written before the measurement.
