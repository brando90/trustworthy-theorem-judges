# Experiment 07: Experiment 1 metric table and scaling fit on cached judge scores

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/07_exp1_metrics/README.md>

**TLDR:** One table of nRMSE (scores/5), sqrt RPS, KL, constant-guess nRMSE, Pearson, Spearman and Kendall for the five cached scalar judges of experiment 06, with 10,000-resample task-level bootstrap intervals, plus a subsampling fit of l = E + A n^-alpha + B k^-beta. Zero new model calls, no paid API, no R^2, no DT, Gemini is not a judge. Results: [results.md](results.md).

Created 11-09-2026 for Brando Miranda's judge paper (his Nov 7 and Nov 8 voice notes and whiteboard photo). Computed by CPU scripts (Python 3, numpy, scipy); the cached judge scores come from the veribench experiment-100 runs at commit `be287d9`.

## Question

Which metric should be experiment 1 of the judge paper, and how many tasks and human ratings are needed to measure a judge's nRMSE precisely? The table compares metric families on the same cached judges; the fit uses subsampling of the same ratings.

## Data

75 artifacts, 25 tasks, three expert columns with 195 ratings (primary), five rater columns with 345 ratings (secondary). Per-item ratings and scores stay in the ignored `private/` directory; this folder holds aggregates only. Judge probabilities are histograms of three sampled repeats (no digit logprobs exist in the receipts), floored at eps = 1e-3.

## Run

```
VERIBENCH_SRC=/path/to/veribench@be287d9 ./run.sh
```

`run.sh` imports the private dataset with experiment 06's `import_cached.py`, then runs `scripts/exp1_metrics.py` (about 25 minutes of CPU for three panels at 10,000 resamples), `scripts/exp1_scaling.py` (about 1 hour, dominated by 500 refits) and `scripts/write_results.py`. Logs: `logs/`.

## Files

- `results.md`: tables, answers, limits.
- `results/metrics.json`, `results/scaling.json`, `results/import_audit.json`: aggregate outputs.
- `scripts/`: the three scripts above. `logs/`: run logs and the working transcript.
