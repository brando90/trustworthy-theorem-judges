# Fit five-judge mixtures to 75 rated outputs: Pearson versus ranked probability training

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/archive/10_fit_5_judge_mixtures_to_75_outputs_pearson_vs_ranked_probability/README.md>

**Placement, 11-11-2026:** retained while the sole coordinator reconciles the unique publication receipt in the existing detached worktree; the analysis itself is complete. See the [archive placement record](../README.md#reading-and-reproducing-historical-work).

**TLDR:** Fit methods 2 and 4 on the existing historical human ratings using the same five cached judge configurations, probability family and validation criterion. This is an offline retrospective probability-mixture experiment, not new semantic judge inference or validation on the incoming human collection.

Completed: the primary RPS difference is unresolved; validation selected method 4. See the [result and publication-scope receipt](results/ELIGIBILITY.json).

The [study definition](PROTOCOL.md) and [machine configuration](protocol.json) are fixed before fitting and test scoring. [Results](results.md) record actual completion and evidence. The [checkpoint](CKPT_practical_judge.md) carries execution state. All individual ratings, source-row traces and per-artifact forecasts remain in the approved private store.

The sister repository's [completed CE-versus-Pearson study](https://github.com/brando90/judges-dont-need-psychometrics-or-corr/blob/main/experiments/03_exp06_ce_vs_pearson_matched_budget/RESULTS_comparison.md) already fixes the numerical Pearson failure in a probability-mixture family. This experiment reuses its exact solver and adds a distinct ranked probability score (RPS) training condition, the original train/validation/test split, and common validation-selected shrinkage. It does not revise that completed study's cross-entropy (CE) primary endpoint or five-partition results.

## Reproduce

Use Python with NumPy and SciPy. For this machine, the verified interpreter is `/Users/brandomiranda/uv_envs/no-gold-ref-judge/bin/python3`.

```sh
python3 -m unittest discover -s experiments/archive/10_fit_5_judge_mixtures_to_75_outputs_pearson_vs_ranked_probability/tests -v
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 experiments/archive/10_fit_5_judge_mixtures_to_75_outputs_pearson_vs_ranked_probability/scripts/run.py \
  --data /absolute/authorized/private/dataset.json \
  --out /absolute/new/public_aggregate_results \
  --private-out /absolute/new/private_forecasts
```

The runner verifies the exact dataset, source and premeasurement file hashes and refuses to overwrite existing result directories. The runtime has no provider calls or network operations. The historical cache is not included in this public repository.

The exported model accepts the same five ordered sets of cached integer ratings, forms six-category histograms, applies the fixed probability-floor convention, and produces a weighted mixture shrunk toward the stored training marginal. Using new source-code artifacts would additionally require rerunning the exact historical prompts/models or a separately validated replacement; this experiment does not establish that transport or transfer.
