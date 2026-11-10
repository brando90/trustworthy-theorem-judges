# Formulation ④ on cached judge scores: train-only cross-entropy mixture, repeated 5-fold CV

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/11_formulation4_train_only_ce_mixture_cv/README.md>

**TLDR:** Formulation ④ (fit the judge on all training tasks by loss, no validation split) was run on the five cached judges with repeated task-grouped 5-fold cross-validation. The cross-entropy-trained mixture beats the constant and the best single judge on ranked probability score (RPS), ties the equal-weight mixture on cross-entropy (CE), and is worse than the constant on CE. Retrospective, 0 model calls, $0, CPU only. Formulation ③ (validation selection) was not run.

Results and numbers: [results.md](results.md) and [results/results.json](results/results.json). Run log: [results/run_transcript.txt](results/run_transcript.txt).

## What was run

- Data: 75 artifacts, 25 tasks, 195 expert ratings (raters 1 to 3), five cached judges (H0 Sol, H0 Opus, H1 Sol, H2 Sol, H2 Opus), three cached scalar repeats each, from VeriBench commit `be287d9bb2f7bd35ba6db1b8735c9ba10d00eade`, experiment 100. Rebuilt by [scripts/build_dataset.py](scripts/build_dataset.py); the rebuild reproduces experiment 10's cached-judge test CE, RPS and TVD to six digits. The dataset itself stays private (individual ratings).
- Method: [scripts/run_formulation4.py](scripts/run_formulation4.py). 20 repeats of 5-fold cross-validation grouped by task (100 outer folds, 100 CE fits). In each fold, ④ fits the mixture weights by minimizing CE on all training-fold artifacts and is scored once on the untouched test fold. No validation split, no shrinkage and no inner selection. The CE solver and probability floor (1e-6) are experiment 03's of the sister repository `judges-dont-need-psychometrics-or-corr`, vendored under `scripts/vendor_exp03`.
- Comparators in the same folds: train-marginal constant, equal-weight mixture, and the single judge with the lowest train CE.
- Statistics: per-artifact metric averaged over the 20 repeats, then a 10,000-draw task bootstrap (25 tasks) of the paired difference; a result counts only if the 95% percentile interval excludes 0.

## Limits

Prior exposure: these ratings and the original split were already inspected in experiments 06, 07 and 10. Folds are grouped by task, not by task family (the 19 families cross tasks), so family leakage is possible. The cached judges come from one solver population and rater panel. This is not a test of ③ versus ④ and does not validate a deployable judge.
