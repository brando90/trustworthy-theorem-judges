# Experiment 27: Cursor high independent QA, 11-24-2026

Cursor `grok-4.7-high` completed successfully. All 63 comparisons with the frozen report match at three decimals: 45 RPS/CE/TVD point estimates (five forecasts on pooled, old and new test sets), plus 18 paired-bootstrap estimates and interval endpoints. No numerical mismatch at that precision was found. The largest absolute difference across these 63 values is 2.66e-06. The pre-registered verdict remains **promising**, because the paired RPS interval against the set-aware constant includes zero.

## Model, execution and input

- Model: `grok-4.7-high`; harness: Cursor Agent CLI, `--mode ask --output-format json --model grok-4.7-high`; lane: `personal-cursor`, included usage only. No separate effort setting was supplied (the receipt field is null).
- The 1500-second request completed 11-24-2026 at 16:47 PST. Cursor was instructed to read only `QA_TASK.md` and `qa_input.json`, excluding previous QA code and reported results, and returned self-contained Python. It did not execute its code. The caller inspected and executed the returned Python unchanged in an isolated directory against the same input. The comparison with frozen results was performed afterward.
- Script SHA-256: `aca27268c14dacd6374abc4616399b5facb22c3fffa5e7e9aa0604473cc39863`.
- Input SHA-256: `67b8dde95cb0fc32d23f7522fa325103c6aa33b9fdf94b308e61c3805116bad9`.
- Reproduce: place the unchanged `qa_cursor_high.py` beside `qa_input.json`, install numpy/scipy, and run `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 qa_cursor_high.py`; then compare `qa_cursor_high.json` with `../results/test_results_11-24-2026.json`. Only SciPy deprecation warnings occurred.
- RPS averages the five threshold terms including the human-distribution variance term. CE uses natural logs and the specified probability floor. TVD is a distribution distance; RPS and CE are proper scores. Artifacts have equal weight. Constants pool individual train+validation ratings; H2 pools Astra and Opus scores.

## RPS, CE, TVD: independent values versus frozen report

Values below are the independent recomputation. Each row matches all three frozen metric values at three decimals; exact frozen and independent values are in `cursor_high_comparison.json`. Correlations are secondary and were not part of the 63-value match count.

| Test set | Forecast | RPS | CE | TVD | Match RPS/CE/TVD | Spearman | Pearson |
|---|---|---|---|---|---|---|---|
| pooled | Final judge | 0.075070 | 0.969504 | 0.354948 | 3/3 match | 0.894325 | 0.909365 |
| pooled | Constant per set | 0.109965 | 1.188888 | 0.478664 | 3/3 match | not checked | not checked |
| pooled | Pooled constant | 0.170697 | 1.508718 | 0.602990 | 3/3 match | not checked | not checked |
| pooled | Uniform | 0.230952 | 1.791759 | 0.733333 | 3/3 match | not checked | not checked |
| pooled | Earlier H2 | 0.100237 | 4.115285 | 0.330954 | 3/3 match | 0.898860 | 0.897586 |
| old | Final judge | 0.134885 | 1.569246 | 0.490030 | 3/3 match | 0.895215 | 0.874230 |
| old | Constant per set | 0.179711 | 1.793773 | 0.658120 | 3/3 match | not checked | not checked |
| old | Pooled constant | 0.261913 | 2.158265 | 0.716416 | 3/3 match | not checked | not checked |
| old | Uniform | 0.175926 | 1.791759 | 0.677778 | 3/3 match | not checked | not checked |
| old | Earlier H2 | 0.190925 | 7.681909 | 0.583333 | 3/3 match | 0.829154 | 0.861026 |
| new | Final judge | 0.030209 | 0.519698 | 0.253637 | 3/3 match | 0.648453 | 0.938230 |
| new | Constant per set | 0.057656 | 0.735224 | 0.344072 | 3/3 match | not checked | not checked |
| new | Pooled constant | 0.102285 | 1.021558 | 0.517920 | 3/3 match | not checked | not checked |
| new | Uniform | 0.272222 | 1.791759 | 0.775000 | 3/3 match | not checked | not checked |
| new | Earlier H2 | 0.032222 | 1.440317 | 0.141670 | 3/3 match | 0.717924 | 0.926208 |

## Paired task bootstrap

Final judge minus baseline; negative favors the final judge. Whole tasks sampled with replacement, 10,000 draws, numpy default_rng seed 20261124, equal artifact weighting within each sampled multiset, percentile 95% intervals. Each estimate and both interval endpoints match the frozen report at three decimals.

| Baseline | RPS difference [95% CI] | CE difference [95% CI] | TVD difference [95% CI] | Match |
|---|---|---|---|---|
| Constant per set | -0.034895 [-0.075959, +0.002444] | -0.219384 [-0.458774, +0.009236] | -0.123716 [-0.204913, -0.055366] | 9/9 match |
| Earlier H2 | -0.025167 [-0.049291, -0.005410] | -3.145780 [-4.973874, -1.579688] | +0.023994 [-0.058767, +0.099131] | 9/9 match |

## Independent ordinal refit

The returned script fits the four selected F8 features on the 105 train+validation artifacts, using train+validation standardization, no L2 penalty and no constant mixture. It uses 16 deterministic starts and optimizer polishing; all five fitted thresholds are strictly increasing. This checks the fixed F8 refit, not the earlier 125-candidate selection.

| Forecast | RPS | CE | TVD |
|---|---|---|---|
| Independent refit | 0.075070599 | 0.969505319 | 0.354950244 |
| Frozen final_Q | 0.075070346 | 0.969504259 | 0.354948281 |
| Refit minus frozen | 0.000000253 | 0.000001060 | 0.000001963 |

Training+validation CE: 0.949774044. The refit reproduces each test metric within 2e-6. Individual coefficients are not causal effects; the H3 features are nearly collinear in this unpenalized fit.

## Split and input checks

| Split | Old artifacts / tasks | New artifacts / tasks | Total artifacts / tasks |
|---|---|---|---|
| train | 30 / 10 | 40 / 10 | 70 / 20 |
| val | 15 / 5 | 20 / 5 | 35 / 10 |
| test | 30 / 10 | 40 / 10 | 70 / 20 |

175 artifacts, 50 tasks; no task crosses splits or data sets, no missing human ratings, no duplicate artifact IDs. Exactly 70 test artifacts have final_Q; none outside test do. Maximum probability-sum error is 2.22e-16. All six explicit structural checks pass; fatal and warning lists are empty. These are checks of the supplied input, not an audit of upstream data use.

## All 63 match/mismatch comparisons

| Comparison | Independent | Frozen | Difference | Match at 3 decimals |
|---|---|---|---|---|
| pooled/final_Q/RPS | 0.075070346 | 0.075070346 | +0 | match |
| pooled/final_Q/CE | 0.969504259 | 0.969504259 | +0 | match |
| pooled/final_Q/TVD | 0.354948281 | 0.354948281 | +0 | match |
| pooled/constant_per_set/RPS | 0.109965348 | 0.109965348 | +0 | match |
| pooled/constant_per_set/CE | 1.188887827 | 1.188887827 | +5.72e-13 | match |
| pooled/constant_per_set/TVD | 0.478663912 | 0.478663912 | +0 | match |
| pooled/pooled_constant/RPS | 0.170696855 | 0.170696855 | +0 | match |
| pooled/pooled_constant/CE | 1.508718098 | 1.508718098 | +0 | match |
| pooled/pooled_constant/TVD | 0.602989617 | 0.602989617 | +0 | match |
| pooled/uniform/RPS | 0.230952381 | 0.230952381 | +0 | match |
| pooled/uniform/CE | 1.791759469 | 1.791759469 | +0 | match |
| pooled/uniform/TVD | 0.733333333 | 0.733333333 | +0 | match |
| pooled/h2/RPS | 0.100237451 | 0.100237451 | +0 | match |
| pooled/h2/CE | 4.115284721 | 4.115286107 | -1.39e-06 | match |
| pooled/h2/TVD | 0.330954157 | 0.330954157 | +0 | match |
| old/final_Q/RPS | 0.134885126 | 0.134885126 | +0 | match |
| old/final_Q/CE | 1.569245639 | 1.569245639 | +0 | match |
| old/final_Q/TVD | 0.490029697 | 0.490029697 | +0 | match |
| old/constant_per_set/RPS | 0.179711447 | 0.179711447 | +0 | match |
| old/constant_per_set/CE | 1.793772834 | 1.793772834 | +0 | match |
| old/constant_per_set/TVD | 0.658119658 | 0.658119658 | +0 | match |
| old/pooled_constant/RPS | 0.261912990 | 0.261912990 | +0 | match |
| old/pooled_constant/CE | 2.158264635 | 2.158264635 | +0 | match |
| old/pooled_constant/TVD | 0.716416040 | 0.716416040 | +0 | match |
| old/uniform/RPS | 0.175925926 | 0.175925926 | +0 | match |
| old/uniform/CE | 1.791759469 | 1.791759469 | +0 | match |
| old/uniform/TVD | 0.677777778 | 0.677777778 | +0 | match |
| old/h2/RPS | 0.190924687 | 0.190924687 | +0 | match |
| old/h2/CE | 7.681908915 | 7.681911571 | -2.66e-06 | match |
| old/h2/TVD | 0.583332994 | 0.583332994 | +0 | match |
| new/final_Q/RPS | 0.030209261 | 0.030209261 | +0 | match |
| new/final_Q/CE | 0.519698225 | 0.519698225 | +0 | match |
| new/final_Q/TVD | 0.253637220 | 0.253637220 | +0 | match |
| new/constant_per_set/RPS | 0.057655773 | 0.057655773 | +0 | match |
| new/constant_per_set/CE | 0.735224072 | 0.735224072 | +1e-12 | match |
| new/constant_per_set/TVD | 0.344072103 | 0.344072103 | +0 | match |
| new/pooled_constant/RPS | 0.102284753 | 0.102284753 | +0 | match |
| new/pooled_constant/CE | 1.021558195 | 1.021558195 | +0 | match |
| new/pooled_constant/TVD | 0.517919799 | 0.517919799 | +0 | match |
| new/uniform/RPS | 0.272222222 | 0.272222222 | +0 | match |
| new/uniform/CE | 1.791759469 | 1.791759469 | +0 | match |
| new/uniform/TVD | 0.775000000 | 0.775000000 | +0 | match |
| new/h2/RPS | 0.032222024 | 0.032222024 | +0 | match |
| new/h2/CE | 1.440316576 | 1.440317009 | -4.33e-07 | match |
| new/h2/TVD | 0.141670029 | 0.141670029 | +0 | match |
| paired/constant_per_set/RPS/point | -0.034895002 | -0.034895002 | +0 | match |
| paired/constant_per_set/RPS/ci_low | -0.075959056 | -0.075959056 | +0 | match |
| paired/constant_per_set/RPS/ci_high | 0.002443810 | 0.002443810 | -4.08e-17 | match |
| paired/constant_per_set/CE/point | -0.219383568 | -0.219383568 | -5.72e-13 | match |
| paired/constant_per_set/CE/ci_low | -0.458773968 | -0.458773968 | -4.72e-13 | match |
| paired/constant_per_set/CE/ci_high | 0.009236360 | 0.009236360 | -5.23e-13 | match |
| paired/constant_per_set/TVD/point | -0.123715631 | -0.123715631 | +0 | match |
| paired/constant_per_set/TVD/ci_low | -0.204912925 | -0.204912925 | +5.55e-17 | match |
| paired/constant_per_set/TVD/ci_high | -0.055365977 | -0.055365977 | -5.55e-17 | match |
| paired/h2/RPS/point | -0.025167105 | -0.025167105 | +0 | match |
| paired/h2/RPS/ci_low | -0.049291249 | -0.049291249 | +0 | match |
| paired/h2/RPS/ci_high | -0.005409818 | -0.005409818 | -6.07e-18 | match |
| paired/h2/CE/point | -3.145780462 | -3.145781848 | +1.39e-06 | match |
| paired/h2/CE/ci_low | -4.973873638 | -4.973875812 | +2.17e-06 | match |
| paired/h2/CE/ci_high | -1.579688219 | -1.579688962 | +7.44e-07 | match |
| paired/h2/TVD/point | 0.023994124 | 0.023994124 | +0 | match |
| paired/h2/TVD/ci_low | -0.058767224 | -0.058767224 | -1.11e-16 | match |
| paired/h2/TVD/ci_high | 0.099131398 | 0.099131398 | +0 | match |

## Limits

This verifies arithmetic, a fixed-model refit and structural split separation from the supplied input. It does not independently verify raw rating provenance, rater/solver separation, model-call repetition or caching, chronological non-use of test data, the edit-distance baseline, the 125-candidate selection, or generalization beyond these 20 test tasks. The old test tasks were already used by the earlier experiment 22 judge, as recorded in the frozen report. This QA adds no new human ratings, no new judge predictions and no new independent test set. The previous 180-second and 600-second Cursor attempts timed out; this later completed call supersedes that incomplete high-model check.

[Dated result Doc](https://docs.google.com/document/d/1iCWPmGFOU9X4l-zrR4TO6S72Bi3BEr05MmpDNkrksV8/edit).
