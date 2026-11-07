# Cached objective comparison: results and limitations

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/06_information_loss_vs_correlation_judge_selection/RESULTS.md>

**TLDR:** The cached histogram comparison did not establish that cross-entropy selection improves held-out performance. A separate fitted probability-head comparison favored proper-loss models over the specified Pearson implementation, but that implementation usually failed to converge; general superiority remains unestablished.

Experiment `06_information_loss_vs_correlation_judge_selection`, completed 11-06-2026 (America/Los_Angeles).
Historical sample: **75 artifacts, 25 tasks, 19 task families, 195 expert ratings, five cached judges with three scores per artifact (1,125 historical calls)**.
Five seeded five-fold partitions reuse these same artifacts; they are not 375 independent artifacts.
All eight selection objectives completed all 25 outer folds (200 selections), followed by all 900 declared probability-head fits.
There were zero new model calls and $0 new provider inference charges.
The bounded CPU analyses took about 17 and 10 seconds on skampere3, excluding preparation, transfer, subscription coordination and hardware costs.

## Answer to the hypothesis

1. **Primary, fixed cached histograms:** held-out cross-entropy (CE; natural-log units, lower better) was 8.868 for CE selection versus 8.098 for Spearman selection. Difference **+0.770 [-0.895, 1.317], p-val=n/a**. This 95% interval resamples task families and reruns candidate selection within the fixed partitions. It includes zero, so this experiment does not resolve the direction of the selection effect.
2. **Secondary, fitted probability heads:** CE fitting versus Pearson fitting gave CE 1.527 versus 1.897; difference **-0.370 [-0.690, -0.080], p-val=n/a**. This interval is conditional on the fitted heads and excludes fitting/regularization-selection uncertainty. **215/225 Pearson fits did not converge, including 24/25 outer refits; all 675 proper-loss fits converged.** The comparison describes these bounded implementations, not fully optimized objective optima. Brier fitting had lower observed CE (1.497) than CE fitting (1.527); that difference was not the primary contrast.
3. **Practical conclusion:** use proper probability losses when the target is a rating distribution, but do not claim that CE/KL must improve every test metric. Three sampled scalar ratings are particularly weak probability forecasts. Fresh human data, a stable matched optimization comparator and identified probability outputs are needed before a general or deployment claim.

The primary protocol was frozen in `ea9d63b` before measurement. The head follow-up was frozen separately in `aba79e9`, after the histogram result, as the planned secondary fitting condition. It does not replace the primary outcome. No confirmatory test or success threshold was specified; all p-values are n/a.

## Primary common held-out metric matrix

The rows change only the selection objective over the same five candidates. CE and forward Kullback–Leibler divergence (KL) are one equivalent selection objective. Brier uses the six-category sum convention [0,2]; ranked probability score (RPS) averages five ordinal thresholds [0,1]. Pearson, Spearman and Kendall compare expected rating to human mean; higher is better. Other losses are lower better.

The following 95% intervals use **1,000 paired task-family bootstrap draws conditional on the already selected forecasts**, averaging each metric across the five seeded partitions. They exclude selection/fitting variability and new human/model samples. Their narrower intervals must not replace the selection-refit interval above.

| Objective | ce | brier | rps |
| --- | ---: | ---: | ---: |
| Brier | 8.852 [7.199, 10.218] | 1.280 [1.042, 1.479] | 0.207 [0.161, 0.245] |
| CE / forward KL | 8.868 [7.176, 10.244] | 1.287 [1.043, 1.484] | 0.203 [0.159, 0.243] |
| Kendall | 8.098 [6.134, 9.733] | 1.191 [0.922, 1.419] | 0.179 [0.126, 0.229] |
| Pearson | 8.098 [6.134, 9.733] | 1.191 [0.922, 1.419] | 0.179 [0.126, 0.229] |
| RPS | 8.749 [7.084, 10.149] | 1.269 [1.032, 1.469] | 0.215 [0.168, 0.253] |
| Spearman | 8.098 [6.134, 9.733] | 1.191 [0.922, 1.419] | 0.179 [0.126, 0.229] |
| TVD | 8.827 [7.157, 10.225] | 1.284 [1.041, 1.482] | 0.204 [0.161, 0.243] |
| Weighted PMF | 8.790 [7.311, 10.010] | 1.264 [1.051, 1.442] | 0.205 [0.163, 0.238] |

| Objective | pearson | spearman | kendall |
| --- | ---: | ---: | ---: |
| Brier | 0.640 [0.423, 0.810] | 0.615 [0.316, 0.825] | 0.483 [0.244, 0.698] |
| CE / forward KL | 0.678 [0.477, 0.822] | 0.671 [0.415, 0.847] | 0.546 [0.330, 0.728] |
| Kendall | 0.777 [0.599, 0.903] | 0.769 [0.527, 0.911] | 0.652 [0.439, 0.819] |
| Pearson | 0.777 [0.599, 0.903] | 0.769 [0.527, 0.911] | 0.652 [0.439, 0.819] |
| RPS | 0.601 [0.361, 0.790] | 0.592 [0.271, 0.824] | 0.465 [0.213, 0.698] |
| Spearman | 0.777 [0.599, 0.903] | 0.769 [0.527, 0.911] | 0.652 [0.439, 0.819] |
| TVD | 0.671 [0.476, 0.813] | 0.665 [0.407, 0.844] | 0.536 [0.323, 0.726] |
| Weighted PMF | 0.619 [0.381, 0.806] | 0.586 [0.271, 0.825] | 0.456 [0.202, 0.700] |

Remaining common metrics are point estimates; their conditional intervals and all paired differences are in `results/results.json`. PMF means probability mass function; TVD means total variation distance. Weighted PMF distance is sum p_hat(r)(p_hat(r)-q(r))²; TVD is half the absolute PMF difference. Human entropy is subtracted for forward KL, with identical weighting. Sparse empirical human frequencies are noisy targets for these distances.

| Objective | kl | weighted_pmf | tvd | mae | bias | judge_mean | human_mean |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Brier | 8.286 | 0.289 | 0.651 | 0.211 | 0.060 | 0.585 | 0.525 |
| CE / forward KL | 8.302 | 0.295 | 0.651 | 0.203 | 0.082 | 0.607 | 0.525 |
| Kendall | 7.532 | 0.279 | 0.600 | 0.176 | 0.112 | 0.637 | 0.525 |
| Pearson | 7.532 | 0.279 | 0.600 | 0.176 | 0.112 | 0.637 | 0.525 |
| RPS | 8.183 | 0.288 | 0.643 | 0.219 | 0.050 | 0.576 | 0.525 |
| Spearman | 7.532 | 0.279 | 0.600 | 0.176 | 0.112 | 0.637 | 0.525 |
| TVD | 8.261 | 0.292 | 0.649 | 0.204 | 0.076 | 0.601 | 0.525 |
| Weighted PMF | 8.224 | 0.288 | 0.645 | 0.211 | 0.042 | 0.567 | 0.525 |

Mean absolute error (MAE), mean bias and means use the [0,1] rating scale. Bias is judge minus human; positive means higher/lenient ratings. Spearman selection: judge mean 0.637, human mean 0.525, bias +0.112.

For comparison, the conditional primary difference is +0.770 [0.168, 1.792], while repeating candidate selection yields +0.770 [-0.895, 1.317]. This change of interval is why fixed-prediction uncertainty alone would be misleading for the selection question. All 1,000 selection-refit draws were valid; no replacement retries occurred.

## Selected candidates and sparse support

Historical identities: H0 uses the human-mirror rubric; H1 adds rater conventions; H2 adds conventions and leave-task-out expert demonstrations. Sol is the saved `openai/gpt-6-sol-high` gateway selector at high effort; Opus is `anthropic/claude-opus-5-5-no-fallback`, compute effort max. Full saved configurations and input hashes are in `source_audit.json`; no new provider identity claim is inferred from these aliases.

| Selection objective | Candidate counts across 25 outer selections |
| --- | --- |
| Brier | H0_sol: 17, H2_opus: 8 |
| CE / forward KL | H0_sol: 8, H1_sol: 1, H2_opus: 16 |
| Kendall | H2_opus: 25 |
| Pearson | H2_opus: 25 |
| RPS | H0_sol: 11, H2_opus: 14 |
| Spearman | H2_opus: 25 |
| TVD | H0_sol: 10, H2_opus: 15 |
| Weighted PMF | H0_sol: 19, H2_opus: 6 |

Pearson, Spearman and Kendall chose H2 Opus in all 25 selections and therefore have identical results here. Undefined-correlation selection fallbacks: 0.

| Cached candidate | Artifacts with observed human rating outside raw forecast support /75 | Mean unsupported human mass | RMS within-artifact sample SD of three raw normalized scores |
| --- | ---: | ---: | ---: |
| H0_opus | 64 | 0.620 | 0.055 |
| H0_sol | 65 | 0.593 | 0.131 |
| H1_sol | 65 | 0.609 | 0.112 |
| H2_opus | 64 | 0.582 | 0.050 |
| H2_sol | 65 | 0.607 | 0.084 |

Without the epsilon mixture, those unsupported observations have infinite log loss. With epsilon=1e-6, they receive about 13.816 loss each. The train-only constant human-distribution baseline had CE 1.928, Brier 0.870, RPS 0.187 (descriptive point estimates). All eight histogram-based selection procedures are much worse in CE than this baseline; high ranking correlation does not make their sampled-score histograms adequate human-rating distributions. The repeated-score standard deviations above concern raw calls, not the repeatability of the three-call aggregate; there is only one cached three-call batch per artifact.

## Prespecified sensitivities

All preserve the declared selection recipe. Intervals were not computed for these secondary checks.

| Condition | Artifacts / tasks / families / expert ratings | CE-selected CE | Spearman-selected CE | Difference |
| --- | --- | ---: | ---: | ---: |
| 0.0001 | 75 / 25 / 19 / 195 | 5.929 | 5.417 | +0.512 |
| 1e-08 | 75 / 25 / 19 / 195 | 11.807 | 10.779 | +1.027 |
| ordinary | 60 / 20 / 14 / 165 | 10.142 | 8.971 | +1.170 |
| ordinary_unambiguous | 45 / 15 / 13 / 120 | 8.341 | 7.766 | +0.575 |
| Historical validation selection / old test | 30 test artifacts / 10 tasks / 78 expert ratings | 9.133 | 8.710 | +0.423 |

`ordinary` removes 15 placeholder-reference artifacts; `ordinary_unambiguous` also removes the 15 ambiguous-reference artifacts. These are predeclared sensitivities, not a replacement dataset. Original-split selection uses only its 15 validation artifacts; its test split was previously exposed and is not fresh.

## Separate matched probability-head comparison

All conditions use the five cached mean scores as features and the same six-class affine softmax model, 36 stored coefficients, training-only feature scaling, initialization schedule, optimizer and fitting budget. Four inner family folds select between two L2 strengths by the same held-out RPS rule, independently for every fit objective. No LLM is fine-tuned; these are fitted probability mappings. See `HEAD_PROTOCOL.md`.

These 95% intervals are conditional on the fitted heads and regularization choices. They resample 19 families with all attached artifacts/ratings, 1,000 draws, and do not account for upstream prompt exposure or model-fitting uncertainty.

| Objective | ce | brier | rps |
| --- | ---: | ---: | ---: |
| Brier | 1.497 [1.292, 1.700] | 0.721 [0.648, 0.775] | 0.116 [0.095, 0.144] |
| CE / forward KL | 1.527 [1.244, 1.855] | 0.730 [0.645, 0.798] | 0.117 [0.092, 0.150] |
| Pearson | 1.897 [1.799, 2.051] | 0.853 [0.830, 0.895] | 0.182 [0.150, 0.231] |
| RPS | 1.555 [1.329, 1.757] | 0.723 [0.643, 0.778] | 0.118 [0.097, 0.145] |

| Objective | pearson | spearman | kendall |
| --- | ---: | ---: | ---: |
| Brier | 0.736 [0.495, 0.888] | 0.652 [0.321, 0.856] | 0.491 [0.213, 0.695] |
| CE / forward KL | 0.736 [0.472, 0.898] | 0.659 [0.321, 0.865] | 0.504 [0.228, 0.708] |
| Pearson | 0.057 [-0.120, 0.313] | 0.143 [-0.081, 0.382] | 0.105 [-0.064, 0.305] |
| RPS | 0.728 [0.493, 0.880] | 0.645 [0.319, 0.843] | 0.484 [0.217, 0.690] |

| Objective | kl | weighted_pmf | tvd | mae | bias | judge_mean | human_mean |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Brier | 0.931 | 0.154 | 0.482 | 0.144 | -0.000 | 0.525 | 0.525 |
| CE / forward KL | 0.961 | 0.156 | 0.467 | 0.139 | -0.007 | 0.519 | 0.525 |
| Pearson | 1.331 | 0.238 | 0.672 | 0.240 | -0.044 | 0.481 | 0.525 |
| RPS | 0.989 | 0.158 | 0.495 | 0.144 | -0.007 | 0.518 | 0.525 |

| Fitting objective | Fits | Nonconverged fits | Nonconverged final refits /25 | Mean train Pearson | Mean within-fold test Pearson | Mean within-fold test expected-rating SD |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Brier | 225 | 0 | 0 | 0.907 | 0.698 | 0.201 |
| CE / forward KL | 225 | 0 | 0 | 0.911 | 0.709 | 0.220 |
| Pearson | 225 | 215 | 24 | 0.942 | 0.548 | 0.010 |
| RPS | 225 | 0 | 0 | 0.900 | 0.679 | 0.201 |

The fit diagnostics were added after observing the convergence failures; they do not change the frozen analysis. Pearson's mean training correlation is high, while its expected ratings have a small within-fold spread. Correlation does not identify an absolute location or scale; pooling differently fitted folds can therefore give much lower correlation than averaging within-fold correlations. The table documents that behavior without claiming it is the only cause of failure. The equal numerical regularization grid also has different effective strengths under differently scaled losses. All finite failed fits were retained, and no objective received extra retries. A stable comparator and independent data are necessary before claiming general training-objective superiority.

## Human reference and evidence limits

Descriptive leave-one-expert-out agreement on overlapping artifacts (same historical sample, no population ceiling claim):

| Anonymous expert index | Artifacts | Pearson | Spearman | Kendall | MAE |
| --- | ---: | ---: | ---: | ---: | ---: |
| 1 | 75 | 0.873 | 0.878 | 0.778 | 0.139 |
| 2 | 75 | 0.870 | 0.872 | 0.770 | 0.145 |
| 3 | 45 | 0.593 | 0.543 | 0.466 | 0.167 |

- These old ratings, test outcomes, and candidate prompts had prior exposure. New family folds do not undo upstream selection or demonstration exposure. This is retrospective evidence, not an independent validation round.
- The importer matched all 75 candidate hashes to the annotation revision, all 12 input manifest hashes, and 1,125 receipt prompt hashes to their run manifests. Original rater-time delivery bytes were not independently reconstructed; reference ambiguity remains explicit. A manifest match does not eliminate these historical limitations.
- The study has one historical solver-output population and three expert columns with missingness (75/75/45 artifacts). There is no held-out solver-family or rater-family transfer test, nor evidence over all benchmark tasks.
- Both human frequencies (two or three ratings per artifact) and judge histograms (three calls) are noisy. This study does not establish closeness to the full conditional human rating distribution or all its moments.
- Proper-score theory identifies population targets under its assumptions; finite samples, model class, optimization and regularization determine the empirical result. No novelty or universal-superiority claim follows from this run.

## Reproduction and verification

See `protocol.json`, `PROTOCOL_FROZEN.md`, `HEAD_PROTOCOL.md`, `head_protocol.json`, `source_audit.json` and `scripts/`.
Private data remain in the canonical repository's ignored `private/06_information_loss_vs_correlation_judge_selection/`; no individual ratings or learned weights are published.
Run `run_cached.py` with the recorded private dataset/configuration, then `fit_heads.py` against the same root; the remote supervisors show exact argument and resource conventions.
Source/data hashes and process exit codes are in `results/terminal.json` and `results/head_terminal.json`.

Verification passed seven scoring/splitting tests, four analytic-gradient finite-difference checks (all below 1e-5), the two-example fit, independent reconstruction of 3,000 primary plus 1,500 head forecasts, 100 training-only preprocessing checks, full manifest counts and bootstrap interval recomputation. Project checks and the unchanged workshop-paper build passed. The paper's prospective claims were not replaced by retrospective results.

All aggregate matrices, per-seed metrics, selections, fit convergence records, paired intervals and sensitivity outputs are in `results/results.json` and `results/head_results.json`. Independent verification receipts are beside them. The experiment remains active as the home for the planned fresh-human confirmation; the cached conditions are complete.

Copy-ready message: I compared probability-loss and correlation-based selection using our historical human ratings. The cached selection result did not resolve an advantage for cross-entropy; fitted proper-loss probability models looked more useful, but the Pearson optimization comparator mostly failed to converge, so we still need a stable comparison and fresh ratings.

**TLDR-end:** [ttj: objective comparison] Both cached-data comparisons finished and were independently checked. They support better probability modeling and a fresh study, not a general claim that CE/KL beats correlation-based objectives.
