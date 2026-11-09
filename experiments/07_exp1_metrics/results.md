# Experiment 07: Experiment 1 metric table and scaling fit on cached judge scores

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/07_exp1_metrics/results.md>

**TLDR:** Five cached scalar judges, 75 artifacts, 25 tasks, 195 expert ratings, zero new model calls, no paid API. All numbers below were computed by CPU scripts in this folder (Python 3, numpy, scipy), not by a model; the cached judge scores themselves come from the historical runs named in the table below.

## 1. Which count is right: 343 or 195?

Both describe the same 75 artifacts (25 tasks x 3 agent samples each), different rater panels. Counted from `inputs/items.jsonl` at veribench commit `be287d9`: **195** ratings come from the three expert columns (p1 75, p2 75, p3 45); the two other columns add p4 75 and p5 75, so **345** ratings over five raters (45 artifacts have 5 ratings, 30 have 4). I did not find 343 in the files I searched (`items.jsonl`, the experiment README and PROTOCOL.md, the phase-0 audit, `results/VERIFICATION.json`); the 345 here and the 44/75 versus 45/75 for the third rater differ from the notes in the prompt text by 2 and 1. The primary target is the expert panel (195), as PROTOCOL.md of experiment 100 specifies ("mean of available ratings from participants 1-3"); the five-rater panel (345) is secondary. The "25x3x5" tensor shape is tasks x agent samples x raters.

## 2. Method

- **Judges (cached, no new calls):** per artifact 3 sampled scalar repeats (integer 0-5), 1,125 historical calls in total. Probabilities come from **sampled repeats**, not digit logprobs: the receipts hold no token probabilities. Judge pmf = histogram of the 3 repeats over ratings 0-5, floored at one eps = **0.001** and renormalised (the same floor for every metric that uses a pmf).
- **Judge names (from the run configs):** H0 Sol, H1 Sol, H2 Sol = `openai/gpt-6-sol-high` (reasoning effort high, Vals gateway); H0 Opus, H2 Opus = `anthropic/claude-opus-5-5-no-fallback` at compute_effort=max with adaptive thinking. H0 is the raters' instructions, H1 adds rater-convention notes, H2 adds expert-rated demonstration examples; prompts were developed on the training split of this same 75-artifact set. Gemini is not a judge in any row. Harness: the veribench experiment-100 judge runner; the numbers here come from this folder's Python scripts.
- **Human target:** expert panel, mean rating / 5 for nRMSE and correlations; empirical pmf of the 2-3 expert ratings per artifact for sqrt RPS and KL.
- **Metrics:** nRMSE = sqrt(mean over artifacts of (judge mean/5 - human mean/5)^2). sqrt RPS = sqrt(mean over artifacts of (1/5) sum over 5 thresholds of (F_judge - F_human)^2). **KL** = forward KL(q || p) with q the human empirical pmf (more than one rating per artifact, so KL rather than cross-entropy; CE = KL + H(q) is in `results/metrics.json`). Constant nRMSE = nRMSE of predicting the mean human score for every artifact (in-sample best constant, so it is the hardest constant to beat). Pearson, Spearman (average ranks) and Kendall (tau-b) compare the judge mean and the human mean across artifacts. **No R^2.** Artifacts are weighted equally.
- **Uncertainty:** 95% percentile intervals from **10,000 task-level bootstrap resamples** (25 tasks drawn with replacement, all of a drawn task's artifacts kept, seed 20261109). Intervals cover task sampling only, not rater or judge-sampling variation, and not the prompt-development exposure.
- **Tag: no DT.** These cached judges score formal-specification coverage on the original candidate Lean files; no DT variant of the gold or candidates is involved.

## 3. Experiment 1 table (expert panel, 75 artifacts, 25 tasks, 195 ratings; no DT)

nRMSE, constant nRMSE, sqrt RPS and KL: lower is better. Correlations: higher is better. Values: point [95% CI].

| Judge | nRMSE | constant nRMSE | sqrt RPS | KL | Pearson | Spearman | Kendall |
|---|---:|---:|---:|---:|---:|---:|---:|
| H0 Opus | 0.283 [0.214, 0.350] | 0.287 [0.225, 0.330] | 0.412 [0.342, 0.479] | 3.81 [3.09, 4.51] | 0.609 [0.309, 0.801] | 0.562 [0.175, 0.805] | 0.415 [0.105, 0.653] |
| H0 Sol | 0.255 [0.196, 0.318] | 0.287 [0.225, 0.330] | 0.373 [0.318, 0.431] | 3.62 [3.02, 4.20] | 0.616 [0.300, 0.796] | 0.548 [0.161, 0.785] | 0.422 [0.111, 0.645] |
| H1 Sol | 0.253 [0.204, 0.298] | 0.287 [0.225, 0.330] | 0.384 [0.329, 0.434] | 3.72 [3.06, 4.38] | 0.717 [0.535, 0.838] | 0.680 [0.431, 0.836] | 0.546 [0.334, 0.698] |
| H2 Opus | 0.234 [0.180, 0.283] | 0.287 [0.225, 0.330] | 0.364 [0.304, 0.419] | 3.52 [2.84, 4.17] | 0.777 [0.607, 0.887] | 0.769 [0.551, 0.901] | 0.652 [0.447, 0.800] |
| H2 Sol | 0.265 [0.201, 0.327] | 0.287 [0.225, 0.330] | 0.391 [0.324, 0.450] | 3.68 [2.96, 4.38] | 0.693 [0.429, 0.858] | 0.665 [0.374, 0.865] | 0.550 [0.304, 0.742] |

Cross-entropy (point, nats, equals KL plus the human entropy): H0 Opus 4.37, H0 Sol 4.18, H1 Sol 4.29, H2 Opus 4.08, H2 Sol 4.25. KL and CE are large because three sampled repeats put zero mass on most ratings and the eps floor of 1e-3 costs about 6.9 nats per unsupported rating; they move with eps and must not be compared across eps values.

Against the constant guess: H0 Opus 0.283 vs 0.287, H0 Sol 0.255 vs 0.287, H1 Sol 0.253 vs 0.287, H2 Opus 0.234 vs 0.287, H2 Sol 0.265 vs 0.287. Judges within 0.01 of the constant (or worse): H0 Opus. The intervals of judge and constant overlap for every judge; no paired judge-minus-constant interval was computed.

### Does the judge ranking change between metric families?

Best to worst by point estimate:

| Metric | Order | P(best) in bootstrap |
|---|---|---|
| nRMSE | H2 Opus > H1 Sol > H0 Sol > H2 Sol > H0 Opus | H0 Opus 0.05, H0 Sol 0.30, H1 Sol 0.01, H2 Opus 0.63, H2 Sol 0.02 |
| sqrt RPS | H2 Opus > H0 Sol > H1 Sol > H2 Sol > H0 Opus | H0 Opus 0.02, H0 Sol 0.41, H1 Sol 0.02, H2 Opus 0.52, H2 Sol 0.03 |
| KL | H2 Opus > H0 Sol > H2 Sol > H1 Sol > H0 Opus | H0 Opus 0.07, H0 Sol 0.33, H1 Sol 0.03, H2 Opus 0.47, H2 Sol 0.10 |
| Pearson | H2 Opus > H1 Sol > H2 Sol > H0 Sol > H0 Opus | H0 Opus 0.05, H0 Sol 0.05, H1 Sol 0.00, H2 Opus 0.90, H2 Sol 0.01 |
| Spearman | H2 Opus > H1 Sol > H2 Sol > H0 Opus > H0 Sol | H0 Opus 0.02, H0 Sol 0.03, H1 Sol 0.00, H2 Opus 0.94, H2 Sol 0.01 |
| Kendall | H2 Opus > H2 Sol > H1 Sol > H0 Sol > H0 Opus | H0 Opus 0.00, H0 Sol 0.01, H1 Sol 0.00, H2 Opus 0.97, H2 Sol 0.01 |

Paired bootstrap differences between judges (10 pairs per metric) whose 95% interval excludes zero: nRMSE: 0; sqrt RPS: 0; KL: 0; Pearson: 2 (H1_sol - H2_opus, H2_opus - H2_sol); Spearman: 2 (H1_sol - H2_opus, H2_opus - H2_sol); Kendall: 4 (H0_opus - H2_opus, H0_sol - H2_opus, H1_sol - H2_opus, H2_opus - H2_sol).

Kendall tau between the point-estimate rankings of two metrics: nrmse vs sqrt_rps 0.80, nrmse vs kl 0.60, nrmse vs pearson 0.80, nrmse vs spearman 0.60, nrmse vs kendall 0.60, sqrt_rps vs kl 0.80, sqrt_rps vs pearson 0.60, sqrt_rps vs spearman 0.40, sqrt_rps vs kendall 0.40, kl vs pearson 0.40, kl vs spearman 0.20, kl vs kendall 0.60, pearson vs spearman 0.80, pearson vs kendall 0.80, spearman vs kendall 0.60.

Reading: see the order table. Where the order differs between families, the intervals decide whether the difference is resolved; with 25 tasks and 5 judges most pairwise differences are not resolved, so no claim is made that the probability-based metrics (sqrt RPS, KL) rank judges better than the correlations or nRMSE.

## Secondary A: expert panel, validation + test artifacts only (judge prompts were developed on the training split)

45 artifacts, 15 tasks, 117 ratings; same method and 10,000 resamples.

| Judge | nRMSE | constant nRMSE | sqrt RPS | KL | Pearson | Spearman | Kendall |
|---|---:|---:|---:|---:|---:|---:|---:|
| H0 Opus | 0.302 [0.207, 0.395] | 0.283 [0.192, 0.339] | 0.433 [0.337, 0.520] | 4.00 [2.97, 4.96] | 0.628 [0.248, 0.848] | 0.609 [0.091, 0.897] | 0.472 [0.043, 0.785] |
| H0 Sol | 0.219 [0.161, 0.271] | 0.283 [0.192, 0.339] | 0.341 [0.280, 0.394] | 3.47 [2.59, 4.31] | 0.717 [0.386, 0.877] | 0.631 [0.230, 0.856] | 0.506 [0.170, 0.744] |
| H1 Sol | 0.252 [0.196, 0.299] | 0.283 [0.192, 0.339] | 0.390 [0.314, 0.452] | 3.79 [2.81, 4.73] | 0.784 [0.664, 0.867] | 0.756 [0.444, 0.897] | 0.616 [0.350, 0.782] |
| H2 Opus | 0.223 [0.160, 0.273] | 0.283 [0.192, 0.339] | 0.359 [0.276, 0.426] | 3.42 [2.43, 4.40] | 0.839 [0.723, 0.920] | 0.823 [0.520, 0.943] | 0.693 [0.401, 0.865] |
| H2 Sol | 0.253 [0.185, 0.308] | 0.283 [0.192, 0.339] | 0.388 [0.299, 0.462] | 3.61 [2.58, 4.60] | 0.804 [0.678, 0.894] | 0.770 [0.390, 0.929] | 0.628 [0.302, 0.829] |

Order by nRMSE: H0 Sol > H2 Opus > H1 Sol > H2 Sol > H0 Opus; by sqrt RPS: H0 Sol > H2 Opus > H2 Sol > H1 Sol > H0 Opus; by KL: H2 Opus > H0 Sol > H2 Sol > H1 Sol > H0 Opus.

## Secondary B: all five raters (345 ratings)

75 artifacts, 25 tasks, 345 ratings; same method and 10,000 resamples.

| Judge | nRMSE | constant nRMSE | sqrt RPS | KL | Pearson | Spearman | Kendall |
|---|---:|---:|---:|---:|---:|---:|---:|
| H0 Opus | 0.224 [0.173, 0.271] | 0.223 [0.167, 0.267] | 0.347 [0.295, 0.397] | 3.48 [2.88, 4.07] | 0.702 [0.430, 0.857] | 0.606 [0.241, 0.827] | 0.454 [0.154, 0.673] |
| H0 Sol | 0.243 [0.174, 0.313] | 0.223 [0.167, 0.267] | 0.350 [0.293, 0.412] | 3.49 [3.00, 3.98] | 0.654 [0.346, 0.830] | 0.567 [0.189, 0.801] | 0.449 [0.131, 0.670] |
| H1 Sol | 0.184 [0.154, 0.213] | 0.223 [0.167, 0.267] | 0.307 [0.271, 0.340] | 3.25 [2.71, 3.77] | 0.817 [0.672, 0.897] | 0.738 [0.515, 0.866] | 0.599 [0.403, 0.729] |
| H2 Opus | 0.179 [0.147, 0.208] | 0.223 [0.167, 0.267] | 0.301 [0.265, 0.333] | 3.23 [2.72, 3.74] | 0.853 [0.742, 0.920] | 0.808 [0.613, 0.908] | 0.677 [0.496, 0.793] |
| H2 Sol | 0.195 [0.153, 0.240] | 0.223 [0.167, 0.267] | 0.315 [0.272, 0.353] | 3.31 [2.74, 3.86] | 0.798 [0.604, 0.906] | 0.730 [0.480, 0.882] | 0.600 [0.382, 0.755] |

Order by nRMSE: H2 Opus > H1 Sol > H2 Sol > H0 Opus > H0 Sol; by sqrt RPS: H2 Opus > H1 Sol > H2 Sol > H0 Opus > H0 Sol; by KL: H2 Opus > H1 Sol > H2 Sol > H0 Opus > H0 Sol.

## 4. Scaling fit by subsampling the same ratings

**Reading used (open with Brando: N and D were not defined on the whiteboard).** The cached judges are not trained on tasks or ratings, so l is the squared **estimation error of a judge's nRMSE** (scores/5): evaluate on n tasks with k human ratings per artifact and m judge repeats, and compare with the value on the 13 disjoint held-out tasks using all ratings and m=3. N = n tasks, D = k human ratings per artifact (3 n k ratings in total per evaluation). The five-rater panel is used so that k = 1..4 exists for every artifact. l is averaged over the five judges; per-judge fits are in `results/scaling.json`. Grid: n in {2,3,4,6,8,10,12}, k in {1,2,3,4}, m in {1,2,3}; 20,000 random task/rater/repeat draws (seed 20261109), zero model calls. This measures how fast the measurement error of the metric falls with more tasks and ratings; it does not show how a trained judge improves.

### Fit 1: l = E + A n^-alpha + B k^-beta (m = 3)

| Coefficient | Estimate | 95% CI (Monte-Carlo, see below) |
|---|---:|---|
| E | 0.000658 | [0.000558, 0.000801] |
| A | 0.0134 | [0.0129, 0.0135] |
| alpha | 0.898 | [0.862, 0.923] |
| B | 0.00786 | [0.00777, 0.00801] |
| beta | 2.2 | [2.15, 2.25] |

Fit quality: RMS error of log l over the 28 grid cells = 0.018 (a factor of about 1.02); no R^2.

Predicted sqrt l (RMS error of the estimated nRMSE): observed grid corner n=12, k=4: 0.050; n=2, k=1: 0.125; EXTRAPOLATION n=25, k=5: 0.040.

### Fit 2: MSE(n,k,m) = E0 + A/n^a + B/k + C/m^b (tasks, raters, judge repeats)

| Coefficient | Estimate | 95% CI (Monte-Carlo) |
|---|---:|---|
| E0 | 1.43e-19 | [5.1e-23, 9.13e-16] |
| A | 0.0195 | [0.0187, 0.0197] |
| a | 1.56 | [1.53, 1.58] |
| B | 0.00888 | [0.00882, 0.00902] |
| C | 0.000842 | [0.000824, 0.000871] |
| b | 4 | [4, 4] |

Fit quality: RMS error of log l over the 84 grid cells = 0.105. Variant with a free k exponent (B/k^beta_k): beta_k = 2.08, RMS log error 0.032. Parameters at a bound (b = 4, E0 = 0) are not identified. The loss is a squared error, so a 1/k bias term enters squared; the fixed-1/k form is the one requested and is reported as such. Agent count (3 samples per task) is too small for a curve and is not varied.

The Monte-Carlo CI refits the curve on 500 resamples of 40 independent simulation batches; it captures simulation noise only. Task-set sensitivity: leave-5-tasks-out refits of Fit 1 (5 refits) give alpha in [0.81, 0.95] and beta in [2.04, 2.30]; with only 25 tasks the exponents are loosely determined.

### n and k needed for a target precision (EXTRAPOLATION beyond n = 12, k = 4)

Target = predicted RMS error of the estimated nRMSE (sqrt l). "Reducible only" removes the floor E (which here is partly the noise of the 13-task reference); "including floor" keeps it. Smallest total ratings 3nk on the fitted curve; all values beyond the observed grid are extrapolation.

| Target sqrt l | Reducible only (n, k, total ratings) | Including floor E |
|---|---|---|
| 0.02 | n=72, k=7, 1512 ratings | not reached for n<=200, k<=40 |
| 0.01 | not reached for n<=200, k<=40 | not reached for n<=200, k<=40 |

## 5. What this does not show

- Judge prompts H0-H2 were developed on the training split of these same artifacts, and the raters and artifacts have prior exposure; the table is retrospective, not a fresh validation.
- 25 tasks, one solver population, one rater pool; intervals cover task sampling only.
- Sampled-repeat histograms from 3 calls are a weak probability estimator; KL and sqrt RPS depend on it and on eps.
- The scaling fit measures metric-estimation precision under one reading of N and D; extrapolations are model-based.
