# Experiment 12 results: ② (pick by correlation) versus ④ (pick by cross-entropy), 80/20 task splits

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/12_formulation2_vs_4_corr_vs_ce_80_20_splits/results.md>

**TLDR:** On 1000 random 20-train/5-test task splits of the 75 cached artifacts, ② (mixture of the five cached judges chosen to maximize train Pearson) and ④ (mixture chosen to minimize train cross-entropy) tie on the main metric RPS: ② minus ④ = +0.0056 [-0.0059, +0.0181] (lower is better, so no evidence either way). ④ is better on CE (+0.374 [+0.101, +0.693], ② worse), ② is better on the correlations with the human mean rating (Spearman +0.063 [+0.052, +0.073]). Retrospective on cached judge scores, 0 model calls, $0, CPU only.

Method: each split holds out 5 whole tasks (15 artifacts); every method is fitted on the other 20 tasks (60 artifacts) only. ② = judge that maximizes the Pearson (or Spearman) correlation between its expected rating and the human mean rating; ④ = judge that minimizes cross-entropy to the human rating distribution. The searched family is the same for both: a single cached judge, or a weighted mixture of the five cached judges (weights on the simplex). Test metrics per artifact are averaged over the splits where the artifact was held out, then a 10,000-draw task bootstrap (25 tasks) gives the 95% percentile interval of the paired difference. Correlations need several test artifacts, so each split's test-set correlation is attributed to its 5 test tasks and averaged per task before the same bootstrap. Lower is better for RPS, CE, TVD; higher for correlations.

## Repeated splits (1000), mean test score

| Method | RPS (main) | CE | TVD | Spearman (mean over splits) | Pearson (mean over splits) |
| --- | --- | --- | --- | --- | --- |
| constant (train marginal) | 0.1836 | 1.852 | 0.682 | n/a | n/a |
| equal-weight mixture | 0.1496 | 5.431 | 0.531 | 0.608 | 0.703 |
| ② best single judge by train Pearson | 0.1797 | 8.104 | 0.600 | 0.719 | 0.750 |
| ② mixture maximizing train Pearson | 0.1419 | 5.787 | 0.522 | 0.669 | 0.730 |
| ② mixture maximizing train Spearman | 0.1792 | 8.095 | 0.600 | 0.721 | 0.751 |
| ④ best single judge by train CE | 0.2051 | 8.934 | 0.654 | 0.609 | 0.644 |
| ④ mixture minimizing train CE | 0.1362 | 5.413 | 0.510 | 0.606 | 0.717 |

The constant has no spread, so its correlations are undefined.

## Paired differences, ② minus ④ (95% task-bootstrap interval)

| ② variant versus ④ variant | RPS | CE | TVD | Spearman | Pearson |
| --- | --- | --- | --- | --- | --- |
| ② Pearson mixture vs ④ CE mixture | +0.0056 [-0.0059, +0.0181] | +0.374 [+0.101, +0.693] | +0.012 [-0.012, +0.036] | +0.063 [+0.052, +0.073] | +0.013 [+0.000, +0.023] |
| ② Spearman mixture vs ④ CE mixture | +0.0429 [+0.0167, +0.0696] | +2.682 [+1.445, +4.008] | +0.090 [+0.028, +0.153] | +0.115 [+0.098, +0.132] | +0.034 [+0.014, +0.053] |
| ② best single judge vs ④ best single judge | -0.0254 [-0.0570, +0.0005] | -0.830 [-1.657, -0.182] | -0.054 [-0.102, -0.013] | +0.111 [+0.088, +0.136] | +0.106 [+0.084, +0.132] |

Against the plain baselines (② Pearson mixture, ④ CE mixture), paired difference on RPS:

| | versus constant | versus equal-weight mixture |
| --- | --- | --- |
| ② Pearson mixture | -0.0417 [-0.0916, +0.0087] | -0.0077 [-0.0235, +0.0066] |
| ④ CE mixture | -0.0473 [-0.0947, -0.0008] | -0.0133 [-0.0240, -0.0027] |

Mean fitted weights (H0 Sol, H0 Opus, H1 Sol, H2 Sol, H2 Opus): ② Pearson mixture 0.291, 0.002, 0.000, 0.031, 0.675; ④ CE mixture 0.389, 0.085, 0.102, 0.033, 0.391. Best single judge chosen: ② H2 Opus in 998 of 1000 splits; ④ H2 Opus 601, H0 Sol 313, H2 Sol 77. Each artifact was a test artifact in 167 to 226 splits. Optimizer certificate failures: 0.

## One fixed split (seed 1210, declared before fitting), 20 train / 5 test tasks

Test tasks: 18_MyFibonacci, 1_MyAdd, 3_heappop, bubble_sort, humaneval_13__gcd (15 artifacts). Five tasks is very small: these are single numbers, not evidence.

| Chooser | Judge chosen | RPS | CE | TVD | Spearman | Pearson |
| --- | --- | --- | --- | --- | --- | --- |
| optimizer: ② mixture maximizing train Pearson | H0_sol:0.36 H2_opus:0.64 | 0.1121 | 4.570 | 0.471 | 0.841 | 0.877 |
| optimizer: ④ mixture minimizing train CE | H0_sol:0.41 H0_opus:0.04 H1_sol:0.13 H2_opus:0.42 | 0.1131 | 3.702 | 0.440 | 0.749 | 0.824 |
| optimizer: ② best single judge by train Pearson | H2_opus:1.00 | 0.1600 | 8.452 | 0.611 | 0.910 | 0.895 |
| optimizer: ④ best single judge by train CE | H2_opus:1.00 | 0.1600 | 8.452 | 0.611 | 0.910 | 0.895 |
| optimizer: constant (train marginal) | constant | 0.1576 | 1.793 | 0.640 | nan | nan |
| optimizer: equal-weight mixture | H0_sol:0.20 H0_opus:0.20 H1_sol:0.20 H2_sol:0.20 H2_opus:0.20 | 0.1282 | 3.748 | 0.478 | 0.807 | 0.823 |
| Claude Code agent, correlation objective only | H0_sol:0.25 H2_opus:0.45 train_marginal:0.30 | 0.1094 | 1.591 | 0.471 | 0.841 | 0.878 |
| Claude Code agent, CE objective only | H0_sol:0.17 H2_sol:0.02 H2_opus:0.21 train_marginal:0.59 | 0.1219 | 1.555 | 0.511 | 0.840 | 0.851 |

Agent ② minus agent ④ on RPS, per test task: 18_MyFibonacci -0.0123, 1_MyAdd -0.0513, 3_heappop +0.0020, bubble_sort +0.0006, humaneval_13__gcd -0.0018; mean -0.0125, 5-task bootstrap interval [-0.0328, +0.0005] (illustration only).

The agents searched a slightly larger family than the repeated-split optimizers: the five judges plus the constant train marginal as a sixth component. Pearson is unchanged by adding a constant, so the marginal weight in ② is arbitrary (the agent said so); for ④ the marginal weight is what fixes calibration, which is why the agent-④ CE on the fixed split is much lower than the optimizer-④ CE.

## What the metrics are (per artifact; p = human rating distribution from the 2 to 3 expert ratings, q = the judge's output distribution over the six ratings 0 to 5)

- RPS (ranked probability score, main): mean over the five cumulative cut points of (Q_k - P_k)^2 + P_k(1 - P_k), with P, Q the cumulative sums of p and q. Proper for ordinal ratings, sensitive to how far off the mass is, and it never blows up. Lower is better.
- CE (cross-entropy): -sum_r p(r) log q(r), with q floored at 1e-6. Proper but unbounded: a judge that puts almost no mass on a human-given rating pays a lot. Lower is better.
- TVD (total variation distance): half the sum of |p(r) - q(r)|, the largest probability difference between the two distributions, 0 to 1. Lower is better.
- Spearman and Pearson (secondary): rank and linear correlation, over the 15 test artifacts of a split, between the judge's expected rating and the human mean rating. They only check the means, not the whole distribution. Higher is better.

## Harness and models

- Optimizing agent: a Claude Code subagent started by the Claude Code worker (Sonnet 5.5 is the worker; the subagent model was not recorded separately), one for ② and one for ④, each given only the 60 training artifacts of the fixed split and one objective, using a 0.05-grid search over the simplex in plain Python (the second also an EM optimizer). They did not see the 5 test tasks. Both made 0 model calls.
- Repeated splits: no LLM in the loop. The selection is the exact solver of experiment 10/03 (Pearson mixture by active-face enumeration, CE mixture by SLSQP with a checked certificate), a 4,000-point simplex search for Spearman, and argmax or argmin over single judges. Orchestrated by the Claude Code worker.
- Judges: the five cached judges, produced earlier (VeriBench experiment 100, commit be287d9): GPT-6 Sol high and Claude Opus 5.5 max with the H0, H1, H2 prompt variants. Nothing new was called.
- Cost $0 (cached scores, CPU).

## Limits and what was not checked

- Small: 25 tasks, 75 artifacts (three Claude 3.7 Sonnet samples per task), 2 to 3 expert ratings per artifact (195 in total), not about five raters. A split tests on only 5 tasks.
- Prior exposure and leakage risk: the five judges' prompts and conventions were developed in experiment 100 using the original train split's human ratings (10 of the 25 tasks, and some prompts also saw validation tasks). In these random splits some held-out tasks were therefore seen when the judges were designed, which can flatter every method alike; a clean test needs new rated tasks. These ratings were also inspected in experiments 06, 07, 10 and 11.
- No new prompts or models were searched: "choose the best prompt or model" here means choosing among five cached prompt-and-model judges and their mixtures. A search over new prompts or local open-weight judges needs model calls and was not run.
- Folds are grouped by task, not by task family, so family leakage is possible. Splits overlap, so the 1,000 splits are not independent; the intervals come from bootstrapping the 25 tasks.
- Test-set correlations use 15 artifacts per split and are task-attributed (see Method); they are not the pooled correlation over all 75 artifacts.
- The cached judges' CE is poor because three cached samples put near-zero mass on many human-rated values; ② does not try to repair calibration, so a CE gap against ④ is expected by construction.
