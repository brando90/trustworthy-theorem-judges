# Experiment 18 results (big-data version 1): fit on the large AI-labelled pool, test on the 75 human-rated artifacts

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/18_big_ai_label_pool_test_on_75_humans/results.md>

**TLDR:** Fitting on 591 AI-labelled artifacts (50 fresh tasks) and testing on the 75 human-rated ones: the loss-fitted mixture (④, RPS 0.1490) beats the correlation-fitted mixture (②, 0.1579) (RPS difference ④ minus ② -0.0089 [-0.0205, -0.0010]), but neither beats the untrained equal-weight mixture (0.1407), and training on the 75 humans themselves does better (0.1338). The pool fits put most weight on the H0 Opus judge, which is the worst single config on humans. Cached judges, CPU only, no model calls, $0.

Harness and models: no LLM in the loop for this run. The four candidate judges are cached outputs of the VeriBench experiment 106 runs: H0_sol: Vals Valkyrie vb103_judge, openai/gpt-6-sol-high, prompt H0 (bare instructions); H0_opus: Vals Valkyrie vb103_judge, anthropic/claude-opus-5-5 max, prompt H0; H2_sol: Vals Valkyrie vb103_judge, openai/gpt-6-sol-high, prompt H2 (frozen judge); H2_opus: Vals Valkyrie vb103_judge, anthropic/claude-opus-5-5 max, prompt H2. Their outputs on both the fresh pool and the 75 come from the same runs (3 repeats; some pool items have 2). The AI-rater labels are the saved `score_0_5` cells of the six rater families in the checkout (experiment 106 Valkyrie `vb106_rater_v2`; astra, fable51, grok47, kimik3, mimo26pro, qwen38max; the seventh, argon, is not in the checkout). The fitting script was written and run in Claude Code (Sonnet 5.5).

## Data

- Pool: 591 fresh non-blank artifacts, 50 tasks, none shared with the 25 test tasks. Label per artifact: histogram of its AI-rater scores (0 to 5), pooled over families, personas and repeats; cells per item min 19, median 23, max 72. In experiment 106's leave-one-agent-out design each fresh item was rated by only about two families, so labels are noisier than the 75's.
- Test: the 75 human-rated artifacts, 25 tasks, 195 expert ratings, never used for fitting or choosing. Mean rating (0 to 1): humans 0.525, AI panel on the same 75 0.589, AI labels of the pool 0.739.
- Intervals: 2,000 joint bootstrap draws that resample pool tasks (and refit everything) and test tasks together.

## Test on the 75 human-rated artifacts (point [95% interval])

| Method | weights on H0_sol/H0_opus/H2_sol/H2_opus | RPS (main) | CE | TVD | Pearson | Spearman |
|---|---|---|---|---|---|---|
| constant (pool marginal) | - | 0.2271 [0.1729, 0.2870] | 2.107 [1.778, 2.490] | 0.6862 [0.6209, 0.7515] | undefined | undefined |
| equal-weight mixture | 0.25/0.25/0.25/0.25 | 0.1407 [0.1122, 0.1724] | 5.513 [4.269, 6.780] | 0.5233 [0.4433, 0.5989] | 0.761 [0.570, 0.871] | 0.677 [0.364, 0.849] |
| ② best single judge by pool Pearson | 0.00/1.00/0.00/0.00 | 0.2157 [0.1627, 0.2781] | 8.913 [7.393, 10.396] | 0.6600 [0.5600, 0.7622] | 0.614 [0.303, 0.805] | 0.585 [0.182, 0.815] |
| ② mixture maximizing pool Pearson | 0.18/0.55/0.09/0.18 | 0.1579 [0.1239, 0.1964] | 5.602 [4.355, 6.857] | 0.5619 [0.4771, 0.6452] | 0.714 [0.461, 0.845] | 0.636 [0.293, 0.833] |
| ② mixture maximizing pool Spearman (4,000-point simplex search) | 0.13/0.51/0.17/0.19 | 0.1578 [0.1206, 0.1931] | 5.605 [4.353, 6.891] | 0.5593 [0.4656, 0.6379] | 0.725 [0.507, 0.851] | 0.646 [0.310, 0.841] |
| ④ best single judge by pool CE | 0.00/1.00/0.00/0.00 | 0.2157 [0.1627, 0.2781] | 8.913 [7.393, 10.396] | 0.6600 [0.5600, 0.7622] | 0.614 [0.303, 0.805] | 0.585 [0.182, 0.815] |
| ④ mixture minimizing pool CE | 0.22/0.42/0.16/0.19 | 0.1490 [0.1175, 0.1838] | 5.553 [4.306, 6.818] | 0.5413 [0.4580, 0.6207] | 0.734 [0.509, 0.856] | 0.653 [0.309, 0.842] |
| ④ mixture minimizing pool RPS | 0.24/0.46/0.11/0.19 | 0.1511 [0.1199, 0.1867] | 5.565 [4.316, 6.832] | 0.5460 [0.4643, 0.6249] | 0.724 [0.483, 0.852] | 0.647 [0.290, 0.837] |
| ④ CE mixture plus temperature and rating bias (exploratory) | - | 0.1627 [0.1237, 0.2094] | 2.139 [1.733, 2.596] | 0.5698 [0.4929, 0.6449] | 0.726 [0.470, 0.860] | 0.618 [0.272, 0.815] |

Pearson and Spearman are undefined for the constant forecast. Reference rows (not fitted, not deployable): each cached judge alone on the 75, and the AI panel's own label distribution as a forecast of the human distribution on the same 75.

| Reference | RPS | CE | TVD | Pearson | Spearman |
|---|---|---|---|---|---|
| judge H0_sol alone | 0.2033 | 8.454 | 0.6289 | 0.573 | 0.498 |
| judge H0_opus alone | 0.2157 | 8.913 | 0.6600 | 0.614 | 0.585 |
| judge H2_sol alone | 0.1953 | 8.226 | 0.6267 | 0.696 | 0.664 |
| judge H2_opus alone | 0.1793 | 8.070 | 0.6000 | 0.775 | 0.763 |
| AI panel label of the same 75 as forecast | 0.1184 | 2.587 | 0.4471 | 0.809 | 0.741 |

## Paired differences on the 75 (first minus second; negative = first better for RPS, CE, TVD)

| Comparison | RPS | CE | Pearson | Spearman |
|---|---|---|---|---|
| ④ mixture minimizing pool CE minus ② mixture maximizing pool Pearson | -0.0089 [-0.0205, -0.0010] | -0.048 [-0.121, -0.008] | +0.020 [-0.008, +0.068] (includes 0) | +0.017 [-0.022, +0.059] (includes 0) |
| ④ mixture minimizing pool RPS minus ② mixture maximizing pool Pearson | -0.0068 [-0.0147, -0.0007] | -0.037 [-0.092, -0.004] | +0.010 [-0.009, +0.039] (includes 0) | +0.011 [-0.026, +0.034] (includes 0) |
| ④ mixture minimizing pool CE minus ② mixture maximizing pool Spearman (4,000-point simplex search) | -0.0088 [-0.0173, +0.0084] (includes 0) | -0.052 [-0.110, +0.035] (includes 0) | +0.009 [-0.058, +0.043] (includes 0) | +0.007 [-0.067, +0.042] (includes 0) |
| ④ mixture minimizing pool CE minus equal-weight mixture | +0.0083 [+0.0010, +0.0184] | +0.041 [+0.015, +0.077] | -0.027 [-0.088, +0.010] (includes 0) | -0.023 [-0.119, +0.029] (includes 0) |
| ② mixture maximizing pool Pearson minus equal-weight mixture | +0.0173 [+0.0040, +0.0355] | +0.089 [+0.038, +0.175] | -0.047 [-0.142, +0.015] (includes 0) | -0.041 [-0.156, +0.036] (includes 0) |
| ④ mixture minimizing pool CE minus constant (pool marginal) | -0.0781 [-0.1417, -0.0233] | +3.446 [+2.211, +4.718] | undefined | undefined |

## Controls

**(a) Fit on the 75 humans only** (same four configs, experiment 12's 20/5 task splits, 1000 splits, RPS on test tasks): constant 0.1836; equal_mixture 0.1407; corr_mixture_pearson 0.1425; ce_mixture 0.1338; rps_mixture 0.1324. ④ minus ②: -0.0088 [-0.0219, +0.0026]; ④ minus equal weights: -0.0069 [-0.0150, +0.0007].

**(b) Label shift versus judge quality.** Fit on groups G01 to G10 (441 items), score against AI labels of held-out fresh groups G11 to G13 (150 items), against the AI labels of the 75, and against the human labels of the 75 (RPS; fitted on the 441 only, single fit, no interval):

| Method | held-out fresh, AI labels | the 75, AI labels | the 75, human labels |
|---|---|---|---|
| constant (pool marginal) | 0.1429 | 0.1917 | 0.2372 |
| equal-weight mixture | 0.0770 | 0.0937 | 0.1407 |
| ② mixture maximizing pool Pearson | 0.0744 | 0.0986 | 0.1565 |
| ④ mixture minimizing pool CE | 0.0746 | 0.0949 | 0.1495 |
| ④ mixture minimizing pool RPS | 0.0744 | 0.0961 | 0.1503 |

## Plain reading

- Loss beats correlation, narrowly: the ④ CE mixture is ahead of the ② Pearson mixture on RPS (-0.0089 [-0.0205, -0.0010]), CE and TVD, and level on Pearson and Spearman. Against the Spearman-fitted mixture the RPS interval includes 0. This matches the guess I gave earlier (loss ahead on RPS), with a small gap.
- Big data from AI labels did not help against humans. Both fitted mixtures are worse than the equal-weight average of the four judges (0.1407); ④ minus equal is +0.0083 [+0.0010, +0.0184]. Fitting on the 75 human-rated artifacts themselves gave 0.1338, better than either pool-fitted mixture.
- Why, as far as the numbers show: the AI raters score these artifacts higher than humans (pool mean 0.74, humans 0.53) and the fits put most weight on the H0 Opus judge, which gets 42% of the weight in ④ and 55% in ②, although H0 Opus alone is the worst config against humans (RPS 0.216) and H2 Opus the best (RPS 0.179). Control (b) shows the same fits do well against AI labels (RPS about 0.075 on held-out fresh items) and worse against humans (about 0.15). This is an explanation from the tables, not a separate test.
- CE is dominated by near-zero probabilities (about 5.5 for every mixture against 2.1 for the constant); the exploratory temperature-and-bias head fixes CE (2.14) but not RPS (0.163, worse than the plain mixture).

## What was not checked

- Only four judge configs exist on both the pool and the 75, so this is a small first check, not a big search. No new inference, no agent search on the pool (version 2), no frontier arm.
- The seventh rater family (Argon) is missing from the checkout; each fresh item has labels from about two families, and the labels of different items come from different families.
- Judge outputs for the 75 here are experiment 106's own repeats of the four configs, not the experiment 100 caches used in experiments 10 to 17; I did not compare the two byte for byte.
- The frozen H2 prompt was designed using part of the 75's human ratings (experiment 106 report, not rechecked here), so the test is not clean of design-time exposure for the H2 configs. The test has 25 tasks; intervals are wide.
- Rater counts per cell were recounted from the saved cells in this run; the experiment 106 report's own numbers (panel agreement with experts, 0.770) were not rechecked.
