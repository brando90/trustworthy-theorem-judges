# Results, experiment 13: toy, Pearson fit vs cross-entropy fit on nonlinear synthetic ratings

**TOY, works by construction. An illustration of the argument, not evidence about the real ratings.** CPU only, $0, numpy/scipy (Claude Code worker, Sonnet 5.5, 11-10-2026). No LLM judge is involved: the "judge" is a fitted function of one feature.

## Key findings (toy; written by hand from the tables below)

- **Gap that does not close:** with a calibrated head, the Pearson-fit judge plateaus at about 0.0072 (A) and 0.0057 (B) RPS excess and 0.115 (A) and 0.101 (B) CE excess in the n-to-infinity fit, and the sweep agrees (n = 2048: 0.0080 and 0.0073 RPS, 0.119 and 0.109 CE). Its Spearman and Pearson are the best of all fits (0.97 to 0.99) while its distribution is still wrong. The raw Pearson fit is worse and its excess grows with n (A: RPS 0.0097 at n = 20, 0.0251 at n = 2048), because its shape beyond the mean is set by the start and a ridge that weakens as n grows; that curve measures my setup choice as much as the objective.
- **Gap that closes:** the CE fit's excess falls roughly as a power law (alpha 0.62 to 0.89, intervals in the table) to 0.0007 (A) and 0.0037 (B) RPS and 0.0065 (A) and 0.022 (B) CE at n = 2048, close to the class floor (B: 0.0031 RPS, 0.0106 CE, from the fit, because the 13-feature class does not contain the truth exactly).
- **Not uniformly better:** below roughly n = 30 tasks (the real 20-task scale), in scenario A the raw Pearson fit is as good as or better than the CE fit on RPS (n = 20: 0.0097 vs 0.0113), and the Pearson + head variant is far worse (0.13). CE fitting wins on distribution metrics from about n = 60 on in these runs.
- **Tasks needed (fitted E + A n^-alpha, not a bound; seed-noise intervals only), CE fit:** within 0.01 RPS: about 33 (A) and 131 (B); within 0.05 CE: about 131 (A) and 306 (B); within 0.003 RPS: about 234 (A), not reached in B (floor 0.0031). Pearson + head: within 0.01 RPS about 542 (A) and 350 (B), a fragile number because its floor (0.0076) sits just under that target; within 0.05 CE never (floor 0.12 and 0.115). So on RPS at 0.01 the toy separates the fits only weakly; on CE and at 0.003 RPS it separates them clearly. My guess "tens to a few hundred tasks" holds for the CE fit here (33 to 306).
- Those counts are for this one-dimensional toy with a matched function class, 3 raters per task and a smooth truth. The real ratings (25 tasks) are too few to extrapolate a curve like this with confidence.

## Setup (details in README.md)

- Each task has a feature x in [-1, 1]. Human ratings 0 to 5 follow a beta-binomial whose spread depends nonlinearly on x: kappa(x) = exp(1.5 + 2.2 cos(1.5 pi x)), from U-shaped (disagreement) to tight.
- **Scenario A, same mean:** human mean 2.1 to 2.9 on a small linear drift in x, so the mean says almost nothing while the spread changes a lot.
- **Scenario B, monotone nonlinear mean:** human mean = 5(0.1 + 0.8((x+1)/2)^2), plus the same spread pattern. Spearman and Pearson are both high for any judge that gets the mean right.
- Every judge: softmax of a linear map of 13 cosine/sine features (same class). Fits differ only in the objective on the n training tasks (k = 3 raters each, empirical histogram): **CE** (④), **RPS** (second proper score), **Pearson** of the judge's mean vs the human mean (②), and **Pearson + head** (Pearson-fit score, then an ordinal head fitted by CE on that one scalar, the "score, then calibrate" practice). Same ridge c/n for all.
- Test: 500 fresh tasks per seed, scored against the TRUE distribution. Excess = loss minus the loss of the true distribution (excess RPS = mean over the 5 thresholds of (Qc-Pc)^2; excess CE = KL). 100 seeds per n; intervals are 95% bootstrap over seeds (train and test tasks are redrawn each seed, so this plays the role of the task bootstrap). n from 4, 8, 16, 20, 32, 64, 128, 256, 512, 1024, 2048.

## Scenario A (same mean, spread varies): held-out metrics by number of training tasks

**n = 20 training tasks** (mean over 100 seeds [95% CI]); RPS excess first (lower better)

| fit | RPS excess | CE excess | TVD | Spearman | Pearson |
|---|---|---|---|---|---|
| CE fit (④) | 0.0113 [0.0108, 0.0119] | 0.1403 [0.1360, 0.1448] | 0.2092 [0.2055, 0.2130] | 0.247 [0.186, 0.303] | 0.259 [0.198, 0.316] |
| RPS fit | 0.0090 [0.0088, 0.0092] | 0.1172 [0.1161, 0.1183] | 0.1949 [0.1939, 0.1960] | 0.235 [0.176, 0.292] | 0.249 [0.185, 0.309] |
| Pearson fit (②, raw) | 0.0097 [0.0096, 0.0098] | 0.1316 [0.1302, 0.1331] | 0.2078 [0.2065, 0.2091] | 0.046 [-0.000, 0.092] | 0.036 [-0.021, 0.092] |
| Pearson fit + calibrated head | 0.1299 [0.1200, 0.1398] | 2.6570 [2.3607, 2.9350] | 0.4797 [0.4588, 0.4998] | 0.049 [0.004, 0.095] | 0.047 [0.003, 0.092] |

**n = 64 training tasks** (mean over 100 seeds [95% CI]); RPS excess first (lower better)

| fit | RPS excess | CE excess | TVD | Spearman | Pearson |
|---|---|---|---|---|---|
| CE fit (④) | 0.0085 [0.0081, 0.0089] | 0.1060 [0.1026, 0.1095] | 0.1779 [0.1749, 0.1809] | 0.379 [0.334, 0.426] | 0.398 [0.351, 0.442] |
| RPS fit | 0.0077 [0.0075, 0.0079] | 0.0973 [0.0960, 0.0985] | 0.1758 [0.1743, 0.1773] | 0.383 [0.336, 0.428] | 0.408 [0.358, 0.454] |
| Pearson fit (②, raw) | 0.0102 [0.0100, 0.0104] | 0.1459 [0.1420, 0.1497] | 0.2162 [0.2133, 0.2192] | 0.210 [0.174, 0.248] | 0.176 [0.132, 0.220] |
| Pearson fit + calibrated head | 0.0375 [0.0350, 0.0400] | 0.3898 [0.3483, 0.4338] | 0.2698 [0.2640, 0.2755] | 0.211 [0.177, 0.247] | 0.204 [0.165, 0.242] |

**n = 256 training tasks** (mean over 100 seeds [95% CI]); RPS excess first (lower better)

| fit | RPS excess | CE excess | TVD | Spearman | Pearson |
|---|---|---|---|---|---|
| CE fit (④) | 0.0032 [0.0031, 0.0034] | 0.0391 [0.0378, 0.0404] | 0.1067 [0.1049, 0.1087] | 0.674 [0.647, 0.702] | 0.677 [0.652, 0.701] |
| RPS fit | 0.0042 [0.0041, 0.0044] | 0.0544 [0.0535, 0.0553] | 0.1273 [0.1261, 0.1284] | 0.682 [0.653, 0.710] | 0.685 [0.659, 0.709] |
| Pearson fit (②, raw) | 0.0130 [0.0122, 0.0139] | 0.1916 [0.1829, 0.2019] | 0.2434 [0.2388, 0.2483] | 0.485 [0.456, 0.513] | 0.489 [0.462, 0.519] |
| Pearson fit + calibrated head | 0.0136 [0.0132, 0.0140] | 0.1484 [0.1459, 0.1512] | 0.2104 [0.2089, 0.2119] | 0.485 [0.455, 0.515] | 0.490 [0.461, 0.517] |

**n = 2048 training tasks** (mean over 100 seeds [95% CI]); RPS excess first (lower better)

| fit | RPS excess | CE excess | TVD | Spearman | Pearson |
|---|---|---|---|---|---|
| CE fit (④) | 0.0007 [0.0007, 0.0007] | 0.0065 [0.0064, 0.0067] | 0.0425 [0.0419, 0.0432] | 0.902 [0.896, 0.907] | 0.891 [0.886, 0.896] |
| RPS fit | 0.0009 [0.0008, 0.0009] | 0.0134 [0.0132, 0.0136] | 0.0570 [0.0564, 0.0576] | 0.907 [0.902, 0.913] | 0.897 [0.892, 0.902] |
| Pearson fit (②, raw) | 0.0251 [0.0225, 0.0283] | 0.3937 [0.3561, 0.4370] | 0.3205 [0.3081, 0.3337] | 0.855 [0.846, 0.863] | 0.845 [0.836, 0.853] |
| Pearson fit + calibrated head | 0.0080 [0.0079, 0.0081] | 0.1190 [0.1182, 0.1198] | 0.1956 [0.1948, 0.1964] | 0.855 [0.845, 0.863] | 0.844 [0.835, 0.852] |

**n to infinity** (fit on a dense grid of tasks with the true distributions, no sampling noise, ridge to 0):

| fit | RPS excess | CE excess | TVD | Spearman | Pearson |
|---|---|---|---|---|---|
| CE fit (④) | 0.0003 | 0.0014 | 0.0124 | 0.9474 | 0.9395 |
| RPS fit | 0.0002 | 0.0021 | 0.0172 | 0.9551 | 0.9508 |
| Pearson fit (②, raw) | 0.0872 | 5.7374 | 0.6585 | 0.9988 | 0.9987 |
| Pearson fit + calibrated head | 0.0072 | 0.1153 | 0.1952 | 0.9988 | 0.9987 |

## Scenario B (monotone nonlinear mean, spread varies): held-out metrics by number of training tasks

**n = 20 training tasks** (mean over 100 seeds [95% CI]); RPS excess first (lower better)

| fit | RPS excess | CE excess | TVD | Spearman | Pearson |
|---|---|---|---|---|---|
| CE fit (④) | 0.0399 [0.0383, 0.0417] | 0.2499 [0.2413, 0.2590] | 0.2692 [0.2637, 0.2744] | 0.704 [0.680, 0.728] | 0.733 [0.713, 0.752] |
| RPS fit | 0.0620 [0.0608, 0.0632] | 0.3418 [0.3361, 0.3476] | 0.3378 [0.3354, 0.3403] | 0.667 [0.643, 0.690] | 0.691 [0.672, 0.710] |
| Pearson fit (②, raw) | 0.0897 [0.0891, 0.0903] | 0.4835 [0.4804, 0.4866] | 0.3961 [0.3945, 0.3975] | 0.197 [0.137, 0.258] | 0.088 [0.022, 0.149] |
| Pearson fit + calibrated head | 0.1605 [0.1451, 0.1767] | 2.4462 [2.1541, 2.7470] | 0.4598 [0.4407, 0.4794] | 0.195 [0.135, 0.256] | 0.247 [0.186, 0.301] |

**n = 64 training tasks** (mean over 100 seeds [95% CI]); RPS excess first (lower better)

| fit | RPS excess | CE excess | TVD | Spearman | Pearson |
|---|---|---|---|---|---|
| CE fit (④) | 0.0156 [0.0148, 0.0164] | 0.1240 [0.1199, 0.1281] | 0.1765 [0.1730, 0.1800] | 0.889 [0.880, 0.897] | 0.905 [0.897, 0.912] |
| RPS fit | 0.0320 [0.0311, 0.0328] | 0.1922 [0.1885, 0.1959] | 0.2517 [0.2489, 0.2544] | 0.872 [0.862, 0.880] | 0.886 [0.879, 0.893] |
| Pearson fit (②, raw) | 0.0902 [0.0896, 0.0908] | 0.4871 [0.4838, 0.4904] | 0.3972 [0.3956, 0.3988] | 0.777 [0.759, 0.795] | 0.765 [0.734, 0.793] |
| Pearson fit + calibrated head | 0.0319 [0.0294, 0.0348] | 0.2643 [0.2412, 0.2930] | 0.2479 [0.2439, 0.2525] | 0.777 [0.760, 0.795] | 0.805 [0.784, 0.825] |

**n = 256 training tasks** (mean over 100 seeds [95% CI]); RPS excess first (lower better)

| fit | RPS excess | CE excess | TVD | Spearman | Pearson |
|---|---|---|---|---|---|
| CE fit (④) | 0.0068 [0.0065, 0.0071] | 0.0539 [0.0524, 0.0553] | 0.1058 [0.1038, 0.1079] | 0.929 [0.924, 0.934] | 0.952 [0.949, 0.954] |
| RPS fit | 0.0114 [0.0111, 0.0117] | 0.0862 [0.0847, 0.0877] | 0.1470 [0.1453, 0.1489] | 0.928 [0.924, 0.933] | 0.949 [0.947, 0.951] |
| Pearson fit (②, raw) | 0.0917 [0.0909, 0.0925] | 0.5118 [0.5063, 0.5177] | 0.4045 [0.4025, 0.4067] | 0.928 [0.924, 0.932] | 0.948 [0.946, 0.951] |
| Pearson fit + calibrated head | 0.0119 [0.0116, 0.0123] | 0.1348 [0.1332, 0.1364] | 0.1986 [0.1969, 0.2004] | 0.928 [0.924, 0.932] | 0.951 [0.949, 0.953] |

**n = 2048 training tasks** (mean over 100 seeds [95% CI]); RPS excess first (lower better)

| fit | RPS excess | CE excess | TVD | Spearman | Pearson |
|---|---|---|---|---|---|
| CE fit (④) | 0.0037 [0.0036, 0.0039] | 0.0222 [0.0216, 0.0227] | 0.0540 [0.0533, 0.0548] | 0.948 [0.946, 0.950] | 0.970 [0.969, 0.971] |
| RPS fit | 0.0038 [0.0037, 0.0039] | 0.0372 [0.0366, 0.0378] | 0.0732 [0.0723, 0.0741] | 0.957 [0.955, 0.959] | 0.974 [0.973, 0.975] |
| Pearson fit (②, raw) | 0.0951 [0.0932, 0.0973] | 0.5957 [0.5812, 0.6117] | 0.4266 [0.4224, 0.4313] | 0.973 [0.971, 0.974] | 0.985 [0.984, 0.986] |
| Pearson fit + calibrated head | 0.0073 [0.0072, 0.0074] | 0.1091 [0.1084, 0.1098] | 0.1792 [0.1784, 0.1801] | 0.973 [0.971, 0.974] | 0.983 [0.983, 0.984] |

**n to infinity** (fit on a dense grid of tasks with the true distributions, no sampling noise, ridge to 0):

| fit | RPS excess | CE excess | TVD | Spearman | Pearson |
|---|---|---|---|---|---|
| CE fit (④) | 0.0035 | 0.0172 | 0.0368 | 0.9479 | 0.9704 |
| RPS fit | 0.0017 | 0.4552 | 0.0929 | 0.9842 | 0.9929 |
| Pearson fit (②, raw) | 0.0281 | 3.6023 | 0.4176 | 0.9961 | 0.9988 |
| Pearson fit + calibrated head | 0.0057 | 0.1011 | 0.1727 | 0.9962 | 0.9946 |

## Power-law fit and the number of training tasks needed

Form fitted, per scenario and fit: **excess(n) = E + A n^(-alpha)**, nonlinear least squares in log space on the seed-mean curve over n >= 16, E >= 0 (a floor), alpha in [0, 4]. Intervals: 300 bootstrap resamples of the seeds. n needed = (A / (target - E))^(1/alpha), "not reached" when the fitted floor E is at or above the target. This is an empirical curve fit to simulated data, **not a proven bound**; it holds only for this toy, this function class and k = 3 raters per task; it says nothing about misspecified classes, other noise, or the real ratings. Targets: 0.01 RPS and 0.05 CE above the true distribution; a stricter 0.003 RPS target is added because the 0.01 target turns out not to separate the fits.

**Scenario A**

| fit | metric | alpha [95% CI] | floor E [95% CI] | n for target | 95% CI of n |
|---|---|---|---|---|---|
| CE fit (④) | rps_excess <= 0.01 | 0.62 [0.61, 0.63] | 0.0000 [0.0000, 0.0000] | 33 | [32, 34] (unreachable in 0% of resamples) |
| CE fit (④) | rps_excess <= 0.003 | 0.62 [0.61, 0.63] | 0.0000 [0.0000, 0.0000] | 234 | [228, 241] (unreachable in 0% of resamples) |
| CE fit (④) | ce_excess <= 0.05 | 0.66 [0.65, 0.66] | 0.0000 [0.0000, 0.0000] | 131 | [129, 133] (unreachable in 0% of resamples) |
| RPS fit | rps_excess <= 0.01 | 0.48 [0.47, 0.48] | 0.0000 [0.0000, 0.0000] | 24 | [23, 24] (unreachable in 0% of resamples) |
| RPS fit | rps_excess <= 0.003 | 0.48 [0.47, 0.48] | 0.0000 [0.0000, 0.0000] | 295 | [289, 302] (unreachable in 0% of resamples) |
| RPS fit | ce_excess <= 0.05 | 0.44 [0.44, 0.45] | 0.0000 [0.0000, 0.0000] | 192 | [190, 194] (unreachable in 0% of resamples) |
| Pearson fit (②, raw) | rps_excess | n/a: curve does not decay with n (rises as the ridge c/n weakens), power law not applicable | | not reached | |
| Pearson fit (②, raw) | ce_excess | n/a: curve does not decay with n (rises as the ridge c/n weakens), power law not applicable | | not reached | |
| Pearson fit + calibrated head | rps_excess <= 0.01 | 1.19 [1.15, 1.23] | 0.0076 [0.0073, 0.0077] | 542 | [521, 562] (unreachable in 0% of resamples) |
| Pearson fit + calibrated head | rps_excess <= 0.003 | 1.19 [1.15, 1.23] | 0.0076 [0.0073, 0.0077] | not reached (floor above target) | [nan, inf] (unreachable in 100% of resamples) |
| Pearson fit + calibrated head | ce_excess <= 0.05 | 1.89 [1.81, 1.98] | 0.1206 [0.1188, 0.1226] | not reached (floor above target) | [nan, inf] (unreachable in 100% of resamples) |

**Scenario B**

| fit | metric | alpha [95% CI] | floor E [95% CI] | n for target | 95% CI of n |
|---|---|---|---|---|---|
| CE fit (④) | rps_excess <= 0.01 | 0.89 [0.86, 0.92] | 0.0031 [0.0030, 0.0033] | 131 | [127, 137] (unreachable in 0% of resamples) |
| CE fit (④) | rps_excess <= 0.003 | 0.89 [0.86, 0.92] | 0.0031 [0.0030, 0.0033] | not reached (floor above target) | [110,836, inf] (unreachable in 95% of resamples) |
| CE fit (④) | ce_excess <= 0.05 | 0.67 [0.65, 0.69] | 0.0106 [0.0094, 0.0119] | 306 | [297, 314] (unreachable in 0% of resamples) |
| RPS fit | rps_excess <= 0.01 | 0.69 [0.67, 0.70] | 0.0010 [0.0008, 0.0012] | 339 | [331, 347] (unreachable in 0% of resamples) |
| RPS fit | rps_excess <= 0.003 | 0.69 [0.67, 0.70] | 0.0010 [0.0008, 0.0012] | 3,047 | [2,806, 3,311] (unreachable in 0% of resamples) |
| RPS fit | ce_excess <= 0.05 | 0.58 [0.57, 0.59] | 0.0133 [0.0119, 0.0147] | 880 | [866, 896] (unreachable in 0% of resamples) |
| Pearson fit (②, raw) | rps_excess | n/a: curve does not decay with n (rises as the ridge c/n weakens), power law not applicable | | not reached | |
| Pearson fit (②, raw) | ce_excess | n/a: curve does not decay with n (rises as the ridge c/n weakens), power law not applicable | | not reached | |
| Pearson fit + calibrated head | rps_excess <= 0.01 | 1.44 [1.39, 1.51] | 0.0076 [0.0074, 0.0078] | 350 | [331, 369] (unreachable in 0% of resamples) |
| Pearson fit + calibrated head | rps_excess <= 0.003 | 1.44 [1.39, 1.51] | 0.0076 [0.0074, 0.0078] | not reached (floor above target) | [nan, inf] (unreachable in 100% of resamples) |
| Pearson fit + calibrated head | ce_excess <= 0.05 | 2.11 [2.02, 2.22] | 0.1150 [0.1135, 0.1165] | not reached (floor above target) | [nan, inf] (unreachable in 100% of resamples) |

Sanity reference, not fitted: for a well-specified parametric model the excess CE is about (free parameters)/(2 x number of ratings) = 65/(2 x 3n), about 11/n, which would mean alpha = 1. It matches the CE fit in size (scenario A at n = 256: about 0.043 predicted, 0.039 measured; at n = 2048: 0.0053 predicted, 0.0065 measured), but the fitted exponents over n = 16 to 2048 are lower (0.6 to 0.9). Over this range the curve is probably not yet in its asymptotic regime (a guess, not tested), so extrapolating far beyond n = 2048 or below n = 16 would be unsafe. Intervals here cover seed noise only, not the choice of functional form or of the fitting range.
