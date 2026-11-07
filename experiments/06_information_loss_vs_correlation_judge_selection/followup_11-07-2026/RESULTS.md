# Distance-objective selection: cached follow-up results

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/06_information_loss_vs_correlation_judge_selection/followup_11-07-2026/RESULTS.md>

**TLDR:** Neither first Wasserstein distance nor the specified Gaussian-kernel distance established an advantage over Spearman selection on its own held-out distance. This is an exploratory extension of the historical experiment, not fresh human validation.

Experiment `06_information_loss_vs_correlation_judge_selection`, condition `followup_11-07-2026`: 75 artifacts /25 tasks /19 task families /195 expert ratings; five cached judge candidates, three scalar calls per artifact. Five seeded partitions reuse the same sample. All 50 new selections finished; 200 prior selections were reused. There were zero new model calls and $0 new provider inference charges. Ordinary CPU execution on skampere3 took 8.98 seconds inside the 600-second bound; the supervisor exited 0.

## Answer and uncertainty

The notes appear to list W and MMD. We specified W as first Wasserstein distance (W1) and MMD as squared maximum mean discrepancy (MMD²), Gaussian kernel width 0.2 on normalized ratings r/5. These interpretations remain tentative pending handwriting clarification; the saved equations define what was actually tested.

| New selection objective | Its own test distance | Spearman-selected test distance | Difference, new minus Spearman; selection-refit 95% interval |
| --- | ---: | ---: | --- |
| W1 [0,1] | 0.204267 | 0.180445 | +0.023822 [-0.036327, +0.053333], p-val=n/a |
| MMD² [0,2] | 0.628975 | 0.521168 | +0.107807 [-0.128950, +0.171668], p-val=n/a |

Lower distances are better. Both point differences favor the Spearman-selected forecasts, but both intervals include zero. No confirmatory test or success threshold was specified, so this does not establish either superiority or equivalence. Intervals resample all 19 task families with their artifacts and repeat selection within each fixed fold: 1,000/1,000 valid paired draws for each contrast, no replacement retries. They do not remove upstream prompt/test exposure, estimate uncertainty over a new population of judges or raters, or refit language models.

## Same metric panel for every objective

Cross-entropy (CE) and forward Kullback–Leibler divergence (KL) use natural logs; Brier is the six-category sum [0,2]; ranked probability score (RPS) averages five ordinal thresholds [0,1]. Correlations compare expected rating with human mean. All losses below are lower better; correlations are higher better. These are point estimates; conditional intervals for the new objectives and full precision are in results/results.json. Those intervals condition on selected forecasts and must not replace the reselection intervals above.

| Selection objective | CE | Brier | RPS | Pearson | Spearman | Kendall | W1 | MMD² |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| brier | 8.8522 | 1.2803 | 0.2067 | 0.6398 | 0.6149 | 0.4831 | 0.2155 | 0.6162 |
| ce | 8.8675 | 1.2871 | 0.2032 | 0.6781 | 0.6711 | 0.5460 | 0.2080 | 0.5986 |
| kendall | 8.0979 | 1.1911 | 0.1793 | 0.7774 | 0.7692 | 0.6521 | 0.1804 | 0.5212 |
| mmd2 | 8.8636 | 1.2794 | 0.2126 | 0.6042 | 0.5803 | 0.4524 | 0.2219 | 0.6290 |
| pearson | 8.0979 | 1.1911 | 0.1793 | 0.7774 | 0.7692 | 0.6521 | 0.1804 | 0.5212 |
| rps | 8.7488 | 1.2690 | 0.2154 | 0.6007 | 0.5916 | 0.4648 | 0.2222 | 0.6318 |
| spearman | 8.0979 | 1.1911 | 0.1793 | 0.7774 | 0.7692 | 0.6521 | 0.1804 | 0.5212 |
| tvd | 8.8268 | 1.2838 | 0.2036 | 0.6707 | 0.6651 | 0.5362 | 0.2089 | 0.6021 |
| wasserstein1 | 8.2905 | 1.2095 | 0.1991 | 0.6692 | 0.6715 | 0.5476 | 0.2043 | 0.5744 |
| weighted_pmf | 8.7898 | 1.2640 | 0.2049 | 0.6192 | 0.5860 | 0.4563 | 0.2149 | 0.6007 |

| Selection objective | KL | Weighted PMF | TVD | MAE | Bias | Judge mean | Human mean |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| brier | 8.2863 | 0.2894 | 0.6511 | 0.2110 | 0.0597 | 0.5851 | 0.5253 |
| ce | 8.3016 | 0.2953 | 0.6511 | 0.2027 | 0.0816 | 0.6069 | 0.5253 |
| kendall | 7.5320 | 0.2790 | 0.6000 | 0.1760 | 0.1120 | 0.6373 | 0.5253 |
| mmd2 | 8.2977 | 0.2887 | 0.6511 | 0.2180 | 0.0492 | 0.5746 | 0.5253 |
| pearson | 7.5320 | 0.2790 | 0.6000 | 0.1760 | 0.1120 | 0.6373 | 0.5253 |
| rps | 8.1829 | 0.2885 | 0.6427 | 0.2194 | 0.0503 | 0.5756 | 0.5253 |
| spearman | 7.5320 | 0.2790 | 0.6000 | 0.1760 | 0.1120 | 0.6373 | 0.5253 |
| tvd | 8.2608 | 0.2920 | 0.6493 | 0.2043 | 0.0757 | 0.6011 | 0.5253 |
| wasserstein1 | 7.7246 | 0.2805 | 0.6124 | 0.2009 | 0.0727 | 0.5980 | 0.5253 |
| weighted_pmf | 8.2238 | 0.2885 | 0.6449 | 0.2107 | 0.0421 | 0.5675 | 0.5253 |

PMF means probability mass function; TVD means total variation distance; MAE means mean absolute error. Bias is judge minus human on [0,1]; positive means higher/lenient ratings. The means accompany the bias explicitly. Every task has exactly three artifacts, so equal artifact weights also give equal task weights.

## What these tests do and do not answer

- They add two selection objectives over the same historical fixed candidate pool. They do not train a new large language model or fix the prior Pearson optimizer. The prior 215/225 nonconverged Pearson fits remain disclosed in ../RESULTS.md.
- Three repeated scalar scores form a sparse histogram, not a model's native forecast of human disagreement. All prior reference ambiguities, noisy human frequencies and historical exposure carry forward.
- W1 and TVD against one observed rating are not generally proper per-observation probability losses. A Gaussian-kernel score is proper under its stated conditions; the MMD² distance used here is to a noisy empirical target. Do not group every distance under “proper loss.”
- Low conditional distributional error is stronger evidence than high mean/rank correlation alone, but no small historical study proves the full human distribution is learned. Matching pooled marginal histograms is insufficient. Neither new rater transfer, new solver transfer nor fresh human confirmation was measured here.
- Cross-entropy and forward KL remain the same selection criterion for fixed targets and weights. Properness does not guarantee better finite-sample results on every metric.

## Verification and reproduction

The procedure was committed at 693ad50 and the bounded supervisor at b012238 before execution. Controls checked exact equality, endpoint point masses, equal-mean/different-distribution examples, Pearson shift invariance, an independent Wasserstein implementation and independent kernel expectations. All 375 real candidate/artifact W1 values matched scipy.stats.wasserstein_distance. Reconstructed old results matched every published metric; all 50 new selections and 1,000 bootstrap draws were retained. Hashes and exit status are in results/terminal.json. Independent receipt verification is in results/verification.json.

Run scripts/run_distances.py with --data pointing at the unchanged private dataset, --out to a new results directory and --private-out to private bootstrap storage. The saved supervisor records the exact remote command. Aggregate results, choices and uncertainties are public; individual ratings, private input artifacts and bootstrap traces remain in the canonical ignored private store and the recorded remote execution directory.

The full transcript of the four new attachments, original files, source paths and SHA-256 hashes are preserved privately under private/06_information_loss_vs_correlation_judge_selection/inputs/notes_11-07-2026/. This public report does not disclose the private chat screenshot or participant ratings.

Copy-ready message: I checked the previous objective comparison and extended it with Wasserstein and a fixed Gaussian-kernel distance on the same historical ratings. Neither new objective established a held-out advantage over Spearman; fresh probability forecasts and human ratings are still needed for the stronger claim.

**TLDR-end:** [ttj: objective comparison] Both additional cached-distance tests are complete and do not resolve an advantage. The stronger fresh-data and stable-fitting questions remain open.
