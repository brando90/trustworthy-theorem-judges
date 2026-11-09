<!-- TLDR: Weighted mixture training has lower observed held-out weighted loss than stable Pearson training, but the paired interval includes zero; softmax differences are also unresolved. -->
# Weighted training results — 11-08-2026

**Status: COMPLETE, independently verified.** Weighted squared probability mass function (PMF) training reduced observed held-out weighted loss from **0.202068 to 0.191659**, but the paired difference was **−0.010409 [−0.061911, +0.005933]** (95% task-family bootstrap interval with both mixtures refitted; 998/1,000 valid draws; p-val=n/a). This historical sample does **not resolve an advantage** over stable Pearson training. All 50 primary fits passed their optimality checks, and all 900 secondary softmax fits converged.

**Collaborator message:** “I tested weighted probability training against a stable correlation baseline on the same family-held-out artifacts. The weighted mixture looks better on several distribution scores, but the uncertainty still includes no improvement, so I would treat this as exploratory evidence rather than a demonstrated win.”

**Experiment:** `06_information_loss_vs_correlation_judge_selection/training_followup_11-08-2026`. All rows below belong to this condition. [Protocol](PROTOCOL.md) · [Configuration](protocol.json) · [Mathematical baseline](MATH_baseline.md) · [Raw aggregate results](results/results.json) · [Verification](results/verification.json) · [Resample verification](results/verification_refit_samples.json) · [Checkpoint](CKPT_training_followup.md).

## What was tested

Both primary methods fit one global nonnegative mixture of the same five cached judge histograms, with weights summing to one. Weighted training minimizes the human-frequency-weighted squared PMF distance; Pearson training globally maximizes correlation between expected ratings. The predictions, folds and held-out metric panel are identical. The numerical baseline replaces the earlier unstable comparison with a separately frozen condition; it does not repair or relabel the old softmax Pearson fits.

A secondary experiment fits the same six-category affine softmax family under weighted loss, cross-entropy, Brier loss and ranked probability score. Four inner family folds choose regularization by ranked probability score for every method. Comparing a softmax result with a mixture result changes the model class as well as the objective, so that comparison cannot isolate the objective.

Data: 75 artifacts, 25 tasks, 19 task families, 195 human ratings, five cached judges with three scalar ratings per artifact. Each of five fixed partitions has five outer task-family folds. Every method produces 375 held-out forecast rows across the five overlapping partitions; this is still 75 distinct artifacts, not 375 independent observations. Means and absolute errors use rating/5; log losses use natural logarithms. Cached model/rubric provenance remains in [the source audit](../source_audit.json).

## Primary matched mixture comparison

Each point estimate averages the five pooled out-of-fold results. The last column is weighted minus Pearson, with the 95% family-bootstrap interval **including mixture refitting**. Lower losses/errors are better; higher correlations are better; a bias closer to zero is better. No hypothesis test was prespecified (p-val=n/a).

| Held-out metric | Weighted mixture | Pearson mixture | Paired difference [95% interval] |
|---|---:|---:|---:|
| Weighted squared PMF loss | 0.191659 | 0.202068 | -0.010409 [-0.061911, +0.005933] |
| Cross-entropy | 5.659607 | 5.751842 | -0.092235 [-1.369972, +0.178213] |
| Forward Kullback–Leibler divergence | 5.093675 | 5.185910 | -0.092235 [-1.369972, +0.178213] |
| Brier loss | 0.871819 | 0.913693 | -0.041873 [-0.242952, +0.009162] |
| Normalized ranked probability score | 0.134227 | 0.143634 | -0.009408 [-0.044143, +0.003470] |
| Total variation distance | 0.504990 | 0.518075 | -0.013086 [-0.085325, +0.013593] |
| Pearson r | 0.768025 | 0.753947 | +0.014078 [-0.097808, +0.139982] |
| Spearman rho | 0.669717 | 0.687232 | -0.017516 [-0.127915, +0.115369] |
| Kendall tau | 0.509416 | 0.526896 | -0.017480 [-0.111877, +0.100145] |
| Mean absolute error | 0.156471 | 0.156112 | +0.000359 [-0.037272, +0.018729] |
| Mean bias (judge minus human) | 0.051370 | 0.063496 | -0.012125 [-0.066024, +0.025066] |
| Human mean | 0.525333 | 0.525333 | +0.000000 [+0.000000, +0.000000] |
| Judge mean | 0.576704 | 0.588829 | -0.012125 [-0.066024, +0.025066] |
| Human empirical entropy | 0.565932 | 0.565932 | +0.000000 [+0.000000, +0.000000] |

Weighted training had lower observed weighted distance, cross-entropy, Brier loss, ranked probability score and total variation. It also had higher observed held-out Pearson correlation, while Pearson training had higher Spearman and Kendall correlations. Every paired interval for these contrasts includes zero. Absolute agreement also has no resolved advantage: mean absolute errors are 0.156471 and 0.156112, respectively. Both methods rate higher than the human mean (0.525333): weighted mean 0.576704, bias +0.051370; Pearson mean 0.588829, bias +0.063496.

Training behaved as intended: the unweighted average over the 25 training folds gives weighted loss 0.184840 for weighted fitting versus 0.209614 for Pearson fitting, and training Pearson 0.775709 versus 0.808762. These training summaries are diagnostics, not held-out evidence. Globally optimizing training correlation did not guarantee the highest held-out correlation.

## Secondary softmax comparison

All four methods use the same probability family, features, initialization convention, optimizer limits, regularization grid and validation score. Each has 225 fits, including 25 final outer-training refits. All 900 fits converged; iteration counts ranged from 16 to 151. The table is descriptive; paired uncertainty follows.

| Training objective | Weighted PMF loss | Cross-entropy | Brier | Ranked probability score | Pearson |
|---|---:|---:|---:|---:|---:|
| Weighted softmax | 0.153445 | 1.524401 | 0.731237 | 0.117856 | 0.733365 |
| Cross-entropy softmax | 0.155547 | 1.527168 | 0.730275 | 0.117429 | 0.735567 |
| Brier softmax | 0.154337 | 1.496757 | 0.721035 | 0.116142 | 0.736206 |
| Ranked-score softmax | 0.157551 | 1.555056 | 0.723495 | 0.118396 | 0.727835 |
| Training-marginal constant | 0.258201 | 1.928001 | 0.869580 | 0.187208 | -0.404177 |

Weighted softmax has the lowest observed weighted PMF loss of these four fitted objectives, but none of its weighted-loss contrasts resolves an advantage. Brier training has the lowest observed cross-entropy, Brier and ranked probability scores in this condition; this does not establish a general winner. The constant is fitted independently in each outer training fold, so its pooled out-of-fold expected ratings vary and its pooled correlation can be negative even though it is constant within a fold.

| Weighted softmax minus | Weighted PMF difference [95% interval] | Cross-entropy difference [95% interval] | Ranked-score difference [95% interval] |
|---|---:|---:|---:|
| Cross-entropy softmax | -0.002102 [-0.014796, +0.009861] | -0.002767 [-0.206782, +0.173742] | +0.000427 [-0.007781, +0.010060] |
| Brier softmax | -0.000893 [-0.008727, +0.005759] | +0.027645 [-0.042223, +0.096678] | +0.001713 [-0.003063, +0.006086] |
| Ranked-score softmax | -0.004107 [-0.016691, +0.009055] | -0.030655 [-0.132849, +0.058070] | -0.000540 [-0.007669, +0.005443] |

These secondary intervals use 1,000 paired task-family resamples of the **fixed fitted predictions**; they exclude fitting and regularization-selection uncertainty. They must not be presented as full-procedure intervals. All draws were valid; p-val=n/a.

## Verification, failures and uncertainty limits

The full manifest completed in 56.288 seconds on one CPU thread on skampere3: 50 mixture fits, 900 softmax fits, 100 regularization choices, 175 final models and 2,625 forecast rows including the constant. Independent verification reconstructed every final forecast, checked all 900 training-only transformations, reproduced all 100 validation choices, checked all 50 mixture certificates and recomputed all 14 aggregate metrics. Source and result hashes match the frozen launch revision `6e8f609011e539ca41e7e1e0015f8458513d3fa2`. Python 3.12.3, NumPy 2.2.6, SciPy 1.17.1.

The earlier preflight summary listed different installed package versions; the run receipt above is authoritative. See [environment clarification](ENVIRONMENT_NOTE.md). Both control suites passed inside the actual scientific process before empirical fitting. No scientific settings or results were changed.

The 1,000 paired family-bootstrap draws attempted 49,049 mixture fits. Empty test folds need no fits. Two draws failed the frozen 1e-8 certificate gate and remain invalid: draw 192 failed the weighted simplex gap (1.38010e-7); draw 562 failed the Pearson cone certificate (4.34071e-8). No tolerance was relaxed and no draw was replaced. The reported refit intervals condition on the 998 successful draws, so they have this numerical missingness limitation. No training correlation was undefined. Independent replay reproduced both failures and draws 0, 499 and 999; the largest metric discrepancy was 3.33e-16. The replay validates existing evidence and creates no new resampling draws.

These are exploratory results on previously inspected historical ratings and a fixed candidate pool, not a fresh sealed test. Resampling covers task-family sampling and mixture-weight refitting conditional on the fixed partitions and cached ratings. It does not cover upstream judge/prompt selection, repeated human sampling, new solvers or new rater populations. Two or three human ratings per artifact give sparse empirical histograms; three sampled scalar model ratings are not native probability forecasts of human uncertainty. Standard deviations over five overlapping repartitions quantify split sensitivity, not five independent experiments.

Weighted squared PMF distance here is mean_i sum_r p_ir (p_ir − q_ir)^2. It is an empirical distribution distance, not the single-observation loss (1 − q_R)^2 and not a claim that this weighting is a proper scoring rule for a new individual rating. Brier and ranked probability scores average their ordinary categorical/ordinal scoring rules over available human ratings.

No new inference calls were made; provider inference charges were $0. Subscription coordination usage was not measured. Individual ratings, forecasts, fitted weights and resampling arrays are retained in ignored canonical private storage; public evidence contains aggregates only.

## Which ideas remain untested

This phase completes weighted-PMF numerical training and a stable, matched Pearson baseline. Earlier conditions already tested fixed-candidate selection with correlation, cross-entropy, weighted PMF, Brier, ranked probability score, total variation, Wasserstein and Gaussian-kernel distance. The earlier softmax experiments and this phase are fitted mappings of cached ratings.

Still untested here: direct language-model or agent-prompt optimization under these objectives; native six-category probability forecasts; a fresh sealed human-rating comparison; transfer to unseen solvers and raters; direct stable Spearman/Kendall training; Wasserstein/Gaussian-kernel training; and softmax uncertainty that refits the full training/validation procedure. The focused literature check also remains a focused check, not a systematic frontier-wide survey. These require separately specified conditions; no claim of their completion follows from this run.

## Full common metric panel and variability

Every row below shows the point estimate, a 95% family-bootstrap interval conditional on fixed predictions, and the standard deviation (SD) across the five overlapping repartitions. These per-method intervals differ from the primary paired **refit** intervals above. Each method has 1,000 valid conditional draws. All metrics and full paired contrasts are also machine-readable in results/results.json.

### Weighted mixture

| Metric | Estimate [conditional 95% interval] | Repartition SD (5) |
|---|---:|---:|
| Weighted squared PMF loss | 0.191659 [0.144738, 0.240518] | 0.002490 |
| Cross-entropy | 5.659607 [4.276888, 6.815278] | 0.090464 |
| Forward Kullback–Leibler divergence | 5.093675 [3.723412, 6.241433] | 0.090464 |
| Brier loss | 0.871819 [0.740111, 0.974289] | 0.008863 |
| Normalized ranked probability score | 0.134227 [0.105679, 0.157220] | 0.001664 |
| Total variation distance | 0.504990 [0.416682, 0.575422] | 0.003469 |
| Pearson r | 0.768025 [0.562598, 0.893054] | 0.004946 |
| Spearman rho | 0.669717 [0.318316, 0.892428] | 0.005490 |
| Kendall tau | 0.509416 [0.218336, 0.752309] | 0.008451 |
| Mean absolute error | 0.156471 [0.119649, 0.186061] | 0.001841 |
| Mean bias (judge minus human) | 0.051370 [-0.024992, 0.117709] | 0.002609 |
| Human mean | 0.525333 [0.411848, 0.637973] | 0.000000 |
| Judge mean | 0.576704 [0.468939, 0.682336] | 0.002609 |
| Human empirical entropy | 0.565932 [0.473941, 0.638212] | 0.000000 |

### Pearson mixture

| Metric | Estimate [conditional 95% interval] | Repartition SD (5) |
|---|---:|---:|
| Weighted squared PMF loss | 0.202068 [0.150553, 0.253918] | 0.004982 |
| Cross-entropy | 5.751842 [4.353150, 6.870918] | 0.054036 |
| Forward Kullback–Leibler divergence | 5.185910 [3.855867, 6.291002] | 0.054036 |
| Brier loss | 0.913693 [0.749274, 1.057209] | 0.020042 |
| Normalized ranked probability score | 0.143634 [0.105229, 0.175852] | 0.005013 |
| Total variation distance | 0.518075 [0.416123, 0.601497] | 0.009150 |
| Pearson r | 0.753947 [0.544495, 0.902743] | 0.025744 |
| Spearman rho | 0.687232 [0.339724, 0.901420] | 0.015152 |
| Kendall tau | 0.526896 [0.229854, 0.765237] | 0.017306 |
| Mean absolute error | 0.156112 [0.106739, 0.196615] | 0.005898 |
| Mean bias (judge minus human) | 0.063496 [-0.015574, 0.138499] | 0.005277 |
| Human mean | 0.525333 [0.411848, 0.637973] | 0.000000 |
| Judge mean | 0.588829 [0.476664, 0.694696] | 0.005277 |
| Human empirical entropy | 0.565932 [0.473941, 0.638212] | 0.000000 |

### Weighted softmax

| Metric | Estimate [conditional 95% interval] | Repartition SD (5) |
|---|---:|---:|
| Weighted squared PMF loss | 0.153445 [0.118430, 0.192076] | 0.009905 |
| Cross-entropy | 1.524401 [1.343507, 1.698348] | 0.054498 |
| Forward Kullback–Leibler divergence | 0.958469 [0.784820, 1.155935] | 0.054498 |
| Brier loss | 0.731237 [0.655643, 0.778079] | 0.017288 |
| Normalized ranked probability score | 0.117856 [0.096301, 0.142155] | 0.005657 |
| Total variation distance | 0.487215 [0.441202, 0.525632] | 0.022840 |
| Pearson r | 0.733365 [0.509681, 0.890237] | 0.027365 |
| Spearman rho | 0.650816 [0.338391, 0.855116] | 0.021783 |
| Kendall tau | 0.491223 [0.226010, 0.699689] | 0.023256 |
| Mean absolute error | 0.144005 [0.111897, 0.178193] | 0.010414 |
| Mean bias (judge minus human) | 0.008079 [-0.069196, 0.072786] | 0.011240 |
| Human mean | 0.525333 [0.411848, 0.637973] | 0.000000 |
| Judge mean | 0.533412 [0.444423, 0.610546] | 0.011240 |
| Human empirical entropy | 0.565932 [0.473941, 0.638212] | 0.000000 |

### Cross-entropy softmax

| Metric | Estimate [conditional 95% interval] | Repartition SD (5) |
|---|---:|---:|
| Weighted squared PMF loss | 0.155547 [0.114981, 0.201842] | 0.006791 |
| Cross-entropy | 1.527168 [1.247506, 1.838576] | 0.055921 |
| Forward Kullback–Leibler divergence | 0.961236 [0.691540, 1.305159] | 0.055921 |
| Brier loss | 0.730275 [0.638215, 0.793351] | 0.016476 |
| Normalized ranked probability score | 0.117429 [0.090763, 0.146867] | 0.005989 |
| Total variation distance | 0.466800 [0.403180, 0.518027] | 0.017717 |
| Pearson r | 0.735567 [0.495797, 0.905112] | 0.024699 |
| Spearman rho | 0.658670 [0.335459, 0.877960] | 0.030257 |
| Kendall tau | 0.503974 [0.232007, 0.721609] | 0.033382 |
| Mean absolute error | 0.139349 [0.103497, 0.177114] | 0.005574 |
| Mean bias (judge minus human) | -0.006812 [-0.090716, 0.059689] | 0.011730 |
| Human mean | 0.525333 [0.411848, 0.637973] | 0.000000 |
| Judge mean | 0.518521 [0.422197, 0.605016] | 0.011730 |
| Human empirical entropy | 0.565932 [0.473941, 0.638212] | 0.000000 |

### Brier softmax

| Metric | Estimate [conditional 95% interval] | Repartition SD (5) |
|---|---:|---:|
| Weighted squared PMF loss | 0.154337 [0.118832, 0.195805] | 0.005315 |
| Cross-entropy | 1.496757 [1.308053, 1.700881] | 0.026629 |
| Forward Kullback–Leibler divergence | 0.930824 [0.748750, 1.152535] | 0.026629 |
| Brier loss | 0.721035 [0.639724, 0.772286] | 0.010222 |
| Normalized ranked probability score | 0.116142 [0.094078, 0.141811] | 0.002864 |
| Total variation distance | 0.481921 [0.433982, 0.523535] | 0.013007 |
| Pearson r | 0.736206 [0.509897, 0.896616] | 0.019842 |
| Spearman rho | 0.652332 [0.329837, 0.864817] | 0.010422 |
| Kendall tau | 0.491092 [0.212827, 0.704203] | 0.013764 |
| Mean absolute error | 0.143584 [0.109605, 0.178563] | 0.003532 |
| Mean bias (judge minus human) | -0.000435 [-0.079509, 0.066031] | 0.008355 |
| Human mean | 0.525333 [0.411848, 0.637973] | 0.000000 |
| Judge mean | 0.524898 [0.439570, 0.607093] | 0.008355 |
| Human empirical entropy | 0.565932 [0.473941, 0.638212] | 0.000000 |

### Ranked-score softmax

| Metric | Estimate [conditional 95% interval] | Repartition SD (5) |
|---|---:|---:|
| Weighted squared PMF loss | 0.157551 [0.119645, 0.197522] | 0.006905 |
| Cross-entropy | 1.555056 [1.334591, 1.763344] | 0.056804 |
| Forward Kullback–Leibler divergence | 0.989124 [0.790898, 1.203241] | 0.056804 |
| Brier loss | 0.723495 [0.636658, 0.774464] | 0.015391 |
| Normalized ranked probability score | 0.118396 [0.097060, 0.143932] | 0.004695 |
| Total variation distance | 0.494567 [0.441649, 0.534164] | 0.018347 |
| Pearson r | 0.727835 [0.508648, 0.890650] | 0.023040 |
| Spearman rho | 0.645333 [0.334412, 0.860004] | 0.021034 |
| Kendall tau | 0.484184 [0.222208, 0.698769] | 0.028002 |
| Mean absolute error | 0.144490 [0.111558, 0.181568] | 0.006617 |
| Mean bias (judge minus human) | -0.006900 [-0.087653, 0.059576] | 0.012028 |
| Human mean | 0.525333 [0.411848, 0.637973] | 0.000000 |
| Judge mean | 0.518434 [0.437118, 0.602691] | 0.012028 |
| Human empirical entropy | 0.565932 [0.473941, 0.638212] | 0.000000 |

### Training-marginal constant

| Metric | Estimate [conditional 95% interval] | Repartition SD (5) |
|---|---:|---:|
| Weighted squared PMF loss | 0.258201 [0.203135, 0.342499] | 0.006471 |
| Cross-entropy | 1.928001 [1.835583, 2.058575] | 0.064996 |
| Forward Kullback–Leibler divergence | 1.362068 [1.221685, 1.559386] | 0.064996 |
| Brier loss | 0.869580 [0.845352, 0.901865] | 0.011585 |
| Normalized ranked probability score | 0.187208 [0.155033, 0.233343] | 0.006139 |
| Total variation distance | 0.696790 [0.660004, 0.740382] | 0.008192 |
| Pearson r | -0.404177 [-0.589177, -0.187147] | 0.177553 |
| Spearman rho | -0.347285 [-0.556837, -0.131178] | 0.144724 |
| Kendall tau | -0.272850 [-0.439058, -0.106376] | 0.119420 |
| Mean absolute error | 0.249185 [0.184522, 0.340678] | 0.007611 |
| Mean bias (judge minus human) | 0.005811 [-0.111777, 0.119019] | 0.001465 |
| Human mean | 0.525333 [0.411848, 0.637973] | 0.000000 |
| Judge mean | 0.531145 [0.520401, 0.539040] | 0.001465 |
| Human empirical entropy | 0.565932 [0.473941, 0.638212] | 0.000000 |

**TLDR-end:** [ttj: weighted training] The requested historical-data comparison is complete. Weighted mixture training improved observed distribution losses, but its paired uncertainty does not establish superiority over stable correlation training.
