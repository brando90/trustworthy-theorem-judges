<!-- TLDR: Compare weighted squared probability training against a globally solved Pearson mixture baseline on fixed historical task-family folds, with a separate weighted softmax extension. -->
# Weighted probability training and stable correlation — 11-08-2026

**Status:** Procedure specified before this condition's new test results. This is an exploratory follow-up to already inspected historical evidence, not a fresh confirmatory test. Frozen configuration: [protocol.json](protocol.json). The executed source revision and hashes will be recorded at launch.

## Question and scope

Does training with the weighted squared probability mass function (PMF) distance improve the same held-out metrics relative to stable Pearson-correlation training within the same model class? The primary comparison learns one global convex mixture of the same five cached judge histograms under each objective. A separate secondary comparison adds the weighted objective to the existing affine softmax model alongside cross-entropy, Brier and ranked probability score. Cross-class comparisons are descriptive, not evidence about the objective alone. Neither condition trains a language model or changes its prompt.

Use the existing hash-bound dataset: 75 candidate files, 25 tasks, 19 task families, 195 available expert ratings, five historical judges and three cached scalar ratings per judge/file. The exact identities, inputs, prior exposure and reference flags remain in ../source_audit.json and ../RESULTS.md. All new model calls and provider inference charges are zero. Human histograms contain only two or three ratings; the cached model histograms are not native forecasts of human uncertainty. No fresh or sealed ratings enter this run.

## Primary: matched mixture training

For artifact i, use human empirical PMF p_i and five cached model PMFs q_ij on categories r=0,...,5. Apply the historical mixture smoothing q_epsilon=(1-6*epsilon)q+epsilon, epsilon=1e-6. Both methods learn weights w_j>=0 with sum_j w_j=1 and predict q_i(w)=sum_j w_j q_ij. Thus both have the same four-dimensional feasible probability family, same inputs and same training artifacts. No hyperparameter selection is needed.

- Weighted objective: mean_i sum_r p_ir(p_ir-q_ir(w))^2. This is a convex quadratic; enumerate all nonempty active faces of the five-weight simplex and verify a global optimality gap.
- Correlation objective: maximize Pearson between q_i(w)'s expected rating r/5 and the human expected rating. Center the training candidate means and target; project the target onto their nonnegative cone, then normalize nonnegative coefficients to sum one. This globally solves the positive-correlation case. Use the best nonconstant vertex when every candidate covariance is nonpositive. Undefined human variance or all-constant candidate means produce an explicitly flagged uniform-mixture fallback, never a fabricated correlation.
- Pearson's mean-only objective need not uniquely determine a PMF. The recorded finite active-set enumeration and deterministic minimal-support/lexicographic tie convention identify one solution. This is not an added probability loss. See MATH_baseline.md for derivation and exact numerical tolerances. Report zero-projection, fallback, rank-deficiency, certificate failures and prediction variance.
- The fixed folds and five seeds are identical to the preceding study: five outer task-family folds per seed, 25 fits per objective, 50 fits total. Train exclusively outside each outer test family; publish every completed/failed cell. Evaluate each resulting forecast on the same test artifacts and full metric panel.

## Secondary: weighted softmax training

Use the same five cached mean scores, six-class affine softmax and train-only standardization as the previous fitted-mapping experiment. Parameterize each six-class coefficient row in an orthonormal zero-sum basis: 30 identifiable coefficients, equivalent probability family to the historical 36 stored coefficients. All four objectives use the same basis, initialization seed, optimizer limits and regularization grid. The weighted gradient with respect to probabilities is 2*p*(q-p)/n; this is distance to a sparse empirical histogram, not the one-observation loss (1-q_R)^2.

Fit weighted PMF, cross-entropy, multiclass Brier and normalized ranked probability score. Use four inner task-family folds to choose L2 strength from [0.001,0.01] by the same pooled inner ranked probability score for every objective; refit on all outer-training artifacts. Pair initialization seeds as in the earlier protocol. L-BFGS-B: maxiter=1000, maxfun=2000, ftol=1e-12, gtol=1e-7. This is a separately specified numerical condition, not a relabeling of old fits. Preserve every finite nonconverged fit; fail loudly on nonfinite forecasts. Total 900 fits, 100 final models, 1,500 held-out artifact forecasts. Do not claim that this extension repairs Pearson in the softmax family; Pearson's stable primary baseline uses the matched mixture family above.

## Metrics, estimands and uncertainty

Report all objectives under weighted PMF distance [0,1], cross-entropy/log loss (natural logs), forward Kullback–Leibler divergence, Brier [0,2], normalized ranked probability score [0,1], total variation [0,1], Pearson/Spearman/Kendall [-1,1], mean absolute error, signed bias (judge minus human), both means and prediction variability. Means and errors use rating/5. Show a training-only constant human-distribution baseline. Every task contributes three files, so equal-file averages equal equal-task averages here.

Primary contrast: mixture weighted training minus mixture Pearson training on held-out weighted distance; lower is better. Report the rest of the metric differences to expose tradeoffs. Secondary: weighted softmax minus each proper-loss softmax on the same metrics. No confirmatory hypothesis test, superiority threshold or universal-best claim; p-val=n/a. Test outcomes never choose the method, grid or reporting metric.

Use 1,000 paired bootstrap draws of the 19 task families, retaining all attached artifacts and averaging the five fixed seeds. For both mixture methods, additionally refit both methods in every resampled training fold and evaluate resampled test families; fixed partitions remain fixed, no substitute retries for empty/undefined draws. Report valid/invalid counts and retain failures. These intervals include mixture-weight fitting uncertainty conditional on the fixed cached candidate pool/partition, not upstream prompt exposure or fresh rater sampling. Softmax intervals hold all fitted models and chosen regularization fixed and exclude fitting/selection uncertainty. Distinguish these from standard deviations across the five overlapping resplits, which are not independent repetitions or confidence intervals.

## Predictions and controls before measurement

- Identity forecast q=p has weighted distance zero; per-observation Brier and ranked probability scores need not be zero for a nondegenerate target.
- Weighted mixture training cannot exceed the training weighted loss of any component, up to the certified numerical tolerance; Pearson mixture training cannot have lower training correlation than any valid component.
- Exact mixture targets recover zero weighted loss when representable; nonpositive, duplicate-column and constant-target cases follow the stated branches.
- Analytic weighted/CE/Brier/ranked-score gradients match finite differences; an unregularized two-item weighted fit approaches zero; train-only scaling reproduces model forecasts.
- A positive affine change of expected scores preserves Pearson. Equal means can describe different PMFs. None of these controls predicts a held-out winner.
- Expected held-out signs: uncertain. The weighted method may trade ranking quality for distribution error, and sparse targets can make that worse. Preserve negative or inconclusive outcomes.

## Execution, privacy and completion

One CPU thread on Stanford skampere3, no graphics processor, expected minutes and at most two hours, within the prior eight-hour envelope. A named persistent session runs ordinary Python with a bounded supervisor and launch/progress/terminal receipts; the coordinator watches completion and sends one start/done notification. Hash inputs, configuration and sources. Private ratings, per-artifact predictions, learned parameters and resamples stay in ignored private storage; publish aggregate results, counts, code and verification. Final verification reconstructs every forecast from saved models and reruns metric aggregation independently, checks family separation, hashes, normalization and full denominators. Preserve old results. Save protocol, prompts, live results, final results and checkpoint in this folder.
