# Formulation ④ results

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/11_formulation4_train_only_ce_mixture_cv/results.md>

**TLDR:** Out-of-fold, ④'s CE-trained mixture has RPS 0.1367 versus 0.1829 for the constant (difference −0.0462, 95% interval [−0.0937, −0.0005]) and 0.1496 for the equal-weight mixture (−0.0129 [−0.0232, −0.0024]). On CE it is 5.427 versus 1.848 for the constant (+3.580 [+2.292, +4.939], worse), and ties the equal-weight mixture (−0.004 [−0.072, +0.076]).

Method: repeated (20) 5-fold task-grouped cross-validation over 75 artifacts and 25 tasks, task bootstrap (10,000 draws). Lower is better. 0 model calls, $0; 100 CE fits, 0 certificate failures.

| Method (out-of-fold mean over 75 artifacts) | CE (primary) | RPS | TVD |
| --- | --- | --- | --- |
| constant (train marginal) | 1.848 | 0.1829 | 0.682 |
| equal-weight mixture | 5.431 | 0.1496 | 0.531 |
| best single judge by train CE | 8.902 | 0.2032 | 0.652 |
| ④ CE-trained mixture | 5.427 | 0.1367 | 0.511 |

| Paired difference, ④ minus comparator | CE | RPS | TVD |
| --- | --- | --- | --- |
| constant | +3.580 [+2.292, +4.939] | −0.0462 [−0.0937, −0.0005] | −0.171 [−0.269, −0.077] |
| equal-weight mixture | −0.004 [−0.072, +0.076] | −0.0129 [−0.0232, −0.0024] | −0.020 [−0.041, +0.004] |
| best single judge by train CE | −3.475 [−4.702, −2.266] | −0.0665 [−0.0870, −0.0466] | −0.141 [−0.187, −0.094] |

Mean fitted weights (H0 Sol, H0 Opus, H1 Sol, H2 Sol, H2 Opus): 0.390, 0.085, 0.102, 0.036, 0.387. Train-only best single judge: H2 Opus chosen in 61 of 100 folds, H0 Sol 30, H2 Sol 9.

Reading: the CE objective does not help over equal weights here (CE tie), and CE is dominated by the 1e-6 probability floor on three-call histograms, which is why the constant wins on CE. Training on the loss does help against picking one judge by train CE, and gives the best RPS. The constant's CE advantage matches experiment 10's earlier finding that mixtures forecast worse than the constant on CE. Not tested here: formulation ③, shrinkage, new data.
