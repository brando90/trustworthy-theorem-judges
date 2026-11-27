# Cumulative-logit heads fit by cross-entropy or ranked probability score on 445 ratings (11-27-2026)

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/29_refit_cumulative_logit_heads_ce_versus_rps_on_445_ratings_start_27Nov2026/results.md>

**TLDR:** The pre-registered primary head on the 20 held-out tasks does **not** clear the bar. It lowers ranked probability score (RPS) versus the set-aware constant, but its cross-entropy (CE) is worse, and the fit did not converge. The fixed experiment-27 F8 refit is still 0.002 short of the bar. A separate H3-free 5-fold pass, also written down before the test scores, **does** clear the bar on all 50 tasks.

**As of:** 11-27-2026. CPU only. $0. No new model call. Harness: Python 3, NumPy 2.5.5, SciPy 1.18.1, run by Cursor Grok 4.7.

- Pre-registration: [PREREG.md](PREREG.md)
- Selection, written before test scores: [results/validation_selection_11-27-2026.json](results/validation_selection_11-27-2026.json)
- Held-out receipt: [results/heldout_eval_11-27-2026.json](results/heldout_eval_11-27-2026.json)
- 50-task receipt: [results/nested_oof_11-27-2026.json](results/nested_oof_11-27-2026.json)
- Join audit: [data_11-27-2026/join_audit_11-27-2026.json](data_11-27-2026/join_audit_11-27-2026.json)
- Google Doc: [Cumulative-logit judge on 445 ratings (11-27-2026)](https://docs.google.com/document/d/1q0OQXbbMUw7azwB6K-wMXbC0Pb6NM2xOEeLLBjO8A6M/edit). The Drive connector cannot set anyone-with-the-link, so the doc stays in the owner's Drive until that toggle is turned on.

## Bottom line

1. **20 held-out tasks (the pre-registered verdict): not found.** The head with the lowest validation RPS is a cumulative-logit head on the H2 Astra mean, the H2 Opus mean, the H3 score and the H3 expected score, fit by RPS, with L2 penalty 0, mixture weight 0.25 toward the pooled train marginal, and temperature 2. The optimizer did not converge (weight norm about 165 on the training tasks). On the 70 test artifacts its RPS is 0.0698 versus 0.1088 for the set-aware constant, paired difference \(-0.0390\) with 95% task-bootstrap interval \([-0.0721, -0.0087]\) (seed 20261127, 10,000 draws, \(p_{\ge 0} = 0.0052\)). Total variation distance (TVD) is also lower (0.363 versus 0.479). CE is worse: 1.249 versus 1.159. The written rule needs all three point estimates to improve and the RPS interval to lie entirely below 0. This head fails that rule.
2. **F8 refit: still short of the bar.** The experiment-27 configuration (same four features, CE, penalty 0, mixture 0, temperature 1), refit on this snapshot, has test RPS 0.0737. Paired difference versus the set-aware constant: \(-0.0351\) \([-0.0764, +0.0020]\), \(p_{\ge 0} = 0.0327\). The point matches experiment 28's published 0.0737. The interval still includes 0, by 0.002 on this seed.
3. **Best converged head on the same validation menu (robustness, not the argmin): meets the numerical bar on this opened split, and does not clearly beat F8.** CE fit, features H2 means plus H3 expected score plus three H4 expected scores plus four structural features, penalty 0.1, mixture 0, temperature 0.5. Test RPS 0.0653, CE 0.981, TVD 0.301. Paired RPS versus the set-aware constant: \(-0.0435\) \([-0.0782, -0.0139]\), \(p_{\ge 0} = 0.0009\). Versus the F8 refit: \(-0.0083\) \([-0.0219, +0.0039]\), \(p_{\ge 0} = 0.0945\). Pooled bias is \(+0.314\) (judge mean 4.014 versus human mean 3.700). The old cohort is still scored high: \(+0.632\) (2.993 versus 2.361).
4. **50-task H3-free nested pass: works.** Every outer fold selected the same feature set (H2 means, three H4 expected scores, four structural features). Four folds selected CE and one selected RPS. Temperature stayed at 1. All five refits converged, with weight norms between 2.9 and 5.8. Pooled RPS 0.0684 versus 0.1186 for the fold-wise set-aware constant. Paired difference \(-0.0502\) \([-0.0726, -0.0290]\), \(p_{\ge 0} = 0.0001\). CE 1.003 versus 1.308, difference \(-0.305\) \([-0.486, -0.119]\). TVD 0.345 versus 0.492, difference \(-0.147\) \([-0.193, -0.104]\). Pooled bias \(+0.023\) (3.764 versus 3.742). Old and new cohorts each have RPS, CE and TVD intervals entirely below 0.

This 20-task split was already scored in experiments 27 and 28. The nested pass reuses experiment 28's fold ids. Neither number is a sealed first look. The nested pass is the one that never fits a fold on its own labels, and it is the one that clears the bar.

## What was already on main

Before this run, `main` was at `efdc8c3` (11-26-2026 18:20 PST). Experiment 28 was already there: the multi-family H4 judge and the open-weight study on these same 445 ratings. Its registered 20-task head was still **promising** (RPS 0.0729 versus 0.1088, interval up to \(+0.0011\)). Its H3-free 50-task nested head had RPS 0.0704, and a post-hoc all-frontier nested head had RPS 0.0685. No experiment 29 existed. Experiment 27 and experiment 09 were not edited.

## Join and attestations

New scores are the 250 numeric rows already in experiment 09, joined on `(rater_id, item_id)`. `candidate_file` is not a key. One row, on `native-heavy-11-11-2026__item020`, has free text in `candidate_file` instead of a path. The join keeps it. The three scores on that item are 5, 5 and 5, so dropping that row does not change the histogram. The all-scores histogram of every new artifact matches the experiment 28 freeze.

Attestations on the 250 rows: `yes` 118, `partial` 100, blank 32. The 32 blanks are 30 from one rater id and one each from two others. Old expert ratings (195) have no attestation field. Primary targets keep every numeric score. Two sensitivities, using the hyperparameters already chosen, are below.

The in-sample RPS floor, the RPS of each artifact's own histogram against itself, is 0.0292 on the 70 test artifacts (0.0509 old, 0.0129 new) and 0.0300 on all 175 artifacts.

## Held-out test, 20 tasks, 70 artifacts

Point estimates are means over artifacts. Intervals are 10,000-draw task bootstraps, seed 20261127. Lower is better for RPS, CE and TVD. Bias is judge mean minus human mean. Spearman and Pearson are secondary and are undefined when the forecast does not vary inside a cohort.

| Forecast | Cohort | RPS [95%] | CE [95%] | TVD [95%] | Bias (judge vs human) | Paired RPS vs set-aware constant |
| --- | --- | --- | --- | --- | --- | --- |
| Set-aware constant | pooled | 0.1088 [0.0725, 0.1503] | 1.159 [0.866, 1.468] | 0.479 [0.402, 0.563] | +0.055 (3.755 vs 3.700) | reference |
| Set-aware constant | old | 0.1797 [0.1358, 0.2235] | 1.794 [1.644, 1.959] | 0.658 [0.595, 0.718] | +0.365 (2.726 vs 2.361) | reference |
| Set-aware constant | new | 0.0556 [0.0246, 0.0961] | 0.682 [0.411, 1.011] | 0.345 [0.302, 0.415] | -0.178 (4.526 vs 4.704) | reference |
| F8 refit (CE, penalty 0, mixture 0, temperature 1) | pooled | 0.0737 [0.0462, 0.1062] | 0.943 [0.665, 1.265] | 0.359 [0.292, 0.439] | +0.213 (3.913 vs 3.700) | -0.0351 [-0.0764, +0.0020] |
| F8 refit | old | 0.1333 [0.0905, 0.1787] | 1.553 [1.166, 1.961] | 0.486 [0.364, 0.608] | +0.739 (3.100 vs 2.361) | -0.0464 [-0.1281, +0.0352] |
| F8 refit | new | 0.0289 [0.0153, 0.0437] | 0.486 [0.310, 0.680] | 0.263 [0.231, 0.303] | -0.180 (4.524 vs 4.704) | -0.0267 [-0.0587, -0.0054] |
| Primary (RPS, unconverged) | pooled | 0.0698 [0.0440, 0.1004] | 1.249 [0.817, 1.750] | 0.363 [0.274, 0.467] | +0.208 (3.908 vs 3.700) | -0.0390 [-0.0721, -0.0087] |
| Primary | old | 0.1301 [0.0968, 0.1697] | 2.321 [1.862, 2.816] | 0.585 [0.493, 0.695] | +0.690 (3.051 vs 2.361) | -0.0496 [-0.1115, +0.0146] |
| Primary | new | 0.0246 [0.0108, 0.0393] | 0.446 [0.230, 0.694] | 0.197 [0.155, 0.246] | -0.154 (4.550 vs 4.704) | -0.0311 [-0.0625, -0.0101] |
| Best converged (CE, H2+H3+H4+structural, temperature 0.5) | pooled | 0.0653 [0.0409, 0.0937] | 0.981 [0.634, 1.386] | 0.301 [0.219, 0.392] | +0.314 (4.014 vs 3.700) | -0.0435 [-0.0782, -0.0139] |
| Best converged | old | 0.1122 [0.0808, 0.1502] | 1.638 [1.180, 2.200] | 0.470 [0.382, 0.566] | +0.632 (2.993 vs 2.361) | -0.0676 [-0.1331, -0.0016] |
| Best converged | new | 0.0302 [0.0066, 0.0563] | 0.488 [0.169, 0.851] | 0.174 [0.101, 0.260] | +0.075 (4.779 vs 4.704) | -0.0254 [-0.0462, -0.0117] |
| Cohort-specific H2 head (set-aware, not primary) | pooled | 0.0663 [0.0420, 0.0941] | 1.030 [0.683, 1.414] | 0.322 [0.238, 0.415] | +0.254 (3.954 vs 3.700) | -0.0425 [-0.0734, -0.0158] |
| Cohort-specific H2 head | old | 0.1167 [0.0871, 0.1495] | 1.817 [1.484, 2.175] | 0.517 [0.440, 0.608] | +0.546 (2.907 vs 2.361) | -0.0630 [-0.1179, -0.0072] |
| Cohort-specific H2 head | new | 0.0285 [0.0078, 0.0532] | 0.441 [0.174, 0.765] | 0.175 [0.115, 0.251] | +0.035 (4.740 vs 4.704) | -0.0272 [-0.0550, -0.0103] |

Pooled secondary correlations: F8 Spearman 0.876, Pearson 0.907. Primary 0.913 and 0.954. Best converged 0.919 and 0.964. Cohort-specific 0.928 and 0.965. The set-aware constant's pooled Spearman is 0.782 and its Pearson is 0.734, because the two cohorts have different constants. Inside one cohort those two correlations are undefined.

Paired RPS, best converged minus F8, pooled: \(-0.0083\) \([-0.0219, +0.0039]\). Primary minus F8, pooled: \(-0.0039\) \([-0.0152, +0.0069]\).

The new cohort is 74% fives (185 of 250). Its set-aware constant is already at RPS 0.0556, and every head is near the floor of 0.0129. The old cohort is where the heads still miss: F8 bias \(+0.739\), the converged head \(+0.632\).

## 50-task nested pass (H3 excluded)

H3 is excluded because its prompt used labeled demonstrations from experiment 27's training tasks, which cross these folds. Inside each outer fold the head is chosen by inner 4-fold validation RPS, then refit on the other 40 tasks. Menu: penalty in \(\lbrace 0, 1 \rbrace\), mixture in \(\lbrace 0, 0.25 \rbrace\), temperature in \(\lbrace 1, 1.5 \rbrace\).

| Forecast | Cohort | RPS [95%] | CE [95%] | TVD [95%] | Bias (judge vs human) | Paired RPS vs set-aware constant |
| --- | --- | --- | --- | --- | --- | --- |
| Set-aware constant | pooled | 0.1186 [0.0924, 0.1458] | 1.308 [1.089, 1.527] | 0.492 [0.435, 0.550] | -0.025 (3.716 vs 3.742) | reference |
| Set-aware constant | old | 0.1825 [0.1513, 0.2169] | 1.853 [1.725, 1.996] | 0.670 [0.627, 0.714] | -0.072 (2.555 vs 2.627) | reference |
| Set-aware constant | new | 0.0708 [0.0440, 0.1001] | 0.900 [0.629, 1.191] | 0.359 [0.303, 0.420] | +0.009 (4.588 vs 4.578) | reference |
| Nested head | pooled | 0.0684 [0.0528, 0.0866] | 1.003 [0.804, 1.232] | 0.345 [0.303, 0.388] | +0.023 (3.764 vs 3.742) | -0.0502 [-0.0726, -0.0290] |
| Nested head | old | 0.1031 [0.0797, 0.1340] | 1.460 [1.168, 1.840] | 0.427 [0.373, 0.483] | +0.186 (2.813 vs 2.627) | -0.0794 [-0.1201, -0.0412] |
| Nested head | new | 0.0424 [0.0279, 0.0581] | 0.661 [0.472, 0.862] | 0.283 [0.234, 0.336] | -0.100 (4.478 vs 4.578) | -0.0283 [-0.0500, -0.0095] |

Pooled paired CE \(-0.305\) \([-0.486, -0.119]\). Pooled paired TVD \(-0.147\) \([-0.193, -0.104]\). Old and new paired RPS, CE and TVD intervals are also entirely below 0. Spearman 0.775 and Pearson 0.898 on the pooled 175 artifacts. The nested RPS of 0.0684 sits next to experiment 28's post-hoc all-frontier nested RPS of 0.0685. The heads are different: this one is a cumulative logit on cached means and structural features; that one was a pool of three H4 probability vectors.

## Attestation sensitivity

Same hyperparameters, refit on the filtered labels. Test size stays 70 artifacts.

| Target | F8 RPS (paired vs its constant) | Primary RPS (CE) | Converged RPS (paired) |
| --- | --- | --- | --- |
| All numeric scores | 0.0737 (-0.0351 [-0.0764, +0.0020]) | 0.0698 (CE 1.249, worse than 1.159) | 0.0653 (-0.0435 [-0.0782, -0.0139]) |
| Drop 32 blank attestations | 0.0746 (-0.0343 [-0.0758, +0.0029]) | 0.0731 (CE 1.281, worse than 1.156) | 0.0652 (-0.0437 [-0.0786, -0.0140]) |
| Schema attestations only (`yes` / `no` / `unsure`) | 0.0800 (-0.0393 [-0.0791, -0.0042]) | 0.0775 (CE 1.228, below 1.265) | 0.0713 (-0.0479 [-0.0829, -0.0181]) |

Dropping blanks moves F8 by less than 0.001 and does not pull its interval below 0. Restricting the target to schema attestations does pull F8's interval below 0. That is a different target (100 `partial` rows and 32 blanks removed), not the primary one. The item020 edit does not move any histogram.

## What the pre-registered predictions got right

The set-aware constant on the 20 test tasks is 0.1088, matching experiment 28 within 0.0001. The F8 refit is 0.0737, inside the predicted 0.005 band. RPS training did not produce a head that wins the proper-score panel: it won validation RPS by about 0.0007 over the best converged head and then lost on CE. Dropping blank attestations moved test RPS by less than 0.01. The prediction that temperature would stay near 1 was wrong for the 20-task menu (the argmin used temperature 2, and the converged runner-up used 0.5). The nested menu, which only offered 1 and 1.5, selected 1 in every fold.

## What is still in the way

The 20-task primary fails because an unpenalized RPS fit saturates the cumulative logit and spends its RPS gain on a worse CE. Requiring a converged fit, or selecting on CE among heads that already have a good validation RPS, avoids that head. It does not, by itself, beat F8 by a clear interval on 20 tasks.

On the 50-task nested head the pooled level is close (bias \(+0.023\)). The old cohort is still about 0.19 too high, and its RPS of 0.103 is well above its floor of 0.046. The new cohort's RPS of 0.042 is close to its floor of 0.018, because most new ratings are 5s. Another penalty grid will not move that. The next gain has to come from the old cohort's remaining error, or from ratings that are not piled on 5, scored on a split that these heads have not already seen.

## How to rerun

```bash
python3 scripts/build_snapshot.py
python3 -m unittest tests/test_heads_and_join.py
python3 scripts/run_experiment.py --stage select
python3 scripts/run_experiment.py --stage eval
python3 scripts/run_experiment.py --stage nested
```

`select` does not compute a test metric. `eval` reads the selection file and scores the 20 test tasks once. Cached judge features come from experiment 27 and experiment 28. No model is called.
