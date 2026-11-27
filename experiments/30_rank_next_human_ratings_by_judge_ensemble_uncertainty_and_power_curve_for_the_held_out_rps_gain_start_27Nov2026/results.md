# Next human ratings by judge-ensemble uncertainty, and the power curve for the held-out RPS gain (11-27-2026)

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/30_rank_next_human_ratings_by_judge_ensemble_uncertainty_and_power_curve_for_the_held_out_rps_gain_start_27Nov2026/RESULTS.md>

**TLDR:** Rank the 100 new artifacts by logged judge disagreement and non-ceiling uncertainty. The top 25 are 21/61 fives (34.4%); the bottom 25 are 66/70 fives (94.3%); the new set overall is 185/250 fives (74.0%). Extra ratings on the same 20 held-out tasks do not push the ranked probability score (RPS) interval below 0. A planning extrapolation that holds the point estimate fixed crosses at 23 tasks.

**Date:** 11-27-2026. **As of:** 11-27-2026 11:23 PST. CPU only. $0. No new model call. No differential testing. No Lean check.

Pre-registration, written before the run: [PREREG.md](PREREG.md). Receipt: [results/analysis_11-27-2026.json](results/analysis_11-27-2026.json). Priority list: [results/next_ratings_priority_top25_11-27-2026.csv](results/next_ratings_priority_top25_11-27-2026.csv) and the full 100 in [results/next_ratings_priority_all_new_items_11-27-2026.csv](results/next_ratings_priority_all_new_items_11-27-2026.csv). Derivation: [derivation/active_selection_and_rps_power_11-27-2026.pdf](derivation/active_selection_and_rps_power_11-27-2026.pdf). Google Doc: [Next human ratings by judge disagreement, and the held-out RPS power curve (11-27-2026)](https://docs.google.com/document/d/1Nvwklzb89u223bSt5pU92F9lN7yf6ZvUJYOsYK1DpIg/edit). Derivation PDF on Drive: <https://drive.google.com/file/d/1tiCvjQecqQyoPcLECFmRO54UHpZcztw4/view>. The connector cannot set anyone-with-the-link. The Doc and the derivation files are shared with brando.science@gmail.com as commenter and stay in the owner's Drive.

## Bottom line

The next human ratings should go to artifacts the six logged judges do not already call a five. On the live queue of 100 new artifacts, the rank score (disagreement of the six expected scores, plus entropy away from a five, plus a small bonus for fewer ratings so far) puts heap-sort and a few low or split items first. The top 25 already-collected ratings on those items are 21/61 fives. The bottom 25 are 66/70 fives. Spearman of the rank score with the five-rate is -0.617. The split was not an input.

That ranking does not, by itself, make the held-out RPS gain significant. Replaying experiment 27 on its frozen 247-new-rating table reproduces the published paired RPS -0.034895 [-0.075959, +0.002443] (the Cursor QA target was -0.034895 [-0.075959, +0.002444]; absolute errors 1.2e-7, 1.5e-7 and 5.5e-7). On the current 445 ratings (195 old + 250 new) the same F8 head, refit on train and validation only, has test RPS 0.0737 versus 0.1088 for the set-aware constant. Paired difference -0.0351 [-0.0764, +0.0020], seed 20261127, 10,000 task draws, p-val=0.0327 for the one-sided bootstrap probability that the difference is at least 0 (the plus-one correction (1 + count of draws at least 0) / 10001). The upper bound is still positive.

Drawing up to 2,240 further ratings from each test artifact's current histogram, either uniformly or by the active rule, moves the median upper bound by at most 0.0008. It never goes negative. The median upper bound of a retrospective subsample of the real test ratings is also positive at every budget, and both policies meet at +0.0020 when every existing test rating is included. The binding limit is the 20 tasks. Holding the point estimate fixed and scaling only the upper distance by sqrt(20 / m), the extrapolated upper bound is +0.0003 at 22 tasks and -0.0005 at 23 tasks. That is a planning figure, not a measured interval and not a certification that three more tasks would make the judge pass.

## What to rate next

Six members, equal weight, logged calls only: H2 Astra (three integer scores as a histogram), H2 Opus, H3 Astra, H4 Astra, H4 Argon, H4 Opus. H0, H1 and H2 Sol exist only on the old 75 artifacts and are not in the score. Rank score = disagreement + (normalized entropy times (1 - probability of 5)) + 0.5 / (1 + ratings so far). Higher is first. Ties break by item id. Empty slots use the examiner note's 3,300 rows, which is 33 rows per new artifact.

| Rank | Item | Task | Ratings so far | Fives | Rank score | Disagreement | Ceiling mass |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | native-heavy-11-11-2026__item045 | task_01_heap_sort | 3 | 1/3 | 1.363 | 0.789 | 0.300 |
| 2 | native-heavy-11-11-2026__item066 | task_01_heap_sort | 3 | 1/3 | 1.302 | 0.695 | 0.238 |
| 3 | native-heavy-11-11-2026__item047 | task_01_heap_sort | 2 | 1/2 | 1.287 | 0.611 | 0.181 |
| 4 | native-heavy-11-11-2026__item091 | task_10_lower_median | 2 | 0/2 | 1.247 | 0.655 | 0.328 |
| 5 | native-heavy-11-11-2026__item031 | task_18_topological_sorting | 3 | 0/3 | 1.047 | 0.358 | 0.002 |

Item 045 is the trace. Its six expected scores are 3.00 (H2 Astra), 5.00 (H2 Opus), 3.30 (H3), 3.15 (H4 Astra), 4.35 (H4 Argon) and 4.07 (H4 Opus). The ensemble probability of a five is 0.300. One of its three human ratings is a five. It sits in the train split; the rank did not use the split. Of the top 25, 13 are train, 3 are validation and 9 are test.

The top 25 have mean ceiling mass 0.283 and mean disagreement 0.418. The bottom 25 have mean ceiling mass 0.915 and mean disagreement 0.152. Shuffling human rating values, while keeping the count per artifact, does not change the rank score. There is no logged six-member ensemble on VeriBench tasks outside these 175 artifacts, so this list cannot prioritize the rest of the 896-task public set.

## Held-out scores on the 445 ratings

20 test tasks, 70 artifacts, 176 test ratings. The forecast is the experiment 27 F8 cumulative logit (Astra mean, Opus mean, H3 score, H3 expected score), cross-entropy, penalty 0, mixture 0, refit on the 105 train and validation artifacts and then held fixed. The set-aware constant is the train-plus-validation human marginal inside each set. Intervals are 10,000-draw task bootstraps, tasks in sorted order, seed 20261127. Lower is better for RPS, cross-entropy (CE) and total variation distance (TVD). Spearman and Pearson are secondary. Bias is judge mean minus human mean on the 0–5 scale.

| Forecast | RPS [95%] | CE [95%] | TVD [95%] | Spearman | Pearson |
| --- | --- | --- | --- | --- | --- |
| F8 refit | 0.0737 [0.0462, 0.1062] | 0.943 [0.665, 1.265] | 0.359 [0.292, 0.439] | 0.876 | 0.907 |
| Set-aware constant | 0.1088 [0.0725, 0.1503] | 1.159 [0.866, 1.468] | 0.479 [0.402, 0.563] |  |  |

Paired, F8 minus the set-aware constant. Negative means the judge has the lower score.

| Metric | Difference [95%] | Bootstrap probability the difference is at least 0 |
| --- | --- | --- |
| RPS | -0.0351 [-0.0764, +0.0020] | 0.0327 |
| CE | -0.2153 [-0.4593, +0.0119] | 0.0318 |
| TVD | -0.1206 [-0.2038, -0.0506] | 0.0003 |

Bias +0.213 (judge mean 3.913 versus human mean 3.700). These RPS, CE, TVD, Spearman, Pearson and bias figures match the F8 row in experiment 29 at the rounding printed there. The RPS interval still includes 0. CE's paired interval also includes 0. TVD's paired interval is entirely below 0. The pre-registered "works" bar from experiment 27 needs the RPS interval entirely below 0, so the verdict on this snapshot stays promising.

## Power curve

Two different calculations. Both use the fixed F8 forecast and the fixed set-aware constant above. Neither refits the judge.

**Retrospective, real ratings.** Start with one rating on each of the 70 test artifacts (106 further real ratings remain). Add them back either uniformly or by the active allocation score (disagreement plus non-ceiling uncertainty, divided by (n+1)(n+2)). Forty shuffles. The median task-bootstrap upper bound stays positive at every budget and is +0.0020 for both policies when all 176 test ratings are in. At one rating per artifact, about 30% of shuffles have an upper bound below 0 because the histogram is a single draw. That share falls to 0 at the full set. It is sampling noise, not evidence that a smaller study would have been significant.

The five-rate among the next 100 revealed ratings, averaged over the 40 shuffles, is 0.454 for active and 0.482 for uniform. Active is lower, as predicted, and the gap is small because this comparison can only reorder ratings that already exist. The top-25 versus bottom-25 contrast above is the clearer ceiling separation.

**Forward simulation.** Add 0, 70, 140, 280, 560, 1,120 or 2,240 synthetic ratings drawn from each artifact's current histogram. Forty replicates. Label: simulation and planning, not new human ratings and not a certification. The median upper bound stays between +0.0018 and +0.0028 for both policies. The largest move away from the full-data upper bound of +0.0020 is 0.0008. The largest gap between active and uniform at the same budget is 0.0010. No budget has a median upper bound below 0. Under the assumption that future ratings look like the histograms we already have, more ratings on these 20 tasks do not close the +0.002 gap, because a task bootstrap treats those histograms as fixed once they have stopped moving.

**Task count.** Subsampling the 20 tasks (200 draws for each size below 20) gives a median interval width that tracks 1/sqrt(m): the coefficient of variation of width times sqrt(m), for sizes 6 through 18, is 0.019. The median upper bound is +0.030 at 6 tasks, +0.018 at 10, +0.007 at 16, and +0.0020 at 20. The fraction of subsamples with an upper bound below 0 stays near 0.20 and is 0 at the full 20, so shrinking the test set does not manufacture a significant result.

Extrapolation, labeled as extrapolation: upper(m) = -0.035133 + 0.037142 times sqrt(20 / m). This holds the 20-task point estimate fixed and scales only the distance from that point to the upper endpoint. It is +0.0003 at 22 tasks and -0.0005 at 23 tasks. The smallest such m is 23. At the current depth of 176 ratings on 20 tasks, three further tasks of the same depth are about 26 ratings. That figure is a planning translation of the extrapolation. It is not a count this study measured, and it assumes the new tasks have the same paired RPS.

## Alignment and checks

| Check | Result |
| --- | --- |
| Experiment 27 paired RPS, judgelib bootstrap, seed 20261124, 10,000 draws | -0.034895 [-0.075959, +0.002443] versus the Cursor QA target -0.034895 [-0.075959, +0.002444] |
| Same replay, judge RPS / CE / TVD | 0.075070 / 0.969506 / 0.354954 |
| Same replay, set-aware constant RPS / CE / TVD | 0.109965 / 1.188888 / 0.478664 |
| Experiment 25 set-aware difference, 195+247 ratings, seed 20261124 | Astra +0.001966 and Opus -0.017716, absolute error under 2e-17 against results/setaware.json |
| Experiment 25 interim, 195+250 ratings | Astra +0.000232 and Opus -0.016911, absolute error under 1e-17 against the interim setaware file |
| Fit index versus test index | Disjoint. 105 fit artifacts, 70 test artifacts, no shared task |
| Rank score versus rating values | Unchanged when the count is held fixed and the values are ignored |
| Same-seed bootstrap | Two calls match exactly, asserted in the script |
| 445-rating F8 versus experiment 29's printed F8 row | RPS 0.0737, paired -0.0351 [-0.0764, +0.0020], p-val=0.0327, bias +0.213 |

The five predictions in PREREG.md all landed: the two alignments, no forward crossing and a policy gap under 0.005, an extrapolated task count between 22 and 40 (it is 23), a lower five-rate in the top 25 than in the bottom 25, and a lower five-rate for the active reveal than for the uniform reveal.

## What this does not show

These curves do not certify a judge and do not replace a new human round. The forward curve assumes the next rating is drawn from the histogram already on that artifact. If the missing ratings are systematically different, the point estimate can move, and this resampling cannot see that. The task extrapolation assumes new tasks would have the same mean paired RPS. Active selection changes which artifacts a rater sees. It does not add a 21st test task, and the opened 20-task interval was not refit. No Lean check and no differential testing entered any number. `git ls-remote` on `brando90/veribench` failed from this environment (repository not found). This run does not score a VeriBench release. The 50 tasks are the frozen human-rating tasks already in experiments 27, 28 and 29.

## Harness and model

No judge was called. The logged scores are the ones already in experiments 27, 28 and 29: H2 Astra and H2 Opus (three calls; old calls from the experiment 21 and 22 caches, new calls from Codex CLI and Claude Code), H3 Astra (one Codex CLI call, high, experiment 27), and H4 Astra, Argon and Opus (experiment 28, one call each). The F8 head is a CPU cumulative logit in NumPy and SciPy, the same class as experiment 27. This run used NumPy 1.26.4 and SciPy 1.13.1. Seeds 20261124 (alignment) and 20261127 (the 445-rating curves).

**TLDR-end:** [trustworthy-theorem-judges: next ratings and RPS power] The top 25 items are 21/61 fives against 66/70 in the bottom 25. Extra ratings on the same 20 tasks leave the RPS upper bound at +0.002; the planning extrapolation crosses at 23 tasks.
