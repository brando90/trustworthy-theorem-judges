# Pre-registration: cumulative-logit heads fit by cross-entropy or ranked probability score on the 445-rating snapshot (11-27-2026)

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/29_refit_cumulative_logit_heads_ce_versus_rps_on_445_ratings_start_27Nov2026/PREREG.md>

**TLDR:** Before any test metric of this run, fix the comparison. Refit experiment 27's cumulative-logit head on the ratings already in the repo (195 old + 250 new = 445), select every new head by validation ranked probability score only, and score the 20 held-out tasks once. This test split was already scored in experiments 27 and 28. It is a previously opened benchmark, not a sealed first look.

**Dated:** 11-27-2026. Written before `scripts/run_experiment.py --stage select` and before any test metric. Owner: Brando Miranda. Run by Cursor Grok 4.7. CPU only. $0. No new model call.

## 1. Data and the join

- **Old cohort.** 25 tasks, 75 artifacts, 195 expert ratings, copied from the anonymised experiment 28 file (itself copied from experiment 27). No attestation field exists for these rows.
- **New cohort.** 25 disjoint tasks, 100 artifacts, 250 numeric scores already in experiment 09's main-round CSVs (the 11-26-2026 sync: 185 of 250 are 5s, 74%). Not a new Sheet sync. Experiment 09 is not edited.
- **Join.** Each new score is joined on `(rater_id, item_id)`. `candidate_file` is not a key. Experiment 09 records one inspected edit: rater `T06` wrote free text into `candidate_file` on `native-heavy-11-11-2026__item020`. That row is kept. On this snapshot the three scores on that item are all 5, so dropping the edited row would not change the artifact histogram. The audit records that fact.
- **Attestation sensitivity, not the primary target.** On the 250 scored rows the attestation field is `yes` 118, `partial` 100, blank 32. Blank rows are 30 from one rater id plus two singleton blanks. Primary histograms keep every numeric score. After the head is fixed, two sensitivities rescore and refit without re-selecting: drop blank attestations; keep only schema values `yes` / `no` / `unsure` (this drops `partial` and blanks).
- **Split.** The experiment 27 task split, unchanged: 20 train / 10 validation / 20 test tasks. A task never moves. The 5-fold ids are the experiment 28 draw (`default_rng(20261126)`), reused rather than redrawn.
- **Prior exposure.** Experiment 22 scored the 10 old test tasks. Experiment 27 scored all 20 test tasks. Experiment 28 scored them again on the 250-rating snapshot. This run does not pretend otherwise.

## 2. What is fit, and what is only reported

Every head outputs a distribution on {0, 1, 2, 3, 4, 5}.

**Primary menu (no cohort identity):**

- Cumulative logit, \(P(r \le k) = \mathrm{sigmoid}((\theta_k - w \cdot x) / T)\), fit by cross-entropy or by ranked probability score, plus \((\alpha/2) \lVert w \rVert^2\).
- \(\alpha \in \lbrace 0, 0.1, 1, 10 \rbrace\), mixture weight \(m \in \lbrace 0, 0.25, 0.5 \rbrace\) toward the pooled train marginal, temperature \(T \in \lbrace 0.5, 0.75, 1, 1.5, 2 \rbrace\) applied after the fit and chosen on validation.
- Features, all cached, none refit from labels: H2 means (GPT-6 Astra, Claude Opus 5.5); those plus experiment 27 H3 score and H3 expected score; H4 expected scores (GPT-6 Astra, Gemini 4 Argon, Claude Opus 5.5); the H2/H3/H4 pool; that pool plus structural counts (`thm_ratio`, `excess_thm_log`, `ident_jaccard`, `edit_similarity`).
- A log-pool of the cached probability vectors (H2 histogram, H3, three H4 distributions), same \(\alpha\), \(m\), \(T\), and the same two proper scores.

**Not eligible for the primary choice:**

- The same cumulative logit with a cohort indicator `isnew`.
- A separate head for the old cohort and the new cohort.
- Shrinkage toward the set-aware constant (the train marginal of the artifact's own cohort) instead of the pooled marginal.

Those three are selected on validation inside their own menu and reported as set-aware results. Experiment 27 kept the cohort indicator out of the primary judge because a deployed judge is not handed the cohort label. This run keeps that rule.

**Fixed reference, not selected:** experiment 27's F8 head, cross-entropy, \(\alpha = 0\), \(m = 0\), \(T = 1\), features Astra, Opus, H3 score, H3 expected score, refit on train+validation of this snapshot.

## 3. Selection and the one test pass

1. Fit each primary and set-aware configuration on the 20 training tasks.
2. Score it on the 10 validation tasks. Choose the lowest validation ranked probability score. Ties: lower validation cross-entropy, then smaller \(\alpha\), then \(T\) closer to 1, then smaller \(m\).
3. Write `results/validation_selection_11-27-2026.json` before any test metric.
4. Refit the chosen hyperparameters on train+validation. Apply the chosen \(T\). Score the 20 test tasks once.
5. Separately, an H3-free 5-fold out-of-fold pass: inside each outer fold of 40 tasks, an inner 4-fold (5 old and 5 new tasks per inner fold, seed `20261127 + fold`) selects among a smaller menu (\(\alpha \in \lbrace 0, 1 \rbrace\), \(m \in \lbrace 0, 0.25 \rbrace\), \(T \in \lbrace 1, 1.5 \rbrace\), no H3). The outer 10 tasks are scored only after that choice. H3 is excluded here because its prompt used labeled demonstrations from experiment 27's training tasks, which cross these folds.

The point estimate is the mean over artifacts. Uncertainty is a 10,000-draw task bootstrap, seed `20261127`. Paired differences use the same resampled tasks.

## 4. Metrics and the decision rule

Primary metric: normalized ranked probability score, the five-threshold mean of \((Q_c - P_c)^2 + P_c(1 - P_c)\), per artifact, then the mean over artifacts. Lower is better.

Also reported, in this order: cross-entropy, total variation distance, then signed bias (mean judge score minus mean human score, with both means), then Spearman and Pearson of the two means as secondary diagnostics. Correlation is never a training objective and never the selection criterion.

The baseline is the set-aware constant: the train+validation rating histogram of the same cohort, applied to that cohort's test artifacts.

On the pooled 20 test tasks, for the one primary head:

- **Works** if the paired ranked-probability-score difference (head minus set-aware constant) has a 95% interval entirely below 0, and the point cross-entropy and total variation distance are also lower.
- **Promising** if all three point estimates are lower but the ranked-probability-score interval includes 0.
- **Not found** otherwise.

Old and new cohorts are reported separately. The new cohort is about 74% fives, so a pooled number can hide a cohort failure. The set-aware family does not change the verdict word. The nested pass has its own verdict against its own fold-wise set-aware constant, labeled as the 50-task estimate.

## 5. Predictions written before selection

These use the published experiment 27 and 28 numbers as context. They are not a claim that this test split is unseen.

1. The set-aware constant on the 20 test tasks will match experiment 28's published 0.1088 ranked probability score within 0.002, because the all-scores histograms are the same snapshot. If it does not, the join or the metric code is wrong and the run stops.
2. The fixed F8 refit will land within 0.005 ranked probability score of experiment 28's published 0.0737. Experiment 28 reported the paired difference versus the set-aware constant as \(-0.0351\) with interval \([-0.0747, +0.0029]\).
3. On validation, cross-entropy and ranked-probability-score ordinal heads will be close. I do not expect the ranked-probability-score head to beat the cross-entropy head by more than 0.01 test ranked probability score. Experiment 28's matched probability-pool head had the same pattern: cross-entropy won or tied.
4. The selected penalty will be small (\(\alpha \in \lbrace 0, 0.1 \rbrace\), \(m \in \lbrace 0, 0.25 \rbrace\)). Temperature will stay at 1 or move only to 0.75 or 1.5.
5. A set-aware head can clear the interval against the set-aware constant on this opened split. Experiment 28's set-aware F9 refit already did (\(0.0659\), interval entirely below 0). The primary head, which may not use the cohort label, is less likely to: I put that probability near 0.4.
6. Dropping the 32 blank attestations will move pooled test ranked probability score by less than 0.01. The item020 candidate-file edit will not move any histogram.
7. The binding limit is the 20-task interval and the new cohort's pile of 5s, not the choice between the two proper scores. A gain of a few thousandths will not clear an interval whose width is several hundredths.

## Amendment 1 (11-27-2026, during validation, before any test metric)

The first validation pass hit `overflow` in `exp` for one ranked-probability-score fit with \(\alpha = 0\) (thresholds near \(-250\), weight norm near \(165\)). That fit was marked unsuccessful and still won validation ranked probability score by about \(0.0007\) over the best converged head, with worse validation cross-entropy (\(0.99\) vs \(0.77\)). The sigmoid input is now clipped to \([-40, 40]\). \(\mathrm{sigmoid}(40)\) equals 1 within \(10^{-17}\), so an unsaturated head is unchanged at reported precision. Selection is re-run with that clip before any test metric. The decision rule is unchanged. If the re-run still selects an unsuccessful fit, that fit remains the primary under the written rule, and the best successful primary-eligible row is reported beside it as a robustness check, not as a replacement.

## 6. Limits stated before the numbers

Twenty test tasks. Two to four ratings per artifact. The new cohort is 74% fives. H2 calls for the old and new artifacts came from different harnesses (experiment 27's limitation, inherited). H3 on the opened split is valid for that split and invalid for the 50-task folds. H4 is zero-demonstration and is used as a cached feature, not as a new call. No Lean check. No sealed test remains in this pool.
