# Pre-registration: can a judge be built that beats the constant forecast on held-out tasks, using the old and the new human ratings?

**Dated:** 11-24-2026 (Tue), written and committed before any judge call for this experiment and before any metric was computed on the splits below. Owner: Brando Miranda. Run by ub9sc (ultimate brando9 scalable coworker); harness and model for every piece are named below.

**TLDR:** Exp 22 and exp 25 showed that the earlier judge (H2 prompt) does not beat a constant forecast on held-out tasks, and that both frontier judges overscore the old files by about half a point. This experiment tries to build a judge that does work: new prompt variant, model mixture and calibration, searched on train and validation tasks only, fitted by cross-entropy (CE), evaluated once on held-out test tasks. Correlation is never a training target and never a headline.

## 1. Data and splits (all by task, never by artifact)
Dated copies of the data are in [data_11-24-2026/](data_11-24-2026/). Rater names and ids are removed; ratings are sorted within an artifact.
- **Old set (exp 100 / exp 21 ratings):** 25 tasks, 75 artifacts, 195 ratings. Split = the canonical exp 22 split: 10 train, 5 validation, 10 test tasks. The earlier judge was already scored on the old test tasks in exp 22; nothing in this experiment is fitted on them, but they are not fresh.
- **New set (exp 09 main packet, returned ratings read from the 33 rating Sheets on Tue 11-24-2026 at 12:58 PST):** 25 tasks, 100 artifacts, 247 ratings from 5 raters (73% are 5s). Every artifact has at least 2 ratings. Split = a seeded permutation of the 25 sorted task names (numpy `default_rng(20261124)`): first 10 train, next 5 validation, last 10 test. Drawn before any rating was looked at per task.
- **Pooled:** 50 tasks. Train 20 tasks (old 30 + new 40 artifacts; 78 + 96 ratings), validation 10 tasks (old 15 + new 20 artifacts; 39 + 53 ratings), test 20 tasks (old 30 + new 40 artifacts; 78 + 98 ratings).
- **Ratings still arriving** (Wed 11-25 6 PM PT wave, Thu 12-03): they are added to the same tasks only. A task never moves between splits. A re-run reads the new ratings of the same tasks and states the new freeze time; this experiment's numbers use the 12:58 freeze only.
- **Test is untouched until the final step:** no model is fitted, selected or tuned on test tasks; no prompt demonstration comes from a test or validation task; the test artifacts are judged by the new prompt variant only after the final configuration is committed (section 5).

## 2. What "a judge that does work" means (decided now)
On the pooled test tasks, with 95% task-bootstrap intervals (10,000 draws, seed 20261124), the final judge must beat BOTH (a) the constant forecast inside each set (the human rating distribution of that set's train+validation tasks, applied to the test artifacts of the same set) and (b) the earlier H2 judge (raw GPT-6 Astra + Claude Opus 5.5 H2 histograms, 6 calls per artifact):
- **Works:** RPS difference (judge minus baseline) has a 95% interval entirely below 0 against both, and the point estimates of CE and TVD are also lower than the constant's.
- **Promising, not shown:** all three point estimates (RPS, CE, TVD) are lower than the constant's but the RPS interval includes 0.
- **Not found:** anything else. The bottom line says so plainly, with the evidence size (50 tasks, 442 ratings, 73% of new ratings are 5s).
Also reported per set (old test, new test) and against the pooled constant, the uniform forecast and an edit-distance baseline.

## 3. Metrics
Primary and first in every table: RPS (5-threshold mean of (Qc-Pc)^2 + Pc(1-Pc), lower is better), CE (human distribution against the judge's, lower better), TVD (lower better), each per artifact first then equal weight per artifact, always with the 95% task-bootstrap interval. Spearman and Pearson of the judge's mean against the human mean are secondary columns only. Human distribution = the artifact's rating histogram over 0..5. Judge distribution is floored once at eps = 1e-6 and renormalised (as exp 22, 25).

## 4. Search space (train and validation tasks only)
All candidates give a distribution Q over the 6 scores for each artifact and are fitted by minimising mean CE to the human histograms on train tasks (plus an L2 penalty alpha on slopes, alpha in {0, 0.1, 1, 10}, chosen on validation).
- **Model family (calibration):** ordinal cumulative-logit, P(r <= k) = sigmoid(theta_k - w.x), thresholds theta_0 < ... < theta_4 free, slopes w, features x standardised on train. A candidate may also mix with the train constant, Q = (1-m) Q_ord + m Q_const, m in {0, 0.25, 0.5}.
- **Feature sets (x):** F1 Astra H2 mean score; F2 Opus H2 mean score; F3 both means; F4 F3 plus the absolute Astra-Opus gap; F5 edit-distance similarity alone; F6 F3 plus edit-distance similarity; F7 H3 features (below) alone; F8 F3 plus H3 features; F9 = F8 plus a set indicator (old/new) as a **set-aware sensitivity only**: not eligible as the primary judge, because the set of an artifact is not a property a deployed judge may rely on.
- **Direct-distribution candidate:** the H3 judge's own verbalised distribution p over 0..5, Q proportional to p^beta * const^gamma, beta and gamma fitted by CE on train.
- **H3 prompt variant (the only new prompt, run on Vals Codex):** same system text as H2 (rater instructions and conventions), with (i) four rated demonstrations drawn only from TRAIN tasks other than the item's own task, two from the old set and two from the new set (one per task, closest to the 0.15 and 0.85 quantiles of that set's train mean ratings), (ii) one sentence stating the base rate of expert scores computed on all train ratings, (iii) an extra output key `score_distribution`: probabilities for the score of a randomly drawn expert rater over 0..5, summing to 1. Features: h3_score (final_score_0_5) and h3_expected (mean of score_distribution). One call per artifact at first (repeat 1); more repeats only if time allows and then for all artifacts.
- **Selection rule:** among candidates that are not set-aware, fit on train, choose the one with the lowest pooled-validation RPS (ties: lower validation CE). Then refit that configuration on train+validation tasks and score it on test. Candidates, validation scores and the choice are written to `results/search_log_11-24-2026.json` and committed in the freeze commit before the H3 test calls and before any test metric is computed.

## 5. Order of work (each step committed)
1. This pre-registration, the dated data copies and the splits (this commit).
2. Edit-distance feature (CPU), H3 calls on train and validation artifacts (Vals Codex), calibration search on train/validation (CPU).
3. Freeze commit: selected configuration and its fitted settings, with the search log.
4. H3 calls on test artifacts (only if H3 features are in the selected configuration), then the one test evaluation.
5. Results, Google Doc, QA by a second model family and a second recomputation by Cursor/Grok (recomputing every headline number from the anonymised data with its own code and checking the splits for leakage).

## 6. Harness and model for every piece
- Old judge scores (H2): cached exp 21/22 runs (GPT-6 Astra via the OpenAI API; Claude Opus 5.5 via the Vals gateway; H2_sol via the Vals gateway). New-set H2 scores: exp 25 runs (GPT-6 Astra high via Codex CLI one-turn on the personal Codex plan; Claude Opus 5.5 high via Claude Code one-turn on the Stanford plan). The mixed harnesses are a known limitation.
- H3 calls: GPT-6 Astra, reasoning high, Codex CLI one-turn, read-only sandbox, no tools, on the Vals Codex plan (included usage only, no extra charges).
- Calibration search, metrics, bootstrap: CPU Python (numpy, scipy), no model.
- QA: Claude Opus 5.5 (Claude Code on a Vals or Stanford plan) and Grok/Cursor (heaviest lane), from the anonymised data only.

## 7. Predictions (before seeing numbers)
1. Calibrating to the train marginal removes most of the old-set offset, so a calibrated judge beats the pooled constant on test. Against the set-aware constant the gain will be small: my guess is about 25% that the work criterion in section 2 is met.
2. H3 (pooled demonstrations plus base rate) lowers validation CE relative to raw H2, but adds little RPS beyond calibrated H2 means.
3. The edit-distance baseline is about as good as the constant.
4. Spearman and RPS will disagree on the ranking of at least one pair of judges.

## 8. Limits stated in advance
Only 247 of 3,300 new rating rows are back (5 raters, 73% 5s); a 2-rating artifact gives a noisy human distribution; 20 test tasks give wide intervals; no Lean check or differential testing; judge scores for old and new artifacts come from different harnesses for H2; the old test tasks were seen by the earlier judge in exp 22.
