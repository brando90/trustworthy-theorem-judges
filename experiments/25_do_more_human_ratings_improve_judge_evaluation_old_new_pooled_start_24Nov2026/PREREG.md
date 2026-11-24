# Pre-registration: does pooling old and new human ratings give a better evaluation of the trustworthy judge?

**Dated:** 11-24-2026, written before any judge call on the new artifacts and before any new rating was analysed. Owner: Brando Miranda. Run by: ub9sc (ultimate brando9 scalable coworker), harness and models named below.

**TLDR:** The old study (exp 21/22) evaluated judges on 75 artifacts (25 tasks, 195 expert ratings) and its split-level numbers ("0.6, 0.8, 0.8" = Spearman on train/val/test of 10/5/10 tasks) were unstable with wide intervals. New ratings (100 artifacts, 25 other tasks, returned so far) are arriving. This experiment asks whether pooling gives a *better evaluation* (narrower, more stable intervals, a higher human-agreement ceiling), not whether the judge is better.

## Questions
- Q1. For old alone, new alone and pooled: how wide are the 95% task-bootstrap intervals of RPS, CE, TVD, Spearman, Pearson for the same judge?
- Q2. Human ceiling: split-half agreement between human raters of the same artifact, on old (3 experts) and new (returned raters), in RPS, Spearman and Pearson.
- Q3. Learning curve: interval width and spread of the point estimate against the number of tasks (subsample k tasks).
- Q4. What does more data not fix? (a judge that is miscalibrated stays miscalibrated; checked by the RPS decomposition and by comparing RPS to the constant baseline.)

## Data (only returned ratings; no sealed keys; no individual ratings or rater names leave the private working copy)
- Old: 75 artifacts, 25 tasks, 195 expert ratings (VeriBench exp 100 inputs, source commit be287d9), judge scores cached (exp 21/22).
- New: 100 artifacts = 25 new tasks x 4 agents (exp 09 main packet). Ratings read from the returned rating Sheets (final_score_0_5 filled; blank rows are not ratings). The set analysed is frozen at the read time recorded in results/INVENTORY.md; later waves (Wed Nov 25 6 PM PT, Thu Dec 3) go in a re-run, not into this one.
- An artifact enters "new" if it has at least 2 returned ratings (an artifact with 1 rating is listed but excluded from distribution metrics, since a one-rating distribution cannot give a ceiling).

## Judges
- Old artifacts: cached judges from exp 21/22 (H2 prompt; GPT-6 Astra high via OpenAI Responses API; H2_sol+H2_opus via Vals gateway; others as in exp 22). No new calls.
- New artifacts (no judge scores existed): the same frozen H2 prompt (exp 100 `prompts.py` H2_human_mirror_conventions_demos, same four leave-task-out rated demos from old training tasks), 3 calls per artifact per judge:
  - GPT-6 Astra, reasoning high, through Codex CLI (read-only sandbox, no tools) on the Codex plan of skampere1.
  - Claude Opus 5.5, effort high, through Claude Code one-turn isolated call (no tools) on the plan.
  Both differ from the old harness (API / Vals gateway, Opus effort max). Pooled numbers for a judge are therefore labelled "mixed harness"; the harness gap is a limitation, not corrected.
- Cost: plans only, $0 extra; list-price equivalent about $10 to $15 (300 + 300 calls, ~30k tokens in, <1k out).

## Metrics (as in exp 22, same code definitions)
- Judge distribution: histogram of the 3 repeat scores over 0..5, smoothed once at eps = 1e-6 (primary); Laplace 0.5 reported as sensitivity.
- Human distribution: empirical histogram of the artifact's returned ratings.
- Primary: normalized Ranked Probability Score (RPS), lower is better. Then CE, TVD. Secondary columns: Spearman and Pearson (judge mean score vs human mean score). Per artifact first, then equal weight per artifact.
- Baselines: constant = pooled-rating marginal computed leave-one-task-out; uniform.
- Intervals: 95% percentile bootstrap resampling whole tasks, 10,000 draws, seed 20261124.

## Ceiling
For artifacts with >= 2 raters, randomly split raters into two halves (1,000 random splits), compute RPS between the two empirical half-distributions and Spearman/Pearson between half means; report the Spearman-Brown corrected full-rater ceiling for correlations.

## Learning curve
For k in {5, 10, 15, 20, 25} (and {30, 40, 50} for pooled): 300 random subsets of k tasks without replacement; for each, the metric and a 1,000-draw task-bootstrap interval. Report mean interval width, and the SD of the point estimate across subsets.

## Predictions (before seeing numbers)
1. Pooled intervals are narrower than old-alone by roughly sqrt(2) in width on RPS and Spearman (50 vs 25 tasks) if the two task sets behave alike; Spearman intervals stay wide for k <= 10 whichever data.
2. The human ceiling on new data is lower or comparable to old for the same artifact count, because few artifacts have more than 2 returned ratings.
3. The judge's RPS is not better than the constant baseline in a statistically clear way on either set (as in exp 22), so more data tightens the evaluation but does not turn a weak judge into a good one.
4. Spearman and RPS rank judges differently on at least one pair.

## Decision rule
"Better evaluation" = (a) pooled 95% interval width of RPS at most 0.8 of old-alone width AND (b) spread of the point estimate across k-task subsets at k = 25 below that at k = 10 AND (c) pooled ordering of judges by RPS is stable across half of the subsets. If (a) fails, report "no". This says nothing about the judge being better.

## Not done / limits (stated in advance)
- New ratings so far come from a few raters; many artifacts have 2 ratings. Distribution metrics on 2-rating artifacts are noisy; this is reported, not hidden.
- No Lean proof check, no differential testing (FSC human-rating judgments only).
- Two judges only on new artifacts; the other cached judges cannot be pooled without paid calls.
- Light QA by a second model family (GPT-6 Astra through Codex re-computing the headline numbers from the raw private data) after the run.
