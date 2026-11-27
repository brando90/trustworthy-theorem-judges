# Pre-registration: next-rating rank and power curve (11-27-2026)

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/30_rank_next_human_ratings_by_judge_ensemble_uncertainty_and_power_curve_for_the_held_out_rps_gain_start_27Nov2026/PREREG.md>

**TLDR:** Rank the 100 new-set artifacts for the next human rating using only logged judge distributions and the count of ratings so far. Separately, estimate whether more ratings on the same 20 held-out tasks can push the experiment 27 ranked probability score (RPS) interval upper bound below 0. Written before the measurement script is run.

**Date:** 11-27-2026. CPU only. No new model call. No differential testing. No Lean check.

## Question

The new ratings are 74% fives (185 of 250). Experiment 27's held-out RPS gain versus the set-aware constant is about -0.035 with a task-bootstrap interval that still reaches +0.002. Where should the next real human ratings go, and how many more ratings or tasks would make that upper bound negative?

## What this does not show

Resampling the 445 ratings cannot certify a judge. Every power number is a simulation or a retrospective subsample of ratings that already exist. A curve that uses draws from the current histograms is a planning calculation under that assumption, not a human-certification result.

## Rank score (fixed before looking at the order)

Six logged members, equal weight, on every artifact that has them: H2 Astra (3 integer calls, as a histogram), H2 Opus (3 calls), H3 Astra (one probability vector), H4 Astra, H4 Argon, H4 Opus. Members that exist only on the old 75 artifacts (H0, H1, H2 Sol) stay out of the score so the new and old sets are not scored with different ensembles.

- Disagreement = sample standard deviation (ddof 1) of the six expected scores on the 0–5 scale.
- Ensemble distribution = the mean of the six probability vectors.
- Normalized entropy = Shannon entropy of that mean, in nats, divided by log(6).
- Ceiling mass = probability of score 5 under that mean.
- Non-ceiling uncertainty = normalized entropy times (1 − ceiling mass).
- Rank score = disagreement + non-ceiling uncertainty + 0.5 / (1 + number of ratings so far).

The live queue is the 100 new artifacts (250 of 3,300 sheet rows filled, 33 rows per artifact). Higher rank score is rated next. The split (train, validation, test) is not an input. Ties break by item id.

Sequential allocation, used only inside the simulation, puts the next rating on the artifact that maximizes (disagreement + non-ceiling uncertainty) / ((n+1)(n+2)), among artifacts that still have a rating left to reveal or a synthetic rating left to place.

## Power endpoint

Estimand: mean over test artifacts of RPS(human histogram, F8 forecast) minus RPS(human histogram, set-aware constant). The F8 forecast is the experiment 27 cumulative logit (Astra mean, Opus mean, H3 score, H3 expected score), cross-entropy, L2 penalty 0, mixture 0, refit on train+validation and then held fixed. The set-aware constant is the train+validation human marginal inside each set, also held fixed. The interval is the 2.5 and 97.5 percentiles of a task bootstrap, 10,000 draws.

Primary planning number: the smallest count of extra ratings, or extra tasks, at which the upper endpoint is below 0. If the rating curve never crosses, say so and give the extrapolated task count.

## Predictions, committed before the run

1. Replaying experiment 27's own loader and fit reproduces the paired RPS -0.034895 with interval endpoints -0.075959 and +0.002444 within 0.0005 on the point and 0.001 on each endpoint (seed 20261124, 10,000 draws).
2. An independent leave-one-task-out set-aware recomputation on the frozen rating tables matches the stored experiment 25 differences within 0.001: Astra +0.001966 and Opus -0.017716 on the 247-rating freeze; Astra +0.000232 and Opus -0.016911 on the 250-rating interim file.
3. Extra ratings drawn from each test artifact's current histogram do not push the median task-bootstrap upper bound below 0 at any extra count up to 2,240. The upper bound stays within 0.01 of the full-data upper bound. Active and uniform allocation differ by less than 0.005 on that upper bound.
4. The same interval's distance from the point estimate scales close to 1/sqrt(number of tasks). Holding the full-data point fixed, the extrapolated task count that puts the upper bound below 0 is between 22 and 40 tasks (20 are in the test set now).
5. Retrospective check that the rank is not ignoring the ceiling: the five-rate in the top 25 new artifacts is lower than the five-rate in the bottom 25. Among ratings revealed after the first rating per artifact, up to 100 further ratings, the active policy's five-rate is lower than the uniform policy's five-rate.

A miss is reported. The formulas are not retuned after the numbers appear.

## Controls

- Shuffling rating values, while keeping the count per artifact, does not change the rank score.
- No task sits in two splits. The fit index and the test index are disjoint.
- Two task bootstraps with the same seed return the same endpoints.
- One traced artifact prints its six member distributions, its rank score, and its RPS terms.
