# Matched probability-head follow-up

**TLDR:** Separately compare CE, Brier, ranked probability score and Pearson as fitting objectives for the same small softmax model.

This condition was specified after inspecting the frozen histogram experiment, which exposed its sparse-support limitation. It implements the previously planned secondary matched-optimization phase. It is exploratory and cannot replace the primary result or make the old human data independent.

- Inputs: five cached judges' mean normalized scalar ratings, identical for every condition. Target: six-category distribution of available expert ratings per artifact.
- Model: affine six-class softmax, five features plus an intercept, 36 stored coefficients (with softmax redundancy). Standardize features using only the fit's training rows. No language-model weights or prompts change.
- Fit objectives: average individual-rating cross-entropy (CE), multiclass Brier, normalized ranked probability score (RPS), or one minus Pearson correlation of expected rating and human mean. Pearson is the exact smooth correlation objective up to a 1e-12 denominator stabilizer. This condition does not fit exact Spearman or Kendall objectives.
- Same capacity, random initializations, optimizer and stopping budgets: L-BFGS-B, analytic gradients, at most 300 iterations and 600 function evaluations, common 0.02-standard-deviation Gaussian initialization, fixed paired seeds. Nonfinite fits fail execution; finite unconverged fits remain in the denominator and are reported, without extra retries.
- Same validation criterion for every fit objective: RPS on pooled four-inner-fold held-out predictions selects L2 strength from [0.001, 0.01]. Penalize all coefficients by strength times squared norm divided by two. This is a common numerical strength grid, not a guarantee of identical effective regularization across differently scaled losses.
- Use the same five outer task-family folds and five seeds as the frozen primary phase. Fit four inner models for each of two strengths; refit the selected strength on all outer-training artifacts and evaluate the outer test. All splits keep families intact. Total: 900 fits and 100 outer forecasts, no missing cells discarded.
- Apply common epsilon=1e-6 probability smoothing only for reported forecasts and validation RPS. Fit CE using stable log-softmax; fit other objectives on the unsmoothed softmax probabilities.
- Evaluate all four conditions on every common metric. Secondary comparison: CE fitting minus Pearson fitting. Preserve all metrics and seeds; no success threshold or confirmatory p-value. Expect CE to favor CE and Brier/RPS to favor their scores; no predicted guaranteed correlation improvement.
- Report 1,000 paired task-family bootstrap intervals conditional on fitted heads and chosen regularization. These do not refit the 900 models and exclude fitting/selection uncertainty; do not give them the stronger interpretation of the primary phase's selection-refit interval.
- Verify every analytic gradient against finite differences and demonstrate a two-example unregularized CE fit before admission. Verify forecast rows, full fit counts and all output hashes after execution.
- Execution: one CPU thread on the existing skampere3 owner/session; same eight-hour/$0-new-inference envelope. Private weights and per-artifact forecasts remain private.

**TLDR-end:** [ttj: objective comparison] This follow-up isolates the training loss of a small fitted probability mapping; it is not end-to-end judge training or fresh validation.
