<!-- TLDR: Implement the prespecified same-class weighted-PMF and Pearson mixture fits and synthetic controls without consulting empirical test results. -->
# Mixture implementation prompt

Implement `mixture_models.py` and `check_mixtures.py` for experiment `06_information_loss_vs_correlation_judge_selection/training_followup_11-08-2026`.

Use the shared simplex-mixture class q_i=sum_j w_j Q_ij, with nonnegative weights summing to one. Expose `fit_mixture(qtrain[n,5,6], p[n,6], objective) -> (weights[5], receipt)` for `weighted_pmf` and `pearson`, and `predict_mixture(q, weights)`.

Minimize empirical weighted squared probability mass function loss with finite enumeration of all 31 nonempty active faces of its convex quadratic program. Verify the result using the simplex Frank–Wolfe gap. Maximize Pearson correlation by projecting the centered human mean onto the nonnegative cone of centered candidate expected-rating columns. Enumerate all 31 nonempty least-squares supports; normalize recovered nonnegative coefficients to simplex weights. Include the correct nonpositive-correlation solution, explicit undefined handling for constant targets or forecasts, deterministic minimum-support/lexicographic tie-breaking, and numerical certificates.

Fix feasibility and linear-solve tolerances at 1e-10, certificate tolerance at 1e-8, and objective-tie/constant-vector tolerances at 1e-12. Record these settings, actual support, certificate residuals, training loss/correlation and undefined status in receipts. Retain failures for the coordinator rather than changing the objective or tolerances after empirical outcomes.

Use synthetic controls for exact mixture recovery, independently enumerated dense two-candidate grids, negative/zero correlations, duplicate columns, constant targets and predictions, and different distributions with identical expected ratings. Use NumPy only. Save the mathematical proof, assumptions and model-class limits in `MATH_baseline.md`.

This implementation task has full inherited filesystem access with approvals disabled. Root owns the run protocol, runner, scientific-data access, execution and publication. This subtask does not inspect empirical test data or alter earlier experiment evidence. No model inference is measured or required by the numerical implementation.
