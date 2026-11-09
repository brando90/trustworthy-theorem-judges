<!-- TLDR: Implement the weighted-PMF softmax fitting module and synthetic controls without changing historical experiments or inspecting held-out outcomes. -->
# Weighted softmax implementation prompt

Dispatched 11-08-2026 to the implementation worker; this is a faithful condensed record of the parent task and explicit continuation.

Implement `training_followup_11-08-2026/scripts/weighted_softmax.py` in the owned experiment 06 checkout. Read the existing `HEAD_PROTOCOL.md`, `scripts/fit_heads.py` and `scripts/metrics.py`. Preserve all historical files and leave publication to the coordinator.

Expose `objective`, `fit` and `predict` for the existing six-category affine softmax probability model. Add weighted probability mass function (PMF) training loss, equal-row mean of `sum_r p_r (p_r-q_r)^2`, with probability gradient `2 p (q-p)`. Support cross-entropy, Brier and normalized ranked probability score under the same configurable fitting budget.

Remove the irrelevant common class-logit offset with a fixed orthonormal zero-sum basis, yielding centered six-class coefficient rows and five independent coordinates per row. Include an intercept and fit feature centering/scaling only on the supplied training rows. Make optimizer limits and tolerances explicit. Return full convergence, finite-value, gradient-norm and parameter-count receipts; preserve finite nonconverged fits without automatic retries.

Use synthetic inputs only for this subtask. Verify analytic gradients by finite differences, the weighted oracle, a two-example weighted fit, probability normalization, coefficient centering and training-only preprocessing. The coordinator freezes the experiment protocol and runs all empirical comparisons, including a separately specified stable correlation baseline. No empirical dataset or held-out results are needed for this implementation.

Continuation after the interrupted turn: finish this module and controls, save this prompt, report the public function interface and changed files, and do not commit.
