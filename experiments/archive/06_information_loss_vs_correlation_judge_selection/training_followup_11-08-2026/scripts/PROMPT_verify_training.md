<!-- TLDR: Independently verify the frozen training run from saved inputs, models, forecasts and resampling arrays without replacing or retrying measured fits. -->
# Deterministic verification prompt

Dispatched 11-08-2026 to the implementation worker as a continuation; this is a faithful condensed task record.

Implement `scripts/verify_training.py` with command-line arguments `--data`, `--out` and `--private-out`. Read the frozen protocol and the completed run's receipts. Do not inspect empirical held-out outcomes before the frozen run finishes. Leave empirical execution and publication to the coordinator.

Independently rebuild the six-category empirical targets and cached forecasts. Reconstruct every final mixture, softmax and training-marginal forecast from saved model parameters; verify family splits and training-only feature transformations for all 900 softmax fits. Check complete model/forecast counts, finite results, convergence flags and independent mixture optimality conditions, retaining failed cases rather than dropping them.

Recompute every reported aggregate metric using independent formulas and SciPy's correlation implementations, preserving the recorded 12-decimal expected-rating tie convention. Verify every saved interval against its resampling arrays and the input/protocol hashes. The coordinator separately verifies selected resampling draws by refitting. Write `verification.json` only when the verifier is executed on the completed frozen run. Preserve historical files and make no commits from this subtask.
