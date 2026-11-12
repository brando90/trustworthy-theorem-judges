<!-- TLDR: Replay three existing bootstrap draws and every recorded failure to verify resampling wiring without changing the measured condition. -->
# Bootstrap-refit verification prompt

Dispatched 11-08-2026 after the scientific run was frozen; this is a faithful condensed record of the coordinator's verification task and completion update.

Add a separate `scripts/verify_refit_samples.py` without modifying the frozen source or protocol. Reconstruct bootstrap draws 0, 499 and 999 from the recorded seed. Refit both mixture methods on their resampled training folds with the frozen production `fit_mixture`; independently check each fitted model using `verify_training.mixture_certificate` and aggregate the forecast metrics using `verify_training.metrics`. Compare all 14 differences with the saved resampling arrays. Save aggregate `verification_refit_samples.json` with hashes, counts and maximum errors. The coordinator executes this after completion; this is deterministic evidence verification, not a new scientific condition.

After completion the run had two recorded invalid draws, both reporting an optimality-certificate failure. Replay those indices as well and retain them as failures. Save only aggregate diagnostics: draw, method, seed, fold, residuals, status and tolerances. Do not expose private fitted weights or individual ratings, adjust an algorithm or tolerance, replace a failed draw or change the measured results.
