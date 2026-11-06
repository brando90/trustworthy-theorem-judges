<!-- TLDR: Planned fresh validation of explicitly identified AI judges that forecast VeriBench's prover-based coverage outcome; nothing has run. -->
# Experiment 04: fresh prover-target judge validation

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/04_fresh_prover_target_judge_validation/README.md>

**Status, 11-06-2026:** planned, not started. 0 model calls, 0 prover searches, $0.

This experiment follows the retrospective [experiment 03](../03_prover_target_fsc_judge/README.md). It asks whether an explicitly identified AI judge forecasts the outcome of VeriBench's adopted prover procedure, with its trusted kernel-replay checker, on outputs whose outcomes were sealed while the judge was built. The target and prover belong to VeriBench; this repository owns the judges and the forecasting evaluation.

- [Plan](PLAN.md): phases, gates, judge arms, predictions, success criterion, decisions needed and risks.

Phase 0, a zero-call transfer check of experiment 03's frozen map on 1,352 artifacts from 339 tasks outside Tiny-256, can run now. Fresh outcomes wait on two things: more statement-only contexts than the current 14/100 natural pairs, and restored sandbox credits for the measured prover route.

**TLDR-end:** [ttj: fresh prover-target judge validation] A plan exists; no measurement has run. Phase 0 is free and ready, and the fresh test is gated on context yield and sandbox funding.
