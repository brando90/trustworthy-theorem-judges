<!-- TLDR: Planned fresh validation of explicitly identified AI judges that forecast VeriBench's prover-based coverage outcome; nothing has run. -->
# Test prover-success predictions on unseen tasks

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/04_test_prover_success_predictions_on_unseen_tasks/README.md>

**Status, 11-06-2026:** Phase 0 done (zero-call retrospective transfer check); Phases 1–4 not started. 0 model calls, 0 prover searches, $0. [Phase 0 results](RESULTS_phase0_transfer.md): experiment 03's unchanged map gives Brier loss 0.107 versus 0.144 for the constant on 1,352 artifacts from 339 unseen tasks (paired -0.037 [-0.049, -0.026], p-val=n/a). Live ledger: [results.md](results.md).

This experiment follows the retrospective [experiment 03](../archive/03_predict_prover_success_from_saved_judge_scores_1024_outputs/README.md). It asks whether an explicitly identified AI judge forecasts the outcome of VeriBench's adopted prover procedure, with its trusted kernel-replay checker, on outputs whose outcomes were sealed while the judge was built. The target and prover belong to VeriBench; this repository owns the judges and the forecasting evaluation.

- [Plan](PLAN.md): phases, gates, judge arms, predictions, success criterion, decisions needed and risks.

- [Phase 0 protocol](PROTOCOL_phase0.md), frozen at commit `9d9a29b` before scoring, with its [configuration](config_phase0.json) and [script](scripts/phase0_transfer.py).

Phase 0 is complete. Within a solver, file length ranks outcomes about as well as the rating, so the fresh test must also beat that baseline. Fresh outcomes wait on two things: more statement-only contexts than the current 14/100 natural pairs, and restored sandbox credits for the measured prover route.

**TLDR-end:** [ttj: fresh prover-target judge validation] Phase 0 shows the historical map transfers to unseen tasks under the historical target. The fresh named-judge test is gated on context yield and sandbox funding.
