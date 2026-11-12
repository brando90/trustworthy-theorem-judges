# Experiment 04 results ledger

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/04_fresh_prover_target_judge_validation/results.md>

**Status:** Phase 0 DONE; Phases 1–4 PENDING (gated on statement-only context yield and the measured prover route).
**Last updated:** 11-06-2026 15:00 PST

| Phase | State | Result |
|---|---|---|
| 0. Frozen-map transfer, zero calls | DONE 11-06-2026 | Brier 0.107 versus constant 0.144, paired -0.037 [-0.049, -0.026], 1,352 artifacts / 339 tasks, p-val=n/a. [Report](RESULTS_phase0_transfer.md) |
| 1. Freeze prover target | PENDING | VeriBench experiment `169_natural_output_prover_fsc_validation_11-06-2026` owns it; 14/100 contexts emitted; measured route blocked on sandbox credits |
| 2. Fresh evaluation population | PENDING | Needs about 64 family-disjoint test tasks with emitted contexts |
| 3. Named judges | PENDING | Local arms J0–J3 need no paid calls; J4 needs an eligible route |
| 4. Sealed test | PENDING | — |

Run receipt for Phase 0: protocol commit `9d9a29b`; command `uv run --python 3.12 --with numpy==2.4.2 --with scipy==1.17.0 python experiments/04_fresh_prover_target_judge_validation/scripts/phase0_transfer.py --source-repo <authorized VeriBench checkout>`; wall time 2 min 35 s on Brando's Mac; 0 model calls; $0.

**TLDR-end:** [ttj: experiment 04] Phase 0 shows the historical map transfers to unseen tasks; the fresh named-judge test has not started.
