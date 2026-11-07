# Experiment index

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/README.md>

**TLDR:** Historical VeriBench evidence, prospective human-rating prediction, and prover-outcome forecasting have separate experiment records. The prover studies have completed retrospective analyses and a fresh local feasibility test; broad validation remains pending.

| Experiment | Status | Evidence or next step |
| --- | --- | --- |
| [01_legacy_veribench_judge](01_legacy_veribench_judge/README.md) | Historical evidence import | Aggregate receipts with original conditions, confidence intervals, and exposure limitations; no rerun or new validation. |
| [02_probabilistic_ordinal_judge](02_probabilistic_ordinal_judge/README.md) | Prospective methodology | Freeze a benchmark manifest and pilot the rating protocol, then collect independent human ratings. |
| [03_prover_target_fsc_judge](03_prover_target_fsc_judge/README.md) | Retrospective feasibility analysis complete | Predict historical prover acceptance using saved scalar ratings; a fresh statement-only forecasting study requires a verified target protocol and eligible funding. |
| [04_fresh_prover_target_judge_validation](04_fresh_prover_target_judge_validation/README.md) | Phase 0 done 11-06-2026; fresh test not started | Zero-call transfer: experiment 03's frozen map gives Brier 0.107 versus 0.144 for the constant on 1,352 artifacts from 339 unseen tasks. Next: a sealed test of explicitly identified judges against VeriBench's trusted prover outcome; gated on context yield and sandbox funding. |
| [05_fresh_local_prover_target_judges](05_fresh_local_prover_target_judges/README.md) | Local feasibility complete 11-06-2026; no validated judge | Eight fresh generation attempts: five malformed artifacts and three unsuccessful bounded-prover outcomes, covering only two unique well-formed statements. Explicit direct/checklist judge prompts tie the constant-zero baseline on available cells. Both conditions used 46 local calls, $0 provider charges; broader validation remains pending. |
| [06_information_loss_vs_correlation_judge_selection](06_information_loss_vs_correlation_judge_selection/RESULTS.md) | Cached comparisons complete 11-06-2026; fresh confirmation pending | 75 artifacts, 25 tasks, 195 expert ratings. CE selection did not resolve an advantage over Spearman; 900 matched probability-head fits completed, with Pearson nonconvergence limiting the comparison. Zero new model calls; [11-07 distance extension](06_information_loss_vs_correlation_judge_selection/followup_11-07-2026/RESULTS.md) complete without a resolved advantage. |

The existing [reference-anchoring plan](../docs/reference-anchoring-plan.md) is a separate proposed controlled comparison. It can supply semantic and reference-sensitivity checks; its two-rater pilot is not the main study's three/eight-rating collection design. Neither plan has been executed by adding this index.
