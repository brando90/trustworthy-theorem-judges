# Experiment 08: master-specification entailment

**Status:** Execution and deterministic verification complete; parent review and main publication pending.
**Last updated:** 11-08-2026 21:10 PST

All 48 primary forecasts completed, plus one preflight and zero transport diagnostics, at $0 provider charges. All 36 eligible controls received the correct endpoint probability. On the held-out test, raw Brier loss was 0 [0, 0] versus 0.25 [0.25, 0.25] for the constant (12 eligible controls, two families; descriptive family bootstrap, p-val=n/a). The model abstained on 3/4 ineligible test controls and 11/12 ineligible controls overall. One contradictory candidate was incorrectly assigned a probability instead of an abstention.

These are simple, constructed certificate-labeled controls. Zero loss and degenerate intervals do not demonstrate broad judge validity, uncertainty estimation, or natural-output generalization. Fitted mappings did not improve the raw judge.

| Phase | Status |
| --- | --- |
| 48 controls and 60 exact-goal kernel audits | Complete |
| Model/input/prompt/scoring freeze before calls | Complete at commit 488f186 |
| 32 training/validation calls, fitting and selection | Complete before test |
| 16 test calls and all declared analyses | Complete |
| Request/response hashes and independent loss verification | Complete |
| GPU cleanup | Study-owned server stopped; no remaining owned model PIDs |
| Parent multi-provider review and main publication | Pending |

[Full results](RESULTS_master_entailment.md), [reproduction commands](README.md), [certificate report](CERTIFICATE_REPORT.md), [forecast checkpoint](CKPT_forecasts.md), and [verification receipt](results/verification.json).

Fresh human returns were not verified from cloud sources. Experiments03–06, Tiny-256, and separately owned VeriBench work were not rerun or modified by this study.
