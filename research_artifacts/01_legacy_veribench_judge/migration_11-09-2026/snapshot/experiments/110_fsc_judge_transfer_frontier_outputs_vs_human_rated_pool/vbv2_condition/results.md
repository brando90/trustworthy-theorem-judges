<!-- TLDR: Live ledger for experiment 110's VBV2 condition (H2 FSC judge validation pool vs VeriBench V2 frontier-model outputs, 15 frozen criteria, zero model calls). -->
# Results ledger: experiment 110, VBV2 condition

**Doc link:** [Results report](RESULTS_judge_transfer_vbv2.md) · [Pre-registration](CRITERIA_VBV2.md)

**Status:** DONE (started 10-09-2026 15:45 PDT). **Last updated:** 10-09-2026 16:33 PDT.

| Phase | Status | Evidence |
|---|---|---|
| Pre-registration (criteria, prediction, blinding) | DONE | [CRITERIA_VBV2.md](CRITERIA_VBV2.md), committed in `f1bfbe3564` before any VBV2 value; amendment V-A1 appended |
| Gather VBV2 judged candidates (texts the judge saw, H2 repeats) | DONE | 30 primary cells (0 repeat-pack problems; J1/J2 complete 30/30) + 83 secondary phase-7 cells |
| Pool reproducibility check | DONE | 3/3 seeded pool rows identical; pool null equals experiment 110's |
| Criteria and k/15 with task-cluster bootstrap | DONE | primary pooled VBV2 FM **11/15 [8–11]**, "partially in-distribution"; prediction (k <= 7) refuted |

| Condition | Files / tasks | k/15 [95% interval] |
|---|---|---|
| Primary pooled VBV2 FM (experiment 103) | 26 / 5 | 11 [8–11] |
| Secondary phase 7, original packaging | 33 / 6 | 8 [6–11] |
| Secondary phase 7, reference-scoped packaging | 30 / 5 | 10 [6–11] |
| VBV1 pooled FM (experiment 110, comparison) | 8,106 / 896 | 8 [7–10] |

**TLDR-end:** [vb: experiment 110 VBV2 condition, FSC judge transfer to VeriBench V2] VBV2 frontier-model outputs are partially in-distribution for the H2 judge (11/15 [8–11]) and shift only on size and completeness, not on the error-linked criterion; human ratings of VBV2 outputs remain the missing validation.
