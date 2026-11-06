<!-- TLDR: Frozen Phase 0 protocol: score experiment 03's unchanged probability map and simple baselines on 1,352 Core-614 artifacts from 339 tasks outside Tiny-256; zero model calls. -->
# Experiment 04 Phase 0 protocol: frozen-map transfer to unseen tasks

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/04_fresh_prover_target_judge_validation/PROTOCOL_phase0.md>

**TLDR:** Score experiment 03's unchanged probability map, a constant and three simple baselines on Lean-checked prover outcomes for 1,352 artifacts from 339 tasks outside Tiny-256. This is a retrospective transfer check with the historical target and an unbound historical judge, not fresh validation. Committed 11-06-2026 together with [the script](scripts/phase0_transfer.py) and [configuration](config_phase0.json), before any Phase 0 metric was computed.

## Prior exposure

Before this commit the author saw only aggregate counts: 1,352 joinable rows, 339 tasks, 1,120 final accepted outcomes, 0 tasks shared with Tiny-256, and exact equality of the saved ratings with experiment 03's feature on 1,024/1,024 Tiny-256 artifacts. VeriBench experiment `154_core614_dt_overview_358_tasks_11-01-2026` had already published per-solver entailment counts. No forecast, baseline or per-artifact rating–outcome relation on Core-614 had been computed. The [plan](PLAN.md) recorded the predictions at commit `8be94a8`.

## Data

- **Outcome:** `E_lean` in each `lean_entailment/E_LEAN_CHECKED.csv` of VeriBench experiments `144_core614_dt_first_batch_claude_code_11-01-2026`, `147_core614_dt_batch1_codex_11-01-2026`, `148_core614_dt_batch1_fable_5_1_11-01-2026`, `149_core614_dt_batch1_astra_11-01-2026`, `150_core614_dt_security238_claude_code_11-01-2026`, `151_core614_dt_security238_codex_11-01-2026`, `152_core614_dt_security238_fable_5_1_11-01-2026` and `153_core614_dt_security238_astra_11-01-2026`, at VeriBench revision `ec1f9b2a44`. Their READMEs state the experiment 145 rules: bridge compiles, every gold theorem proved, standard axioms in the bridge and in every named solver theorem, gold unedited, non-vacuity witness from the solver's real definitions. That is the same five-condition rule as experiment 03's target, with the same historical integrity limits: agent-written bridges, name-based statement correspondence and no trusted kernel replay.
- **Primary outcome is first-pass.** Three runs became counted only in a later retry round (experiment 150 `S077`; experiment 153 `S063` and `S072`); they are scored 0 in the primary analysis and 1 in a pooled sensitivity row. Retry rounds in experiments 148 and 149 changed no outcome. Experiment 144's 21 partly proved runs were never retried.
- **Input:** the saved judge-ensemble rating `FSC_cov` in VeriBench experiment `137_public_vbv1_896_harsh_failure_reasons_and_smooth_components_10-30-2026`, joined by lowercase task key and solver system name; the join must be complete and unique. As in experiment 03, no exact judge model is bound to a rating row.
- **Candidate files** for the simple baselines are each run's `solver.lean`; hashes are checked against the solver manifests (Core-614) and receipts (Tiny-256, VeriBench experiment 138 at `be287d9`), and mismatches are counted and reported.

## Forecasts, all frozen before scoring

| Name | Definition | Fitted on |
|---|---|---|
| `mapped` | `expit(-7.402941748053847 + 9.463768107149697 · FSC_cov)`, experiment 03's pooled ridge-0 map | Experiment 03 only; not refit. The script refits it on experiment 03's training split only to check reproduction within 1e-4. |
| `constant` | 0.800781, experiment 03's training prevalence | Experiment 03 |
| `raw_scalar` | `FSC_cov` itself; diagnostic only | none |
| `thm_ratio_map` | logistic map of `min(1, candidate theorem/lemma declarations ÷ gold theorems)` | Experiment 03's Tiny-256 training split (256 artifacts); ridge from {0, 0.01, 0.1, 1} chosen by validation Brier loss |
| `length_map` | logistic map of `log(1 + non-blank lines of solver.lean)` | Same as above |
| `solver_prevalence` | training-split acceptance rate of the artifact's solver | Same training split |

Theorem declarations are counted by the regular expression in the configuration (line-start `theorem` or `lemma`, optionally after an attribute and `private`/`protected`/`noncomputable`). Gold theorem counts are `gold_theorems` (Core-614) and `k_gold` (Tiny-256). A missing candidate file gives features 0 and is counted.

## Analysis

- **Primary:** pooled paired Brier difference, `mapped` minus `constant`, on all 1,352 artifacts with first-pass outcomes.
- **Secondary:** paired differences of `mapped` against each simple baseline and of each baseline against `constant`; Brier loss, mean absolute error (descriptive), signed bias (forecast minus outcome), both means, Pearson, Spearman and Kendall (tau-b) correlations and area under the receiver operating characteristic curve for every forecast; the same for the 120-task first batch, the 238-task security set and each solver; a calibration band table by saved rating.
- **Uncertainty:** 10,000 task-clustered bootstrap draws (seed 11062026), resampling tasks with all their artifacts; intervals condition on the frozen forecasts and the fixed four solvers and omit family dependence. `p-val=n/a`: descriptive retrospective screening.
- **Controls checked by the script:** oracle `q = Y` gives Brier 0, `q = 0.5` gives 0.25, `q = 1 - Y` gives 1; the split manifest must reproduce experiment 03's hash split; no Core-614 task may appear in Tiny-256.

## Predictions (from the plan, unchanged)

`mapped` beats `constant` with a pooled paired difference between -0.03 and -0.07; the gain is smaller on the security set than on the first batch; `mapped` overpredicts in the 0.9 rating band; whether `thm_ratio_map` matches `mapped` is unknown.

## Reading

- Interval of `mapped` minus `constant` below zero: the historical association transfers to unseen tasks under the same target.
- `mapped` minus the best simple baseline with an interval containing or above zero: the signal is not shown to be specific to the judge rating.
- Neither result validates a judge, fixes the target's integrity limits or binds a judge identity.

Outputs: aggregate `results/phase0_transfer.json`, source hashes `results/phase0_sources.json`, report `RESULTS_phase0_transfer.md`, ledger `results.md`. Per-artifact rows stay in ignored `private/phase0_transfer/`.

**TLDR-end:** [ttj: experiment 04 Phase 0] Frozen definitions for a zero-call check of whether experiment 03's map transfers to 339 unseen tasks, against constant and simple baselines.
