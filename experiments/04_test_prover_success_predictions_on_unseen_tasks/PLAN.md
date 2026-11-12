<!-- TLDR: Plan to validate explicitly identified AI judges that forecast VeriBench's prover-based coverage outcome on fresh outputs; nothing has run. -->
# Experiment 04 plan: fresh validation of AI judges that forecast the prover outcome

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/04_test_prover_success_predictions_on_unseen_tasks/PLAN.md>

**Status, 11-06-2026:** plan only. Nothing has run: 0 model calls, 0 prover searches, $0. This plan follows [experiment 03](../archive/03_predict_prover_success_from_saved_judge_scores_1024_outputs/README.md) (`03_predict_prover_success_from_saved_judge_scores_1024_outputs`) and supersedes its 12-pair pilot sketch where the two differ, because VeriBench work completed on 11-06-2026 changed the binding constraint.

**Addendum, 11-06-2026:** Phase 0 ran under its [frozen protocol](PROTOCOL_phase0.md); see [its results](RESULTS_phase0_transfer.md). The plan text below is unchanged.

## Goal and decision

Experiment 03 showed that saved formal specification coverage (FSC) ratings, passed through a fitted probability map, predict historical prover acceptance better than a constant (test Brier loss 0.107 versus 0.165, paired difference -0.058 [-0.087, -0.031], 512 artifacts from 128 tasks, p-val=n/a). An artifact is one solver run on one task. Three limitations block naming a validated judge: the historical target has integrity gaps, the test was retrospective with task families crossing splits, and no exact judge identity is bound to each saved rating.

This experiment asks: **does an explicitly identified AI judge forecast the outcome of VeriBench's adopted, trusted prover procedure on outputs whose outcomes nobody has seen, better than constant and simple baselines?**

The evidence decides one of three actions. Adopt a judge as a cheap forecaster and triage step for the prover. Keep the prover alone if no judge beats the simple baselines. Stop this line if a trustworthy prover target cannot be built on a natural population of useful size.

## What changed on 11-06-2026

VeriBench experiment `169_natural_output_prover_fsc_validation_11-06-2026` (restricted VeriBench repository) now owns the target this plan needs:

- VeriBench adopted prover-based FSC for its version 1 (VBV1) paper. The primary prover condition is native Pi 1.4.0 with `google/gemini-3.1-pro-preview`, reasoning HIGH, temperature 1, one initial request plus at most two Lean-feedback requests.
- Its checker now accepts a proof only after a trusted kernel replay: the candidate module is read as data, every constant is re-checked, the goal type must match exactly, and transitive axioms are limited to `propext`, `Classical.choice` and `Quot.sound`. A strict gate rejects newly declared axioms. Thirteen designed controls matched; all 94 archived control proofs replay; two audit bypasses that fooled the earlier checker are rejected.
- **Binding constraint:** its model-free exporter built a statement-only context (abstract implementations, satisfiability witness, leakage control) for only **14 of 100** frozen natural pairs. Of the 86 unresolved pairs, 84 show an interface representation mismatch between reference and candidate. No prover has run on a natural context, so natural-output detection and false-alarm rates are still unmeasured.
- **Blocker:** the measured prover route is built and verified, but cannot start because the Valkyrie sandbox provider's credits are depleted ($0.00 spent). Restoring them is a billing change reserved to Brando.

Two zero-call facts were verified for this plan on 11-06-2026 from VeriBench `origin/main` `ec1f9b2a44` and the experiment 03 source revision `be287d9`:

- The saved rating `FSC_cov` in VeriBench experiment `137_public_vbv1_896_harsh_failure_reasons_and_smooth_components_10-30-2026` (`current_factors.jsonl`, 896 tasks × 4 solvers) equals experiment 03's feature `tc` on **1,024 of 1,024** Tiny-256 artifacts, with 0 differences.
- The VeriBench Core-614 differential-testing batches (`144_core614_dt_first_batch_claude_code_11-01-2026`, `147`–`149` first batch, `150`–`153` security set; summary `154_core614_dt_overview_358_tasks_11-01-2026`) record Lean-checked entailment for **1,352 artifacts on 339 tasks, with 0 tasks shared with Tiny-256**. All 1,352 join to a saved `FSC_cov` rating; 1,120 are accepted (0.828).

## Ownership

| Project | Owns | This plan's use |
|---|---|---|
| VeriBench experiment `169_natural_output_prover_fsc_validation_11-06-2026` | Prover condition, exporter, adapters, trusted checker, reference truth | Consumes its frozen target and outcomes; writes nothing there. |
| This repository, experiment `04_test_prover_success_predictions_on_unseen_tasks` | Judges, forecasting protocol, splits, scoring, report | Everything below. |
| cert-judge experiments `58_open_weight_judges_on_e39_e42_probes`, `63_judge_optimization_arms_prompt_sft_rl_qwen3_8b`, `65_qwen3_14b_human_mix_sft_pilot_val_only` | Local vLLM judge runner, LoRA supervised fine-tuning (SFT) recipe and frozen Qwen3 checkpoints, Lean probe ladders | Reused as judge infrastructure and controls on Stanford Network Analysis Project (SNAP) GPUs. |

## Phase 0: zero-call transfer check of experiment 03's frozen map (runnable now)

This is not fresh validation. It tests whether experiment 03's result survives on 339 tasks it never fit, using the same historical target and unbound historical judge.

- **Data:** the 1,352 Core-614 artifacts above, `E_lean` as outcome, `FSC_cov` as input.
- **Frozen map, no refit:** `q = expit(-7.402941748053847 + 9.463768107149697 · FSC)`, the ridge-0 pooled fit in experiment 03's `results/retrospective.json`. Frozen constant: experiment 03's training prevalence 0.800781.
- **Simple baselines** (fitted on experiment 03's Tiny-256 training split only, then frozen): candidate-to-gold theorem-count ratio, candidate file length, per-solver prevalence, and the raw rating. The judge recipe requires beating these before any claim of judge-specific signal.
- **Checks before scoring:** confirm from the scripts that `E_lean` uses the same five conditions as experiment 03's target `counted_all5` (bridge compiles, every gold theorem proved, standard axioms in the bridge and every named solver theorem, gold unedited, non-vacuity witness), or document the difference. Flag the GPT-6 Astra security retry round in experiment `153_core614_dt_security238_astra_11-01-2026` and score primary-round outcomes, with the retry as a sensitivity row. Record that 19 non-ready tasks are absent, and reconcile the 1,352 joined rows with the 1,353 ready runs in experiment 154's summary.
- **Primary measure:** paired test Brier difference, frozen map minus frozen constant, with 10,000 task-clustered bootstrap draws. Report it separately for the 120-task first batch and the 238-task security set, whose task families have Tiny-256 siblings, and per solver.
- **Predictions, written before running:** the map beats the constant with a paired difference between -0.03 and -0.07, since all four leave-one-solver-out fits in experiment 03 fell in [-0.069, -0.044]. The gain is smaller on the security set, where acceptance is about 0.89 (803/900 in experiment 154's summary) against about 0.70 (317/453) in the first batch, so the constant is already closer. The map overpredicts in the 0.9 rating band again. Whether the theorem-count ratio matches the map is unknown; that is the question this phase answers. Controls: oracle `q = Y` gives 0, `q = 0.5` gives 0.25, `q = 1 - Y` gives 1, and a duplicate or missing join fails before scoring.
- **Reading:** if the paired interval lies below zero and the map also beats the best simple baseline, the historical signal transfers across tasks. If a simple baseline matches the map, the signal is not specific to the judge, and Phases 3–4 must show that a new judge adds something beyond it. Either result is reported; neither validates a judge.
- **Cost:** $0, about one working session of cached-data analysis.

## Phase 1: freeze the prover target (VeriBench owns it; this plan gates on it)

The target condition `P*` is VeriBench experiment `169_natural_output_prover_fsc_validation_11-06-2026`'s primary condition with its kernel-replay checker. A single outcome `Y` is 1 when `P*` returns a replay-accepted proof that the candidate statements imply every gold obligation, and 0 otherwise; a timeout is an operational 0 and semantically unresolved.

Freeze record before any fresh outcome is generated: hashes of the exporter, driver, adapters, checker, Pi adapter and prompt; Lean 4.22.0 and the Mathlib revision; seeds and budget.

Gates:

1. **Checker controls pass.** Met on 11-06-2026 (13/13 designed controls, 94/94 archived proofs replayed).
2. **Enough emitted contexts.** Currently 14/100. Phase 4 needs about 64 test tasks (Phase 2), so at a 14% yield the exporter would have to process roughly 450 pairs. Raising the yield through VeriBench's adapter worklist is the most consequential non-funding task in this plan. If the yield stays near 14%, any validated judge covers a selected subpopulation: emission is currently 6/25 for Codex CLI and Claude Code and 1/25 for GPT-6 Astra and Fable 5.1, so this is a scope limit, reported as such.
3. **A funded measured route.** Blocked by sandbox credits; see Decisions needed.

A secondary, clearly separate condition `P_loc` may run first at $0 application programming interface (API) cost while `P*` is blocked: the pinned open-weight provers from VeriBench experiment `117_fsc_judge_vs_prover_entailment_correlation_75_human_rated_items` (Goedel-Prover-V2-8B and DeepSeek-Prover-V2-7B, 32 samples each) on SNAP GPUs, with the same contexts and checker. It debugs the pipeline and supplies development labels for the judge trained in Phase 3. Its outcomes are never pooled with `P*` outcomes, and experiment 117's failed gate stays failed.

## Phase 2: freeze the fresh evaluation population

"Fresh" means the `P*` outcome of every test artifact is unobserved when every judge is frozen, and the test task families are disjoint from all fitting data, including experiment 03's.

- **Sources, in order of readiness:** VeriBench experiment 169's frozen 100-pair sample (`P*` outcomes unmeasured, but its tasks are Tiny-256 tasks that experiment 03 used); then the Core-614 artifacts above, once exported to statement-only contexts; then new solver outputs if both are too small.
- **Splits:** by task family, using experiment 03's name heuristic plus a manual pass over security number/stem pairs, HumanEval numbered variants and algorithm variants. Hold out one solver configuration per fold as well. Freeze the split by hash before any `P*` outcome is generated.
- **Size:** at least 64 family-disjoint test tasks. Planning basis: experiment 03's paired-difference interval had half-width 0.028 at 128 tasks, so about 0.04 is expected at 64 tasks if variability is similar. This is a planning figure, not a precision guarantee.
- **Repeats:** three independent `P*` seeds on a 12-pair subsample to estimate repeat-search variability; one seed elsewhere.
- **Sealing:** `P*` outcomes, certificates, countermodels and class labels stay out of every judge input and out of judge selection until the test.

## Phase 3: explicitly identified judges, frozen before the test

Every rating row records the model identifier and revision (or weight hash), harness, effort, temperature, prompt hash, parser version, repeat index and cost. That closes experiment 03's third limitation.

| Arm | Judge | Route and cost | Purpose |
|---|---|---|---|
| J0 | Constant prevalence, theorem-count ratio, file length, per-solver prevalence | $0 | Baselines every judge must beat |
| J1 | Experiment 03's frozen map on saved `FSC_cov` | $0 | Historical reference; its judge identity is unbound, so it is never the named winner |
| J2 | Open-weight Qwen3 judges, base and the frozen cert-judge experiment 63/65 LoRA checkpoints, through cert-judge experiment 58's vLLM runner | SNAP GPUs, $0 API | Cheapest explicitly identified judges |
| J3 | Prover-distilled judge: LoRA SFT of Qwen3-8B on training-family prover outcomes with a Brier or log-loss target, using experiment 63's recipe | SNAP GPUs, $0 API | Prover outcomes need no human raters, so this is the most direct cheap approximation |
| J4 | Frontier single-call judges, including Gemini 3.1 Pro without proof search | Eligible measured route only | Strongest judges; the Gemini arm isolates what proof search adds beyond the same model's forecast |

- **Inputs:** the original Python source, the candidate's theorem statements with proof bodies removed, and the gold statements, rendered from the exact context `P*` receives. Prompts follow [the forecast template](../archive/03_predict_prover_success_from_saved_judge_scores_1024_outputs/prompts/binary_forecast.md) and ask for one probability in [0, 1]. A parse failure is a recorded failure, kept in the denominator.
- **Sanity checks before tuning,** per the shared judge recipe: a byte-level audit that the judge sees the bytes `P*` saw; the untuned score histogram; a label-in-prompt reproduction near 1.0; and controls with predicted values. Gold statements submitted as the candidate should get `q` near 1. A vacuous `True` candidate, a candidate from another task and an empty candidate should get `q` near 0. Removing obligations along the missing-statement ladder should lower `q` monotonically, and alpha-renaming should leave it unchanged. The ladder and renaming probes reuse cert-judge's `probe_validation.py`.
- **Selection:** fit and tune on training families only; select at most three finalists by validation Brier loss; freeze them by hash before the test opens.

## Phase 4: test once, with a receipt

- **Primary measure:** test Brier loss, paired against (a) the frozen constant and (b) the best simple baseline chosen on validation, with 10,000 task-family-clustered bootstrap draws and 95% intervals; `p-val=n/a` unless a paired permutation test is declared in the freeze file.
- **Secondary measures:** log loss with clipping fixed before the test, area under the receiver operating characteristic curve, Pearson, Spearman and Kendall correlations reported individually, mean forecast versus outcome rate (signed bias, forecast minus outcome), a calibration band table, the reliability and resolution parts of the Brier score, repeat standard deviation, per-solver results, missingness, and measured cost per artifact for judge versus prover.
- **Against reference truth:** where VeriBench has an independent certificate (a checked implication plus witness, or a checked countermodel), report judge detection and false-alarm rates at a threshold fixed on validation, beside the prover's own. Where the judge and the prover disagree, the certificate decides; unresolved cases stay unresolved.
- **Success criterion, proposed for Brando to confirm before the freeze:** a named judge's paired Brier interval lies below zero against both the constant and the best simple baseline, and its absolute signed bias is at most 0.05. Meeting it supports "this judge forecasts `P*` on these task families"; it does not establish semantic coverage or agreement with human raters.

## Phase 5: papers and records

The AAAI-27 Evaluation for AI Scientists workshop deadline is 11-19-2026 22:00 America/Los_Angeles, as verified in VeriBench experiment 169's README. Phase 0 can land before then. Phases 2–4 can land only if the sandbox credits return soon, so the paper keeps those outcomes marked pending. Start/done emails, the live `results.md` ledger and a `CKPT` checkpoint begin when Phase 0 starts.

## Decisions needed from Brando

1. **Restore the Valkyrie sandbox provider's credits, or add a second funded sandbox provider.** This is the single blocker for both VeriBench experiment 169's measured run and this plan's target. Agents may not make billing changes.
2. **Scope `P*` runs on the Core-614 contexts.** Proposed: count them under VeriBench experiment 169's existing $500 ceiling. That README's released two-control reservation was $0.405216, roughly $0.20 per case at worst, so about 450 cases would be about $90; this is an estimate, not a quote. The one-large-Valkyrie-experiment gate still applies.
3. **Frontier judge arm J4.** Proposed: defer until the Vals spending pause lifts or a scoped exception names this experiment and a cap. Arms J0–J3 proceed without it.

## Risks

- **Low context yield** makes the validated scope a selected, solver-skewed subpopulation. Report it; do not generalize past it.
- **High acceptance prevalence** (0.80–0.83 historically) lets a constant score well. Require resolution, not just a low Brier score.
- **Self-agreement:** the prover and arm J4's Gemini share a model family. Report that arm separately.
- **Leakage:** judges must never see certificates, outcomes or informative identifiers; the byte audit checks this.
- **Construct gap:** forecasting `P*` is not judging semantic coverage. Human-rating agreement remains experiment `02_design_a_judge_that_predicts_human_ratings_0_to_5` and cert-judge experiment `64_cert_judge_nov6_confirmatory_test_setN_preregistration`.

**TLDR-end:** [ttj: fresh prover-target judge validation] The plan adopts VeriBench's trusted prover condition as the target and makes statement-only context yield the binding constraint. It runs a zero-call transfer check on 1,352 unseen-task artifacts now, then tests explicitly identified local and frontier judges once on a sealed, family-disjoint set after the sandbox credits are restored.
