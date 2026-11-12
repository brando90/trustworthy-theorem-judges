# Retrospective practical-judge checkpoint

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/10_retrospective_rps_vs_pearson_mixture/CKPT_practical_judge.md>

**TLDR:** Complete the missing original-split RPS-versus-Pearson probability-mixture comparison using existing historical data. The sole coordinator remains Prepare human grading task; this is its bounded offline worker.

## State

- Updated: 11-10-2026.
- Owner: sole coordinator chat `01a1a8f9-dcb7-7381-9368-91d6e51faffd`; delegated worker `/root/finish_practical_judge` completed and handed back its results.
- Effective access: inherited danger-full-access and approval never; local source reads and detached checkout creation succeeded.
- Status: fitted, independently checked, reported and published; canonical result commit `a03109f68564424c4c9561567a044421181dc521`.
- Folder: `experiments/10_retrospective_rps_vs_pearson_mixture/`.
- Owned computation checkout: removed after verified publication; canonical deliverables are preserved.
- Data: canonical private sister-repository experiment-03 historical cache, SHA-256 in protocol.json.
- Protected scope: inherited set-N collection unopened; no participant email or paid inference.
- Interpreter: `/Users/brandomiranda/uv_envs/no-gold-ref-judge/bin/python3`.
- Next study: new human data; no additional inference or test-driven selection in this experiment.
- Publication eligibility: retrospective comparison only; validation selected a candidate, but no deployment threshold was declared or passed.
- Result: method-4 minus method-2 RPS +0.005241, 95% interval [−0.068074,+0.014864], 1,998/2,000 valid draws; no resolved advantage.
- Validation selected method4_rps; saved parameters and eligibility receipt are under results/.
- Private forecasts/logs: canonical private/10_retrospective_rps_vs_pearson_mixture/.
- Companion: https://docs.google.com/document/d/1zB-gYk-zU1wToS_E_carGSRGtUcF1NgZ-jWF5t1SJws/edit
- Parent owns communication, collection and final user-facing knowledge synchronization.

## Event log

- 11-09-2026: inherited the published handoff, checked the completed sister comparison, reserved this missing RPS condition and created the owned detached checkout from `b3ce98e`.

- 11-09-2026: published premeasurement definition d34052e; completed one-CPU run in 31.841 seconds, 2,000 requested bootstrap draws, no numerical-certificate failures and two empty-validation draws.
- 11-09-2026: independently checked losses/forecasts and paired intervals; recorded scalar-versus-BLAS rank tie sensitivity without changing frozen measurements. Export replay matched all 75 forecasts exactly; 1,478 source hashes verified.
- 11-09-2026: saved results.md and results/ELIGIBILITY.json; result is retrospective only. Coordinator owns the Google companion and completion notice.
- 11-10-2026: received the VeriBench paper coordinator's request; rechecked the published definition, selection rule, results and eight evidence hashes. Confirmed the result/claim boundary below without new fitting, inference, rating inspection or teammate email.

## Paper coordination confirmation — 11-10-2026

The canonical result is [commit a03109f68564424c4c9561567a044421181dc521](https://github.com/brando90/trustworthy-theorem-judges/commit/a03109f68564424c4c9561567a044421181dc521), following the premeasurement definition in `d34052eb0ab4272b33dda28f2f8f6cc6cb014c53`.
The evidence packet is [results.md](https://github.com/brando90/trustworthy-theorem-judges/blob/a03109f68564424c4c9561567a044421181dc521/experiments/10_retrospective_rps_vs_pearson_mixture/results.md), [eligibility and provenance](https://github.com/brando90/trustworthy-theorem-judges/blob/a03109f68564424c4c9561567a044421181dc521/experiments/10_retrospective_rps_vs_pearson_mixture/results/ELIGIBILITY.json), [numerical results](results/results.json), [saved candidates](results/selected_models.json) and [prespecified procedure](PROTOCOL.md).
The source dataset SHA-256 is `b3a05699a26d3ffd9f28e793178811219885df78319b3aa57f9d393c68724ba0`; the numerical results SHA-256 is `da877e5e1c22a8f4d40d2163589baa0aab78ad8286c8e17376cdb5125a95b83a`.

**Supported public claim:** within a fixed five-configuration mixture of cached historical judge ratings, matched Pearson and normalized ranked probability score (RPS) training yielded an unresolved test-RPS comparison.
The paired difference, RPS training minus Pearson training, is +0.005241 [−0.068074, +0.014864], p-val=n/a.
The 95% percentile interval uses 1,998 valid joint task-family refit/reselection bootstrap draws out of 2,000.
The historical test partition contains 30 artifacts, 10 tasks, nine families and 78 observed ratings.
Across all partitions, 195 of 225 human-rating slots are observed; missing ratings are not zeros.
No new model calls, Lean proofs or differential testing were performed by this comparison.

| Decision | Prespecified rule and observed outcome | Interpretation |
|---|---|---|
| Candidate selection | Minimum equal-artifact validation RPS over the declared candidates. RPS-trained mixture: 0.073344; Pearson-trained mixture: 0.081657; other controls: 0.104414, 0.105185 and 0.166833. | `method4_rps` is the selected candidate; selection is complete. These validation values are selection criteria, not independent evidence of generalization. |
| Comparative superiority | Primary contrast is method 4 minus method 2 test RPS. The reported 95% interval includes zero; no practical superiority margin was declared. | No resolved advantage; neither equivalence nor superiority is established. The candidate was not switched after inspecting test results. |
| Practical deployment validation | `protocol.json` has `deployment_threshold: null`. The prospective experiment-02 acceptance margins and several analysis definitions are also unresolved. | No deployment acceptance decision can be claimed. Selection is not validation. |

The test outcomes had prior exposure, task families cross partitions and the same expert identities recur.
The bootstrap holds historical prompt/model selection, rater identities and cached judge repetitions fixed.
The result is therefore eligible as an explicitly labeled retrospective comparison in either paper, with these qualifications visible.
It does not validate a semantic judge on current solver outputs or justify replacing either paper's prover-based formal specification coverage (FSC).
Both papers retain prover-based FSC with no large language model (LLM) rating fallback, per the [paired-paper handoff](https://github.com/brando90/veribench/blob/24bce07d14f560a65b0b3167c5b1137c1daf0cee/paper_support/public_v1_dt_11-06-2026/PUBLIC_DT_JUDGE_SYNC_11-09-2026.md).
Private benchmark results and the photographed without-differential-testing baseline are outside this change and remain unchanged.

**Pending evidence for a stronger claim:**

1. Fix the target population, separate permitted training/validation data from evaluation data, and document task-family, solver and rater identities and prior exposure. The prospective strict three-axis design still needs its documented amendment; the inherited set-N collection remains evaluation-only for that new condition.
2. Finalize practical acceptance margins, missingness treatment, repeat count, uncertainty procedure and baseline comparisons before examining the designated test outcomes. The existing experiment-02 configuration leaves these fields unresolved; this checkpoint supplies no retrospective thresholds.
3. Bind the deployed semantic judge's exact model, effort, harness, prompt, parser and proof visibility to matching human inputs. Verify label reproduction and meaningful positive/negative controls for that condition; synthetic mixture checks do not satisfy this requirement.
4. Collect the independent human ratings needed for the intended solver population, select on validation, fix the candidate, and evaluate once with full denominators, paired uncertainty, absolute agreement and repeat variability. Evidence for unseen raters or solver configurations requires their corresponding evaluation design.

This confirmation requests no additional experiment and grants no new funding or send authorization.
The user instructed that all teammate emails remain prepared and unsent while reviewing the previews.
The existing [Google methodology companion](https://docs.google.com/document/d/1zB-gYk-zU1wToS_E_carGSRGtUcF1NgZ-jWF5t1SJws/edit) already records the result and its retrospective limitations; no new numerical result is introduced here.
