# Judge whether candidate statements imply the reference: 48 constructed Lean cases

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/08_judge_whether_candidate_statements_imply_reference_48_lean_cases/README.md>

This pilot forecasts the semantic implication `forall f, AgentMaster f -> GoldMaster f`, conditional on a satisfiable candidate specification. The [live results](results.md) distinguish implementation, measured forecasts, and review status.

The 48 prespecified controls span six task/representation families, split into two training, two validation, and two test families. Eighteen positive labels have both a kernel-checked implication and a separately checked satisfiability witness. Eighteen negative labels have checked countermodels. Six jointly inconsistent candidates and six unsupported-axiom declarations remain ineligible with an abstention target. These labels establish a controlled feasibility set, not independent validation on natural model outputs.

The [completed results](RESULTS_master_entailment.md) show raw Brier loss 0 on 12 eligible held-out controls, versus 0.25 for the constant. The model abstained on 3/4 ineligible held-out controls and missed one required abstention. These simple constructed examples support feasibility only; every returned probability was an endpoint.

The model sees only the statements in [inputs.jsonl](inputs.jsonl), through the fixed [judge prompt](prompts/judge.md). It receives no labels, certificates, truth-bearing case names, supplied proof bodies, or proof-success status. The proof-body controls produce identical statement inputs. Their forecast differences measure duplicate-input variation, not robustness to visible proof bodies. Separate adversarial checker tests cover forged audit strings, wrong goals, forbidden transitive axioms, and placeholders.

The domain consists of abstract Lean functions over a single shared function slot `f : Domain → Codomain` (`AgentMaster` and `GoldMaster` predicate that same `f`). Candidate-private helper abstractions/definitions, quantification over auxiliary helper symbols, and imperative-program equivalence are outside this condition and are not silently added to the master theorem. Overly strong preconditions (`overly_strong_precondition`) are semantic negatives with checked counterexamples, while jointly inconsistent candidates (`joint_inconsistency`) and unsupported axioms remain ineligible with an abstention target. A failed bounded search never supplies a negative semantic label. The prior [experiment05](../archive/05_test_qwen_3_5_9b_prover_success_predictions_4_tasks_8_outputs/README.md) remains separate: its three valid generated outputs all had unsuccessful bounded searches and did not validate a judge. Fresh human returns were not checked against cloud sources in this run; their existence is not determined here.

[VeriBench experiment169](https://github.com/brando90/veribench/tree/ec1f9b2a4455549ba98a4fdf94c9d30bf3a0522d/experiments/169_natural_output_prover_fsc_validation_11-06-2026) is restricted provenance in a private repository. Experiment171's ongoing imperative-equivalence and soundness work is separately owned, as stated in the runbook. Its exact directory/revision was unavailable in the inspected remote main/branch trees and local checkout metadata; the parent handoff requests that link from its owner. No absence of work or results is inferred.

The selected model is the cached `Qwen/Qwen3.6-27B`, revision `6a9e13bd6fc8f0983b9b99948120bc37f49c13e9`, using unquantized bfloat16 on one NVIDIA B200. The [route selection](MODEL_SELECTION.md) explains alternatives, the explicit serving-version limitation, and why this is a feasible free route rather than an established best judge. [Model identity](model_identity.json) pins weights, tokenizer, template, and serving configuration. Provider charges are $0.

- [Forecast procedure and predictions](forecast_protocol.json): budgets, failure accounting, fitting, validation selection, and test analysis fixed before inference.
- [Certificate procedure](CERTIFICATE_PROTOCOL.md) and [certificate report](CERTIFICATE_REPORT.md): trust boundary, exact-goal checking, Lean pins, and all constructed labels.
- [Inference freeze](inference_freeze.json): hashes of inputs, labels, code, prompt, model, and certificate receipts.
- [Forecast checkpoint](CKPT_forecasts.md) and [certificate checkpoint](CKPT_certificates.md): resumable state and event logs.

Each manifest row receives at most one primary call, with 2,048 generated tokens and 120 seconds. One explicit preflight, a fixed-constant JSON echo (probability 0.375) that checks transport and output format rather than reproducing a per-item label, and at most two transport diagnostics are allowed separately. Training and validation calls finish before the mapping selection receipt is written; test calls begin afterward. Raw forecasts, a training-prevalence constant, and cross-entropy/Brier-fitted mappings use common Brier loss, log loss, ordering, absolute error, and bias. Failed or abstained eligible forecasts retain an explicit 0.5 fallback in the full denominator, with failure counts and common-valid analyses also reported.

Only two test families support the held-out analysis. Family-bootstrap intervals are descriptive and cannot establish broad generalization. No human-rated judge agreement, natural-output validation, frontier-model comparison, or provider-level capability conclusion follows.

## Reproduce without new inference

From the repository root:

```sh
python3 scripts/check_project.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 experiments/08_judge_whether_candidate_statements_imply_reference_48_lean_cases/scripts/test_forecasts.py
python3 experiments/08_judge_whether_candidate_statements_imply_reference_48_lean_cases/scripts/test_outcome_checker.py
python3 experiments/08_judge_whether_candidate_statements_imply_reference_48_lean_cases/scripts/verify_controls.py --verify-existing --output /tmp/ttj08-certificate-replay.json
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 timeout 1800 python3 experiments/08_judge_whether_candidate_statements_imply_reference_48_lean_cases/scripts/analyze_forecasts.py evaluate --output /tmp/ttj08-analysis-replay.json
python3 experiments/08_judge_whether_candidate_statements_imply_reference_48_lean_cases/scripts/verify_forecasts.py --output /tmp/ttj08-forecast-verification.json
git diff --check
```

The pinned Lean 4.22.0 executable must be installed; `--lean /path/to/lean` selects it for certificate replay. The analysis requires NumPy 2.2.6 and SciPy 1.17.1. Replay recompiles the saved certificate source and writes its receipt outside the experiment. It does not overwrite certificates, labels, or the original run. Analysis replay reads committed sanitized forecast rows and never calls a model. Raw requests/responses and detailed serving logs remain in the runtime artifact store identified in the handoff.

The parent owns the requested multi-provider review and publication to main. This experiment stays in its canonical location while that review and the next natural-output study remain live dependencies.

## Review note (11-08-2026, stages 01–02 review)

`scripts/certificate_checker.py` returns `accepted: true` for an empty proof mapping when the statement alone compiles, because zero audit records satisfy its acceptance predicate. No label used that path: `verify_controls.py` never calls the checker for the six unsupported-axiom cases, and every one of the other 42 rows in `labels.json` records at least one exact required target (60 audits in total). The checker and its receipts are pinned by `inference_freeze.json` and `results/certificate_validation.json`, so the frozen checker, protocol, and measured hashes remain untouched. For prospective outcome-level checking, `scripts/outcome_checker.py` (`OutcomeCertificateChecker`, tested in `scripts/test_outcome_checker.py`) wraps `CertificateChecker` to reject empty, missing, or mismatched proof-target sets and require `{'Coverage', 'Nonvacuous'}` for positives, `{'Counterexample'}` for negatives, and `{'Inconsistent'}` for inconsistency while keeping unsupported cases ineligible. As `CERTIFICATE_PROTOCOL.md` states, replay runs in the same Lean process with a recompiled support module, and the checker is not a containment boundary for hostile Lean code.
