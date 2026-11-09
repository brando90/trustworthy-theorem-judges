# Experiment 08: certificate-labeled master-specification entailment

The target is semantic entailment of the gold master specification by the candidate master specification, conditional on the candidate master specification being satisfiable.
For each pure total-function interface, define

```lean
Coverage       := ∀ f, AgentMaster f → GoldMaster f
Nonvacuous     := ∃ f, AgentMaster f
Counterexample := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
Inconsistent   := ¬ Nonvacuous
```

A positive label requires kernel-checked proofs of both `Coverage` and `Nonvacuous`.
A negative label requires a kernel-checked proof of `Counterexample`; its witness also establishes satisfiability.
A timeout or rejected proof is unresolved, never a semantic negative.
A checked `Inconsistent` candidate is ineligible for the conditional target, even though an implication from an inconsistent assumption is logically true.
Additional statement-level axioms are outside the source grammar and ineligible.
No supplied proof success enters the label or judge input.

## Prespecified construction and predictions

The full construction is the deterministic output of [build_controls.py](scripts/build_controls.py).
[construction_manifest.json](construction_manifest.json) contains the expected outcomes and certificate terms; [inputs.jsonl](inputs.jsonl) contains only opaque IDs and statement declarations.
The expected outcomes were recorded before certificate compilation.
Source precedence and proof-term layout errors caught during construction checks were fixed before forecasts; their development receipts were retained outside the repository.
No model output was available during construction or certificate repairs.

| Task family | Split | Interface | Controls |
|---|---|---|---:|
| Boolean negation | Training | `Bool → Bool` | 8 |
| Natural successor | Training | `Nat → Nat` | 8 |
| Integer negation | Validation | `Int → Int` | 8 |
| List length | Validation | `List Nat → Nat` | 8 |
| Boolean pair swap | Test | `(Bool × Bool) → (Bool × Bool)` | 8 |
| Optional default | Test | `Option Nat → Nat` | 8 |

Each family has three expected positives (oracle, equivalent reformulation, proof-body variant), three expected negatives (weakening, overly strong input precondition, wrong goal), one joint inconsistency and one unsupported statement-level axiom.
An overly strong input precondition weakens the candidate's guarantee by restricting which inputs it constrains; it does not mean a stronger logical antecedent `AgentMaster`.
All cases within a family stay in the same split.
Control patterns recur across splits, so family-held-out results are not a test of unseen logical perturbation patterns.

The proof-body variant changes the supplied proof body and includes forged audit text, while its forecast statement is byte-identical to its oracle twin.
Only the `statement` value goes into the prompt; opaque IDs, certificates, proof bodies, labels, control names and family/split names are absent.
The separately tested forged-audit attack does not count as independent natural-output validation.
Duplicate oracle/variant prompts are retained to measure observed single-run invariance; they are correlated observations within one family.

## Checker and trusted components

The toolchain is `leanprover/lean4:v4.22.0`, commit `ba2cbbf09d4978f416e0ebd1fceeebc2c4138c05`.
The [validation receipt](results/certificate_validation.json) pins the Lean executable, shared library, checker source, trusted Lean support source, compiled support module and relevant Lean environment/axiom-traversal sources by SHA-256.
The trusted [CertificateAudit.lean](lean/CertificateAudit.lean) command reads the kernel-checked environment, verifies definitional equality with the exact expected goal, replays the theorem value with kernel checking enabled, and traverses all transitive axioms.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted; `sorryAx`, user axioms and native-decision axioms are not permitted.
A generated nonce binds parsed audit records to one checker invocation.
A lexical guard is additional input hygiene; kernel checks establish acceptance.

Proof strings are parsed as exactly one Lean term inside a trusted theorem declaration.
No untrusted compiled module is imported.
The source grammar, generator, checker, Lean distribution and standard library are trusted components.
This is a controlled feasibility checker, not a security sandbox for arbitrary malicious Lean plugins or native code.
The raw-source test hook is used only by deterministic adversarial tests; forecasts are probabilities and never become executable Lean code.

Each compiler call uses one CPU thread, at most 30 seconds and a fixed heartbeat bound; one full verification is capped at 30 minutes.
No model, GPU, provider key, human rating, private candidate artifact or sealed data is used to construct labels.

## Scope and limitations

These six families are new controlled total-function statements, not natural candidate outputs and not sampled benchmark tasks.
The same author constructed statements and proof certificates; kernel checking validates the finite labels but does not make the sample representative.
The pilot has only two families per split and one planned forecast per case.
Counts of checked finite cases have no sampling confidence interval; inferential p-values are not applicable.
Forecast uncertainty and missingness are reported separately by the inference analysis.

Imperative equivalence is explicitly outside this condition.
There is no Python or stateful implementation whose behavior must be related to a pure Lean function, and no independent imperative-equivalence obligation is silently added to `Coverage`.
Any later imperative application needs its own checked abstraction/equivalence relation and an explicitly revised master specification.
[VeriBench experiment169](https://github.com/brando90/veribench/tree/ec1f9b2a4455549ba98a4fdf94c9d30bf3a0522d/experiments/169_natural_output_prover_fsc_validation_11-06-2026) and experiment171 concern separate natural-output proof and soundness work; this experiment neither changes their references nor claims their pending results.
Fresh human returns were not verified from cloud in this worker and are not asserted absent.
The three valid generated outputs in experiment05, all unsuccessful bounded searches, are not this study's validation set and do not establish a good judge.

## Reproduction without new inference

From this experiment directory, replay all saved certificate files without changing their bytes or labels:

```bash
python3 scripts/verify_controls.py --verify-existing --output /tmp/ttj08-certificate-replay.json
TTJ07_CHECKER_TEST_OUTPUT=/tmp/ttj08-checker-tests.json python3 scripts/test_certificates.py
```

The replay compares runtime pins, construction bytes and the saved nonces before compilation, then compares regenerated labels with the saved manifest.
It does not regenerate certificates or rewrite forecast inputs.
After `inference_freeze.json` exists, construction and ordinary label regeneration refuse to run.
The tests write their receipt outside the experiment after inference is frozen.
Before the first inference freeze only, construction was run with `python3 scripts/build_controls.py` followed by `python3 scripts/verify_controls.py`.
