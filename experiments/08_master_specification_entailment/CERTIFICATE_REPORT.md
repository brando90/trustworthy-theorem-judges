# Experiment 08 certificate results

All 48 prespecified construction outcomes were verified in `08_master_specification_entailment` before forecasting: 18 entailment positives, 18 countermodel negatives, six jointly inconsistent candidates and six unsupported axiom declarations.
The 42 supported constructions produced 60 exact-goal, kernel-replayed theorem audits; none failed in the finalized construction.
This establishes the labels of a controlled feasibility set, not the validity of a model judge on natural outputs.

| Outcome | Training | Validation | Test | Total |
|---|---:|---:|---:|---:|
| Entailment + satisfiability | 6 | 6 | 6 | 18 |
| Countermodel | 6 | 6 | 6 | 18 |
| Inconsistent, ineligible | 2 | 2 | 2 | 6 |
| Additional axiom, unsupported | 2 | 2 | 2 | 6 |
| All declared controls | 16 | 16 | 16 | 48 |

Every split has two distinct task families, with all eight variants of a task kept together.
Each oracle and proof-body variant has the same forecast statement bytes; those repetitions are not independent tasks.
The counts describe this finite constructed set exactly: no sampling interval is needed, and p-val=n/a.
No human rating, sealed data, model inference or provider spending was used for certificate construction.

Nine deterministic tests passed: two construction/split checks and seven checker checks.
The checker rejected a proof of the wrong exact goal, a transitive user axiom, `sorryAx`, forged audit text and command injection.
A valid exact-goal theorem was accepted and rechecked by the kernel.
The separate lexical rejection test does not replace those kernel tests.
See [checker receipts](results/checker_tests.json), [all certificate receipts](results/certificate_validation.json), [labels](labels.json) and [procedure and limits](CERTIFICATE_PROTOCOL.md).

The initial development compilation rejected 19 of the 42 supported constructions because of Boolean-expression precedence or proof-term formatting.
These were construction errors, corrected before any forecast, and were not treated as negative semantic labels.
The original development manifest, inputs, labels, certificate files and rejection receipt remain at `/lfs/skampere3/0/brando9/judge-overnight-1108/certificate_development_01/`.
The finalized certificate verification took 28.084 seconds on one CPU thread per compiler call; every call had a 30-second limit.
A subsequent immutable replay accepted the same saved certificates and reproduced the label manifest, writing its new receipt outside the experiment at `/lfs/skampere3/0/brando9/judge-overnight-1108/certificate_replay.json`.

The selected toolchain is `leanprover/lean4:v4.22.0`, commit `ba2cbbf09d4978f416e0ebd1fceeebc2c4138c05`.
Its executable and shared-library hashes, trusted source hashes and source-by-source audit details are in the validation receipt.
The statement input SHA-256 is `fc4c8cde3ce5968df37b51a24d67e70149c85c279d2b9f042a96c4a92eba04ad`.
The construction manifest SHA-256 is `d4eeb24d609d69b8eb8e6af315ca42f7d82ee4504ec7464681acf65888f203c3`.

Imperative equivalence, representative natural-output validation and human agreement remain outside this condition.
The checker is not a sandbox for arbitrary hostile Lean plugins.
Final forecast findings and model identity belong in the separate inference report; no forecast performance is inferred from passing these certificate controls.
