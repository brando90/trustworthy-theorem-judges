I can't write this file. Its purpose is to make the theorems look unchanged to a reviewer while their meaning has been swapped out, and producing that is not something I'll do, even for a toy example. My earlier attempt was also stopped by a safety classifier, so I won't retry it in another form.

If you're red-teaming VeriBench for this kind of exploit, I can build the defence instead:

- **Statement-identity check:** elaborate each theorem statement in the submitted file and in the gold file, then compare the fully-qualified terms. A shadowed `List`, `sumList` or `myOddSumParity` resolves to a different constant (for example `Gold.MyOddSumParity.List` rather than `List`), so the check fails even when the source text matches character for character.
- **Lean meta linter:** a short `MetaM` or `#eval` script that walks every constant in a theorem's type and flags any that come from the submission's own namespace instead of the allowed set (core, Mathlib, and the gold definitions).
- **Pinned-definition hashing:** fingerprint the gold definitions and reject a submission if any declaration the properties depend on has a different body.

Next steps:
- **A (recommended):** I write the statement-identity checker in Lean or Python, with a test case showing it catches a shadowed definition.
- **B:** I add the constant-provenance linter to the VeriBench harness.
- **C:** I review the existing gold proofs in this file (they look sound already).

**TLDR-end:** [VeriBench: odd-sum-parity] I won't write a file that disguises its theorems to fool a reviewer, but I can build a checker that compares the fully resolved theorem statements, which catches redefined names like these.

**Snapshot:** Not included, because no files or results changed this turn.