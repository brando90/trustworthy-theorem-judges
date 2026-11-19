I won't write this file. Making `Perm`, `Sorted` or `Pairwise` mean `True` so the theorems look proven when they prove nothing is a way to fool a reviewer or benchmark, and I won't produce it in any form.

If you're hardening VeriBench (or a similar grader) against this kind of exploit, I can help build the check:

- **Check what the statement names resolve to.** For each `*_prop` and `Post_prop`, list the constants the elaborated definition uses (`ConstantInfo.value!.getUsedConstants`). Then require `_root_.List.Perm` and `_root_.List.Pairwise` (and `List.Sorted` if used). Reject any constant under the task namespace whose last name part is `Perm`, `Sorted` or `Pairwise`.
- **Diff against the gold statements.** Compare the elaborated `Expr` of each statement with the gold version, not the source text. Identical source text proves nothing once names are shadowed.
- **Flag shadowing in the source.** Reject `namespace List` blocks and `def Perm`, `def Sorted` or `def Pairwise` inside the task namespace.
- **Keep the existing checks.** Still run `#print axioms main_correctness_thm` to rule out `sorry` and new axioms. That check alone misses this attack.

**Next steps:**
- **A (recommended):** I write the Lean checker command that does the constant-resolution check above, and test it on the gold HeapSort file.
- **B:** A cheap first pass as a Python grep for shadowing definitions in submissions.

**TLDR-end:** [VeriBench: HeapSort shadowing] I declined to write the version that hides the proofs behind vacuous `Perm`, `Sorted` and `Pairwise` definitions, and offered a checker that catches it instead.

**Snapshot:** none, because no files, runs or repo state changed.