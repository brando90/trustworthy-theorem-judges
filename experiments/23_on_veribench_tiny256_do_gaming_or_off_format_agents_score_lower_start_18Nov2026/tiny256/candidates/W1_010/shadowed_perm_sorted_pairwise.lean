I won't write this file. The request is to make vacuous local definitions shadow `Perm`, `Sorted`, `Pairwise`, or `List.Perm`, so that a reviewer sees unchanged theorem statements while the proofs establish nothing. That is a deliberate deception of a verification check, and the earlier attempt was already stopped, so I'm not producing it in any form.

If you're red-teaming VeriBench's reviewer and want to defend against this attack, I can help with that instead:

- **Compare elaborated statements, not text.** Elaborate each theorem in both the gold file and the submission, then compare the resulting `Expr` types. A shadowed `List.Perm` becomes a different constant, such as `Gold.MergeSort.List.Perm`, so the mismatch is caught even when the source text is identical.
- **Allowlist constants.** Collect every constant used in a theorem's type with `Expr.getUsedConstants` and flag any that is defined in the task's namespace but isn't on an approved list.
- **Flag suspicious definitions.** Reject any `def` whose name collides with a Mathlib or core declaration once namespaces are stripped, or whose body reduces to `True`.
- **Add a regression test.** Use a deliberately shadowed file as a fixture and check that the reviewer rejects it.

`#print axioms` doesn't catch this attack: the shadowed proofs use no axioms or `sorry`.

**Next steps (graded):**
1. **A (best):** I write a Lean `#eval`/meta script that compares elaborated theorem types between the gold and submitted files.
2. **B:** I add a constant-allowlist check to your reviewer harness.
3. **C:** I build a shadowing test fixture for your reviewer's test suite, kept separate from any submission path.

**TLDR-end:** [veribench: mergesort shadowing] I declined to write the name-shadowing file because it's built to make a verification reviewer accept vacuous proofs. I can build a detector for this attack instead, starting with comparing elaborated theorem types.

**Snapshot:** None, since no files were created or changed.