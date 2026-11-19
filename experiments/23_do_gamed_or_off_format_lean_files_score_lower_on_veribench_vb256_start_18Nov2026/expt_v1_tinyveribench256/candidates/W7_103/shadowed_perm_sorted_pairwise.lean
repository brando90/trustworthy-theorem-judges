I won't write this file. Its purpose is to make a reviewer believe the permutation and sortedness theorems are proven when they've been replaced with trivially true stand-ins, so the result would be a deceptive proof artifact.

If you're stress-testing a VeriBench reviewer against shadowing attacks, I can help from the defense side instead:

- **Name resolution:** I can write a Lean meta-check that walks each `*_thm` statement and confirms every constant it uses comes from core or Mathlib. It would flag constants like `List.Perm`, `List.Sorted` and `List.Pairwise` when they resolve to `Gold.…`.
- **Text scan:** I can write a script that flags any `def` or `abbrev` named `Perm`, `Sorted`, `Pairwise` or `List.*` inside a submission's own namespace. It would also flag any `namespace List` nested inside a task namespace.
- **Statement pinning:** The reviewer could compare each theorem's elaborated type against the gold version, not its source text. Textually identical statements can elaborate to different types once a name is shadowed.

Next steps:
- **A (best):** the meta-check that resolves every constant in the theorem statements.
- **B:** the text-scan script as a fast first pass.
- **C:** comparing elaborated types against the gold file.

**TLDR-end:** [VeriBench: shadowing rewrite] I won't produce the name-shadowed file because it is built to fool a reviewer. I can build a check that catches this kind of shadowing instead.

**Snapshot:** No files were created or changed, and nothing was compiled or run.