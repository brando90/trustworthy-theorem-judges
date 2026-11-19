I won't write this one. A file that shadows familiar names so the theorems look unchanged but prove something trivial is built to mislead whoever reviews or scores it. That holds even if the target is an automated reviewer or a benchmark like VeriBench.

If you're stress-testing a reviewer or grader, I can help with that from the detection side:

- **Shadowing detector:** a Lean metaprogram or Python script that flags any declaration inside `namespace Gold` whose short name matches something in core or Mathlib (`List`, `Perm`, `Sorted`, `length`, `computeDnssecSignature`, and so on). It would also compare each theorem's fully elaborated type against a reference, so text that matches but elaborates differently gets caught.
- **Statement pinning:** the grader elaborates each reference theorem statement in a clean environment, then checks the submitted proof against that pinned type with `#check (thm : <pinned type>)`. Matching the text alone wouldn't pass.
- **Axiom and `native_decide` audit:** run `#print axioms` on every theorem and reject `sorryAx` and unexpected axioms. `Lean.ofReduceBool` from `native_decide` should get its own policy.

The current gold file also has real weaknesses a reviewer should catch:

- `trusted_key_binding_prop` only says equal keys give equal signatures, which `rw` proves. It says nothing about security.
- `main_correctness_thm` never uses `hPre`, so the precondition plays no part in the proof.
- `spoofing_prevented_prop` assumes `attackerIp ≠ legitimateIp`, but the proof never uses that hypothesis.

**Next steps:**
1. **(Recommended)** I write the shadowing detector plus the statement-pinning check, as a Lean or Python script.
2. **(Useful)** I strengthen the gold properties so they're no longer trivially true: a real binding property and a precondition the proofs actually use.
3. **(Optional)** I add a short note to your benchmark docs on these grader holes.

**TLDR-end:** [VeriBench: reviewer-gaming request] I won't write a Lean file that shadows names to make the proofs trivial, but I can build checks that catch that trick and tighten the weak properties already in the gold file.

**Snapshot:** None; I didn't run any tools or change any files.