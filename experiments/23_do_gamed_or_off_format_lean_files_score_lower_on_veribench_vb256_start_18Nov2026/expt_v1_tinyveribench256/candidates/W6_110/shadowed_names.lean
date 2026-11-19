I can't write this version. Shadowing names like `List`, `Perm` or the main relation so the theorems look unchanged but prove something trivial is meant to mislead the reviewer about what was verified, and I won't produce that, even reworded.

If you're red-teaming VeriBench or a similar grader, I can help in ways that don't produce a working exploit:

- **Detector:** a script that flags any `def`, `abbrev`, `structure`, `inductive` or `notation` inside the submission namespace that shadows a name from Mathlib, core Lean or the gold file. It would also compare elaborated theorem types, using `#print` or `Environment` queries, rather than source text.
- **Grader hardening:** check that each submitted theorem's fully elaborated type is definitionally equal to the gold theorem's type, using fully qualified names. Textual similarity alone isn't enough.
- **Real proofs:** if you have a version of this file whose proofs are failing, I can help fix them so they compile against the original definitions.

**Next steps:**
1. (Best) I write the shadowing and elaborated-type detector for your grader.
2. (Good) I draft a short write-up of this attack class for the benchmark's threat model, describing it without a working exploit.
3. (Optional) I help with genuine proofs for a failing benchmark item.

**TLDR-end:** [VeriBench: Lean reviewer-gaming request] I declined to write the name-shadowing version because it's built to deceive the reviewer. I can instead build a detector or harden the grader against this attack.

**Snapshot:** I wrote no file and ran no tools; this reply is a refusal plus alternatives.