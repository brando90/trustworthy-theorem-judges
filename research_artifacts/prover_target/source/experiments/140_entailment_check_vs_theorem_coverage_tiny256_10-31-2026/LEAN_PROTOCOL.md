# Lean check of an entailment verdict (one run)

You get one run: an AGENT Lean file (a solver agent's implementation and its own theorem statements) and the GOLD Lean file (the reference implementation and its public theorems). Two readers (ub9sc and Gemini) disagreed on whether the agent's stated specification entails the gold's. Your job is to settle it in Lean, not by reading: compile files and report what the compiler says.

Meaning of "entails" (same as PROTOCOL.md in this folder; read it first): for an ARBITRARY function f_A that satisfies only the statements of the agent's theorems (its master spec M_A, nothing else about f_A, not its definition, not the agent's proofs), every public gold theorem (the master spec M_G), translated through a natural interface adapter (Nat/Int, Option/Except, names, extra fuel), must follow. Each gold theorem is judged with its own hypotheses only (an extra bound the agent needs and the gold theorem lacks is a gap).

## What to build (one Lean file per run, `Entail.lean`)
1. Import the same Mathlib modules the gold and agent files import. Copy the vocabulary you need verbatim (inductive types, structures, spec-level predicates, constants) from the agent and gold files. Do NOT copy the implementation of the function being specified.
2. Make the agent's function(s) abstract: take them as `variable`s / theorem arguments, or as fields of a structure. Write the agent's theorem statements, copied verbatim with the function replaced by the abstract one, as hypotheses. Keep each hypothesis's own preconditions exactly as in the agent file. Skip agent statements that only talk about concrete definitions of its own (they say nothing about an arbitrary f_A) and statements that are vacuous.
3. State the adapter in a comment, and define the gold function(s) through it (a `def`/`abbrev` of the abstract agent function).
4. For each gold public theorem, state it with the gold function replaced by the adapter, and try to prove it from the hypotheses: `theorem G_i (f : ...) (h1 : ...) (h2 : ...) : <gold statement> := by ...`.
5. For a gold theorem you cannot prove, decide whether it is really not entailed: build a COUNTER-MODEL in Lean: a second concrete function f' for which you prove ALL the agent hypotheses and prove the negation of the gold theorem. A counter-model that satisfies all hypotheses and breaks the gold theorem is a Lean proof of "not entailed".
6. Compile on the host with `lake env lean`, see below. A theorem counts only if the compiler reports no error and no `sorry` warning for it. Do not use `sorry` and do not add axioms; do not weaken a gold statement to make it provable; do not strengthen an agent hypothesis beyond what the agent file states.

Which gold theorems: `k_gold` can be large. First do the ones the failing reader named (both readers' stated reasons are in your input); if one of those is refuted by a counter-model the run is decided (not entailed) and you can stop. If you want to claim "entailed" you must prove every public gold theorem (group them if the gold file has many; if the gold file has more than 25 public theorems and the named gaps are all proved, prove the rest too or report `partial` with the numbers).

## Compiling (locally, Lean v4.22.0 with Mathlib; subagents cannot use ssh)
- Compile with Bash: `cd /home/agent/lean_vb && PATH=$HOME/.elan/bin:$PATH timeout 280 lake env lean /var/lib/agent/scratch/at2297/lean/<run id>/Entail.lean 2>&1 | head -80; echo exit=${PIPESTATUS[0]}`. A trivial file takes about 7 seconds; this machine has 1 CPU shared with other jobs, so long files can take minutes: run long compiles with `run_in_background` and read the output file, and keep proofs cheap (prefer `simp`, `omega`, `decide` on small cases over heavy automation).
- Do not touch /home/agent/lean_vb itself (no lake update, no new packages); write only under /var/lib/agent/scratch/at2297/lean/.
- Budget: about 60 minutes of work per run. If you run out, report what you have.

## Report
Write ONE JSON line to the output file in your brief with keys: cell, lean_verdict ("entails": all gold theorems proved; "not_entails": at least one gold theorem refuted by a compiled counter-model; "undecided": neither), refuted (list of gold theorem names refuted, with a one-line meaning of the counter-model), proved (count) and k_gold, file (local path of Entail.lean), compiled_clean (true only if the final file compiles with exit 0 and no sorry; if you have separate files for counter-models list them), note (under 40 words, plain words: what the missing or the holding fact is). Use "run" or "task", not "cell", in note.
Plain wording. Honest reporting: if a file does not compile, say undecided.
