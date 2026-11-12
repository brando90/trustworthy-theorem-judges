# Entailment check protocol (theorem coverage by entailment)

For one cell you get two Lean 4 files for the same task: GOLD (the reference: implementation, tests, public theorem statements) and AGENT (a solver agent's own Lean file: implementation and its own theorem statements, possibly with proofs or `sorry`).

Question: does the AGENT's specification entail the GOLD's specification? Same or stronger passes; equivalence is not required. No pairing of every agent theorem with every gold theorem is wanted: reason with one master spec on each side.

Definitions
- Master spec of GOLD, M_G: the conjunction of the statements of GOLD's public theorems (theorem/lemma with a statement about the task's functions; skip `example`, `#eval`, private helper lemmas that are only proof steps, and statements that are only unit tests of concrete values). Statements are read as precondition => postcondition about the gold function(s) f_G.
- Master spec of AGENT, M_A: the conjunction of the statements of AGENT's theorems about its function(s) f_A (the same reading). Proof status is NOT part of the check (a `sorry` proof still states the spec); a statement that does not typecheck or that is vacuous (hypotheses contradictory, conclusion trivially true) contributes nothing.
- Interface adapter: the map from gold's function(s) and types to the agent's (names may differ, Nat vs Int, List vs Array, Option vs Except, extra fuel or error cases are fine when the adapter is stated explicitly and natural). If no natural adapter exists, entails = 0.
- ENTAILS = 1 iff, for an arbitrary f_A that satisfies M_A (nothing else assumed about f_A, not its definition), each gold theorem in M_G, translated through the adapter, follows logically from M_A (plus standard facts about the data types). Stated preconditions: gold's precondition must imply agent's precondition (the agent may not demand more of the inputs than gold does).
- Do NOT use the agent's implementation or its proofs to argue entailment; only its stated spec. Do NOT penalise a stronger or extra agent theorem.
- A gold theorem that merely restates a concrete implementation detail of f_G that the task description does not require (for example exact tie-breaking, a specific error string) still counts: if M_A does not imply it, it is not entailed.

Procedure per cell
1. Read GOLD and AGENT. List gold public theorems (G1..Gk) with one-line plain-language meaning, and the agent's theorems (A1..Am) likewise.
2. State the adapter in one line.
3. For each Gi: entailed (which Aj give it, one line) or not entailed (what is missing, one line).
4. entails = 1 iff all Gi entailed (k >= 1). If GOLD has no public theorem statement (k = 0), set entails = null and say so. If AGENT has no theorem statement, entails = 0 (reason no_agent_theorems).
5. Write ONE JSON line to the output file given in your brief, with keys:
   cell (string, as given), entails (1, 0 or null), k_gold (int), k_entailed (int), n_agent_theorems (int), adapter (short string), not_entailed (list of "Gname: reason", at most 5, each under 25 words), confidence ("high"|"medium"|"low"), why (under 40 words, plain words), uncertain_reason (only if confidence is not high).
Use plain standard terms (precondition, postcondition, theorem, entails). Do not look at any score for the cell (you are not given one) and do not search the repository for scores or earlier judgments.

Clarifications (apply to every cell)
- Gold theorems about the gold implementation's own runtime details (Python-specific float, overflow, termination, exact error values) are part of M_G and count; if M_A does not imply them they are not entailed.
- A fuel-bounded or bounded-input agent entails gold's unbounded termination or completeness theorem only if its stated theorems cover that input range.
- A gold theorem relating two gold functions (functional vs imperative, spec vs implementation) is mapped to the agent's counterparts; the agent needs both counterparts and a theorem that relates them or implies the claim.
- A gold conjunction theorem counts once as one theorem; a private or helper lemma that is only a proof step is not public.
- An agent that formalizes the opposite design (for example a vulnerable version where gold models the safe one) has no natural adapter: entails = 0.
- Preconditions are checked per gold theorem: the gold theorem's own hypotheses alone must be enough for the agent's stated theorems to give the conclusion (an extra bound or sortedness hypothesis that the agent requires and the gold theorem lacks is a gap).
- A gold lemma stated for any type with a typeclass (for example any `LT`) is judged at the task's concrete type(s) (for example the one the agent uses with `LinearOrder`); needing a stronger standard instance is not a gap.
- k_gold counts public gold theorem declarations after dropping pure vocabulary or proof-step lemmas; say in `why` if the count is large and you grouped them.
