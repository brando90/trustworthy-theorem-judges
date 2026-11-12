# Experiment 142: Lean-checked "agent spec implies gold spec" for all 1,024 Tiny-256 runs (no DT)

> **Update (Nov 1, 2026, experiment 145).** The 840 below are the runs where Lean accepted the entailment proof. Two more checks now apply: the agent's spec must be non-vacuous (a concrete witness) and no agent theorem may depend on `native_decide` or any non-standard axiom. 0 of the 840 are vacuous; 39 depend on `native_decide` (Claude Code 29, Codex CLI 10). The counted passes are **801 of 1,024**: Claude Code 184, Codex CLI 189, Fable 5.1 216, GPT-6 Astra 212. Harsh int_ref (no DT) is unchanged. Use the experiment 145 numbers; read the 840 below as "entailment accepted, before the two checks".

No DT (no differential testing). Tiny-256 only (public tasks); the private set is not in this folder.

## What this is
For each run (one task x one solver agent, 4 x 256 = 1,024) a Lean proof was written by ub9sc (the prover; helper agents of ub9sc) that every public gold theorem follows from the theorems the solver agent's own Lean file states. Lean accepts or rejects it. This replaces the two readings of experiment 140 (U = ub9sc reading, G = Gemini reading), which were opinions of a checker, not proofs.

Labels. **Lean-checked** = the bridge file compiles, every public gold theorem is proved, only the axioms propext, Classical.choice, Quot.sound, no sorry / admit / native_decide. **Reading** = a yes/no or class label a prover assigned by reading the two files (U, G, the class and adapter-kind columns). A failed Lean proof can be a false fail (the prover did not find the proof) but never a false pass, so the Lean-checked rate is a lower bound.

## Result (Lean-checked, no DT)
Bottom line: Lean accepts agent implies gold on **840 of 1,024 runs (0.820)**, a lower bound. By solver agent: Claude Code (Opus 5) 213/256, Codex CLI (GPT-5.6 Sol) 199/256, Fable 5.1 (Terminus 2) 216/256, GPT-6 Astra (Terminus 2) 212/256. ub9sc's readings were right on 986 of the 1,020 runs it judged (834 of its 866 passes are Lean-checked; 2 of its 154 fails are); Gemini's on 948 of 1,024 (797 of 830 passes; 43 of 194 fails are Lean-checked). The entailment passes are shallow: of 809 Lean-checked passes in the 980 wave runs, 676 are classed trivial (gold theorems follow in one or two routine steps from an agent theorem), 76 identical or near-identical, 57 neither (readings). With entailment (Lean-checked) in place of the judged theorem coverage, harsh int_ref (no DT) is 0 at the floor and at most 10 of 1,024 at the high end (1 to 6 per solver agent; see below), so Tiny-256 stays not saturated.

| Solver agent | Runs | Lean-checked entails | Rate |
|---|---:|---:|---:|
| Claude Code (Opus 5) | 256 | 213 | 0.832 |
| Codex CLI (GPT-5.6 Sol) | 256 | 199 | 0.777 |
| Fable 5.1 (Terminus 2) | 256 | 216 | 0.844 |
| GPT-6 Astra (Terminus 2) | 256 | 212 | 0.828 |
| All | 1024 | 840 | 0.820 |

Lean-checked count by what each checker said (denominator = runs with that reading):

| Solver agent | U=1 | U=0 | G=1 | G=0 |
|---|---:|---:|---:|---:|
| Claude Code (Opus 5) | 210/218 | 2/37 | 202/209 | 11/47 |
| Codex CLI (GPT-5.6 Sol) | 198/210 | 0/45 | 189/199 | 10/57 |
| Fable 5.1 (Terminus 2) | 215/221 | 0/34 | 205/212 | 11/44 |
| GPT-6 Astra (Terminus 2) | 211/217 | 0/38 | 201/210 | 11/46 |
| All | 834/866 | 2/154 | 797/830 | 43/194 |

4 runs have no U reading (ub9sc did not judge them): 1,020 judged.

harsh int and harsh int_ref (no DT), entailment = Lean-checked (floor to high end: an unrun check counts failed at the floor and passed at the high end, as in experiments 137 and 138; the floor is 0 for all four):

| Solver agent | harsh int, high end | harsh int_ref, high end |
|---|---:|---:|
| Claude Code (Opus 5) | 2 | 2 |
| Codex CLI (GPT-5.6 Sol) | 2 | 1 |
| Fable 5.1 (Terminus 2) | 44 | 6 |
| GPT-6 Astra (Terminus 2) | 9 | 1 |

Per-task tables, one per solver agent (columns task, U, G, Lean; 0/1): `results/per_task_<solver>.csv`. Per-run data with every check: `results/per_run.csv`; totals: `results/summary.json`, `results/tables.md`.

## Checks per run (acceptance list)
- Compiles, axioms, no sorry: `lean/blogs/<mod>.log` (per-theorem `#print axioms`). All 840 Lean-checked passes use only the three allowed axioms and no sorry / admit / native_decide (809 of 809 wave passes by script; 31 of 31 sample passes in experiment 141).
- Agent precondition satisfiable: every agent file of a Lean-checked pass is sorry-free (the agent's own functions are a model of its theorems), so the hypotheses are not contradictory. This also rules out an agent postcondition that is false for every input.
- Gold postcondition not trivially true: gold theorems proved without using any agent hypothesis: in 53 of the 809 wave passes at least one gold theorem, in 2 all of them. Column `gold_without_agent_hyp` in per_run.csv (counted by script on the proof text, a heuristic).
- Adapter noted per run: `adapter_kind` (cast-only 617, semantic encoding 192 among the 809 wave passes; sorted by a keyword rule on the prover's adapter text, so a reading) and the adapter text in `results/wave_K.jsonl`. A semantic encoding means "entailed modulo the adapter"; faithfulness of the adapter is a reading, not Lean-checked.
- Proof length: `proof_lines` = non-blank, non-comment lines of all gold theorem proofs in the bridge; median 31 per run (809 wave passes), longest 127.

## Not Lean-checked (184 runs)
179 compile but not every gold theorem is proved (Float / Real versus Rat, ASCII versus Unicode digits, differing models, gold parts with no natural adapter), 5 do not compile (T39, the heap_sort bridge of the sample, 3 theorems with errors; W6_000, where the solver agent's own file does not compile; W7_111; W8_017 and W8_074, which have no bridge). A prover that did not find a proof may still be a false fail, so these 184 are not shown to be non-entailed.

## Method
1. `scripts/prep_wave.py` wraps gold and agent files (`namespace Gold` / `namespace Agent`) from `results/waves/wave_K.json`; they compile as separate modules (Lean v4.22.0 with Mathlib, skampere1, `scripts/build.sh`, `queue_runner.sh`).
2. ub9sc helper agents write `Bridge_<mod>.lean`: the agent's theorem statements become hypotheses about abstract function variables, so its definitions cannot be unfolded; each public gold theorem is transported to the agent functions through an explicit adapter and proved from them. One prover per two runs, compile (`bridge.sh`, `runbridges.sh`), at most two fix rounds on compile errors, then the theorem is left in a `-- NOT_PROVED:` comment and the run does not count.
3. `scripts/review_wave.py` computes the checks per run; `scripts/aggregate.py` joins them with U and G (experiment 140), experiment 137 and 138 per-task components and writes the tables. Run: `python3 scripts/aggregate.py <data_dir with review.json and scale/{waves,results}> <experiments dir> <out dir>`.
4. 1,024 runs = the 44-run sample of experiment 141 (`results/review_sample44.json`) + 8 waves (7 x 123 + 119 runs; `results/wave_K.jsonl`).

## Files
- `lean/bridges/Bridge_<mod>.lean|json`: final bridge per run (978 of 980 wave runs have one, plus 44 sample); `lean/blogs/`: compile logs. Gold and agent sources are regenerated by `prep_wave.py` from the manifests. Run to module map: `per_run.csv` columns `run`, `mod`.
- `results/`, `scripts/`: above.

## Caveats
Provers are ub9sc only; Gemini as a Lean prover is a separate follow-up. U and G are readings. The class (trivial, identical, neither) and adapter kind are readings. 752 of the 809 wave passes (93 percent) are classed trivial or identical by reading; a Lean-checked pass is weak evidence that the agent spec is strong. The 44-run sample is stratified toward disagreements, but it is part of the 1,024 so every run has a Lean result.
