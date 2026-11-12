# Experiment 145: vacuity and axiom check of the Lean-checked entailment passes, Tiny-256 (no DT) (Nov 1, 2026)

Tiny-256 (public tasks) only; the private set is in the private repository. Follow-up of experiment 142. No DT unless a table says DT.

**Update (11-04-2026).** Condition 5 (every gold name proved) was added; counted passes are now 789 of 1,024 (0.770), section "Condition 5 (11-04-2026)" below. The bottom line below is the conditions 1 to 4 result.

**Bottom line.** After the two checks, Lean accepts "agent spec implies gold spec" and the pass counts on **801 of 1,024 runs (0.782)**, down from 840 (experiment 142). 0 of the 840 are vacuous (each has a concrete witness for the agent spec), the gold is unedited in all 840, and 39 are dropped because an agent theorem depends on `native_decide`: Claude Code 29, Codex CLI 10. Harsh int_ref (no DT) is unchanged: 0 to 2 (Claude Code), 0 to 1 (Codex CLI), 0 to 6 (Fable 5.1), 0 to 1 (GPT-6 Astra) of 256 each, so Tiny-256 stays unsaturated.

Labels. **Lean-checked** = Lean accepted it with ub9sc as prover: the entailment proof, the axiom list, the witness. **Reading** = a label a prover assigned by reading (U, G, the trivial / identical class). Not Lean-checked: that the bridge file states the agent's theorems and the gold's exactly as written; that stays a reading (see Caveats).

## The rule (what counts as a pass)
Direction (Brando, 11-04-2026): only the agent's spec implies the gold spec is required; equivalence (gold implies agent) is not required and is not claimed. A pass means coverage of the gold; an agent spec stronger than the gold also counts. (The solver-side names `Entails` in the tables mean this one direction.)
A run counts only if all five hold:
1. Lean accepts the entailment proof (agent spec implies every public gold theorem).
2. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry` / `admit`, no added `axiom`, no `native_decide` (`Lean.ofReduceBool`; the unit-test `example` lines of the VeriBench format are outside this rule, it covers every named theorem and the entailment proof), no `unsafe` / `implemented_by` / `extern`, in the entailment proof and in every theorem of the agent's file. Checked with `#print axioms` over every `Agent.*` theorem (`lean/AxLib.lean`).
3. Gold unedited: the gold file in the bridge is byte-identical to the original gold.
4. Non-vacuous: a concrete witness satisfies the agent's preconditions and spec. `lean/WitLib.lean` (`#witness`) instantiates the bridge's `G_*` theorems with the real `Agent.*` definitions and discharges every hypothesis; the witness compiles with the standard axioms only. An agent spec that is false (or whose precondition is unsatisfiable) has no witness, so the run would be flagged.
5. Every gold name proved: each named theorem of the gold file has its bridge counterpart proved by Lean; none is dropped, renamed or skipped. Added by Brando on 11-04-2026, after the first results; the counts in the sections below (801) were computed under conditions 1 to 4 and are rechecked in the section "Condition 5 (11-04-2026)" (789).
A run failing any of them is flagged with its reason and not counted.

## Result (Lean-checked, no DT)
| Solver agent | Runs | Entails (exp 142) | Dropped: axiom (native_decide) | Dropped: vacuous / no witness | Counted passes | Rate |
|---|---:|---:|---:|---:|---:|---:|
| Claude Code (Opus 5) | 256 | 213 | 29 | 0 | 184 | 0.719 |
| Codex CLI (GPT-5.6 Sol) | 256 | 199 | 10 | 0 | 189 | 0.738 |
| Fable 5.1 (Terminus 2) | 256 | 216 | 0 | 0 | 216 | 0.844 |
| GPT-6 Astra (Terminus 2) | 256 | 212 | 0 | 0 | 212 | 0.828 |
| All | 1024 | 840 | 39 | 0 | 801 | 0.782 |

Counted passes by what each checker said: U=1 795/866, U=0 2/154 (ub9sc's reading agrees with the counted result on 947 of 1,020 runs it judged); G=1 760/830, G=0 41/194 (Gemini agrees on 913 of 1,024). All 39 dropped runs have U=1 (37 have G=1).

Harsh int_ref (no DT), floor to high, Lean-checked entailment (counted passes): Claude Code 0 to 2, Codex CLI 0 to 1, Fable 5.1 0 to 6, GPT-6 Astra 0 to 1. Harsh int (no DT): 0 to 2, 0 to 2, 0 to 44, 0 to 9. All as before the two checks: none of the runs that clear every other harsh term is one of the 39.
With DT (as-is copy, 256 tasks, `results/dt/`, non-vacuous variant: only Lean-checked passes count at the high end): harsh int_ref 0 to 2, 0 to 1, 0 to 5, 0 to 1 (experiment 143 said 0 to 2, 0 to 1, 0 to 7, 0 to 3 before the checks; its high end counted readings). Harsh (DT): 181 to 182, 187 to 188, 213 to 214, 210 to 211.

## Condition 5 (11-04-2026): every gold name proved (Lean-checked)
**Result.** Of the 840 Lean-accepted runs, 828 have a proved bridge counterpart for every named gold theorem and 12 do not. Counted passes under all five conditions: **789 of 1,024 (0.770)**, down from 801 (0.782). The 12 are all runs counted before: 3 per solver agent, the same 3 tasks for every solver, each missing one public helper lemma of the gold file that the bridge never restates (`lastOrDefault_ne_nil` in `security_set__security_6858__safe__34_unsafedirectroute_safe`, `zip_all_beq_iff_eq` in `...vulnerabilities__11_unsafetimingcomparison`, `set_get_self` in `...vulnerabilities__12_unsafestackcanary`). The prover's own class label for the 12 (a reading): 10 trivial, 2 identical or near-identical.

| Solver agent | Runs | Accepted (exp 142) | Counted, conditions 1 to 4 | Name drop | Counted, all five | Rate before | Rate after |
|---|---:|---:|---:|---:|---:|---:|---:|
| Claude Code (Opus 5) | 256 | 213 | 184 | 3 | 181 | 0.719 | 0.707 |
| Codex CLI (GPT-5.6 Sol) | 256 | 199 | 189 | 3 | 186 | 0.738 | 0.727 |
| Fable 5.1 (Terminus 2) | 256 | 216 | 216 | 3 | 213 | 0.844 | 0.832 |
| GPT-6 Astra (Terminus 2) | 256 | 212 | 212 | 3 | 209 | 0.828 | 0.816 |
| All | 1024 | 840 | 801 | 12 | 789 | 0.782 | 0.770 |

All numbers Lean-checked. Of the 840 accepted runs, 12 fail condition 5 whether or not they were dropped for the axiom rule (the 12 are all outside the 39 axiom drops); without the axiom rule the count would be 828. The solver order is unchanged (Fable 5.1, GPT-6 Astra, Codex CLI, Claude Code). Counted passes by prover class (a reading): trivial 658, identical or near-identical 74, neither 57.

**How it was checked.** `lean/GoldChkLib.lean` adds the command `#gold_check`. Compiled at the end of each run's unchanged bridge file (Lean 4.22.0, Mathlib, skampere1; `scripts/runone_gold_names.sh`), it lists every user-written theorem in the namespace `Gold` of the imported gold module (declaration ranges present, so no compiler-generated names) and looks up its counterpart: `Bridge.G_<name>`, or `Bridge.G_<parent>_<name>` when the last component is ambiguous or namespaced (bridges use this for gold files with several layers, e.g. `G_RealLayer_half_product_thm`). It requires the counterpart to be a theorem whose transitive axioms are only `propext`, `Classical.choice`, `Quot.sound`. Not required (logged separately): private helper lemmas (488 in 103 runs), structure-field proofs (2, one task: `nonempty`) and lemmas nested in another declaration (18 in 6 runs, e.g. `non_empty_thm.aux_mono`). 4,647 gold names over the 840 runs; 4,635 proved. All 840 checks compiled with exit 0 and no error. `scripts/gold_name_check.py` writes `results/gold_name_check.json` (per run: names, missing, exclusions, reason), `results/gold_name_check_summary.json`, and appends `all_gold_names_proved` (1/0, blank where Lean did not accept the proof) and `counted_all5` to `results/per_run.csv`; existing columns are unchanged. Per-run logs (filtered to the check lines): `lean/gold_name_logs_tiny.tgz`.

**Controls (Lean-checked, `results/gold_name_controls.json`, files in `lean/gold_name_controls/`).** Scratch copies of the W2_104 bridge (5 gold names), originals untouched: the unchanged copy passes 5 of 5; renaming one counterpart to `G_overflow_denies_thm_renamed` is flagged `MISSING`; deleting that theorem is flagged `MISSING`; replacing its proof by `sorry` is flagged `NONSTD [sorryAx]`.

**Choices that move the number.**
- Public helper lemmas count as named theorems (strict reading of "each named theorem"). Excluding the 12 helper-lemma runs would give 801, the old count. They are the only reason any of the 840 fail; if you decide helper lemmas are not named theorems, say so and the rule text changes with the counts.
- A first checker version flagged 22 runs; 10 of those were checker artifacts (namespaced `G_` names, structure fields, nested auxiliary lemmas) and are fixed in `GoldChkLib.lean`; the first-version logs are not kept.
- The check shows a bridge theorem exists and is proved. That its statement is the gold statement transported through the adapter is a reading, not Lean-checked (see Caveats).
- The harsh int_ref numbers above were not recomputed after condition 5; in the per-run DT file none of the 12 runs is a harsh int_ref DT pass.

## Conclusion for today (11-04-2026): prover-based FSC (proposed for co-author review, not yet a rule)
**Proposed statement.** We provisionally retain prover-based FSC as supplementary evidence of directional coverage (Agent.FS implies GoldRef.FS) verified under a fixed proof-search budget. A failure means "not proved under this setup", not a demonstrated specification gap. Integrity gaps were found in the raw pipeline; real-output accuracy and ranking reliability are not validated. The missing human ratings come first. (Statement from the independent validation in veribench-inf experiment 12, commit 4f97c875; the numbers below are from this experiment's data, receipts in `results/ruler_validity_phase0.json`, script `scripts/ruler_validity_phase0.py`, no model calls.)

**What this experiment adds** (counts are over the 789 counted runs under conditions 1 to 5 unless stated; Lean-checked unless marked reading).
- **Task difficulty dominates.** Of the variance in counted pass over 256 tasks x 4 solver agents, 70% is the task, 1.7% the solver, 28% task x solver (ICC(1) of task 0.605). 154 tasks pass for all four solvers, 35 for none; only 67 tasks (1 to 3 solvers pass) can separate solvers. 196 of the 256 tasks are security tasks (pass rate 0.74 to 0.88 per solver; HumanEval 0.45 to 0.59, real code 0.08 to 0.58, CS 0.40 to 0.50).
- **Two tiers, not four ranks.** Paired bootstrap over tasks (5,000 resamples): Fable 5.1 and GPT-6 Astra beat Codex CLI and Claude Code by 0.09 to 0.125 (every 95% interval excludes 0); Fable 5.1 vs Astra [-0.016, 0.047] and Codex CLI vs Claude Code [-0.074, 0.035] are not separated. P(Fable > Astra > Codex > Claude Code) = 0.65. No prover repeat variance was measured, and the tier gap cannot be told apart from how bridgeable each solver's representation is.
- **Most credited passes are low-information.** The prover's own class (reading): 732 of 789 are trivial or identical (658 + 74). Brando's note stands: an A to A pass is not cheating; the consequence is that a 0.8 is mostly easy tasks.
- **Ungrounded passes (script over `gold_without_agent_hyp`, a reading).** 51 of 789 counted runs have at least one gold theorem proved without any agent hypothesis (2 have all); 66 of 4,206 gold theorems (30 runs have no value). Those pass for any agent, including an empty spec. Candidate condition 6 (flag, not applied).
- **Failures are mostly unresolved, not demonstrated.** Of the 184 runs Lean did not accept, 60 have a bridge JSON: 52 not proved with no counter-model claimed, 5 with a prover-claimed counter-model (reading, not Lean-checked), 3 where the solver's own file did not compile; 124 have no bridge JSON and are unclassified.
- **The pass set depends on the prover pipeline.** The saved gpipe bridges of veribench-inf experiment 12 (a different bridge set under the same module ids, Gemini low) clear a mechanical gate (every public gold name, allowed axioms, no NOT_PROVED marker) on 687 of 1,024 runs, versus 789 here. On per-run pass/fail the two agree on 842 of 1,024 (0.82, Cohen kappa 0.56): both 647, only here 142, only there 40, neither 195. The gates differ and neither adjudicates faithfulness, so this is evidence that the score reflects the prover and bridge, not a measured error rate.

**Pros.** An accepted, faithful proof is mathematical evidence of the implication, stronger than a model's reading. Only one direction is needed. A 0.80 can mean at least 0.80 verified coverage once every credited success is integrity-checked.
**Cons.** Lean checks the supplied proposition, not whether the bridge and adapter state the right one (174 of the 759 counted runs with a known adapter use a semantic encoding, a reading). Conditions 1 to 5 do not block a bridge that reuses the gold's own proof (veribench-inf experiment 12: the raw rule accepts 6 of 7 invalid controls, the name and axiom gates alone 3 of 7). Scores reflect proof difficulty, representation and prover budget as well as coverage, so a harsher ruler is not automatically a better one.
**Not established.** Whether prover-based FSC beats the FSC judge on accuracy or ranking (needs the same human-rated items); faithfulness of the 789 bridges; prover repeat variance; agreement with smooth FSC rankings.

## Per-run tables
`results/table_<solver>.csv`, one per solver agent, 256 rows: task, run id, U (ub9sc), Lean entails, axioms ok, non-vacuous, counted, drop reason, offending theorems. Axioms and non-vacuous are `n/a` where the entailment proof was not accepted (nothing to check). `results/per_run.csv` has all 1,024 with the raw experiment 142 flag kept as `lean_entails_raw`; `results/dropped_runs.md` lists the 39.

## What was checked, how
- Entailment: experiment 142 (Lean proofs, unchanged).
- Axioms: `#print axioms` for every named `Agent.*` theorem of the 840 runs (`results/ax_result.json`, logs in `lean/axiom_logs_tiny.tgz`). 39 runs have at least one theorem on `Lean.ofReduceBool`. (A first pass skipped theorems whose namespace contains `match_` or `proof_` as text; `AxLib` now skips only auxiliary names, and the 56 affected runs were rerun: same 39 flagged.)
- Gold unedited: `results/gold_check_waves.json` (840 of 840 same).
- Witnesses: 840 witness files (`lean/witnesses_tiny.tgz`), 796 generated and compiled as is, 44 with a hand-written override for a hypothesis `decide` could not close (String functions defined by well-founded recursion, e.g. `toInt?`, `splitOn`, `substrEq.loop`; the files are in the same archive under `witnesses_hand_written_overrides`). All 840 compiled with `WITNESS_OK` and the standard axioms (`results/nonvacuity_witness_status.json`, logs in `lean/witness_logs_tiny.tgz`).
- Static scan of the 840 agent, gold and bridge files for `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `extern`, `opaque`, `native_decide`, macros and attributes (`results/static_check.json`): no `sorry`, no added axiom, no `implemented_by` / `extern` / `opaque`. The `unsafe` hit is an identifier (`unsafe_thm`), and the few macro and attribute hits (agent 1 and 3, bridge 3, gold 3) were read and are benign. `native_decide` appears as text in all 840 agent files and 812 gold files because the VeriBench format has unit-test `example ... := by native_decide` lines; an `example` is not a named theorem, nothing uses it, and it is outside the axiom rule's scope (every named theorem and the entailment proof). The 39 dropped runs are the ones where a named agent theorem itself depends on `native_decide`.

## Caveats
- A witness shows the agent's spec is satisfiable on the real agent definitions. It does not show the bridge states the agent's theorems exactly as the agent wrote them; that is a reading. It also does not detect an unsatisfiable `Pre` inside an agent theorem the gold does not use; entailment through the gold's own preconditions covers the gold-relevant ones.
- The `native_decide` rule is applied literally. The 39 dropped runs have accepted entailment proofs and witnesses; without the rule the count is 840.
- Lean-checked counts are lower bounds (a failed proof can be a prover miss).

## Files
`scripts/aggregate2.py` (counted flag; run `python3 aggregate2.py <data> <experiments> <out> tiny_status.json`, `tiny_status.json` is in `results/`), `scripts/dt_metrics.py` (experiment 143's script with `--per_run`), `agg_w.py`, `mk_one.py` (witness generator), `static_check.py`, `axrun.sh`, `run1c.sh`; `lean/WitLib.lean`, `lean/AxLib.lean`.
