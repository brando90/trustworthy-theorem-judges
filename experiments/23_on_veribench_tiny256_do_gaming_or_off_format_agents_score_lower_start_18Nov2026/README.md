# Experiment 23: on VeriBench Tiny256, do gaming or badly behaving agents score lower under our evaluation pipelines?

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/23_on_veribench_tiny256_do_gaming_or_off_format_agents_score_lower_start_18Nov2026/README.md>

**TLDR:** Design pre-registered 11-18-2026 before any judge score was read. Results: see [Results](#results).

## Question (Brando, 11-18-2026)

"(Q: gaming, bad agents doing vb tiny score lower with our eval pipelines?)" — when a Lean candidate games the evaluation (vacuous, weakened or shadowed properties, `sorry`/false-axiom proofs, theorem spam, dropped theorems), ignores the required VeriBench file format, or comes from a weak prompt, does our evaluation give it a lower score than a faithful candidate for the same task? Motivation: thesis defense 12-10-2026; the version-8 agent prompt warns against gaming, so we need direct evidence that the scoring itself penalizes it.

## Task set: Tiny256

Tiny256 is Brando's 256-task subset of VeriBench (full VBV1: 896 tasks; VeriBench `AGENTS.md` line 64). Frozen manifest: `~/veribench-inf/experiments/11_tiny256_gold_self_implication_lean_tactics_11-04-2026/evidence/v1/manifest.json` (256 byte-distinct gold references, `veribench@1.3`, no differential testing). Files fetched from `skampere2:/lfs/skampere2/0/brando9/at2314/src/<id>/{gold,agent}.lean`; **all 256 gold sha256 values match the manifest** (`scripts/import_tiny256.py`, `inputs/tiny256_manifest.json`). `agent.lean` is the historical natural agent output saved with each task.

Python sources are not in the Tiny256 bundle; `scripts/map_python_sources.py` maps each gold file to a `veribench_dataset/py_src` file by implementation-function name (255/256 mapped; 57 ambiguous, flagged).

**Relation to existing Tiny256 controls.** veribench-inf 13 and VeriBench 168/171 measure the LLM prover's detection (P_D/P_F) on synthetic `f = g` mutations (36/36 accepted covering, 0/34 accepted non-covering; natural accuracy unmeasured). They do not test gaming strategies (sorry/axiom proofs, vacuous/weakened/shadowed properties, spam, dropped theorems), format violations, weak prompts, or the LLM statement-coverage judge. This experiment adds exactly those; it does not re-run the prover (paid key, needs Brando's yes).

## Conditions

| Condition | Kind | Built by | Tasks |
| --- | --- | --- | --- |
| `faithful_gold_copy` | faithful ceiling | gold verbatim | 256 |
| `historical_natural_agent` | natural agent output (`veribench@1.3`) | saved `agent.lean` | 256 |
| `sorry_proofs` | gaming | rule: every theorem proof `sorry` | 256 |
| `false_axiom_proofs` | gaming | rule: `axiom veribench_cheat : False`, proofs `veribench_cheat.elim` | 256 |
| `theorem_spam` | gaming | rule: gold + 40 trivial `k + 0 = k` theorems | 256 |
| `vacuous_true_props` | gaming | LLM edit of gold | 30-task sample |
| `weakened_props` | gaming | LLM edit of gold | 30-task sample |
| `shadowed_names` | gaming | LLM edit (local `List` etc. that trivialize props) | 30-task sample |
| `dropped_most_theorems` | gaming | LLM edit (one easy property kept) | 30-task sample |
| `off_format_missing_sections` | format violation | LLM edit (no Pre/Post/correctness/sections) | 30-task sample |
| `weak_prompt_natural` | natural output, weak prompt | Opus 5.5 given only the Python and "Translate this Python program to Lean 4 and add some theorems about it" | 30-task sample |

30-task sample: `random.Random(0).sample` over the 185 tasks with an unambiguous Python map and gold of at most 400 lines (bounds generation time; a stated selection, not representative of the longest tasks). LLM edits and weak-prompt generation: Claude Opus 5.5 (`claude-opus-5-5`), Claude Code CLI `claude -p`, no tools, subscription, one sample each, prompts in `scripts/generate_llm_variants.py`. An LLM edit that does not compile or does not do what was asked is kept and reported, not repaired.

## Evaluation pipelines (all $0)

1. **Deterministic admission gate** (`scripts/gate.py`), all files: Lean 4.22.0 + Mathlib v4.22.0 compile (`lake env lean`, using experiment 09's pinned packet project read only); no `sorry`; no `axiom` declaration; no `native_decide` inside theorem/lemma proofs (gold uses it only in `example` tests). Also reported: heuristic vacuous-prop flag and presence of `Pre`/`Post`/`correctness` (format).
2. **Blind LLM statement-coverage judge** (`scripts/judge.py`), 30-task sample, all 11 conditions: Claude Opus 5.5 via Claude Code CLI with experiment 09's human rubric verbatim (0-5, spam adjustment), Python + gold + candidate under the neutral name `candidate.lean`; condition labels never appear. One sample per file. A frontier-model reading, not the VeriBench prover and not a human rating.

Pipeline scores: `judge_only`; `gated = judge if passes_gate else 0`; `gated_format = judge if passes_gate and format checks and no vacuous flag else 0`. On all 256 tasks: binary gate pass rate per condition.

## Pre-registered success criterion

- Analysis population: tasks whose `faithful_gold_copy` passes the gate (a gold that fails to compile here is an infrastructure exclusion, reported).
- 256-task gate: for each rule-based gaming condition, gate pass rate with exact Clopper-Pearson 95% interval; paired McNemar-style count of tasks where faithful passes and the condition fails. "Penalized" = condition pass rate's upper bound below 0.05.
- 30-task judge pipelines: per condition and score, paired per-task drop `faithful - condition`, mean with 95% percentile bootstrap interval over tasks (10,000 resamples, seed 0) and exact two-sided sign test. "Scores lower" = interval excludes 0 **and** mean drop at least 1 point of 5.
- Primary claim: every gaming condition scores lower under the `gated` pipeline. Secondary: off-format, weak-prompt and historical natural conditions (descriptive), and `judge_only` (to show what the judge alone does). Intervals unadjusted; the 11 x 3 grid is read descriptively outside the primary family.
- Stated in advance: the human rubric judges statements only, so the judge alone is not expected to penalize `sorry_proofs`/`false_axiom_proofs`; the gate is.

## Pilot (experiment 09's 25 tasks)

`pilot_exp09_25_tasks/` holds a first run on experiment 09's 25 packet tasks (rule-based variants judged; LLM edits partly generated) before the task set was clarified as Tiny256. It is kept as a labeled pilot, not merged with Tiny256 results.

## Files

`scripts/` (import, map, build, generate, gate, judge, analyze), `inputs/` (Tiny256 copies + manifest), `tiny256/candidates/`, `tiny256/results/`.

## Results

Pending.
