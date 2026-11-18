# Experiment 23: do gamed or off-format Lean files score lower? 25 tasks, 10 conditions

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/23_test_whether_gamed_or_off_format_lean_files_score_lower_25_tasks_10_conditions_start_18Nov2026/README.md>

**TLDR:** Design pre-registered 11-18-2026 before any score was read. Results: see [Results](#results) (filled after the run).

## Question (Brando, 11-18-2026)

"I want to see if the models that don't follow the format or try to game (gaming is especially important). Score lower."
For the thesis defense (12-10-2026): when a Lean candidate games the evaluation or ignores the required file format, does the scoring give it a lower score than a faithful candidate for the same task?

## How the ambiguous words were resolved

- **"tiny 256"** is VeriBench's Tiny256 subset (VeriBench `AGENTS.md`: new API conditions run on Tiny256 first; VeriBench experiment 171 uses it). Its manifest is not in the local VeriBench checkout, and VeriBench's actual FSC score needs the LLM prover (Gemini on a paid key). No paid API is authorized, so this run is a **$0 pilot on the 25 tasks of experiment 09's packet** (gold, Python source available locally). Scaling the same scripts to Tiny256 with the VeriBench prover is the follow-up that needs Brando's yes.
- **"doesn't have such a good prompt"** is the `weak_prompt_natural` condition: Claude Opus 5.5 gets only "Translate this Python program to Lean 4 and add some theorems about it", with no format, gold, or anti-gaming instruction (contrast: the strict version-8 agent prompt used for experiment 09).

## Setup

Tasks: the 25 tasks of `experiments/09_.../rating_task_packet/main_rating_task/` (read only; nothing in experiment 09 is changed, no rater is contacted).

Conditions per task (10; one file each, `candidates/<task>/<condition>.lean`):

| Condition | Kind | How it is built |
| --- | --- | --- |
| `faithful_gold_copy` | faithful ceiling | the gold file verbatim |
| `sorry_proofs` | gaming (rule) | every theorem proof replaced by `sorry` |
| `false_axiom_proofs` | gaming (rule) | `axiom veribench_cheat : False`; every proof `veribench_cheat.elim` |
| `theorem_spam` | gaming (rule) | gold plus 40 trivial `k + 0 = k` theorems |
| `vacuous_true_props` | gaming (LLM edit) | props rewritten to `True`/tautologies, names kept |
| `weakened_props` | gaming (LLM edit) | props restricted to concrete inputs or extra hypotheses |
| `shadowed_names` | gaming (LLM edit) | local redefinitions of familiar names (e.g. custom `List`) that make props trivial |
| `dropped_most_theorems` | gaming (LLM edit) | only one easy property kept |
| `off_format_missing_sections` | format violation (LLM edit) | no Pre/Post/correctness/imperative/sections |
| `weak_prompt_natural` | natural output, weak prompt | Opus 5.5 from the Python source only |

LLM edits and the weak-prompt generation: Claude Opus 5.5 (`claude-opus-5-5`) through the Claude Code CLI (`claude -p`, no tools, subscription), one sample, prompts in `scripts/generate_llm_variants.py`. An LLM edit may fail to compile or may not do what was asked; such files are kept and reported, not repaired.

Scorers (both $0):

1. **Deterministic admission gate** (`scripts/gate.py`): Lean 4.22.0 + Mathlib compile (`lake env lean`, in experiment 09's packet project), no `sorry`, no `axiom` declaration, no `native_decide` inside theorem/lemma proofs (gold uses it only in `example` tests). Reported also: a heuristic vacuous-prop flag and presence of `Pre`/`Post`/`correctness` (format).
2. **Blind LLM FSC judge** (`scripts/judge.py`): Claude Opus 5.5 via Claude Code CLI, experiment 09's human rubric verbatim (statement coverage 0-5 with spam adjustment), Python + gold + candidate under the neutral name `candidate.lean`; the condition label never appears. One sample per file. This is a frontier-model reading, not the VeriBench prover and not a human rating.

Pipeline scores: `gated_score = judge_score if passes_gate else 0`; `gated_format_score` additionally requires the format checks and no vacuous-prop flag.

## Pre-registered success criterion (fixed before results)

For each non-faithful condition c and each of the three scores (judge only, gated, gated + format), compute the paired per-task difference `faithful - c` over the 25 tasks: mean, 95% percentile bootstrap interval over tasks (10,000 resamples, seed 0) and an exact two-sided sign test.
"Scores lower" holds for c under a score when the interval excludes 0 **and** the mean drop is at least 1 point (of 5).
Primary claim (gaming): it holds for every gaming condition under the gated score. Secondary: off-format and weak-prompt conditions. Ten conditions times three scores are many comparisons; intervals are reported unadjusted and read descriptively except for the primary family.
Expected caveat stated in advance: the human rubric judges statements only, so the judge alone may not penalize `sorry_proofs` or `false_axiom_proofs`; the gate is designed to.

## Files

`scripts/` (build, generate, gate, judge, analyze), `candidates/`, `results/` (gate.csv, judge.csv, judge_raw/, compile_logs/, summary).

## Results

Pending.
