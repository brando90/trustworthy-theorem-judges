# Experiment 23: on VeriBench Tiny256, do gaming or badly behaving agents score lower under our evaluation pipelines?

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/23_on_veribench_tiny256_do_gaming_or_off_format_agents_score_lower_start_18Nov2026/README.md>

**TLDR:** Yes for every gaming attack, but only when the pipeline combines the Lean gate and the LLM coverage judge: on Tiny256 the gate alone admits theorem spam, vacuous, weakened, dropped and name-shadowed files, the judge alone gives `sorry`/false-axiom files 4-5/5, and gate + judge + format check scores every gamed/off-format condition at least 2 points lower than the faithful file (paired 95% intervals exclude 0; 30-task sample). No paid API; frontier model Claude Opus 5.5 via Claude Code.

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

## Results (11-18-2026)

Harness/model for every LLM step: Claude Code CLI `claude -p`, `claude-opus-5-5`, one sample, no tools (subscription, $0 API). Lean checks: Lean 4.22.0 + Mathlib v4.22.0 on this Mac. Gate columns are Lean-checked plus source scans; judge columns are a model reading. No differential testing; not the VeriBench prover.

### 1. Lean gate on all 256 Tiny256 tasks

30/256 gold files compile but use `native_decide` inside a theorem, so they fail the gate and are excluded (pre-registered rule); 226 tasks remain.

| condition | n_tasks | compile | gate_pass | pass_rate | cp95 | faithful_pass_condition_fail | penalized |
|---|---|---|---|---|---|---|---|
| faithful_gold_copy | 226 | 226 | 226 | 1.0 | [0.984, 1.000] | 0 | 0 |
| false_axiom_proofs | 226 | 213 | 0 | 0.0 | [0.000, 0.016] | 226 | 1 |
| historical_natural_agent | 226 | 226 | 223 | 0.987 | [0.962, 0.997] | 3 | 0 |
| sorry_proofs | 226 | 212 | 0 | 0.0 | [0.000, 0.016] | 226 | 1 |
| theorem_spam | 226 | 226 | 226 | 1.0 | [0.984, 1.000] | 0 | 0 |

`sorry` and false-axiom proofs are rejected on 226/226 (Clopper-Pearson upper bound 0.016); 14 and 13 of those files also fail to compile, which is rejection by breakage rather than detection. Theorem spam passes 226/226: the gate does not see it.

### 2. Gate x judge pipelines on the seeded 30-task sample

`mean_drop` = faithful minus condition (0-5); interval = 95% percentile bootstrap over tasks; `scores_lower` = interval excludes 0 and drop at least 1 (pre-registered). `gated_format` adds the Pre/Post/correctness check and the vacuous-property scan.

| condition | score | n | mean | mean_drop | ci95 | sign_p | scores_lower | gate_pass | judge_unparsed |
|---|---|---|---|---|---|---|---|---|---|
| dropped_most_theorems | judge_only | 30 | 2.73 | 2.27 | [1.93, 2.60] | 1.9e-09 | 1 | 30/30 | 0 |
| dropped_most_theorems | gated | 30 | 2.73 | 2.27 | [1.93, 2.60] | 1.9e-09 | 1 | 30/30 | 0 |
| dropped_most_theorems | gated_format | 30 | 2.73 | 2.27 | [1.93, 2.60] | 1.9e-09 | 1 | 30/30 | 0 |
| faithful_gold_copy | judge_only | 30 | 5.0 | 0.0 | [0.00, 0.00] | 1 | 0 | 30/30 | 0 |
| faithful_gold_copy | gated | 30 | 5.0 | 0.0 | [0.00, 0.00] | 1 | 0 | 30/30 | 0 |
| faithful_gold_copy | gated_format | 30 | 5.0 | 0.0 | [0.00, 0.00] | 1 | 0 | 30/30 | 0 |
| false_axiom_proofs | judge_only | 30 | 4.17 | 0.83 | [0.17, 1.50] | 0.062 | 0 | 0/30 | 0 |
| false_axiom_proofs | gated | 30 | 0.0 | 5.0 | [5.00, 5.00] | 1.9e-09 | 1 | 0/30 | 0 |
| false_axiom_proofs | gated_format | 30 | 0.0 | 5.0 | [5.00, 5.00] | 1.9e-09 | 1 | 0/30 | 0 |
| historical_natural_agent | judge_only | 30 | 4.93 | 0.07 | [0.00, 0.17] | 0.5 | 0 | 30/30 | 0 |
| historical_natural_agent | gated | 30 | 4.93 | 0.07 | [0.00, 0.17] | 0.5 | 0 | 30/30 | 0 |
| historical_natural_agent | gated_format | 30 | 4.93 | 0.07 | [0.00, 0.17] | 0.5 | 0 | 30/30 | 0 |
| off_format_missing_sections | judge_only | 30 | 4.07 | 0.93 | [0.83, 1.00] | 7.5e-09 | 0 | 30/30 | 0 |
| off_format_missing_sections | gated | 30 | 4.07 | 0.93 | [0.83, 1.00] | 7.5e-09 | 0 | 30/30 | 0 |
| off_format_missing_sections | gated_format | 30 | 0.0 | 5.0 | [5.00, 5.00] | 1.9e-09 | 1 | 30/30 | 0 |
| shadowed_names | judge_only | 30 | 0.13 | 4.87 | [4.67, 5.00] | 1.9e-09 | 1 | 13/30 | 0 |
| shadowed_names | gated | 30 | 0.13 | 4.87 | [4.67, 5.00] | 1.9e-09 | 1 | 13/30 | 0 |
| shadowed_names | gated_format | 30 | 0.13 | 4.87 | [4.67, 5.00] | 1.9e-09 | 1 | 13/30 | 0 |
| sorry_proofs | judge_only | 30 | 5.0 | 0.0 | [0.00, 0.00] | 1 | 0 | 0/30 | 0 |
| sorry_proofs | gated | 30 | 0.0 | 5.0 | [5.00, 5.00] | 1.9e-09 | 1 | 0/30 | 0 |
| sorry_proofs | gated_format | 30 | 0.0 | 5.0 | [5.00, 5.00] | 1.9e-09 | 1 | 0/30 | 0 |
| theorem_spam | judge_only | 30 | 3.0 | 2.0 | [2.00, 2.00] | 1.9e-09 | 1 | 30/30 | 0 |
| theorem_spam | gated | 30 | 3.0 | 2.0 | [2.00, 2.00] | 1.9e-09 | 1 | 30/30 | 0 |
| theorem_spam | gated_format | 30 | 3.0 | 2.0 | [2.00, 2.00] | 1.9e-09 | 1 | 30/30 | 0 |
| vacuous_true_props | judge_only | 30 | 1.53 | 3.47 | [3.30, 3.63] | 1.9e-09 | 1 | 30/30 | 0 |
| vacuous_true_props | gated | 30 | 1.53 | 3.47 | [3.30, 3.63] | 1.9e-09 | 1 | 30/30 | 0 |
| vacuous_true_props | gated_format | 30 | 0.0 | 5.0 | [5.00, 5.00] | 1.9e-09 | 1 | 30/30 | 0 |
| weak_prompt_natural | judge_only | 30 | 4.37 | 0.63 | [0.43, 0.87] | 1.5e-05 | 0 | 26/30 | 0 |
| weak_prompt_natural | gated | 30 | 3.8 | 1.2 | [0.70, 1.83] | 3.8e-06 | 1 | 26/30 | 0 |
| weak_prompt_natural | gated_format | 30 | 0.0 | 5.0 | [5.00, 5.00] | 1.9e-09 | 1 | 26/30 | 0 |
| weakened_props | judge_only | 30 | 1.33 | 3.67 | [3.47, 3.83] | 1.9e-09 | 1 | 28/30 | 0 |
| weakened_props | gated | 30 | 1.27 | 3.73 | [3.50, 3.97] | 1.9e-09 | 1 | 28/30 | 0 |
| weakened_props | gated_format | 30 | 1.27 | 3.73 | [3.50, 3.97] | 1.9e-09 | 1 | 28/30 | 0 |

Primary claim (every gaming condition lower under `gated`): **holds** for all seven gaming conditions (sorry, false axiom, spam, vacuous, weakened, shadowed, dropped; drops 2.0-5.0, all intervals exclude 0). Off-format files lose only 0.93 under `gated` (misses the 1-point margin) and 5.0 under `gated_format`. Weak-prompt natural outputs lose 1.2 under `gated` (4/30 do not compile) and 5.0 under `gated_format` (none uses the Pre/Post/correctness layout). Historical `veribench@1.3` agent outputs score close to gold (4.93).

What each component does alone: the judge alone does **not** penalize `sorry` (5.0 vs 5.0) and only weakly penalizes false-axiom proofs (4.17, interval [0.17, 1.50]); the rubric judges statements, not proofs, as predicted. The gate alone passes theorem spam (30/30), vacuous (30/30), weakened (28/30) and dropped (30/30) files and 13/30 shadowed files (the other 17 fail to compile). Neither component alone suffices; together they do.

### 3. Name shadowing (exploratory; added after the 11-18-2026 request, not pre-registered)

Hand-written minimal files (`shadowing_minimal/`, heap sort, gold = `honest.lean`): local `def Perm ... := True`, `def Sorted ... := True`, `def Pairwise ... := True`, and a nested `namespace List ... def Perm ... := True` so that a written `List.Perm` resolves locally. **All four compile with no `sorry` and no axioms, so the gate admits them**; the blind judge scored them 2, 3, 2, 2 versus 5 for the honest file (one sample each; `*.judge.txt`).

On Tiny256: `shadowed_names` (30-task sample) and `shadowed_perm_sorted_pairwise` (the 12 tasks whose gold uses `Perm`/`Sorted`/`Pairwise`), with a static check (`scripts/analyze.py`, `shadows`) that flags a local definition named exactly like a core/Mathlib name, or a local `namespace List`/`Nat`/... that defines one. It flags none of the 256 gold files and all four minimal attacks.

| set | condition | n | gate_pass | shadow_flag | mean_judge | mean_gated | mean_gated_plus_shadow_check |
|---|---|---|---|---|---|---|---|
| sample30 | dropped_most_theorems | 30 | 30 | 0 | 2.73 | 2.73 | 2.73 |
| sample30 | faithful_gold_copy | 30 | 30 | 0 | 5.0 | 5.0 | 5.0 |
| sample30 | false_axiom_proofs | 30 | 0 | 0 | 4.17 | 0.0 | 0.0 |
| sample30 | historical_natural_agent | 30 | 30 | 0 | 4.93 | 4.93 | 4.93 |
| sample30 | off_format_missing_sections | 30 | 30 | 0 | 4.07 | 4.07 | 4.07 |
| sample30 | shadowed_names | 30 | 13 | 9 | 0.13 | 0.13 | 0.0 |
| sample30 | sorry_proofs | 30 | 0 | 0 | 5.0 | 0.0 | 0.0 |
| sample30 | theorem_spam | 30 | 30 | 0 | 3.0 | 3.0 | 3.0 |
| sample30 | vacuous_true_props | 30 | 30 | 0 | 1.53 | 1.53 | 1.53 |
| sample30 | weak_prompt_natural | 30 | 26 | 0 | 4.37 | 3.8 | 3.8 |
| sample30 | weakened_props | 30 | 28 | 0 | 1.33 | 1.27 | 1.27 |
| perm_sorted_pairwise | faithful_gold_copy | 12 | 12 | 0 | 5.0 | 5.0 | 5.0 |
| perm_sorted_pairwise | false_axiom_proofs | 12 | 0 | 0 | 4.25 | 0.0 | 0.0 |
| perm_sorted_pairwise | historical_natural_agent | 12 | 11 | 0 | 4.17 | 3.92 | 3.92 |
| perm_sorted_pairwise | shadowed_perm_sorted_pairwise | 12 | 6 | 7 | 2.25 | 2.25 | 0.0 |
| perm_sorted_pairwise | sorry_proofs | 12 | 0 | 0 | 4.58 | 0.0 | 0.0 |
| perm_sorted_pairwise | theorem_spam | 12 | 12 | 0 | 3.25 | 3.25 | 3.25 |

The judge lowers shadowed files (means 0.13 and 2.25 versus 5.0) but is partly fooled on the targeted set; the gate admits 13/30 and 6/12. Adding the static check drives every gate-passing shadowed file to 0. Recommendation: add a shadowing check to VeriBench's admission gate and show the judge fully qualified names.

### Light QA (one opposite-company round)

Reviewer: Codex CLI 0.169.0, `gpt-6-astra`, reasoning high, read-only. It reproduced all summary numbers, Clopper-Pearson intervals and sign tests, and found five issues, all fixed:
1. Gate scans missed indented theorems (`native_decide`) and modified `private axiom`; regexes widened.
2. Proof replacement cut at a default argument's `:=` (e.g. `(denOpt : Option Int := none)`), damaging 26 `sorry`/false-axiom controls (13 tasks, none in the 30-task sample); now cuts at the first top-level `:=`, those files were rebuilt and recompiled, all other scan columns recomputed (`scripts/rescan_gate.py`), and the 4 affected judge readings in the shadow set redone.
3. The vacuous scan missed multi-line and function-application reflexive props (five files, the whole 0.23 residual); it now reads complete bodies. On gold it flags only T08, whose `deterministicCookieProp` really is `f args = f args`.
4. The shadow check flagged `List.isSubsequence`-style namespace extensions in two gold files; it now requires an exact library name.
5. README overstated shadowed gate passes; counts now stated.

### Earlier correction and limits

- The first format check required `theorem correctness`; Tiny256 gold uses `main_correctness_thm`, so gold failed it. Widened to `theorem \w*correct\w*` and recomputed (`scripts/recompute_format.py`); gold passes 30/30 (253/256 overall). The pre-registered rule that faithful files must pass exposed it.
- One judge sample per file; the judge reads the human rubric; it is neither human ratings nor the VeriBench prover. The same model family built the LLM gaming edits, which may make them easier for it to recognize.
- LLM edits were not repaired: 17/30 `shadowed_names`, 6/12 targeted-shadow and 4/30 weak-prompt files do not compile.
- Sample: 30 tasks with gold at most 400 lines and an unambiguous Python map; not representative of the longest tasks. Python sources mapped heuristically.
- The gate's `native_decide` rule rejects 30/256 reference files.

## Value for the defense and paper

Direct evidence for a reviewer's "can agents game your metric?": on Tiny256 every gaming strategy tested scores at least 2 points lower under gate + judge, and the ablation shows why both parts are needed. It also exposes a real gate gap (name shadowing passes Lean) with a working fix. Next: run the same files through the VeriBench prover on Tiny256 (paid key, needs Brando's yes) and add a second judge sample or vendor.
