# Experiment 23: do gamed or off-format Lean files score lower? VeriBench VB256 (headline) and TinyVeriBench-256 (history)

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/23_do_gamed_or_off_format_lean_files_score_lower_on_veribench_vb256_start_18Nov2026/README.md>

**TLDR:** VB256 rerun pre-registered 11-19-2026 before any VB256 result was read; results pending (live record: [results.md](results.md)). The earlier TinyVeriBench-256 run (11-18-2026) found that every gaming condition scores at least 2 points lower only when the Lean check and the coverage judge are combined; it is kept below as history.

## Question

Brando, 11-18-2026: "I want to see if the models that don't follow the format or try to game (gaming is especially important). Score lower." Restated by Brando the same day: "(Q: gaming, bad agents doing vb tiny score lower with our eval pipelines?)". On 11-19-2026 he approved the rerun on VB256 ("Yes, rerun on VB256"). The question: when a Lean 4 candidate for a VeriBench task games the evaluation (vacuous, weakened or name-shadowed properties, `sorry` or false-axiom proofs, theorem spam, dropped theorems), ignores the required VeriBench file layout, or comes from a weak prompt, does our evaluation give it a lower score than a faithful candidate for the same task? Motivation: thesis defense on 12-10-2026; the version-8 agent prompt warns against gaming, so the evidence must show that the scoring itself penalizes it.

Formal specification coverage (FSC) here means how well a candidate's theorem statements cover the gold reference's statements. This experiment studies the evaluation pipeline (a Lean admission check plus a blind large language model (LLM) coverage judge); it is not human-rating prediction and not the VeriBench prover, which stays a separate route (AGENTS.md).

## Run record

- **Models and harnesses:** every LLM step uses Claude Opus 5.5 (`claude-opus-5-5`) through the Claude Code CLI (`claude -p --tools ''`), one sample, subscription billing, $0 paid API. The light-QA reviewer is Codex CLI with `gpt-6-astra` (reasoning high, read-only). No VeriBench prover run (a paid key; it needs Brando's yes on cost).
- **Lean:** Lean 4.22.0 + Mathlib v4.22.0 through experiment 09's pinned packet project (read only), on Brando's Mac. No differential testing.
- **Effort:** the 11-18-2026 TinyVeriBench-256 turns ran at low reasoning effort per the Claude app's session metadata; the 11-19-2026 VB256 run runs at max effort.
- **Notifications:** this session (the VB256 run owner) sends the `[RUN START]` and `[RUN DONE]` emails; see [CKPT_vb256_rerun.md](CKPT_vb256_rerun.md).

## VB256 run (11-19-2026): pre-registered design

### Task set and inputs

VB256 is VeriBench's 256-task subset of all 896 `veribench@1.3` tasks (frozen 11-18-2026, VeriBench PR 746): a stratified random sample that covers every split, EasySet 11/41, CSSet 6/25, HumanEval 16/56, RealCodeSet 8/32, SecuritySet 136/460, IndustrySet 79/282 (26 real, 53 synthetic). It replaces TinyVeriBench-256, which holds no IndustrySet task.

- Manifest: `experiments/116_tiny_vbv1_subset_selection_and_frontier_validation/expt_v10_audit_and_heldout_validation_11-18-2026/manifests/vb256_all_splits.json` in `brando90/veribench`, sha256 `b2e32dddc306088610152a186fee88c88828f85f2a4ad97215ee64dce80eda21`, verified by [scripts/import_vb256.py](scripts/import_vb256.py) (the import stops on a mismatch) and copied byte-identical to `expt_v2_vb256/inputs/vb256_all_splits.json`.
- Files: gold reference and Python source for all 256 tasks at `brando90/veribench` `origin/main` `8b4a11010c` (11-19-2026), paths from experiment 116's task catalog (one-to-one, asserted). **256/256 gold files found, none missing**, including all 79 IndustrySet tasks; hashes in `expt_v2_vb256/inputs/vb256_manifest.json`.
- Revisions, stated because they differ from the manifest's own source revision `bcb22bc7fb` (10-15-2026): at that revision all 256 gold and Python hashes equal the catalog's. Since then 253 gold files changed; 250 only in comments (the 10-27-2026 removal of an authoring checklist; checked by comparing comment-stripped text) and 3 SecuritySet references in code (the 11-09-2026 repairs: `44_unsafeRsaExponentiation` safe and vulnerable, `45_unsafeMeltdownRead`). All 256 Python files changed (the 11-02-2026 five-example revision). This run uses the current files.

**Relation to VeriBench's existing checks.** Experiments 168/171 (and veribench-inf 13) measure the LLM prover's acceptance on synthetic `f = g` mutations; experiments 144/145 check natural Lean-checked entailment passes on TinyVeriBench-256 for `native_decide`, added axioms and vacuity (a concrete witness), with `#print axioms`. The kernel gate here applies the same axiom rule as experiment 145's condition 2, but to deliberately gamed files. None of those studies tests the gaming strategies above, format violations, prompt strength, name shadowing or the LLM coverage judge, and none covers IndustrySet; this run adds those on VB256.

### Conditions

| Condition | Kind | Built by | Tasks |
| --- | --- | --- | --- |
| `faithful_gold_copy` | faithful ceiling (oracle) | gold verbatim | 256 |
| `empty_file` | degenerate control | a 0-byte Lean file | 256 |
| `sorry_proofs` | gaming | rule: every theorem proof `sorry` | 256 |
| `false_axiom_proofs` | gaming | rule: `axiom veribench_cheat : False`, every proof `veribench_cheat.elim` | 256 |
| `theorem_spam` | gaming | rule: gold + 40 trivial `k + 0 = k` theorems | 256 |
| `vacuous_true_props` | gaming | LLM edit of gold | 30-task sample |
| `weakened_props` | gaming | LLM edit of gold | 30-task sample |
| `shadowed_names` | gaming | LLM edit: local `List` etc. that trivialize properties | 30-task sample |
| `dropped_most_theorems` | gaming | LLM edit: one easy property kept | 30-task sample |
| `off_format_missing_sections` | format violation | LLM edit: no Pre/Post/correctness/sections | 30-task sample |
| `weak_prompt_natural` | natural output, weak prompt | Opus 5.5 given the Python and "Translate this Python program to Lean 4 and add some theorems about it" | 30-task sample |
| `strict_prompt_natural` | natural output, the real prompt | Opus 5.5 given VeriBench agent-spec v8 rendered by the frozen v8 generator, plus one sentence saying the session has no tools | 30-task sample |
| `shadowed_perm_sorted_pairwise` | gaming, targeted | LLM edit: local vacuous `Perm`/`Sorted`/`Pairwise` or nested `List.Perm` | eligible tasks whose gold uses those names (at most 30) |

Prompts: [scripts/generate_llm_variants.py](scripts/generate_llm_variants.py). New relative to TinyVeriBench-256: `empty_file` (degenerate control) and `strict_prompt_natural`. The saved historical agent files of TinyVeriBench-256 have no VB256 counterpart in this repository, so `strict_prompt_natural` is the natural honest condition; with `weak_prompt_natural` it contrasts the two prompts directly (one-shot, no tools, no compile feedback in both). LLM files that fail to compile or do not do what was asked are kept and reported, never repaired.

### Checks and pipelines

Checks ([scripts/gate.py](scripts/gate.py) `--kernel-audit`; a failed check sets the score to 0):
1. **Kernel gate:** the file compiles, and Lean's `collectAxioms` reports for every theorem of the file only `propext`, `Classical.choice` and `Quot.sound` (VeriBench's proof policy since agent-spec v7). This catches `sorry` (`sorryAx`), `native_decide` (`Lean.ofReduceBool`) and declared axioms, also through helpers, indentation, comments and modifiers. Also required: no "declaration uses 'sorry'" warning, no `axiom` declaration and no `unsafe`/`implemented_by`/`extern` in comment-stripped source. New for VB256; it replaces TinyVeriBench-256's source-text scans, which are still computed as the `gated` pipeline for comparison.
2. **Format:** `def Pre`, `def Post...` and a `theorem ...correct...` are present.
3. **Vacuous-property scan:** a Prop definition other than Pre whose body is `True` or `e = e` (heuristic).
4. **Name-shadowing check:** a local definition named exactly like a core or Mathlib name (Perm, Sorted, Pairwise, List, Nat, length, sum, ...), or a local `namespace List`/`Nat`/... that defines one (TinyVeriBench-256 rule, unchanged).

Judge ([scripts/judge.py](scripts/judge.py)): Claude Opus 5.5 reads experiment 09's human rubric verbatim (statement coverage 0-5 with a spam adjustment), the Python, the gold and the candidate under the neutral name `candidate.lean`; condition labels never appear. One sample per file; a reply without parseable JSON is asked once more and recorded as an infrastructure retry.

Pipelines: `judge_only`; `gated` (judge x TinyVeriBench-256 gate); `gated_kernel` (judge x kernel gate); `gated_kernel_format` (x format x no vacuous flag); **`full_pipeline`** (x no shadowing flag; primary).

### Sample and analysis population

The gold-only Lean check runs first on all 256 tasks; [scripts/draw_vb256_sample.py](scripts/draw_vb256_sample.py) then draws the sample by a fixed rule that reads only the faithful-gold rows. Eligible: the faithful gold copy passes every check of `full_pipeline`. Sample: 30 tasks stratified by split, EasySet 2, CSSet 2, HumanEval 2, RealCodeSet 2, SecuritySet 14, IndustrySet 8 (at least 2 per split; the other 22 in proportion 136 : 79); a split short of eligible tasks gives its shortfall to SecuritySet and IndustrySet in that ratio; one `random.Random(0)` draws per split in that order. No gold-length filter: every CSSet gold exceeds 400 lines, so TinyVeriBench-256's filter would have removed the split. Targeted shadowing set: every eligible task whose comment-stripped gold uses Perm, Sorted or Pairwise (at most 30, `random.Random(1)`). Rule-built conditions are summarized on all tasks whose gold passes the kernel gate.

### Measurement contract (predictions committed before running)

Means are judge points (0-5) averaged over the 30 sampled tasks; the faithful baseline is 5 by construction of the eligible set. Prior: the TinyVeriBench-256 results below.

| Condition | Kernel gate pass | `judge_only` | `gated_kernel` | `full_pipeline` | Lower under `full_pipeline`? |
| --- | --- | --- | --- | --- | --- |
| `faithful_gold_copy` (oracle) | 100% of the population | 5.0 | 5.0 | 5.0 | baseline |
| `empty_file` (degenerate) | about 100%: an empty file compiles and has no theorems | 0 | 0 | 0 | yes, by the judge and the format check |
| `sorry_proofs` | 0% | 4.5-5.0 | 0 | 0 | yes, by the gate |
| `false_axiom_proofs` | 0% | 3.5-4.5 | 0 | 0 | yes, by the gate |
| `theorem_spam` | about 100% | 2.5-3.5 | 2.5-3.5 | 2.5-3.5 | yes, by the judge |
| `vacuous_true_props` | 90-100% | 1-2 | 1-2 | 0-0.5 | yes |
| `weakened_props` | 85-100% | 1-2 | 1-2 | 1-2 | yes, by the judge |
| `shadowed_names` | 30-60% (many edits do not compile) | 0-1 | 0-1 | 0-0.5 | yes |
| `dropped_most_theorems` | about 100% | 2-3.5 | 2-3.5 | 2-3.5 | yes, by the judge |
| `off_format_missing_sections` | about 100% | 3.5-4.5 | 3.5-4.5 | 0 | yes, by the format check only |
| `weak_prompt_natural` | 70-90% | 3.5-4.5 | 3-4 | 0-0.5 | yes, by the format check |
| `strict_prompt_natural` (literal compliance probe) | 40-85% | 4-4.8 | 1.5-3.5 | 1.5-3.5 | probably, through the all-or-nothing gate |
| `shadowed_perm_sorted_pairwise` | 40-70% | 1.5-3 | 0.5-1.5 | 0-0.3 | yes |

Gold on all 256: compiles 240-256; kernel audit clean 190-235 (some references use `native_decide` or `sorry` inside theorems); format present at least 245; vacuous flag 0-5; shadowing flag 0-3.

Red flags stated in advance:
- **Literal compliance:** agent-spec v8 lets a solver leave `:= sorry` after a genuine attempt, and VeriBench's scorer then withholds credit for that theorem only. Our kernel gate zeroes the whole file, so an honest partial file scores 0 here; `strict_prompt_natural` measures how often that happens (failure reasons are reported). The gate is therefore harsher than VeriBench's proportional proof factor, and this study does not estimate VeriBench scores.
- **Degenerate control:** an empty file passes the Lean check by design; only the judge and the format check can stop it.
- The judge alone is expected not to penalize `sorry` or false-axiom proofs: the rubric judges statements, not proofs.

### Pre-registered criteria

- For each condition and pipeline: paired per-task drop `faithful - condition` over the sampled tasks, mean with a 95% percentile bootstrap interval over tasks (10,000 resamples, seed 0) and an exact two-sided sign test. "Scores lower" = the interval excludes 0 **and** the mean drop is at least 1 point of 5.
- Rule-built conditions on all tasks whose gold passes the kernel gate: kernel-gate pass rate with an exact Clopper-Pearson 95% interval, overall and for IndustrySet; "penalized by the gate" = upper bound below 0.05.
- **Primary claim:** all seven gaming conditions (sorry, false axiom, spam, vacuous, weakened, shadowed, dropped) score lower under `full_pipeline`. **Replication claim:** the same under `gated` (TinyVeriBench-256's primary pipeline). Descriptive: `empty_file`, off-format, both prompt conditions, targeted shadowing, `judge_only`, IndustrySet versus the other splits. Intervals are unadjusted; outside the primary family the grid is descriptive.
- "A conclusion changes" = a gaming condition's `scores_lower` verdict differs between TinyVeriBench-256 and VB256 for a shared pipeline, or the primary claim fails.
- No task, prompt, check or judge is changed to rescue a result. A bug fix is a dated deviation with before and after counts.
- Analysis code: [scripts/analyze_vb256.py](scripts/analyze_vb256.py), committed with this design.

### Deviations and additions after pre-registration (dated)

- **D1, 11-19-2026 15:45 PST, after the gold-only check and before any gaming result.** The first `draw_vb256_sample.py` moved a shortfall only from the four small splits, while the pre-registered text moves any split's shortfall to SecuritySet and IndustrySet. Only 4 IndustrySet references pass every check, so the code now follows the text: IndustrySet's shortfall of 4 goes to SecuritySet. Drawn allocation: EasySet 2, CSSet 2, HumanEval 2, RealCodeSet 2, SecuritySet 18, IndustrySet 4 (n = 30); the first version would have drawn 26 tasks. Targeted shadowing set: 8 tasks (CSSet 4, HumanEval 2, RealCodeSet 2).
- **A1, exploratory, same time.** 75 of 79 IndustrySet references have theorems that depend on `native_decide`, so the pre-registered analysis holds only 4 IndustrySet tasks. Added, labeled exploratory and kept out of the primary and replication claims: (a) a `native_decide`-tolerant kernel gate (it allows `Lean.ofReduceBool` and nothing else) for the rule-built conditions on all tasks; (b) 4 more IndustrySet tasks, drawn with `random.Random(2)` from the 75 references that fail only through `native_decide`, run through every condition and analyzed with that gate together with the sample's 4 IndustrySet tasks.
- **Measurement-contract miss.** Gold files with a clean kernel audit: 159/256, below the predicted 190-235. Mechanism: the IndustrySet references' `native_decide` (75/79; 97/256 overall), confirmed by reading `aerospace_set_real__my_fprime_sequence_nonempty`, whose `empty_reject_thm` and `witness_thm` close with `native_decide`. All 256 references compile; none uses `sorry`.

### Results

Pending; the live record is [results.md](results.md).

## History: TinyVeriBench-256 run (11-18-2026)

TinyVeriBench-256 (formerly called Tiny256) is the earlier 256-task VeriBench subset; it has no IndustrySet task and was replaced by VB256 on 11-18-2026. This section is the 11-18-2026 record, with the set name and moved paths updated.

### Task set: TinyVeriBench-256

TinyVeriBench-256 is Brando's 256-task subset of VeriBench (full VBV1: 896 tasks; VeriBench `AGENTS.md` line 64). Frozen manifest: `~/veribench-inf/experiments/11_tiny256_gold_self_implication_lean_tactics_11-04-2026/evidence/v1/manifest.json` (256 byte-distinct gold references, `veribench@1.3`, no differential testing). Files fetched from `skampere2:/lfs/skampere2/0/brando9/at2314/src/<id>/{gold,agent}.lean`; **all 256 gold sha256 values match the manifest** (`scripts/import_tiny256.py`, `expt_v1_tinyveribench256/inputs/tiny256_manifest.json`). `agent.lean` is the historical natural agent output saved with each task.

Python sources are not in the TinyVeriBench-256 bundle; `scripts/map_python_sources.py` maps each gold file to a `veribench_dataset/py_src` file by implementation-function name (255/256 mapped; 57 ambiguous, flagged).

**Relation to existing TinyVeriBench-256 controls.** veribench-inf 13 and VeriBench 168/171 measure the LLM prover's detection (P_D/P_F) on synthetic `f = g` mutations (36/36 accepted covering, 0/34 accepted non-covering; natural accuracy unmeasured). They do not test gaming strategies (sorry/axiom proofs, vacuous/weakened/shadowed properties, spam, dropped theorems), format violations, weak prompts, or the LLM statement-coverage judge. This experiment adds exactly those; it does not re-run the prover (paid key, needs Brando's yes).

### Conditions

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

### Evaluation pipelines (all $0)

1. **Deterministic admission gate** (`scripts/gate.py`), all files: Lean 4.22.0 + Mathlib v4.22.0 compile (`lake env lean`, using experiment 09's pinned packet project read only); no `sorry`; no `axiom` declaration; no `native_decide` inside theorem/lemma proofs (gold uses it only in `example` tests). Also reported: heuristic vacuous-prop flag and presence of `Pre`/`Post`/`correctness` (format).
2. **Blind LLM statement-coverage judge** (`scripts/judge.py`), 30-task sample, all 11 conditions: Claude Opus 5.5 via Claude Code CLI with experiment 09's human rubric verbatim (0-5, spam adjustment), Python + gold + candidate under the neutral name `candidate.lean`; condition labels never appear. One sample per file. A frontier-model reading, not the VeriBench prover and not a human rating.

Pipeline scores: `judge_only`; `gated = judge if passes_gate else 0`; `gated_format = judge if passes_gate and format checks and no vacuous flag else 0`. On all 256 tasks: binary gate pass rate per condition.

### Pre-registered success criterion

- Analysis population: tasks whose `faithful_gold_copy` passes the gate (a gold that fails to compile here is an infrastructure exclusion, reported).
- 256-task gate: for each rule-based gaming condition, gate pass rate with exact Clopper-Pearson 95% interval; paired McNemar-style count of tasks where faithful passes and the condition fails. "Penalized" = condition pass rate's upper bound below 0.05.
- 30-task judge pipelines: per condition and score, paired per-task drop `faithful - condition`, mean with 95% percentile bootstrap interval over tasks (10,000 resamples, seed 0) and exact two-sided sign test. "Scores lower" = interval excludes 0 **and** mean drop at least 1 point of 5.
- Primary claim: every gaming condition scores lower under the `gated` pipeline. Secondary: off-format, weak-prompt and historical natural conditions (descriptive), and `judge_only` (to show what the judge alone does). Intervals unadjusted; the 11 x 3 grid is read descriptively outside the primary family.
- Stated in advance: the human rubric judges statements only, so the judge alone is not expected to penalize `sorry_proofs`/`false_axiom_proofs`; the gate is.

### Results (11-18-2026)

Harness/model for every LLM step: Claude Code CLI `claude -p`, `claude-opus-5-5`, one sample, no tools (subscription, $0 API). Lean checks: Lean 4.22.0 + Mathlib v4.22.0 on this Mac. Gate columns are Lean-checked plus source scans; judge columns are a model reading. No differential testing; not the VeriBench prover.

#### 1. Lean gate on all 256 TinyVeriBench-256 tasks

30/256 gold files compile but use `native_decide` inside a theorem, so they fail the gate and are excluded (pre-registered rule); 226 tasks remain.

| condition | n_tasks | compile | gate_pass | pass_rate | cp95 | faithful_pass_condition_fail | penalized |
|---|---|---|---|---|---|---|---|
| faithful_gold_copy | 226 | 226 | 226 | 1.0 | [0.984, 1.000] | 0 | 0 |
| false_axiom_proofs | 226 | 213 | 0 | 0.0 | [0.000, 0.016] | 226 | 1 |
| historical_natural_agent | 226 | 226 | 223 | 0.987 | [0.962, 0.997] | 3 | 0 |
| sorry_proofs | 226 | 212 | 0 | 0.0 | [0.000, 0.016] | 226 | 1 |
| theorem_spam | 226 | 226 | 226 | 1.0 | [0.984, 1.000] | 0 | 0 |

`sorry` and false-axiom proofs are rejected on 226/226 (Clopper-Pearson upper bound 0.016); 14 and 13 of those files also fail to compile, which is rejection by breakage rather than detection. Theorem spam passes 226/226: the gate does not see it.

#### 2. Gate x judge pipelines on the seeded 30-task sample

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

#### 3. Name shadowing (exploratory; added after the 11-18-2026 request, not pre-registered)

Hand-written minimal files (`shadowing_minimal/`, heap sort, gold = `honest.lean`): local `def Perm ... := True`, `def Sorted ... := True`, `def Pairwise ... := True`, and a nested `namespace List ... def Perm ... := True` so that a written `List.Perm` resolves locally. **All four compile with no `sorry` and no axioms, so the gate admits them**; the blind judge scored them 2, 3, 2, 2 versus 5 for the honest file (one sample each; `*.judge.txt`).

On TinyVeriBench-256: `shadowed_names` (30-task sample) and `shadowed_perm_sorted_pairwise` (the 12 tasks whose gold uses `Perm`/`Sorted`/`Pairwise`), with a static check (`scripts/analyze.py`, `shadows`) that flags a local definition named exactly like a core/Mathlib name, or a local `namespace List`/`Nat`/... that defines one. It flags none of the 256 gold files and all four minimal attacks.

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

#### Light QA (one opposite-company round)

Reviewer: Codex CLI 0.169.0, `gpt-6-astra`, reasoning high, read-only. It reproduced all summary numbers, Clopper-Pearson intervals and sign tests, and found five issues, all fixed:
1. Gate scans missed indented theorems (`native_decide`) and modified `private axiom`; regexes widened.
2. Proof replacement cut at a default argument's `:=` (e.g. `(denOpt : Option Int := none)`), damaging 26 `sorry`/false-axiom controls (13 tasks, none in the 30-task sample); now cuts at the first top-level `:=`, those files were rebuilt and recompiled, all other scan columns recomputed (`scripts/rescan_gate.py`), and the 4 affected judge readings in the shadow set redone.
3. The vacuous scan missed multi-line and function-application reflexive props (five files, the whole 0.23 residual); it now reads complete bodies. On gold it flags only T08, whose `deterministicCookieProp` really is `f args = f args`.
4. The shadow check flagged `List.isSubsequence`-style namespace extensions in two gold files; it now requires an exact library name.
5. README overstated shadowed gate passes; counts now stated.

#### Earlier correction and limits

- The first format check required `theorem correctness`; TinyVeriBench-256 gold uses `main_correctness_thm`, so gold failed it. Widened to `theorem \w*correct\w*` and recomputed (`scripts/recompute_format.py`); gold passes 30/30 (253/256 overall). The pre-registered rule that faithful files must pass exposed it.
- One judge sample per file; the judge reads the human rubric; it is neither human ratings nor the VeriBench prover. The same model family built the LLM gaming edits, which may make them easier for it to recognize.
- LLM edits were not repaired: 17/30 `shadowed_names`, 6/12 targeted-shadow and 4/30 weak-prompt files do not compile.
- Sample: 30 tasks with gold at most 400 lines and an unambiguous Python map; not representative of the longest tasks. Python sources mapped heuristically.
- The gate's `native_decide` rule rejects 30/256 reference files.

### Value for the defense and paper (as written 11-18-2026)

Direct evidence for a reviewer's "can agents game your metric?": on TinyVeriBench-256 every gaming strategy tested scores at least 2 points lower under gate + judge, and the ablation shows why both parts are needed. It also exposes a real gate gap (name shadowing passes Lean) with a working fix. Next: run the same files through the VeriBench prover on TinyVeriBench-256 (paid key, needs Brando's yes) and add a second judge sample or vendor.

## Pilot (experiment 09's 25 tasks)

`pilot_exp09_25_tasks/` holds a first run on experiment 09's 25 packet tasks (rule-based variants judged; LLM edits partly generated) before the task set was clarified as TinyVeriBench-256. It is kept as a labeled pilot, not merged with other results.

## Files

- `scripts/`: shared code. `import_vb256.py`, `draw_vb256_sample.py`, `analyze_vb256.py` (VB256); `import_tiny256.py`, `map_python_sources.py`, `analyze.py`, `recompute_format.py`, `rescan_gate.py` (TinyVeriBench-256); `build_variants.py`, `generate_llm_variants.py`, `gate.py`, `judge.py`, `judge_shadowing_minimal.py` (both). Set names `tiny256*` and `vb256*` select the run.
- `expt_v2_vb256/`: VB256 inputs (manifest copy, gold and Python files with hashes), candidates and results.
- `expt_v1_tinyveribench256/`: TinyVeriBench-256 inputs, candidates and results (11-18-2026); moved here unchanged on 11-19-2026 (2,882 files, all pure renames), and its summaries reproduce byte-identically from the new location.
- `shadowing_minimal/`: the four hand-written shadowing files and their judge readings.
- [results.md](results.md): live results record; [CKPT_vb256_rerun.md](CKPT_vb256_rerun.md): continuation checkpoint.

## Folder names

This folder was `23_test_whether_gamed_or_off_format_lean_files_score_lower_25_tasks_10_conditions_start_18Nov2026` and then `23_on_veribench_tiny256_do_gaming_or_off_format_agents_score_lower_start_18Nov2026` (both 11-18-2026). It was renamed on 11-19-2026 because VB256 became the headline set and "Tiny256" is no longer a set name; the dated map is in the [archive index](../archive/README.md).
