# Pre-registration, experiment 24 (written 11-24-2026, before any judge call of this experiment)

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/24_does_the_fsc_judge_anchor_on_which_equivalent_gold_reference_it_sees_tinyveribench256_60_tasks_start_24Nov2026/PREREG.md>

**TLDR:** Test, on the part of VeriBench formal specification coverage (FSC) that uses an LLM judge, whether the judge's coverage score depends on *which equivalent gold reference it is shown* (the reference-anchoring hypothesis of Sri's paper), with frontier judges, one prompt for every judge, 60 TinyVeriBench-256 tasks. Nothing below is changed after the first judge call without a dated deviation.

## 1. Hypothesis (from the paper, one sentence)

Source: `papers/AAAI27/main.pdf` ("One Answer Key, Many Correct Answers: LLM Judges Penalize Valid Answers That Differ from the Reference"), read through the synced fork `brando90/judge-reference-anchoring` at commit e2f4ce7, and its experiment-1 spec.

> When a valid response is graded against a reference, an LLM judge gives it a higher grade if the shown reference matches the response than if the shown reference is a different but equally valid one, even when the rubric says other answers may be valid.

The paper's primary metric is the reference-alignment effect AG = mean grade under the matching reference minus mean grade under another valid reference, same candidate, same judge, same prompt; it also compares both with blind (no reference) grading to split a boost for matching references from a penalty for differing ones. Its effects: 0.21 to 0.85 grade points on factual questions, up to 0.54 on math, on a 1 to 5 scale.

**FSC version.** The FSC judge (experiment 09's human rubric, 0 to 5, shown the Python source, a gold Lean file and a candidate Lean file) already says a gold theorem counts as covered by "the same theorem, or a logically equivalent theorem, or a stronger theorem implying the gold theorem". So two gold files that state the same obligations differently are both valid references, and a candidate that covers one fully covers the other. Anchoring on FSC = the judge scores a fixed candidate higher against the reference whose *form* is closer to the candidate than against the equivalent reference whose form differs. A judge that follows the rubric shows AG = 0.

Different from the paper, and stated up front: in FSC the reference is the *target* of the judgment (coverage is relative to it), so dependence on a **non-equivalent** reference is correct behavior. Only dependence on the form of an **equivalent** reference is anchoring. Arm D below checks that the judge does react to non-equivalent references.

## 2. Judges, harness, prompt

- Judges: `claude-opus-5-5` (Claude Code CLI) and `gpt-6-astra` (Codex CLI), through Brando's plan router on skampere1, text only, no tools, one sample per cell, default effort of the lane (gpt-6-astra: high). Lane order: Stanford and Vals lanes first, personal lanes only when those are gated or out of included usage; no agy; no paid API; no extra charges. Every call records the lane, model and receipt. Frontier models only (AGENTS.md, 11-14-2026); small open judges (Qwen, phi-4 as in the paper) are out of scope under that rule and are named as a limit.
- Prompt, identical for every judge and cell: experiment 23's blind coverage judge, i.e. experiment 09's rubric verbatim (everything before "## Output format"), then `## Python source`, `## Gold Lean file`, `## Agent Lean file (candidate.lean)`, then the JSON tail (A, B, C, D, `final_score_0_5`, one-sentence rationale). Condition labels never appear. The only cell-dependent text is the content of the two Lean files. In the **no-reference** cells the "Gold Lean file" section is replaced by the fixed sentence "(No gold Lean file is provided for this problem. Judge coverage of the specifications that the Python source implies.)".
- A reply without parseable JSON is asked once more and recorded; a second failure is a missing cell (counted, never imputed).

## 3. Materials (all built before any judge call; none reads a judge output)

Tasks: 60 TinyVeriBench-256 tasks (`inputs/tasks.json`): the 30 of experiment 23's `llm_sample` that pass the filter plus 30 more by `random.Random(24)`. Filter: faithful gold copy passes the experiment 23 gate (compiles, no sorry, no axiom, no native_decide) and the saved historical natural agent file compiles and is non-empty (225 tasks qualify). Pipeline label: **no DT** (no differential-testing acceptance is applied to these references; they are VeriBench v1 gold files).

- **G**: the gold file with every theorem proof replaced by `sorry` (experiment 23's `replace_proofs`). Reference and candidate files carry no proofs so that proof presence cannot differ between conditions; the rubric judges statements only. The statements (theorems, `*_prop` definitions, Post, Pre) are unchanged and checked to be byte-identical to the original after whitespace normalization.
- **G'x** (x = gpt or claude): an alternative reference written by gpt-6-astra (`G'gpt`) and by claude-opus-5-5 (`G'claude`) from the Python source and G: every property restated in a logically equivalent but structurally different form (different representation or quantification), same implementation, same Pre, same number of theorems, same weights, proofs `sorry`. **Admission gates** (G'x is used only if all pass): (1) compiles in the VeriBench Lean environment (`lake env lean`, warnings for `sorry` only); (2) same theorem count and same theorem names as G, statement similarity to G (difflib ratio of the normalized statement text, `scripts/lean_utils.py`) at most 0.85, and at least half of G's `*_prop` definitions changed (normalized text differs); (3) the *other* family audits each theorem as "equivalent" (verdicts: equivalent, stronger, weaker, different; the auditor sees the Python source, G and G'x), and every theorem is "equivalent". A task whose G'x fails is dropped for that judge; counts reported. Exploratory, not a gate: a Lean proof of `G prop ↔ G' prop` per theorem for as many tasks as time allows, reported as the certified fraction.
- **Cross-family rule:** the judge `claude-opus-5-5` is shown `G'gpt`, the judge `gpt-6-astra` is shown `G'claude`, so no judge grades text it wrote; the other G' of each task is the secondary "own-family" contrast.
- **N**: the saved historical natural agent file, proofs replaced by `sorry` the same way (independent of G and G').
- **Gsk, G'sk** as candidates: G and G'x themselves (twin candidates; each fully covers both references by construction).
- **H**: half-coverage candidate and perturbed reference: the gold file reduced by gpt-6-astra to the first half of its properties (Post and the correctness theorem mention only those); compile-gated. Used as a partial candidate (arm C) and as a weakened reference (arm D).
- **Gother**: G of the next task in `tasks.json` (cyclic), a mismatched reference.

## 4. Arms and cells (per judge, per task, one sample)

| Arm | Candidate | Reference shown | Cells |
|---|---|---|---|
| B twins (exact matching) | G, G'x | G, G'x, none | 6 |
| A natural (similarity matching) | N | G, G'x, G'own, none | 4 |
| C partial | H | G, G'x, none | 3 |
| D perturbed reference | N | H, Gother | 2 |

15 cells per task and judge, 900 calls per judge for 60 tasks. Judges are shown cells in a seeded random order; one task's cells are independent calls.

## 5. Estimands and decision rules (scores are 0 to 5; unit = task; 95% percentile bootstrap over tasks, 10,000 resamples, seed 0; paired by task; no multiplicity adjustment)

- **Primary, AG_B (twins, exact matching):** per task d = [s(G|G) + s(G'x|G'x) - s(G|G'x) - s(G'x|G)] / 2.
- **Co-primary, AG_A (natural candidate, similarity matching):** per task, the reference of {G, G'x} with the higher statement similarity to N is "closer" (similarity = difflib ratio of whitespace-normalized, comment-stripped statement text: theorem and `*_prop` declarations; computed before judging; ties dropped); d = s(N|closer) - s(N|farther).
- **Verdict per judge, on AG_B and on AG_A separately:** HOLDS if the interval's lower end is above 0 and the mean is at least 0.20 (the paper's lowest reported effect); DOES NOT HOLD if the whole interval lies inside (-0.15, +0.15); otherwise INCONCLUSIVE. **Overall verdict on FSC:** yes = HOLDS on AG_B for both judges; no = DOES NOT HOLD on AG_B for both judges; anything else = inconclusive, with the per-judge, per-arm table.
- **Secondary:** boost = s(match) - s(none) and penalty = s(differ) - s(none), arms A and B; own-family contrast (G'own vs G'x, arm A); gap of arm C (s(N|ref) - s(H|ref)) under each reference (does the reference change the judge's ability to separate full from partial coverage); score distributions and the share of exact 5s (ceiling check; a ceiling is reported, not corrected).
- **Manipulation checks (not tests of the hypothesis):** arm D, s(N|G) - s(N|H) and s(N|G) - s(N|Gother), expected clearly above 0 because those references are not equivalent; literal-copy cells (G|G and G'x|G'x) expected near 5. If a check fails, the arm that depends on it is reported as not interpretable.
- Not applicable here: int_ref (the vb-priv prover metric) and any correlation with human ratings; this experiment measures score contrasts of a judge under reference changes only.

## 6. Stopping and deviations

- Attrition at each gate is reported with task ids. If fewer than 40 tasks pass all gates for a judge, the experiment adds tasks from the remaining qualifying 165 (same rule, `random.Random(24)` order) until 60 or the pool ends.
- If scores are within 0.1 of the ceiling in more than 90% of matching cells, a harder second sample (tasks where N scored below 5 in a blind cell) is a labeled exploratory add-on.
- No task, prompt, gate or judge is changed to rescue a result. A bug fix is a dated deviation with counts before and after. The analysis script is committed before the first judge call.
- Repeats: one sample per cell. If the verdict is inconclusive and the interval is wider than 0.3, a second and third sample of every cell are run (same prompts) and the verdict is recomputed on the means; the added samples are labeled.

## 7. Limits stated in advance

Two frontier judges only (no open judges, by the repo's rule); G' is model-written and its equivalence rests on a compile gate and a cross-family audit, not on a Lean proof for every theorem; arm A's "closer" is a text-similarity proxy; TinyVeriBench-256 historical natural agents score near the ceiling on a blind judge (exp 23: mean 4.93 of 5 on the 30-task sample), which limits what a penalty on N can show and is why the twin arm B is primary; results describe these judges on this prompt and these 60 tasks, not FSC judges in general.

## Amendment 1 (2026-11-24 10:05 PST, before any judge call of this experiment; gate generation and audit calls had started, they are not judge calls)

Brando's 2026-11-24 09:51 message asked for the question "how do the findings of this paper apply to VeriBench FSC with an LLM judge?" as four cells: (1) open weights, (i) a single LLM call with prompt engineering, (ii) with harness engineering; (2) frontier agents, (i) the same single LLM call, (ii) with harness engineering. His words override the frontier-only default of section 2 for this experiment. Changes:

- **Judge settings (2 x 2):**
  - open weights, single call: DeepSeek V4.1 Flash 1017 (`deepseek`) and Kimi K3 (`kimi`) through the Stanford AI gateway (STAIR bm key), temperature 0, 8,000 output tokens, no tools; all 60 tasks, all four arms (as section 4);
  - open weights, harness: DeepSeek V4.1 Flash 1017 as a Pi agent with read and shell tools in a per-call workspace (`agent_deepseek`);
  - frontier, single call: `claude-opus-5-5` (Claude Code CLI, text only) and `gpt-6-astra` (Codex CLI, text only), as in section 2;
  - frontier, harness: `gpt-6-astra` as a Codex CLI agent (`agent_codex`), workspace-write sandbox, same files and tools as the Pi agent. A Claude Code agent cell is added only if its Stanford or Vals lane opens in time, as a labeled add-on.
- **Harness cells:** the agent gets a directory with `source.py`, `candidate.lean`, `gold.lean` (absent in no-reference cells) and `check.sh <file>` (compiles a Lean file in the VeriBench Lean environment and prints errors), and may read files and run shell commands. The rubric text and JSON tail are identical to the single-call prompt; the only differences are that the files are named by path instead of pasted and a short header lists the tools. Harness cells run on the first 20 tasks of `inputs/tasks.json` that pass the gates for that judge, arms B and A only (10 cells per task, 200 calls per harness judge); the harness cells are therefore a smaller sample and their intervals are wider.
- **G' for the new judges:** `deepseek`, `kimi` and `agent_deepseek` are shown `G'gpt` (written by gpt-6-astra, audited by claude-opus-5-5); `agent_codex` is shown `G'claude`. `G'own` cells (arm A) exist only for `claude` and `codex`.
- **Decision rules** (section 5) apply per judge setting unchanged. **Headline verdict on FSC:** yes = HOLDS on AG_B in every judge setting that ran; no = DOES NOT HOLD on AG_B in every one; anything else = mixed or inconclusive, reported as the 2 x 2 table (open or frontier, single call or harness) with each judge's interval. Settings are never pooled across the two harness types or the two model groups.
- **Gateway spend:** the gateway reports a cost per call; the run stops at an estimated USD 15 in total for this experiment (open-weight calls are cents per call), recorded in a ledger; calls refused with a rate limit are retried with back-off and counted. Frontier calls go through the plan router as in section 2 (Stanford and Vals lanes first, no agy, no paid API).
- Everything else (materials, gates, estimands, bootstrap, limits) is unchanged. Added limits: DeepSeek and Kimi are two open families only (the paper's Qwen, phi-4 and Llama-3.3 are not used; Llama 4 is never used); the harness comparison confounds model and harness within a column, so it shows whether adding a harness changes the effect for that model, not which harness is better.
