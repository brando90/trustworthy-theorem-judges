<!-- TLDR: Experiment 110's VBV2 condition result: VeriBench V2 frontier-model outputs scored by the H2 FSC judge fall inside the judge's human-rated validation pool on 11/15 pre-registered criteria [8-11] ("partially in-distribution"); they differ by size and completeness, not on the one criterion linked to judge error; zero model calls, no FSC values. -->
**A (TLDR):** On VeriBench V2 (VBV2) the FSC judge is about as far from its validation data as on VeriBench V1. Pooled VBV2 frontier-model outputs fall inside the judge's human-rated validation pool on **11/15 pre-registered criteria [95% interval 8–11]**, the "partially in-distribution" range (VBV1 frontier models: 8/15 [7–10]). They differ in size and completeness, not on the one criterion linked to judge error, but no human has rated a VBV2 output, so the judge is still not validated on VBV2.

# FSC judge transfer to VeriBench V2: experiment 110's VBV2 condition

**Doc link:** <https://github.com/brando90/veribench/blob/main/experiments/110_fsc_judge_transfer_frontier_outputs_vs_human_rated_pool/vbv2_condition/RESULTS_judge_transfer_vbv2.md>

**Setup:**
- **Judge:** the H2 FSC (formal specification coverage) judge of experiment 100, GPT-6 Sol high + Claude Opus 5.5 max. It was validated on 75 human-rated VBV1 items, which are Claude 3.7 Sonnet outputs.
- **Data:** every VBV2 frontier-model output that the judge scored in experiment `103_single_call_baselines_all_models_vbv1_vbv2_valkyrie_validated_fsc_judge`. These are 26 candidates on 5 VBV2 full-source tasks (bst, const_fold, execute, imp_compiler, lower).
- **What was compared:** the exact candidate, reference and Python text the judge read.
- **Method:** the 15 deterministic criteria of [experiment 110](../README.md), with its frozen extractor and analysis functions, imported unmodified (SHA-256 checked).
- **Pre-registration:** [CRITERIA_VBV2.md](CRITERIA_VBV2.md), committed in `f1bfbe3564` before any VBV2 value was computed.
- **Cost:** zero model calls.

**Trigger:** Brando's weekly-notes task of 10-09-2026, "vbv2 - doing FSC coverage with the 0.6 0.8 0.8 judge we have & a FM <> Claude Sonnet 3.7 k/15 comparison to be able to (summarize) how 'trustworthy' this judge is to out of sample eval data".

## Hypothesis and instrument

- **Question:** do VBV2 frontier-model (FM) outputs look like the items the FSC judge was validated on? Measured as the number k of 15 criteria on which they are in-distribution (FM median inside the pool's [P5, P95] and at least 70% of FM files inside it).
- **Instrument:** the H2 judge.
  - Agreement with human ratings: test-split Spearman 0.826 [0.32, 0.97] on 30 items from 10 tasks (experiment 100's one-shot test receipt, as quoted in experiment 110). This is the "0.6 0.8 0.8" judge of the task.
  - It was selected on the validation split and tested once on the test split. All of that is on VBV1 Claude 3.7 Sonnet outputs.
- **Pre-declared labels:** k ≥ 12 "mostly in-distribution", 8–11 "partially", ≤ 7 "substantially shifted".
- **Pre-declared prediction:** k ≤ 7, with file length, definitions, statement count and tests out of distribution.

## Results

| Condition | Files / tasks | k/15 [95% interval, 10,000 draws] | Strict KS rule | Out of distribution | Missing outputs counted outside |
|---|---|---|---|---|---|
| **Primary: pooled VBV2 FM, experiment 103 (single call + Terminus 2 GPT-6 Luna)** | **26 / 5** | **11/15 [8–11]** | 4/15 | C1 length, C2 definitions, C3 statement count, C10 hole rate | 8/15 (7 FM cells without a judged candidate, 5 of them Claude Opus 5) |
| Experiment 103 single call Gemini 3.1 Pro | 4 / 4 | 11/15 [8–12] | 2/15 | C1, C2, C3, C10 | 10/15 (1 missing) |
| Experiment 103 single call GPT-5.6 Luna | 5 / 5 | 10/15 [7–11] | 3/15 | C1, C2, C3, C10, C12 | — |
| Experiment 103 single call GPT-5.6 Sol | 5 / 5 | 10/15 [7–11] | 2/15 | C1, C2, C3, C9, C10 | — |
| Experiment 103 single call GPT-6 Astra | 4 / 4 | 9/15 [7–11] | 0/15 | C1, C2, C3, C9, C10, **C13** | 7/15 (1 missing) |
| Experiment 103 single call GPT-6 Luna | 5 / 5 | 11/15 [9–12] | 3/15 | C1, C2, C3, C10 | — |
| Experiment 103 Terminus 2 + GPT-6 Luna (experiment 96 captures) | 3 / 3 | 10/15 [7–11] | 0/15 | C1, C2, C3, C10, J1 | — |
| Experiment 103 single call Claude Opus 5 | 0 / 0 | — | — | no completion on any VBV2 task | 5 cells missing |
| Experiment 103 recovery_1 (2 files; descriptive, no interval) | 2 / 1 | 9/15 | 2/15 | C1, C2, C3, C9, C10, **C13** | — |
| Qwen3.6 27B single call (not FM; 2 files; descriptive) | 2 / 2 | 7/15 | 1/15 | C1, C2, C3, C5, C7, C9, C10, J1 | 0/15 (3 missing) |
| Secondary (amendment V-A1): experiment 100 phase 7, original packaging, pooled FM | 33 / 6 | 8/15 [6–11] | 3/15 | C1, C2, C3, C9, C10, C12, **C13** | — |
| Secondary (amendment V-A1): experiment 100 phase 7, reference-scoped packaging, pooled FM | 30 / 5 | 10/15 [6–11] | 2/15 | C1, C2, C3, C10, C12 | — |
| *Experiment 110, VBV1 pooled FM (for comparison)* | *8,106 / 896* | *8/15 [7–10]* | *2/15* | *C1, C2, C3, C4, C9, C10, C12* | |

Intervals are task-cluster bootstrap percentiles over pool tasks (25) and VBV2 tasks (5 or 6), resampled independently (seed 20261009); the 2,000 pre-registered draws give the same intervals for the primary set. p-val=n/a (descriptive, no test). Criteria C6, C8 and C11 cannot fail (the pool already spans their range), so the informative count for the primary set is 8/12.

**Where the primary set leaves the pool** (pool median [P5, P95] → VBV2 median; share of VBV2 files inside the pool interval):
- **C1, file length:** 47 lines [22, 106] → 360.5; 0%.
- **C2, definitions:** 5 [3, 14] → 35.5; 0%.
- **C3, statement count:** 1 [1, 4] → 15.5; 0%.
- **C10, hole rate:** 1.0 (nearly every pool theorem is `sorry`) → 0 (fully proved); 0%.

**In distribution:**
- **Statement shape:** length, quantified, conditional and ground-instance fractions.
- **Scaffold and tests:** the pre/post scaffold and executable tests.
- **Fit to the reference:** lexical overlap with the reference, and statement count relative to it.
- **Judge self-consistency:** J1 (repeat spread) and J2 (member disagreement). The judge is as stable on VBV2 projects as on its validation items.

## Verdict

- **Pre-declared prediction refuted.** Pooled VBV2 FM outputs are **partially in-distribution, 11/15 [8–11]**, not substantially shifted.
- **Which criteria shift.** The shifts are size and completeness: VBV2 outputs are 7–15 times larger and fully proved, where the pool is short and `sorry`-heavy.
- **No shifted criterion is linked to judge error.** Experiment 110 found none of the four shifted criteria error-relevant on the pool.
- **The one error-linked criterion stays in distribution.** That is C13, statement count relative to the reference: Spearman with judge error −0.601 [−0.759, −0.343] on all 75 items (experiment 110, which read all three splits; this condition reads no human ratings). It is out of distribution only for GPT-6 Astra (4 files), the recovery pass (2 files) and phase 7's original packaging.
- **Comparison with VBV1.** The VBV2 result is no worse than the VBV1 frontier-model result (8/15 [7–10]).

**What this does not establish.** Judge–human agreement on VBV2 is unmeasured: no VBV2 output has a human rating, and the pool's error correlations rest on 25 VBV1 tasks. The VBV2 side has 5 tasks, so the claim covers these 5 tasks only, and VBV2.1 (experiment `99_vbv2_1_hardest_vsb_developments_to_python_tasks`) has no solver outputs yet. Unmeasured features (semantic correctness of statements, proof style, task difficulty) can still shift.

## What to write next to a VBV2 FSC number

> FSC uses the H2 judge validated on VBV1 human ratings (test-split Spearman 0.826 [0.32, 0.97], 10 tasks). On VBV2 its inputs are partially in-distribution relative to the validation pool: 11 of 15 pre-registered criteria [8–11]. VBV2 files are larger and fully proved, but they match the pool on the one criterion linked to judge error. The judge is not human-validated on VBV2.

**Next step [p 7/10]:** collect human ratings on a small VBV2 sample (for example 5 tasks × 2 frontier models) for a direct judge–human agreement number. This is the only measurement that turns the caveat into a validation. Re-run this condition unchanged on VBV2.1 outputs when experiment 99 produces them.

## Data checks

- **Frozen code verified:** `analyze.py` `d33b23b5…` and `extract_criteria.py` `d72481b8…` are byte-identical to experiment 110's.
- **Pool reproduces:** 3 seeded pool rows recomputed exactly, and the recomputed pool null distribution equals experiment 110's for every criterion.
- **Texts are what the judge read:** they were cut from the rendered prompts. All 3 repeat packs per cell carried byte-identical texts (0 problems over 30 cells), and J1/J2 are complete for all 30 primary cells (every delivered prompt hash matched).
- **Main-function parser coverage:** no Lean match for the Python main function in 15/25 single-call, 2/3 Terminus 2 and 2/2 recovery candidates. C11 is one of the criteria that cannot fail, so this does not move k.
- **Amendment V-A1 (10-09-2026, reported beside the primary result):** experiment 100's phase-7 cells have their exact judge inputs on disk, but not the rendered prompt bytes. They were analyzed as a separately labelled secondary source and never pooled with the primary set. J1/J2 are available for 20 cells in each packaging. Their policy-rejected and prompt-confound flags were not read, because they sit beside FSC values.
- **Blinding:** no FSC level, per-item score or mean judge score was computed into or written to any file here. Private texts and per-item rows stay on SNAP at `/dfs/scratch0/brando9/vb110_vbv2/` (mode 700).

Machine-readable result: [`results/results_vbv2.json`](results/results_vbv2.json). Scripts: [`scripts/gather_vbv2_on_snap.py`](scripts/gather_vbv2_on_snap.py), [`scripts/analyze_vbv2.py`](scripts/analyze_vbv2.py).

**TLDR-end:** [vb: experiment 110 VBV2 condition, FSC judge transfer to VeriBench V2] VBV2 frontier-model outputs are partially in-distribution for the H2 judge (11/15 [8–11]), as close to its validation pool as VBV1's are. Only human ratings of VBV2 outputs can validate the judge there.
