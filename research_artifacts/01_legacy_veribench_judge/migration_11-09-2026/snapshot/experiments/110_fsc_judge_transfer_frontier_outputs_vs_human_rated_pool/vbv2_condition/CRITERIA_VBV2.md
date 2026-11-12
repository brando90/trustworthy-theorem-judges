<!-- TLDR: Pre-registration (10-09-2026, written before any VBV2 criterion value was computed) of experiment 110's separately labelled VBV2 condition: the same 15 frozen criteria, applied to VeriBench V2 frontier-model outputs that the H2 FSC judge scored, against the same 75-item human-rated VBV1 pool. -->

# Experiment 110, VBV2 condition: does the FSC judge's validation pool resemble VeriBench V2 frontier-model outputs?

**Written:** 10-09-2026 ~15:40 PDT, before any criterion value was computed on a VeriBench V2 (VBV2) file.
**Trigger:** Brando's weekly-notes task of 10-09-2026: "vbv2 - doing FSC coverage with the 0.6 0.8 0.8 judge we have & a FM <> Claude Sonnet 3.7 k/15 comparison to be able to (summarize) how 'trustworthy' this judge is to out of sample eval data".
Experiment 110's own pre-registration put VBV2 out of scope for its primary claim and allowed it only as "a separately labeled condition" ([CRITERIA.md](../CRITERIA.md) section 1); this file is that condition.
**Freeze rule:** as in CRITERIA.md. This file and the hashes of the frozen extractor and of the VBV2 scripts are recorded in the first results commit; any later change is a dated amendment reported beside the pre-registered result.
**No model calls.** Every quantity comes from existing files and existing judge records.
**Disclosure:** while checking the judge-prompt format, the author saw the line numbers of the three prompt sections of one VBV2 pack item (`gemini_3.1_pro_high__bst`, repeat 1): Python source about 50 lines, reference about 357 lines, candidate about 272 lines. No other VBV2 file content or criterion value was looked at.

## 1. What is compared

- **Judge under study:** unchanged, the H2 ensemble of experiment 100 (GPT-6 Sol high + Claude Opus 5.5 max, median of 3 repeats per member, mean of members, divided by 5).
- **Pool (P):** unchanged, the 75 human-rated items (25 VBV1 tasks x 3 Claude 3.7 Sonnet May-2026 outputs), all splits, with the features experiment 110 computed and committed in `../results/features.jsonl.gz` (rows with `cond == "POOL"`). Before use, at least 3 pool rows chosen by `random.Random(20261009)` are recomputed with the frozen extractor and must match exactly; any mismatch stops the analysis.
- **VBV2 frontier-model set (F2):** every VBV2 candidate project that has an H2 judge record and whose rendered judge prompt is on disk:
  - experiment 103 suite `vbv2` (single-call baselines, VBV2 full-source tasks), packs `private/packs/judge_vbv2/`, harvests `private/judge/harvests/cells_vbv2__H2_*.json`;
  - experiment 103 suite `vbv2_recovery_1` (its separately labelled recovery pass), packs `judge_vbv2_recovery_1/`;
  - experiment 103 suite `vbv2_agent96` (experiment 96's Terminus 2 + GPT-6 Luna captures), packs `judge_vbv2_agent96/`;
  - experiment 100 phase 7 VBV2 cells, if their rendered prompts are on disk; otherwise they are listed as unavailable with the reason, never substituted.
  The gather step writes the exact manifest (source, model, task, repeat files, candidate SHA-256) before any criterion is computed.
  Qwen3.6 27B is not a frontier model; as in experiment 110 it is analyzed separately as a comparison and excluded from the pooled FM set.
- **Texts used:** exactly what the judge read. From the rendered prompt between `=== VB103_JUDGE_USER_BEGIN ===` and `=== VB103_JUDGE_USER_END ===`:
  - candidate = section `## 3. Agent Lean file: …`;
  - reference = section `## 2. Gold Lean file: …`;
  - Python = section `## 1. Python source: …`.
  Enclosing Markdown code fences are removed; nothing else is changed. The three repeat packs of one cell must carry byte-identical candidate, reference and Python text; a cell whose repeats differ is reported and excluded.
- **Unit and clusters:** one candidate per (source, model, task). Bootstrap clusters are VBV2 tasks.
- **Comparisons:**
  - **Primary:** pooled F2 (all frontier-model VBV2 candidates).
  - **Per condition:** each source x model with at least 3 candidates, reported descriptively.
  - **Matched-task comparison:** not possible (no VBV2 task is in the pool); reported as not applicable.

## 2. Criteria, rules and aggregation

Unchanged from CRITERIA.md sections 2-5:
- **Extractor:** the same frozen `../scripts/extract_criteria.py`, with its SHA-256 checked against the value in experiment 110's results before use. Its interpretation list and amendment A1 apply unchanged.
- **Criteria:** the 15 criteria C1-C13, J1 and J2.
- **Rules:** the primary in-distribution rule (pool [P5, P95], median inside, coverage at least 0.70); the strict KS rule with the same pool-internal null (2,000 splits, seed 20261009); sensitivity at 0.60 and 0.80.
- **Uncertainty:** task-cluster bootstrap with 2,000 pre-registered draws plus 10,000, seed 20261009, pool and VBV2 tasks resampled independently, using `../scripts/analyze.py`'s own functions, imported unmodified.
- **Labels:** k >= 12/15 "mostly in-distribution"; 8-11 "partially in-distribution"; <= 7 "substantially shifted".
- **J1/J2:** computed from experiment 103's harvested H2 repeats only when every repeat's delivered prompt SHA-256 equals the expected one and both members have 3 measured repeats; otherwise unavailable for that candidate. If unavailable for the whole set, k is reported over 13.
- **Main function:** experiment 110's rule (step 5 and amendment A1) applied to the Python section the judge saw. VBV2 sources are larger programs, so the gather step reports how many candidates have no main-function match (parser coverage, not hidden).
- **Low power:** VBV2 full-source has about 5 tasks, so the VBV2 side of the bootstrap has about 5 clusters. Intervals will be wide; the claim is about these tasks only.

## 3. Pre-declared prediction (recorded so the result can be seen to confirm or refute it)

VBV2 candidates are long multi-module projects with many definitions, theorems and tests, unlike the short, `sorry`-heavy pool. The author predicts pooled F2 at **k <= 7 ("substantially shifted")**, with C1 (length), C2 (definitions), C3 (statement count) and C9 (tests) out of distribution.

## 4. Blinding (binding)

Brando is a blinded rater in experiment 102's round. VBV2 FSC values from experiment 103 therefore stay out of anything he reads.
- No FSC level, per-item judge score, mean judge score or score-level diagnostic is written to a public file or chat.
- J1 and J2 are spread and disagreement statistics of the repeats and are reported only as criteria, as in experiment 110.
- Private texts (VBV2 references are private) and per-item rows stay on SNAP under `/dfs/scratch0/brando9/vb110_vbv2/` (mode 700). The repository receives only aggregate criterion statistics and hashes.

## 5. How the result will be used

- **If k <= 7:** FSC on VBV2 (and VBV2.1, experiment 99) carries an explicit "transferred, substantially shifted from the judge's validation pool" caveat next to every number. The out-of-distribution criteria are named, together with whether experiment 110 found each one error-relevant on the pool.
- **If 8-11:** "partially in-distribution", with the same naming.
- **In every case:** only human ratings of VBV2 outputs can validate the judge on VBV2; this condition quantifies the size of the transfer gap and does not close it.
- **VBV2.1:** the same scripts are re-run unchanged on experiment 99's VBV2.1 solver outputs once they exist.

## 6. What this does not establish

The same limits as CRITERIA.md section 8 apply. In addition, the VBV2 references and candidates are multi-module projects flattened into the judge prompt, so file-level criteria describe what the judge read, not the project's module structure.

## Amendment V-A1 (10-09-2026, after the gather, before any analysis output was read)

Section 1 asked for rendered judge prompts on disk. Experiment 100's phase-7 cells have their exact judge inputs on disk (`source.py`, `gold.lean`, `solution.lean`, the files experiment 100's renderer inserts into the prompt), but not the rendered prompt bytes. They are therefore analyzed as a separately labelled secondary source (one set per packaging, never pooled with the primary set), with J1/J2 from experiment 100's committed phase-7 repeats where both members have 3. The primary result uses experiment 103's VBV2 suites exactly as pre-registered.
