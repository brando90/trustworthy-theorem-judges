<!-- TLDR: Experiment 110 measures, with 15 pre-registered deterministic criteria and no model calls, how similar frontier-model (FM) VBV1 Lean outputs are to the 75 human-rated Claude 3.7 Sonnet outputs the H2 FSC judge was validated on, so FSC on FM outputs can carry a quantified transfer caveat; pooled FM outputs are in-distribution on 8/15 criteria [7-10] (5/12 on criteria that can fail). -->

# Experiment 110: does the FSC judge's validation pool resemble frontier-model outputs?

**TLDR:** Pooled frontier-model (FM) outputs on VeriBench V1 (VBV1) fall inside the H2 judge's human-rated validation pool on **8/15 pre-registered criteria [95% interval 7-10]** (5/12 on the criteria that can fail), the pre-declared "partially in-distribution" range; the criteria that shift (length, theorem count, tests, `sorry` rate) were not associated with judge error on the pool, and the judge is as stable on FM outputs as on the pool, but FM scores sit mostly at the ceiling and no human ratings of FM outputs exist yet.

**Status:** Complete 10-09-2026 (analysis plus adversarial verification). Zero model calls. Owner of the direct test: experiment 102's set-N human rating round (closes 11-06-2026).

**VBV2 condition (10-09-2026, separately labelled, pre-registered in [vbv2_condition/CRITERIA_VBV2.md](vbv2_condition/CRITERIA_VBV2.md)):** pooled VeriBench V2 frontier-model outputs judged in experiment 103 fall inside the validation pool on **11/15 criteria [8–11]** (26 files, 5 tasks; "partially in-distribution"). They shift only on size and completeness (C1, C2, C3, C10), none of which is error-relevant on the pool. Report: [vbv2_condition/RESULTS_judge_transfer_vbv2.md](vbv2_condition/RESULTS_judge_transfer_vbv2.md).

## Question and motivation

Brando (10-09-2026): we have meaningful trust in the current formal specification coverage (FSC) judge, the H2 ensemble from experiment 100, but it was validated only on Claude 3.7 Sonnet (May-2026) outputs.
Research tolerates quantified uncertainty, so this experiment estimates how similar FM outputs are to the judge-validation pool and turns that into an honest, quantified transfer claim, instead of either claiming validation on FM outputs or refusing to report FSC on them.

## Design (pre-registered in [CRITERIA.md](CRITERIA.md), unchanged)

- **Judge:** H2 from experiment 100: GPT-6 Sol (high effort) + Claude Opus 5.5 (max effort), median of 3 repeats per member, mean of the two members, divided by 5.
- **Pool:** the 75 human-rated items (25 VBV1 tasks x 3 Claude 3.7 Sonnet outputs), train (30) + validation (15) + test (30) together, with the annotation-era reference the judge actually saw (`prompts.render(reference="annotation")` in experiment 100).
- **FM set:** every VBV1 FM output with an H2 judge record: experiment 102 Table 2 (Claude Code + Opus 5, Codex + GPT-5.6 Sol, single-call Opus 5 baseline) and experiment 103 (single-call Opus 5, Gemini 3.1 Pro, GPT-5.6 Luna, GPT-5.6 Sol, GPT-6 Astra, GPT-6 Luna; Terminus 2 + GPT-6 Luna from experiment 95's bytes). Pooled: 10 FM conditions, 8,106 files plus 854 tasks with no output, over 896 tasks. Experiment 107's set-N and set-B packets (public, blinded) are separate conditions, file-side only, because their judge values are sealed. Leanstral and Qwen3.6-27B are reported for comparison, not as FM. VBV2 is out of scope.
- **Criteria:** 13 file-side (C1-C13: length, definitions, theorem count, statement length, quantified / conditional / ground-instance statement fractions, pre/post scaffold, executable tests, `sorry` rate, main-function focus, lexical overlap with the reference, log2 theorem-count ratio to the reference) and 2 judge-side (J1 repeat spread, J2 member disagreement).
- **In-distribution rule:** a criterion is in-distribution when the FM median lies in the pool's [P5, P95] and at least 0.70 of FM files do. Strict rule additionally requires the Kolmogorov-Smirnov (KS) distance to be at most a pool-internal split-half null's 95th percentile. Sensitivity at 0.60 and 0.80.
- **Uncertainty:** task-clustered bootstrap, seed 20261009; 2,000 draws as pre-registered and 10,000 as requested, both reported (identical except where marked).
- **Error relevance:** on the pool, Spearman correlation between each criterion and judge error (H2 score minus human rating); flagged when |rho| >= 0.30 and the interval excludes 0.
- **Deviations:** amendment A1 (the pre-registered main-function rule picks the helper `pre`/`pre_condition` in 64% of pool files) is reported beside, never instead of, the pre-registered result; pooled k is 8/15 either way. A parser fix for `let`/`have` inside statements was made during the pre-registered hand check. Frozen extractor SHA-256: `d72481b87f0f7714574f2450cf08b42d502234e49c8ca1998c4657fabbf1daa1`; `CRITERIA.md` SHA-256 `eb6f245d1fd5e30fb87a5aa0644f83fdbc28657ca8f3c76ffca4889111568029`. File timestamps put `CRITERIA.md` (11:58) before the extractor's last change (12:07) and the results (12:21), but the step-6 hand-check record was not written down, so "the parser fix and A1 came before any criterion value" is plausible, not provable from files.

## Headline

| Condition | k/N [95% interval, 10,000 draws] | Can-fail criteria | k with missing outputs counted outside |
|---|---|---|---|
| **Pooled FM (deployed set, 8,106 files / 896 tasks)** | **8/15 [7-10]** | **5/12** | 8 |
| Pooled FM, matched to the 25 pool tasks (208 files, 42 missing) | 8/15 [7-10] | 5/12 | 8 |
| Claude Code + Opus 5 (exp 102) | 9/15 [5-10] | 6/12 | n/a (none missing) |
| Codex + GPT-5.6 Sol (exp 102) | 10/15 [8-11] | 7/12 | 10 |
| Single-call Opus 5 baseline (exp 102; 564/896 tasks without output) | 12/15 [8-13] | 9/12 | 0 |
| Single-call Opus 5 (exp 103; 215/896 without output, none in realcode or cs) | 7/15 [5-8] | 4/12 | 6 |
| Single-call Gemini 3.1 Pro (exp 103) | 11/15 [10-13] | 8/12 | 11 |
| Single-call GPT-5.6 Luna (exp 103) | 9/15 [7-11] | 6/12 | 9 |
| Single-call GPT-5.6 Sol (exp 103) | 8/15 [7-10] | 5/12 | 8 |
| Single-call GPT-6 Astra (exp 103) | 10/15 [8-11] (2,000 draws: 8-10) | 7/12 | 10 |
| Single-call GPT-6 Luna (exp 103) | 8/15 [7-10] | 5/12 | 8 |
| Terminus 2 + GPT-6 Luna (exp 95 bytes, exp 103 judge) | 8/15 [6-10] | 5/12 | 8 |
| Exp 107 set-N packet (blinded; judge sealed) | 6/13 [4-7] | 3/10 | n/a |
| Exp 107 set-B packet (blinded; judge sealed) | 7/13 [3-7] | 4/10 | n/a |
| Leanstral (not FM, comparison) | 13/15 [11-14] | 10/12 | 13 |
| Qwen3.6-27B (not FM, comparison) | 10/15 [8-11] | 7/12 | 0 |

C6, C8 and C11 cannot fail (the pool interval already spans their whole feasible range), so every condition gets 3 criteria for free; "can-fail" counts exclude them.
Pooled FM under the strict KS rule: 2/15; at coverage 0.60: 11/15; at 0.80: 8/15.
The matched-task k equals the deployed k, so the criterion shift comes from the models, not the task mix (the judge score level does differ: mean 0.783 matched vs 0.888 deployed).

Where pooled FM files leave the pool (pool median -> FM median; share of FM files inside the pool interval): C1 file length 47 -> 115 lines (0.415); C2 definitions 5 -> 11 (0.641); C3 theorem count 1 -> 6 (0.133); C4 statement length 21 -> 14 tokens (0.618); C9 executable tests 0 -> 20 (0.054); C10 `sorry` rate 1.0 -> 0.0 (0.004); C12 lexical overlap with the reference 0.110 -> 0.219 (0.622).
The pool is mostly short, `sorry`-heavy files (67/75 leave every theorem as `sorry`); FM files are long, fully proved and test-rich.

## Does the shift matter?

On the pool, the only error-relevant criterion is C13 (theorem count relative to the reference): Spearman with judge error -0.601 [-0.759, -0.343], read on all 75 items (train + validation + test).
C13 is in-distribution for pooled FM; it is out for experiment 103's single-call Opus 5 and both experiment 107 packets (in-distribution for experiment 102's baseline).
C4 came closest among the shifted criteria: -0.295 [-0.516, -0.008], just under the 0.30 cut-off.
No criterion that pooled FM files fail was associated with judge error on the pool; with 25 tasks this is weak evidence.

## Direct judge-side evidence

**Judge--human agreement on FM outputs:** n = 0 human-rated FM items, so unavailable (experiment 108 pilot is practice-only; experiment 102 set N has 0 sheets returned).

**Judge--human agreement on the pool** (copied from experiment 100's receipts; recomputation here reproduces them; mean bias = judge minus human on the 0-1 scale):

| Split | n items / tasks | Spearman [95% CI] | Pearson | ICC(A,1) | Judge mean | Human mean | Mean bias |
|---|---|---|---|---|---|---|---|
| Train | 30 / 10 | 0.641 | 0.658 | 0.645 | 0.637 | 0.563 | +0.073 |
| Validation | 15 / 5 | 0.870 (0.880 with the 1e-9 tie fix) | 0.860 | 0.822 | 0.653 | 0.556 | +0.098 |
| Test | 30 / 10 | 0.826 [0.32, 0.97] | 0.858 | 0.727 | 0.653 | 0.472 | +0.181 |
| All 75 (recomputed) | 75 / 25 | 0.758 [0.543, 0.896] | 0.766 | 0.708 | 0.647 | 0.525 | +0.121 [0.060, 0.182] |

H2 was selected on the validation split and validated on the test split (one-shot Phase-5 read, `experiments/100_.../results/TEST_RECEIPT.json`).
The test split has been read by at least 2 judge versions (H2 and experiment 75's finalist); the exact count is unresolved (it may also include the 3 saved judges re-scored in experiment 100 Phase 0 and experiment 104's cross-validated recipe), so quote about 0.15 Spearman of selection inflation and experiment 104's cross-validated 0.60 beside 0.83.

**Judge stability on FM outputs (pooled FM, 8,078 files with 3 repeats per member; FM minus pool, task-bootstrap 95% CI):**
repeat SD 0.014 vs 0.017 ([-0.015, +0.006]); member disagreement 0.047 vs 0.061 ([-0.067, +0.026]); J1 and J2 pass even the strict rule.
The judge is not less stable on FM outputs.

**Judge score level:** mean 0.888 on FM vs 0.647 on the pool (difference +0.24 [+0.139, +0.351]); share at 1.0 is 0.657 vs 0.187 (14 of 75 pool items); KS distance 0.578 vs a pool-internal 95th percentile of 0.382.
FM scores sit mostly at the ceiling, where the pool has few items.

## What we can claim

Under the H2 judge, selected on the validation split and validated on the test split of 75 human-rated Claude 3.7 Sonnet outputs (test Spearman 0.826 [0.32, 0.97], n = 30 items / 10 tasks, test split read by at least 2 judge versions with the exact count unresolved, so about 0.15 selection inflation is possible; mean bias on test +0.181, judge mean 0.653 minus human mean 0.472), frontier-model VBV1 outputs fall within the validation pool on 8/15 pre-registered criteria [7-10] (5/12 on criteria that can fail), the pre-declared "partially in-distribution" range.
On the 7 criteria outside it, FM files are longer, carry more definitions, theorems and executable tests, have shorter statements, are almost never left as `sorry` and overlap more with the reference; none of these criteria was associated with judge error on the pool (the one error-relevant criterion, theorem count relative to the reference, is in-distribution), and the judge is as stable on FM outputs as on the pool, but FM scores concentrate at the ceiling (65.7% at 1.0 vs 18.7% in the pool), where the judge--human agreement rests on few items and the judge already rates above humans on average.
Therefore we report FSC on frontier outputs with this quantified transfer caveat, and treat experiment 102's set-N human ratings of FM outputs as the direct test.

## Limitations

- No human ratings of FM outputs exist, so judge--human agreement on them is unmeasured; criterion similarity is not judge validation.
- 3 of the 15 criteria (C6, C8, C11) cannot fail; the honest file-side figure is 3 of 10 can-fail file-side criteria in-distribution (C5, C7, C13).
- Error relevance rests on 25 tasks and on pool items that are mostly unproved; features that never vary in the pool (proved theorems, tests) cannot show error relevance there.
- Unmeasured features (semantic correctness of statements, proof style, task difficulty) can still shift.
- 28 pooled FM files have fewer than 3 judge repeats per member and are excluded from J1, J2 and the judge-side statistics.
- Judge routes differ: experiment 102's judge scores came through the retired host-side gateway route (`tc_gateway`), experiment 103's through the Valkyrie judge agent (`vb103_judge`); both recompute to the published FSC with 0 mismatches.
- Missing outputs are not random: experiment 102's baseline lacks 564/896 tasks and experiment 103's single-call Opus 5 lacks 215/896 (no realcode or cs outputs), so those rows run on skewed task mixes; counting missing as outside gives 0/15 and 6/15 respectively.
- Experiment 107's judge values stayed sealed and were not read; its rows are file-side only (k out of 13).

## Verification (10-09-2026)

An adversarial re-run reproduced `results.json` exactly (except runtime and input hashes), found no leakage (none of the 75 pool hashes is an FM file), confirmed 30/15/30 splits, 75/75 H2 pool scores recomputed from raw repeats, 75/75 theorem counts against the pool manifest, and a hand check of one GPT-6 Astra file.
It fixed two reporting bugs in `scripts/analyze.py` (matched rows under-counted missing outputs; the 3 criteria that cannot fail were not disclosed) and re-ran; no k, interval, error-relevance value or judge-side number changed.
The pre-verification outputs are kept in `results/pre_verify/`.

## Directory structure

```
110_fsc_judge_transfer_frontier_outputs_vs_human_rated_pool/
  README.md                      this design doc
  CRITERIA.md                    pre-registration (unchanged; SHA-256 eb6f245d...)
  inputs/
    pool_manifest.json           75 pool items: paths, hashes, pseudonymous human ratings (already in exp 100), H2 repeats
    fm_manifest.json.gz          10,601 FM/comparison items: paths, SHA-256, judge repeats, route; no sealed values
  scripts/
    extract_criteria.py          frozen extractor (SHA-256 d72481b8...)
    analyze.py                   criteria, in-distribution tests, bootstrap, judge-side evidence (post-verification version)
    build_pool_manifest.py       builds inputs/pool_manifest.json from exp 100
    build_fm_manifest.py         builds inputs/fm_manifest.json from exp 102/103/107 receipts
    extract103_on_snap.py        read-only copy of exp 103 VBV1 files and judge cells on skampere1
  results/
    results.md                   all numbers (curated summary + generated tables)
    results.json                 machine-readable results
    features.jsonl.gz            per-file criterion values
    run_log.txt, run_fixed_log.txt  original and post-verification run logs
    pre_verify/                  original outputs before the verification fixes
```

**Rerun:** the scripts ran from one flat scratch directory: place `CRITERIA.md`, `scripts/extract_criteria.py`, `scripts/analyze.py`, `inputs/pool_manifest.json` and the gunzipped `fm_manifest.json` side by side, recreate `files/103/` from skampere1 with `extract103_on_snap.py` (experiment 103's files are not committed), and run `python3 -I analyze.py` (about 9 minutes; numpy and scipy required).
