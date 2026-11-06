# Historical VeriBench judge–human agreement

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/01_legacy_veribench_judge/README.md>

**TLDR:** Preserved historical scalar-judge evidence motivates a fresh study; it does not validate the new probability-output judge or a prover judge.

**Status:** Historical evidence imported on 11-06-2026 from the committed VeriBench sources listed in [SOURCE_MANIFEST.json](SOURCE_MANIFEST.json).
The original files remain in their source project because its paper still cites them.
The new study has not collected or evaluated its fresh human data.
This archive concerns artificial intelligence (AI) / large language model (LLM) judges of formal specification coverage (FSC); it does not validate a prover-based judge.

Experiment 100 reports **Kendall tau-b 0.698, Spearman rho 0.826, Pearson r 0.858**.
That is a later continued-paper result, distinct from the original paper's **Pearson r 0.703** and the subsequent automated recipe's **Spearman rho 0.603**.

## Results kept separate

| Historical condition | Scope and target | Spearman rho | Kendall tau-b | Pearson r |
|---|---|---:|---:|---:|
| Original two-fold task-split score-mapping analysis | 72 scored items from a 75-item, 25-task pool; one expert's two earlier-prompt passes averaged; validation folds, no test counterpart | 0.321143 | 0.265060 | 0.703349 |
| `100_karpathy_recipe_tc_judge_search_human_train_val_test`, selected judge | 30 candidate files, 10 test tasks; mean of available expert ratings | 0.825723 [0.316250, 0.965616] | 0.698217 [0.215512, 0.913038] | 0.857844 [0.706843, 0.941211] |
| Same selected judge, ordinary-reference subset | 24 candidate files, 8 test tasks; excludes two tasks whose references were placeholders at rating time | 0.651917 [−0.166241, 0.916077] | 0.513270 [−0.201404, 0.834547] | 0.834653 [0.453743, 0.957865] |
| `104_fsc_judge_5fold_cross_validation_all_75_expert_labels`, automated recipe, primary repetition, ties preserved | All 75 files, 25 tasks, five task-disjoint folds; each scored without its task in the training fold | 0.603 [0.287, 0.836] | 0.498 | 0.621 |

Intervals are 95% percentile intervals resampling tasks, retaining their candidate files together.
Experiment 100 uses seed 20260928 and 10,000 requested draws for the full test; the ordinary subset uses 2,000 requested draws, with 1,998 nondegenerate draws for correlations and 2,000 for absolute agreement.
Experiment 104's tie-preserving addendum uses 10,000 task draws and seed 20260929.
P-values are not supplied by these imported receipts (`p-val=n/a`); no new significance test was performed.
The original aggregate CSV contains no confidence intervals; its continued-paper prose reports a Pearson interval [0.564, 0.804], but this import does not assert that it uses the later task-bootstrap method.

## The selected judge and the human target

The experiment 100 judge sees the Python source, candidate Lean file and reference Lean file at the versions shown to the human raters.
It uses their rating instructions, four conventions derived from training-split errors, and four expert-rated examples from other training tasks.
Its historical model routes are `openai/gpt-6-sol-high` with high reasoning effort and `anthropic/claude-opus-5-5-no-fallback` with maximum compute effort and adaptive thinking, through the Vals model gateway.
The score is the mean of two member medians, with three calls per member: six raw calls per completed judge score.
These are historical route identifiers, not a recommendation or authorization to run them today.

The 25 tasks were split into 10 training, 5 validation and 10 test tasks, with all three candidate files of each task kept together.
The primary target is the mean of available ratings from a panel of three experts, divided by five.
Five people supplied ratings overall; the three-expert target must not be described as uniformly three ratings per item:

| Split | Items with three expert ratings | Items with two expert ratings | Total items |
|---|---:|---:|---:|
| Training | 18 | 12 | 30 |
| Validation | 9 | 6 | 15 |
| Test | 18 | 12 | 30 |
| All | 45 | 30 | 75 |

These counts were computed from the source's committed input manifest without importing individual ratings.

The archived human comparator is the mean leave-one-expert-out Spearman correlation, comparing each expert with the mean of the other available experts:

| Human comparator subset | Artifact / task count | Spearman rho |
| --- | ---: | ---: |
| All historical items | 75 / 25 | 0.764187 |
| Experiment 100 validation plus test | 45 / 15 | 0.746595 |

These aggregate records supply no confidence intervals (`p-val=n/a`). Their subsets and targets differ from the selected judge's 30-artifact test comparison; they do not establish that the judge exceeds matched human agreement.
The candidate-generation provenance traces 74 of the 75 files to `claude-3-7-sonnet-20250219`, temperature 0.7, three single-call zero-shot samples per Python task, without a tool or compiler loop.
One candidate lacks a generation receipt.
Thus the three candidates are generation samples, not three different solver systems, and these data do not establish transfer to frontier coding agents.
The generation prompt allowed missing proofs; these historical files must not be relabeled as outputs of the current prove-first solver contract.

## Absolute agreement and variability

All scores here are on [0, 1].
For experiment 100's full test:

- Single-score absolute-agreement intraclass correlation, ICC(A,1): **0.727290 [0.391056, 0.890003]**.
- Consistency intraclass correlation, ICC(C,1): **0.851506**, with no interval in the imported receipt.
- Mean absolute error: **0.201111**.
- Mean bias, judge minus expert mean: **+0.181111**, from means **0.653333** and **0.472222**.
- Mean repeat standard deviation: **0.020488**; 90th percentile **0.057735**, maximum **0.173205**.

The repeat statistic is computed from three **per-pass averages of the two models**, one call per member in each pass.
It is not the variability of independent repetitions of the complete six-call, median-based judge.
This distinction is explicit in the archived ensemble code. The source paper caption instead describes averaging per-model standard deviations; that wording conflicts with `ensemble.py` and `freeze_and_receipt.py`. This import follows the code and preserves the original receipt.
The imported receipt has no uncertainty intervals for mean absolute error, mean bias, or repeat standard deviation.

On the ordinary-reference subset, ICC(A,1) is **0.579786 [0.169238, 0.774305]**, mean absolute error **0.230556**, and mean bias **+0.205556** (judge **0.566667**, experts **0.361111**).
This exposes material uncertainty and score-level disagreement even though the all-item correlations are high.

## Why the new study needs fresh data

1. **Small independent task count.** The headline test has only ten task clusters; the ordinary-reference interval includes negative correlation.
2. **Reference versions and placeholder tasks.** Nine of the 25 reference files changed their theorem statements between rating and earlier judging. Five were placeholder references when rated. Experiment 100 restored rating-era inputs, but high scores on placeholder tasks contribute to its all-item correlation. Five task references also changed during the rating window, leaving the version each rater opened ambiguous (six test artifacts from two tasks). The source appendix reports three test items whose rating sheet linked a different candidate artifact. Excluding either ambiguous group raises agreement in the source analysis, but does not repair the full historical record.
3. **Previously seen ratings.** The receipt discloses earlier exposure by experiments 75 and 83 and a descriptive initial audit. “One-shot test” refers to the selected candidate's test invocation, not a pristine dataset. The exact total number of judge versions that previously saw these ratings and the resulting selection inflation are not established by the imported receipt, explainer, or continued-paper appendix; no numerical inflation estimate is asserted.
4. **Single solver distribution.** Repeated samples from one older solver do not test transfer across agent families, tools, current model versions, or larger projects.
5. **Absolute score bias.** Correlation does not remove the positive mean bias or establish itemwise agreement.
6. **Human and judge repeat limits.** Two or three expert ratings per file and three paired-model passes provide limited evidence about conditional rating distributions and full-judge repeatability.

These limitations motivate fresh task/agent/rater splits and distribution-sensitive metrics in the new methodology.
They are not problems that disappear merely by adding more correlated ratings to the same historical items.

## Original paper versus later recipe

The original **Pearson 0.703349** row uses a separate `gpt-5.3-codex` human-rubric judge with an isotonic score mapping fit on each training fold and evaluated on the disjoint validation fold.
Its raw zero-shot Pearson value is **0.515424** on the same archived 72-item target.
Judge and mapping choices used that validation protocol; there is no independent test-set counterpart.
The source paper reports that the raw scorer package is unavailable, so this archive preserves the aggregate record rather than claiming a complete executable reproduction.

Experiment 104 evaluates an **automated recipe**, with fold-specific model-written conventions and examples and five calls per member, rather than the frozen experiment 100 judge.
Its original raw-float aggregate gives Spearman **0.601533 [0.285578, 0.834392]**, usually written **0.602**.
The published addendum rounds predictions before ranking to preserve mathematical ties and reports **0.603 [0.287, 0.836]**; use that figure when citing the continued paper.
The original excerpt is retained as provenance and must not silently overwrite the corrected figure.
The same addendum changes the second-repetition Spearman from **0.654** to **0.660**.
Its original two-repetition mean is not relabeled as a tie-corrected result.

## Artifact inventory and reproducibility

- [exp100_TEST_RECEIPT.json](exp100_TEST_RECEIPT.json): byte-exact original aggregate receipt; no per-item ratings.
- [original_cv2_aggregate_results.csv](original_cv2_aggregate_results.csv): byte-exact original aggregate results, including the 0.703349 row.
- [exp104_original_aggregate_excerpt.json](exp104_original_aggregate_excerpt.json): selected aggregate fields only; per-item arrays and other fields deliberately omitted.
- [exp104_tie_preserving_addendum.md](exp104_tie_preserving_addendum.md): byte-exact suffix extracted from the source report, explicitly labeled as an extraction in the manifest.
- [SOURCE_MANIFEST.json](SOURCE_MANIFEST.json): immutable source commit, source-file SHA-256 hashes, extraction descriptions and aggregate missingness counts.

Frozen receipts retain their original spelling and format rather than receiving new comments or terminology edits.
No candidate Lean files, reference files, individual ratings, rater identities, contact information, or new sealed ratings are included.
The source repository is private; paths and hashes document provenance without publishing its contents beyond these authorized aggregates.

## Post hoc error intervals, 11-06-2026

The historical receipt has no mean absolute error or bias intervals.
A separate [post hoc supplement](POSTHOC_ERROR_INTERVALS_11-06-2026.json) computes them from the same frozen old predictions and full-precision expert targets, using task resampling and no model calls:

| Test subset | Mean absolute error [95% interval] | Mean bias [95% interval] |
|---|---:|---:|
| All 30 files / 10 tasks | 0.201111 [0.130000, 0.273333] | +0.181111 [+0.098889, +0.262222] |
| Ordinary 24 files / 8 tasks | 0.230556 [0.147222, 0.304201] | +0.205556 [+0.105556, +0.294444] |

The supplement uses the original seed and requested draw counts stated above; every sampled mean error is defined, so all draws contribute.
It is a new analysis of old data, not a result recorded in the historical receipt or new human evidence.
The old exported CSV rounds human means; the computation restores the full-precision targets from the separately hash-checked input manifest and verifies that its means and mean absolute errors match the original receipt to 1e-12.
No individual or per-item ratings are written into this project.

To reproduce with access to the original private repository and a Python environment containing NumPy:

```bash
python3 experiments/01_legacy_veribench_judge/scripts/recompute_error_intervals.py --source-repo /path/to/veribench
```

The continued private paper's title is *VeriBench: An End-to-End Autoformalization Benchmark for AI Coding Agents in Lean 4*, verified in `paper_latex/TMLR_2026_VeriBench/00_main_tmlr_2026.tex` at the source commit.
No public bibliographic identifier was established by this import; cite these archived aggregates directly unless a public paper reference is separately verified.
