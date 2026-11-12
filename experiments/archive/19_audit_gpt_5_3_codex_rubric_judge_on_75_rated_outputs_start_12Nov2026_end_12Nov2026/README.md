# Audit of the GPT-5.3-Codex rubric judge on the 75 rated outputs

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/archive/19_audit_gpt_5_3_codex_rubric_judge_on_75_rated_outputs_start_12Nov2026_end_12Nov2026/README.md>

**TLDR:** What does the VeriBench launch page's "raw Pearson about 0.61" judge–human check establish? This completed, post hoc analysis of archived scores (no model calls, no new ratings) reproduces the number exactly and shows a judge 0.825 points stricter than the pooled raters, weak within-task ordering, strong dependence on which raters define the target, and mismatched reference inputs for 8 of 25 tasks. [Results](results.md); [TMLR paper](../../../paper_latex/TMLR_2026_Formal_Specification_Coverage_Judge_Audit/README.md).

**Status:** COMPLETE on 11-12-2026. One light QA round by Gemini Argon (`gemini-4-argon-high`) independently recomputed the numbers; its fixes are recorded in the [TMLR paper README](../../../paper_latex/TMLR_2026_Formal_Specification_Coverage_Judge_Audit/README.md#light-qa-one-gemini-argon-round-11-12-2026).

## Question and setup

- **Judge audited:** `gpt-5.3-codex` through `codex exec`, reasoning effort `xhigh`, given the raters' rubric over the full Python program, reference Lean file and candidate Lean file, mean of three calls per output. VeriBench experiment 58 ran it in May 2026 (commit `daaa09451`). It is not VeriBench's deployed coverage scorer (Claude Sonnet 4.6 with an equivalence-style rubric), and it was the best of three configurations tried on these same ratings, so there is no untouched test set.
- **Rated outputs:** the 25-task, 75-output pool of [archive experiment 01](../01_veribench_25_tasks_3_samples_5_raters_judge_evaluation_start_06Nov2026_end_06Nov2026/README.md): three Claude 3.7 Sonnet samples per task, five raters, seven rating files.
- **Target:** the per-output mean of all available ratings in the seven files (the launch claim's target), plus the receipt's lenient, expert, five-rater and single-rater targets.
- **Statistics:** Pearson, Spearman and Kendall correlations; ICC(A,1) and ICC(C,1); mean bias (judge minus human) and mean absolute error on the 0–5 scale; 95% percentile intervals from 10,000 bootstrap draws over tasks (seed 20261112; p-val=n/a for intervals). The receipt's p-values treat outputs as independent.

## Files

- [results.md](results.md): verdict and result tables.
- [POSTHOC_CLI_RUBRIC_JUDGE_AGREEMENT_11-12-2026.json](POSTHOC_CLI_RUBRIC_JUDGE_AGREEMENT_11-12-2026.json): every number, aggregates only.
- [scripts/recompute_cli_rubric_judge_agreement.py](scripts/recompute_cli_rubric_judge_agreement.py): the analysis. It verifies every input's SHA-256 and git blob, reproduces each reused receipt value to 1e-12 before writing anything, and reads individual ratings only locally.
- [SOURCE_MANIFEST.json](SOURCE_MANIFEST.json): pinned private inputs (source commit `be287d9b`, judge run commit `daaa0945`, the seven rating files and the rating-era item manifest).

Reproduce from the repository root with access to the private VeriBench repository and NumPy/SciPy:

```bash
python3 experiments/archive/19_audit_gpt_5_3_codex_rubric_judge_on_75_rated_outputs_start_12Nov2026_end_12Nov2026/scripts/recompute_cli_rubric_judge_agreement.py --source-repo /path/to/veribench
```

This is a new analysis of old data, not new human evidence, and it does not change archive experiment 01's frozen receipts.
