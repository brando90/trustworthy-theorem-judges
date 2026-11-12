# Archived experiments

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/archive/README.md>

**TLDR:** Completed or superseded experiment records live here. Archive means historical, not invalid or deleted. Current work and important live references are listed in the [experiment index](../README.md).

## Relocation record — 11-11-2026

The first reorganization preserved these experiment trees byte-for-byte under `experiments/archive/`. The later ownership consolidation moved the general objective studies to the position-paper project. The table now links current homes; original experiment numbers and source revisions remain traceable.

| Previous home | Current home | Reason and outcome | Preserved tracked files |
| --- | --- | --- | ---: |
| `experiments/01_legacy_veribench_judge/` | [01_veribench_25_tasks_3_samples_5_raters_judge_evaluation](01_veribench_25_tasks_3_samples_5_raters_judge_evaluation/README.md) | Historical scalar-judge evidence; source receipts remain available to the paper and project checks. | 10 |
| `experiments/03_prover_target_fsc_judge/` | [03_prover_target_fsc_judge](03_prover_target_fsc_judge/README.md) | Retrospective prover-outcome analysis complete; prospective follow-up belongs to experiment 04. | 17 |
| `experiments/05_fresh_local_prover_target_judges/` | [05_fresh_local_prover_target_judges](05_fresh_local_prover_target_judges/README.md) | Local feasibility condition complete; no judge validated; broader validation remains in experiment 04. | 55 |
| `experiments/06_information_loss_vs_correlation_judge_selection/` | [06_information_loss_vs_correlation_judge_selection](https://github.com/brando90/judges-dont-need-psychometrics-or-corr/blob/main/experiments/03_exp06_ce_vs_pearson_matched_budget/historical_exp06/README.md) | Canonical package already existed in position-paper experiment 03; redundant public copy removed here. | 83 |
| `experiments/11_formulation4_train_only_ce_mixture_cv/` | [11_formulation4_train_only_ce_mixture_cv](https://github.com/brando90/judges-dont-need-psychometrics-or-corr/blob/main/experiments/archive/11_formulation4_train_only_ce_mixture_cv/README.md) | Train-only cross-entropy mixture study complete; retrospective evidence, no new model calls. | 14 |
| `experiments/12_formulation2_vs_4_corr_vs_ce_80_20_splits/` | [12_formulation2_vs_4_corr_vs_ce_80_20_splits](https://github.com/brando90/judges-dont-need-psychometrics-or-corr/blob/main/experiments/archive/12_formulation2_vs_4_corr_vs_ce_80_20_splits/README.md) | Correlation-versus-cross-entropy split comparison complete; retrospective evidence. | 26 |
| `experiments/13_toy_pearson_vs_ce_nonlinear_ratings/` | [13_toy_pearson_vs_ce_nonlinear_ratings](https://github.com/brando90/judges-dont-need-psychometrics-or-corr/blob/main/experiments/archive/13_toy_pearson_vs_ce_nonlinear_ratings/README.md) | Nonlinear synthetic-rating comparison complete; conclusions are limited to the toy construction. | 13 |
| `experiments/14_open_weight_judge_pool_corr_vs_ce_80_20/` | [14_open_weight_judge_pool_corr_vs_ce_80_20](https://github.com/brando90/judges-dont-need-psychometrics-or-corr/blob/main/experiments/archive/14_open_weight_judge_pool_corr_vs_ce_80_20/README.md) | Open-weight judge-pool comparison complete; retrospective evidence with mixed objective comparisons. | 59 |

The T, A, H planning bundle moved separately from `experiments/02_probabilistic_ordinal_judge/rating_tensor_planning/` to [experiment 15](../15_rating_tensor_size_estimation/README.md). Its source exports and original attachments retain identical bytes; editable navigation, source index and attribution of the optional Codex pilot proposal were updated. The bundle's current hashes are in [provenance.json](../15_rating_tensor_size_estimation/provenance.json).

## Descriptive name for the original rating study — 11-11-2026

`experiments/archive/01_legacy_veribench_judge/` is now [`experiments/archive/01_veribench_25_tasks_3_samples_5_raters_judge_evaluation/`](01_veribench_25_tasks_3_samples_5_raters_judge_evaluation/README.md). The name identifies the original 25-task VeriBench corpus: three candidate generation samples per task and five rater columns. This archive also contains distinct earlier and later judge analyses of those artifacts; it is not the current human-rating collection. Nine supporting files retain identical bytes; the README now names the study and points to current locations. Frozen migration receipts retain their original paths as provenance.

## Objective-study ownership consolidation — 11-11-2026

Experiments 06 and 11–14 belong to the general question about correlation versus proper probability losses. Their canonical home is [judges-dont-need-psychometrics-or-corr](https://github.com/brando90/judges-dont-need-psychometrics-or-corr/blob/main/experiments/archive/README.md). Experiment 11 moves with 12 because it is that comparison's train-only baseline; 14 expands 12's judge pool; 13 is a separate synthetic illustration. These are related conditions, not independent human-rating datasets. The former layout obscured that progression and retained a genuine duplicate of experiment 06.

The transfer copied 112 files from experiments 11–14 unchanged, verified experiment 06's existing 83-file canonical package, and removed the five redundant or misowned source folders. The [per-file manifest](https://github.com/brando90/judges-dont-need-psychometrics-or-corr/blob/main/experiments/archive/MIGRATION_11-11-2026.json) preserves original paths, source revision, Git blobs, digests and the sole README navigation difference. Destination publication: [d585cfe](https://github.com/brando90/judges-dont-need-psychometrics-or-corr/commit/d585cfe).

The complete pre-consolidation layout remains available at [af77a7d](https://github.com/brando90/trustworthy-theorem-judges/tree/af77a7d06e5ea6b0f0a7c3ae68f2120ace676356). This project's original-rating provenance, practical judge comparison, collection and size planning remain here. No measurements were rerun and no raw response values changed.

## Reading and reproducing historical work

Archived documents and frozen configurations retain the paths recorded when the work ran. Use the destination table above for current navigation, including cross-project links. An old path in a recorded result or quoted chat is provenance, not a second active copy. Private stores, sealed ratings and delivered packets have not moved.

The complete pre-relocation layout is available at [commit 15f150d](https://github.com/brando90/trustworthy-theorem-judges/tree/15f150d8a2797a655d0937c7b7fcc37135aa2628). For exact historical reproduction, restore that revision in an isolated temporary checkout and follow that experiment's frozen protocol and private-data requirements. In particular, experiments 03 and 05 derive repository/private paths from their original directory depth; their frozen scripts are preserved here and must be replayed in the original layout, not launched directly from the archive. Moving a script does not authorize inference or lift an existing funding gate.

Current consumers were repaired: the project verifier reads archived experiment 01; experiment 04 resolves experiment 03's recorded input paths into this archive while leaving its frozen configuration unchanged; experiment 07 now calls experiment 03’s preserved historical importer in the position-paper checkout, with `JUDGE_OBJECTIVES_REPO` as an optional location override. Current documentation and Google companion navigation point to the relocated homes. Historical source bodies and immutable commit URLs remain unchanged.

Experiments 02 (current methodology), 04 (paused fresh study), 07 (current metric/sample-size reference), 08 (pending review and follow-up), 09 (active collection) and 15 (current sizing question) retain their numbered homes. Experiment 10 remains in place because its owner's detached publication worktree contains a unique, unlanded checkpoint addition. The worktree at `~/.worktrees/trustworthy-theorem-judges/paper-publication-receipt-11-10-2026` is preserved for the sole collection coordinator; archive 10 after that publication receipt is reconciled and landed. No running analysis was inferred from the presence of the worktree.

## Initial archive checks

Compared all 277 archived tracked files against the pre-relocation commit: every file is byte-identical. Also verified the six experiment-15 source exports/attachments, its current public hash inventory, 104 current local links and passage anchors, the unchanged phase-0 configuration and relocated input hashes, and experiment 07’s importer entry point. The project verifier (33 tests plus design/source/style checks) and paper build passed. The paper-source edit only updates a provenance comment; rebuild-only PDF changes were discarded.
