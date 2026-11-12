# Archived experiments

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/archive/README.md>

**TLDR:** This archive holds completed studies, supporting references and paused work. Each entry states what remains pending; moving a folder here does not accept a review, complete a paused study or discard its evidence. The active homes are 02, 09 and 15 in the [experiment index](../README.md).

## Local archive inventory

| Home | Status |
| --- | --- |
| [01_veribench_25_tasks_3_samples_5_raters_judge_evaluation](01_veribench_25_tasks_3_samples_5_raters_judge_evaluation/README.md) | Original human-rating evidence and subsequent judge analyses; the source records remain the historical anchor. |
| [03_predict_prover_success_from_saved_judge_scores_1024_outputs](03_predict_prover_success_from_saved_judge_scores_1024_outputs/README.md) | Completed retrospective prover-outcome analysis. |
| [04_test_prover_success_predictions_on_unseen_tasks](04_test_prover_success_predictions_on_unseen_tasks/README.md) | **Paused:** phase 0 is complete; phases 1–4 remain unstarted, gated on statement-context coverage and funding. |
| [05_test_qwen_3_5_9b_prover_success_predictions_4_tasks_8_outputs](05_test_qwen_3_5_9b_prover_success_predictions_4_tasks_8_outputs/README.md) | Completed local feasibility condition; no judge validated. |
| [07_compare_5_judges_on_75_outputs_and_estimate_rating_needs](07_compare_5_judges_on_75_outputs_and_estimate_rating_needs/README.md) | Completed cached metric and sample-size calculations; a reference for current methodology, with fresh confirmation still pending. |
| [08_judge_whether_candidate_statements_imply_reference_48_lean_cases](08_judge_whether_candidate_statements_imply_reference_48_lean_cases/README.md) | Bounded constructed-control execution and deterministic verification complete; **parent review remains pending**, as does the proposed natural-output follow-up. |
| [10_fit_5_judge_mixtures_to_75_outputs_pearson_vs_ranked_probability](10_fit_5_judge_mixtures_to_75_outputs_pearson_vs_ranked_probability/README.md) | Retrospective analysis complete; the owner's detached worktree still contains an **unlanded publication receipt and modified PDF**. The worktree is preserved. |
| [16_compare_validation_selection_and_training_on_75_rated_outputs](16_compare_validation_selection_and_training_on_75_rated_outputs/README.md) | Completed cached comparison of validation selection and training objectives. |
| [17_measure_judge_learning_from_4_to_20_tasks_and_more_human_ratings](17_measure_judge_learning_from_4_to_20_tasks_and_more_human_ratings/README.md) | Completed cached learning-curve study; uses experiment 16's shared code. |
| [18_train_judges_on_591_ai_rated_outputs_test_on_75_human_rated_outputs](18_train_judges_on_591_ai_rated_outputs_test_on_75_human_rated_outputs/README.md) | Completed cached AI-rating training-pool study; uses experiment 16's shared code. |

## Active-folder cleanup — 11-11-2026

The pre-cleanup source is [e9f775fe75559c14ba225758164ce98610c60a33](https://github.com/brando90/trustworthy-theorem-judges/tree/e9f775fe75559c14ba225758164ce98610c60a33). This cleanup leaves only methodology (02), human-rating preparation and collection (09), and rating-data size estimates (15) directly under `experiments/`. Completed calculations remain available as references in this archive; the paused and pending statuses above remain binding.

| Previous path under `experiments/` | Destination under `experiments/archive/` |
| --- | --- |
| `04_test_prover_success_predictions_on_unseen_tasks` | [04_test_prover_success_predictions_on_unseen_tasks](04_test_prover_success_predictions_on_unseen_tasks/README.md) |
| `07_compare_5_judges_on_75_outputs_and_estimate_rating_needs` | [07_compare_5_judges_on_75_outputs_and_estimate_rating_needs](07_compare_5_judges_on_75_outputs_and_estimate_rating_needs/README.md) |
| `08_judge_whether_candidate_statements_imply_reference_48_lean_cases` | [08_judge_whether_candidate_statements_imply_reference_48_lean_cases](08_judge_whether_candidate_statements_imply_reference_48_lean_cases/README.md) |
| `10_fit_5_judge_mixtures_to_75_outputs_pearson_vs_ranked_probability` | [10_fit_5_judge_mixtures_to_75_outputs_pearson_vs_ranked_probability](10_fit_5_judge_mixtures_to_75_outputs_pearson_vs_ranked_probability/README.md) |
| `16_formulation3_val_selection_vs_4` | [16_compare_validation_selection_and_training_on_75_rated_outputs](16_compare_validation_selection_and_training_on_75_rated_outputs/README.md) |
| `17_learning_curve_tasks_and_ratings` | [17_measure_judge_learning_from_4_to_20_tasks_and_more_human_ratings](17_measure_judge_learning_from_4_to_20_tasks_and_more_human_ratings/README.md) |
| `18_big_ai_label_pool_test_on_75_humans` | [18_train_judges_on_591_ai_rated_outputs_test_on_75_human_rated_outputs](18_train_judges_on_591_ai_rated_outputs_test_on_75_human_rated_outputs/README.md) |

The detached worktree at `~/.worktrees/trustworthy-theorem-judges/paper-publication-receipt-11-10-2026` is not moved, rewritten or deleted. Its outstanding `experiments/10_retrospective_rps_vs_pearson_mixture/CKPT_practical_judge.md` maps to `experiments/archive/10_fit_5_judge_mixtures_to_75_outputs_pearson_vs_ranked_probability/CKPT_practical_judge.md` when its owner lands that work. The modified paper PDF also remains with that owner. This cleanup does not import the receipt, infer a running analysis from the worktree, or close any review or funding gate.

The sections below preserve the earlier relocation and verification history. Their check counts refer to those earlier changes, not verification of this cleanup.

Cleanup verification: all 448 baseline-tracked files remain present after 157 file relocations. All original result data, source exports, raw ratings and frozen inputs are unchanged. The 63 experiment-08 freeze-bound files retain their pre-cleanup bytes, including the same three pre-existing Markdown hash discrepancies; all ten experiment-10 freeze hashes match. Project checks (62 tests), six mixture tests, seven forecast tests, 83 Python syntax checks, shell syntax and the paper build passed; the PDF is byte-identical. Of 534 local Markdown links checked, only six already-stale references in historical records remain; current navigation has no new broken targets. Experiment 04’s repository-root resolver, experiment 07’s importer root and experiments 17–18’s shared-code imports were repaired. No measurements were rerun.

## Relocation record — 11-11-2026

The first reorganization preserved these experiment trees byte-for-byte under `experiments/archive/`. The later ownership consolidation moved the general objective studies to the position-paper project. The table now links current homes; original experiment numbers and source revisions remain traceable.

| Previous home | Current home | Reason and outcome | Preserved tracked files |
| --- | --- | --- | ---: |
| `experiments/01_legacy_veribench_judge/` | [01_veribench_25_tasks_3_samples_5_raters_judge_evaluation](01_veribench_25_tasks_3_samples_5_raters_judge_evaluation/README.md) | Historical scalar-judge evidence; source receipts remain available to the paper and project checks. | 10 |
| `experiments/03_prover_target_fsc_judge/` | [03_predict_prover_success_from_saved_judge_scores_1024_outputs](03_predict_prover_success_from_saved_judge_scores_1024_outputs/README.md) | Retrospective prover-outcome analysis complete; prospective follow-up belongs to experiment 04. | 17 |
| `experiments/05_fresh_local_prover_target_judges/` | [05_test_qwen_3_5_9b_prover_success_predictions_4_tasks_8_outputs](05_test_qwen_3_5_9b_prover_success_predictions_4_tasks_8_outputs/README.md) | Local feasibility condition complete; no judge validated; broader validation remains in experiment 04. | 55 |
| `experiments/06_information_loss_vs_correlation_judge_selection/` | [06_information_loss_vs_correlation_judge_selection](https://github.com/brando90/judges-dont-need-psychometrics-or-corr/blob/main/experiments/03_exp06_ce_vs_pearson_matched_budget/historical_exp06/README.md) | Canonical package already existed in position-paper experiment 03; redundant public copy removed here. | 83 |
| `experiments/11_formulation4_train_only_ce_mixture_cv/` | [11_formulation4_train_only_ce_mixture_cv](https://github.com/brando90/judges-dont-need-psychometrics-or-corr/blob/main/experiments/archive/11_formulation4_train_only_ce_mixture_cv/README.md) | Train-only cross-entropy mixture study complete; retrospective evidence, no new model calls. | 14 |
| `experiments/12_formulation2_vs_4_corr_vs_ce_80_20_splits/` | [12_formulation2_vs_4_corr_vs_ce_80_20_splits](https://github.com/brando90/judges-dont-need-psychometrics-or-corr/blob/main/experiments/archive/12_formulation2_vs_4_corr_vs_ce_80_20_splits/README.md) | Correlation-versus-cross-entropy split comparison complete; retrospective evidence. | 26 |
| `experiments/13_toy_pearson_vs_ce_nonlinear_ratings/` | [13_toy_pearson_vs_ce_nonlinear_ratings](https://github.com/brando90/judges-dont-need-psychometrics-or-corr/blob/main/experiments/archive/13_toy_pearson_vs_ce_nonlinear_ratings/README.md) | Nonlinear synthetic-rating comparison complete; conclusions are limited to the toy construction. | 13 |
| `experiments/14_open_weight_judge_pool_corr_vs_ce_80_20/` | [14_open_weight_judge_pool_corr_vs_ce_80_20](https://github.com/brando90/judges-dont-need-psychometrics-or-corr/blob/main/experiments/archive/14_open_weight_judge_pool_corr_vs_ce_80_20/README.md) | Open-weight judge-pool comparison complete; retrospective evidence with mixed objective comparisons. | 59 |

The T, A, H planning bundle moved separately from `experiments/02_probabilistic_ordinal_judge/rating_tensor_planning/` to [experiment 15](../15_estimate_required_tasks_solver_configurations_and_human_raters/README.md). Its source exports and original attachments retain identical bytes; editable navigation, source index and attribution of the optional Codex pilot proposal were updated. The bundle's current hashes are in [provenance.json](../15_estimate_required_tasks_solver_configurations_and_human_raters/provenance.json).

## Descriptive name for the original rating study — 11-11-2026

`experiments/archive/01_legacy_veribench_judge/` is now [`experiments/archive/01_veribench_25_tasks_3_samples_5_raters_judge_evaluation/`](01_veribench_25_tasks_3_samples_5_raters_judge_evaluation/README.md). The name identifies the original 25-task VeriBench corpus: three candidate generation samples per task and five rater columns. This archive also contains distinct earlier and later judge analyses of those artifacts; it is not the current human-rating collection. Nine supporting files retain identical bytes; the README now names the study and points to current locations. Frozen migration receipts retain their original paths as provenance.

## Descriptive names for every experiment — 11-11-2026

The number identifies the same study; the rest of each name now states its question and concrete setup. Experiment 01 already uses the approved descriptive name and is unchanged. These are folder/navigation changes, not new experiments or revised scientific conditions.

| Previous path under `experiments/` | Destination after that rename (links open current homes) |
| --- | --- |
| `02_probabilistic_ordinal_judge` | [02_design_a_judge_that_predicts_human_ratings_0_to_5](../02_design_a_judge_that_predicts_human_ratings_0_to_5/README.md) |
| `archive/03_prover_target_fsc_judge` | [archive/03_predict_prover_success_from_saved_judge_scores_1024_outputs](03_predict_prover_success_from_saved_judge_scores_1024_outputs/README.md) |
| `04_fresh_prover_target_judge_validation` | [04_test_prover_success_predictions_on_unseen_tasks](04_test_prover_success_predictions_on_unseen_tasks/README.md) |
| `archive/05_fresh_local_prover_target_judges` | [archive/05_test_qwen_3_5_9b_prover_success_predictions_4_tasks_8_outputs](05_test_qwen_3_5_9b_prover_success_predictions_4_tasks_8_outputs/README.md) |
| `07_exp1_metrics` | [07_compare_5_judges_on_75_outputs_and_estimate_rating_needs](07_compare_5_judges_on_75_outputs_and_estimate_rating_needs/README.md) |
| `08_master_specification_entailment` | [08_judge_whether_candidate_statements_imply_reference_48_lean_cases](08_judge_whether_candidate_statements_imply_reference_48_lean_cases/README.md) |
| `09_human_rating_collection` | [09_prepare_packets_and_collect_human_ratings](../09_prepare_packets_and_collect_human_ratings/README.md) |
| `10_retrospective_rps_vs_pearson_mixture` | [10_fit_5_judge_mixtures_to_75_outputs_pearson_vs_ranked_probability](10_fit_5_judge_mixtures_to_75_outputs_pearson_vs_ranked_probability/README.md) |
| `15_rating_tensor_size_estimation` | [15_estimate_required_tasks_solver_configurations_and_human_raters](../15_estimate_required_tasks_solver_configurations_and_human_raters/README.md) |

At that rename step, current READMEs, instructions, navigation and runnable consumers were updated to the new paths. Historical receipts, results, source exports, pinned Git links and private stores keep their recorded identities. In particular, the experiment 04 resolver accepts the original experiment 03 path in the frozen configuration and resolves it to the current archive. Experiment 15's current navigation hashes are refreshed; original source captures retain identical bytes.

**Temporary compatibility closed — 11-11-2026:** the collection coordinator removed the untracked `experiments/09_human_rating_collection` symlink after confirming the generation batches and dependent watchers had ended. Its absence was verified locally, and the temporary Explorer exclusion was removed. `09_prepare_packets_and_collect_human_ratings` is the sole public collection directory. The private `09_human_rating_collection` store and historical runner paths retain their provenance.

That rename preserved the detached `paper-publication-receipt-11-10-2026` worktree and its owner's unlanded experiment 10 checkpoint/PDF. The later archive destination is recorded in the active-folder cleanup above.

Rename verification: all 411 baseline-tracked files remain present; 211 protected evidence files are byte-identical, including raw ratings, sheet snapshots, Lean files and source exports. Project/design checks (44 collection tests), six mixture tests, seven forecast tests, 62 Python syntax checks, 307 local file links and the paper build passed. Experiment 08 retains its three pre-existing freeze-hash discrepancies in `CERTIFICATE_PROTOCOL.md`, `CERTIFICATE_REPORT.md` and `MODEL_SELECTION.md`; all three retain their pre-rename bytes, and no freeze hash was rewritten. This checks relocation integrity, not new scientific results.

## Objective-study ownership consolidation — 11-11-2026

Experiments 06 and 11–14 belong to the general question about correlation versus proper probability losses. Their canonical home is [judges-dont-need-psychometrics-or-corr](https://github.com/brando90/judges-dont-need-psychometrics-or-corr/blob/main/experiments/archive/README.md). Experiment 11 moves with 12 because it is that comparison's train-only baseline; 14 expands 12's judge pool; 13 is a separate synthetic illustration. These are related conditions, not independent human-rating datasets. The former layout obscured that progression and retained a genuine duplicate of experiment 06.

The transfer copied 112 files from experiments 11–14 unchanged, verified experiment 06's existing 83-file canonical package, and removed the five redundant or misowned source folders. The [per-file manifest](https://github.com/brando90/judges-dont-need-psychometrics-or-corr/blob/main/experiments/archive/MIGRATION_11-11-2026.json) preserves original paths, source revision, Git blobs, digests and the sole README navigation difference. Destination publication: [d585cfe](https://github.com/brando90/judges-dont-need-psychometrics-or-corr/commit/d585cfe).

The complete pre-consolidation layout remains available at [af77a7d](https://github.com/brando90/trustworthy-theorem-judges/tree/af77a7d06e5ea6b0f0a7c3ae68f2120ace676356). This project's original-rating provenance, practical judge comparison, collection and size planning remain here. No measurements were rerun and no raw response values changed.

## Reading and reproducing historical work

Archived documents and frozen configurations retain the paths recorded when the work ran. Use the destination table above for current navigation, including cross-project links. An old path in a recorded result or quoted chat is provenance, not a second active copy. Private stores, sealed ratings and delivered packets have not moved.

The complete pre-relocation layout is available at [commit 15f150d](https://github.com/brando90/trustworthy-theorem-judges/tree/15f150d8a2797a655d0937c7b7fcc37135aa2628). For exact historical reproduction, restore that revision in an isolated temporary checkout and follow that experiment's frozen protocol and private-data requirements. In particular, experiments 03 and 05 derive repository/private paths from their original directory depth; their frozen scripts are preserved here and must be replayed in the original layout, not launched directly from the archive. Moving a script does not authorize inference or lift an existing funding gate.

Current consumers were repaired: the project verifier reads archived experiment 01; experiment 04 resolves experiment 03's recorded input paths into this archive while leaving its frozen configuration unchanged; experiment 07 now calls experiment 03’s preserved historical importer in the position-paper checkout, with `JUDGE_OBJECTIVES_REPO` as an optional location override. Current documentation and Google companion navigation point to the relocated homes. Historical source bodies and immutable commit URLs remain unchanged.

The earlier placement kept supporting references, paused studies and experiment 10 at the top level. The active-folder cleanup above supersedes that placement: 02, 09 and 15 remain active homes, while the other studies are archived with their unfinished work explicitly preserved. The experiment 10 worktree remains owned and unchanged; its publication receipt is still unlanded.

## Initial archive checks — 11-11-2026

Compared all 277 archived tracked files against the pre-relocation commit: every file is byte-identical. Also verified the six experiment-15 source exports/attachments, its current public hash inventory, 104 current local links and passage anchors, the unchanged phase-0 configuration and relocated input hashes, and experiment 07’s importer entry point. The project verifier (33 tests plus design/source/style checks) and paper build passed. The paper-source edit only updates a provenance comment; rebuild-only PDF changes were discarded.
