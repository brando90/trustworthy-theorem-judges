# Experiment index

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/README.md>

**TLDR:** Track three efforts: original human-rating evidence, experiment 09's new packet and collection, and experiment 15's T, A, H estimates. The [standalone judge paper and evidence ledger](../paper_latex/AAAI_2027_Evaluation_AI_Scientists/README.md) connect them. Experiment 02 supplies shared methodology; the remaining folders preserve supporting or paused studies.

## The three efforts

| Effort | Home | What it contains |
| --- | --- | --- |
| Original 25 × 3 × 5 study | [01 — Original VeriBench 25-task rating study](archive/01_veribench_25_tasks_3_samples_5_raters_judge_evaluation/README.md), [count audit in 07](07_compare_5_judges_on_75_outputs_and_estimate_rating_needs/results.md#1-which-count-is-right-343-or-195) | 25 tasks, three generation samples per task, five rater columns: 75 artifacts, 345 observed ratings out of 375 slots, including 195 expert-subset ratings. Later judge analyses reuse these data. |
| New human-rating task | [09 — Prepare packets and collect human ratings](09_prepare_packets_and_collect_human_ratings/README.md) | Editable packet, response values and progress. The authorized replacement emphasizes native Claude Code, Codex and Pi: 85 artifacts and 170 independent ratings planned. Preparation and the completed manifest remain pending. |
| Rating tensor size estimates | [15 — Estimate required tasks, solver configurations and human raters](15_estimate_required_tasks_solver_configurations_and_human_raters/README.md) | Original Claude, Gemini and ChatGPT conversations, linked passages and sizing methods. Final allocation is undecided. |

## Shared methodology and supporting records

| Experiment | Role and status |
| --- | --- |
| [02 — Design a judge that predicts human ratings from 0 to 5](02_design_a_judge_that_predicts_human_ratings_0_to_5/README.md) | Prospective methodology and [methods 2 versus 4](02_design_a_judge_that_predicts_human_ratings_0_to_5/PRIORITY_2_VS_4_11-09-2026.md); identity-split amendment and fresh evaluation remain pending. |
| [04 — Test prover-success predictions on unseen tasks](04_test_prover_success_predictions_on_unseen_tasks/README.md) | Phase 0 complete; fresh study paused pending context coverage and funding. |
| [07 — Compare five judges on 75 outputs and estimate rating needs](07_compare_5_judges_on_75_outputs_and_estimate_rating_needs/README.md) | Completed cached calculations retained as a current reference for experiment 02's metric and sample-size discussion; fresh confirmation pending. |
| [08 — Judge whether candidate statements imply the reference: 48 Lean cases](08_judge_whether_candidate_statements_imply_reference_48_lean_cases/README.md) | Bounded constructed-control study complete; parent review and natural-output follow-up remain pending. |
| [10 — Fit five-judge mixtures: Pearson versus ranked probability training](10_fit_5_judge_mixtures_to_75_outputs_pearson_vs_ranked_probability/README.md) | Analysis complete; retained until its owner reconciles a unique unlanded publication receipt. |
| [16 — Formulation ③ versus ④ and ②](16_formulation3_val_selection_vs_4/README.md) | Choosing the judge by validation loss did not beat fitting by loss on train tasks (1,000 task-grouped splits, cached judges, $0). Retrospective, complete. |
| [17 — Learning curve on the real ratings](17_learning_curve_tasks_and_ratings/README.md) | Held-out RPS against training tasks (4 to 20) and ratings per artifact for the loss-fitted and correlation-fitted mixtures. Cached judges, $0, complete. |
| [18 — Big AI-labelled pool, test on the 75 humans](18_big_ai_label_pool_test_on_75_humans/README.md) | Big-data version 1: fit on 591 VeriBench experiment 106 artifacts with AI-rater labels, test on the 75 human-rated artifacts; four cached judge configs, $0, complete. |

## Historical evidence

The [archive index](archive/README.md) keeps local experiments 01, 03 and 05 and records the cross-project moves. General objective-comparison studies 06 and 11–14 now live only in [the position-paper project](https://github.com/brando90/judges-dont-need-psychometrics-or-corr/blob/main/experiments/archive/README.md). Their original protocols, results, hashes and numbers are preserved; linked analyses of the same ratings are not additional collections.

The [reference-anchoring plan](../docs/reference-anchoring-plan.md) remains a separate proposed controlled comparison; it has not been executed by reorganizing these folders.

Folder names state each study’s purpose and concrete setup. The [dated rename map](archive/README.md#descriptive-names-for-every-experiment--11-11-2026) preserves earlier paths and explains the temporary live-batch compatibility alias.
