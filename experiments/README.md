# Experiment index

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/README.md>

**TLDR:** The active folder list contains five homes: judge methodology (02), human-rating preparation and collection (09), rating-data size estimates (15), persona raters from public information (20), and the frontier-judge pool run (21). The original rating study and supporting, completed or paused studies are in the [archive](archive/README.md).

## Current work

| Home | Purpose and status |
| --- | --- |
| [02_design_a_judge_that_predicts_human_ratings_0_to_5_start_06Nov2026](02_design_a_judge_that_predicts_human_ratings_0_to_5_start_06Nov2026/README.md) | Develop the judge methodology, including [training correlation versus a proper probability loss](02_design_a_judge_that_predicts_human_ratings_0_to_5_start_06Nov2026/PRIORITY_2_VS_4_11-09-2026.md). The identity-split amendment and fresh evaluation remain pending. |
| [09_prepare_packets_and_collect_human_ratings_start_28Sep2026](09_prepare_packets_and_collect_human_ratings_start_28Sep2026/README.md) | Prepare the current packet and collect human ratings: 75 candidate files on 25 tasks (`25 × 3` frontier agent families across four solver conditions), synced across 32 personal 75-row Google Sheets with a baseline target of 150 independent ratings (plus Brando's author ratings); earlier 54-file snapshot archived. Its README owns live preparation status, named data links and completion counts; the editable packet and raw responses stay there. |
| [15_estimate_required_tasks_solver_configurations_and_human_raters_start_04Nov2026](15_estimate_required_tasks_solver_configurations_and_human_raters_start_04Nov2026/README.md) | Decide how many tasks, solver configurations and human raters a study needs. It holds a costed allocation computed from saved results, three open choices for Brando, and the recovered Claude, Gemini and ChatGPT estimates with their original text. The final allocation is undecided. |
| [20_predict_a_persons_ratings_from_a_persona_built_from_public_information_start_14Nov2026](20_predict_a_persons_ratings_from_a_persona_built_from_public_information_start_14Nov2026/README.md) | Test whether a persona built from a person's public information predicts that person's ratings, starting with Brando. Problem and design only; no run. |
| [21_add_3_frontier_judges_to_pool_pearson_vs_ce_80_20_start_16Nov2026](21_add_3_frontier_judges_to_pool_pearson_vs_ce_80_20_start_16Nov2026/README.md) | Add three frontier judges (gpt-6-astra, gpt-6.1-sol, gemini-4-argon) to the pool and repeat ② (pick by correlation) versus ④ (pick by cross-entropy), including with a frontier model as the optimizing agent. Done 16 Nov 2026: ② and ④ still tie on RPS; about $20.5 spent. |

## Original evidence and supporting studies

[01_veribench_25_tasks_3_samples_5_raters_judge_evaluation_start_03May2026_end_29Sep2026](archive/01_veribench_25_tasks_3_samples_5_raters_judge_evaluation_start_03May2026_end_29Sep2026/README.md) is the original study: 25 tasks, three generation samples per task and five rater columns, giving 75 artifacts and 345 observed ratings out of 375 slots, including 195 expert-subset ratings. The [count audit](archive/07_compare_5_judges_on_75_outputs_and_estimate_rating_needs_start_09Nov2026_end_09Nov2026/results.md#1-which-count-is-right-343-or-195) explains the denominators. Later analyses reuse these observations; they are not additional collections.

The [archive index](archive/README.md) lists the other studies, their outcomes and pending gates, the earlier cross-project moves, and the dated old-to-new path maps. Archiving a paused study or a study awaiting review does not complete its remaining work. General objective-comparison studies 06 and 11–14 have their canonical home in [the position-paper project](https://github.com/brando90/judges-dont-need-psychometrics-or-corr/blob/main/experiments/archive/README.md).

The [judge paper and evidence ledger](../paper_latex/AAAI_2027_Evaluation_AI_Scientists/README.md) connect the original evidence, current collection and sizing question. The [reference-anchoring plan](archive/does_a_gold_reference_help_or_bias_a_theorem_judge/README.md) is a proposed comparison that has not been run; it is listed in the archive.
