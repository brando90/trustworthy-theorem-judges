# Experiment index

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/README.md>

**TLDR:** The active folder list contains three homes: judge methodology (02), human-rating preparation and collection (09), and rating-data size estimates (15). The original rating study and supporting, completed or paused studies are in the [archive](archive/README.md).

## Current work

| Home | Purpose and status |
| --- | --- |
| [02_design_a_judge_that_predicts_human_ratings_0_to_5](02_design_a_judge_that_predicts_human_ratings_0_to_5/README.md) | Develop the judge methodology, including [training correlation versus a proper probability loss](02_design_a_judge_that_predicts_human_ratings_0_to_5/PRIORITY_2_VS_4_11-09-2026.md). The identity-split amendment and fresh evaluation remain pending. |
| [09_prepare_packets_and_collect_human_ratings](09_prepare_packets_and_collect_human_ratings/README.md) | Prepare the current packet and collect human ratings: 54 returned files on 25 tasks, with a target of 108 independent ratings. Its README owns live preparation status, named data links and completion counts; the editable packet and raw responses stay there. |
| [15_estimate_required_tasks_solver_configurations_and_human_raters](15_estimate_required_tasks_solver_configurations_and_human_raters/README.md) | Decide how many tasks, solver configurations and human raters a study needs. It holds a costed allocation computed from saved results, three open choices for Brando, and the recovered Claude, Gemini and ChatGPT estimates with their original text. The final allocation is undecided. |

## Original evidence and supporting studies

[01_veribench_25_tasks_3_samples_5_raters_judge_evaluation](archive/01_veribench_25_tasks_3_samples_5_raters_judge_evaluation/README.md) is the original study: 25 tasks, three generation samples per task and five rater columns, giving 75 artifacts and 345 observed ratings out of 375 slots, including 195 expert-subset ratings. The [count audit](archive/07_compare_5_judges_on_75_outputs_and_estimate_rating_needs/results.md#1-which-count-is-right-343-or-195) explains the denominators. Later analyses reuse these observations; they are not additional collections.

The [archive index](archive/README.md) lists the other studies, their outcomes and pending gates, the earlier cross-project moves, and the dated old-to-new path maps. Archiving a paused study or a study awaiting review does not complete its remaining work. General objective-comparison studies 06 and 11–14 have their canonical home in [the position-paper project](https://github.com/brando90/judges-dont-need-psychometrics-or-corr/blob/main/experiments/archive/README.md).

The [judge paper and evidence ledger](../paper_latex/AAAI_2027_Evaluation_AI_Scientists/README.md) connect the original evidence, current collection and sizing question. The [reference-anchoring plan](archive/does_a_gold_reference_help_or_bias_a_theorem_judge/README.md) is a proposed comparison that has not been run; it is listed in the archive.
