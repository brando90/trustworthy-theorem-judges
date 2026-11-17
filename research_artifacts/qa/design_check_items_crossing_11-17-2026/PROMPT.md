You are an independent reviewer (light QA, one round) of a human-rating study design in this repository. Do NOT edit, create, move or delete any file anywhere; read and run read-only commands only. Your final message is your review.

Document under review: experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026/support/DESIGN_CHECK_ITEMS_AND_CROSSING_11-17-2026.md

Context: 32 raters each get a personal Google Sheet listing 100 files (Lean formal specifications written by 4 frontier AI agents for 25 VeriBench tasks) and rate each 0-5 for how well its theorem statements cover a reference specification. The goal is to validate an AI judge of these ratings (valid and reliable), generalizing across tasks T x agents A x human raters H. The project owner asks: (a) did we select a diversity of difficulties and benchmark splits/types; (b) should every rater get the same files so the data are crossed T x A x H, rather than sparse per-rater subsets?

Data to check (read-only):
- experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026/ratings/*__native_main_*.csv (snapshots of the live Sheets: rows and order per rater)
- research_artifacts/09_human_rating_collection/preparation_11-09-2026/full_team_11-14-2026/sealed/RATABLE_COHORT_100_NATIVE.json (cohort: tasks, agent configurations, amendments; file paths inside may be absolute)
- research_artifacts/09_human_rating_collection/legacy_veribench/human_round/README.md (section "Sample (C1)") and PLAN_setN_rating_round.md; sample/ and sample_setN/ packets
- experiments/02_design_a_judge_that_predicts_human_ratings_0_to_5_start_06Nov2026/PRIORITY_2_VS_4_11-09-2026.md (split plan)
- experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026/support/scripts/native_packet_generation/build_full_team_packets.py (row_order)

Do:
1. Re-derive every number and factual claim in the document from the data (item sets, first-20 overlap statistics, task stratification and seed, the task-list match, line/theorem counts, the evaluation-only decision). Report each claim as verified, wrong (with the correct value) or unverifiable.
2. Assess the design: task diversity (splits, difficulty strata), agent diversity and confounds, the crossed design, the effect of per-rater shuffled order under partial completion, and the proposed shared first block (size, which tasks, order counterbalancing, interaction with Sheets already sent to two raters). Say what you would recommend and why, briefly, including anything important the document misses (for example rater workload, order/fatigue effects, prior rater exposure to these tasks, or minimum ratings per file for reliability).
3. Output: a short numbered list of findings, each with severity (high/medium/low), evidence (file and value) and a concrete fix. Then a 2-sentence overall verdict. Plain text, under 700 words.
