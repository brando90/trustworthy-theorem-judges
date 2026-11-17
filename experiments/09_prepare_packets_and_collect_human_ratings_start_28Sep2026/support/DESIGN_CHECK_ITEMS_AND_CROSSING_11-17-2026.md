# Design check: which files raters get, and whether the design is crossed (11-17-2026)

**TLDR:** All 32 raters get the same 100 files (25 tasks x 4 frontier agents), so the round is fully crossed over tasks (T), agents (A) and humans (H) if raters finish. Rows are shuffled file by file, so raters switch task almost every row and partial completion gives a sparse crossing; task blocks with a shared first block would fix both. The 25 tasks were drawn stratified by benchmark set and difficulty, and they are the evaluation-only set N. Light QA: one Gemini 4 Argon round (Codex was rate-limited); findings verified and folded in.

Brando's questions (chat, 11-17-2026): did we select a diversity of difficulties and splits/types, and should everyone rate the same files so results can be split by T, A and H?

## 1. Same files for everyone: yes

- Source: the 32 `ratings/*__native_main_*.csv` snapshots of the live Sheets (form version 6).
- All 32 Sheets list the same set of 100 `item_id`s: 1 distinct item set, 100 items each.
- The 100 files are 25 tasks x 4 agents, one file per task-agent cell (`sealed/RATABLE_COHORT_100_NATIVE.json`, `expected_artifacts` 100, `expected_tasks` 25).
- So the intended data are a complete T x A x H array (25 x 4 x number of raters), the design that allows splitting and variance-component estimates by task, agent and rater.

## 2. Partial completion: the crossing is sparse early

- Row order differs per rater: Brando's Sheet (`A1`) is in task order; every other Sheet keeps its earlier shuffled order with the added files inserted at seeded random positions (`row_order` in `build_full_team_packets.py`).
- Overlap of the first 20 rows between pairs of raters (496 pairs): mean 4.0 files, minimum 0, maximum 10. All 100 files appear in someone's first 20 rows; the most-shared file is in 15 raters' first 20.
- Rows are shuffled file by file, not task by task: working top-down, the 31 shuffled Sheets switch task 90 to 99 times in 100 rows (median 97; Brando's task-ordered Sheet: 24). In the first 20 rows a rater meets 12 to 18 different tasks (median 15) and completes all 4 agents of a task for a median of 0 tasks (maximum 1). Every switch means reading a new Python source and reference.
- Consequence: if raters stop early (the email says "do as many as you can"), most files get few ratings and few files get many, which weakens per-file agreement and rater-effect estimates; within-task comparisons across agents are rarely made by the same rater in one sitting.
- Recommended, not adopted (needs Brando's decision and a recorded amendment): order every unsent Sheet in task blocks (the 4 files of a task together), starting with a shared core of 5 tasks (one per benchmark set, spanning the 5 difficulty strata) in the same task order for everyone, then the other 20 tasks in each rater's own random block order; within each task, rotate the agent order across raters (a 4 x 4 Latin square). This keeps a dense T x A x H core under partial completion, cuts task switches to about 24, and spreads order and fatigue effects across agents. All Sheets have 0 responses as of 11-17-2026. Yegor (`T02`), Sri (`T05`) and Nikil (`V02`) already have their packets and Sheets (28 raters unsent); reorder theirs only while they still have 0 responses.

## 3. Tasks: stratified by benchmark set and difficulty

- The 25 tasks are set N, identical to the stratified sample drawn by `draw_human_round_sample.py` (seed 20260929; task lists compared file by file: 25 of 25 match). Rule ([C1 sampling, legacy README](../../../research_artifacts/09_human_rating_collection/legacy_veribench/human_round/README.md)):
  - 5 tasks from each VeriBench V1 split: easy, cs, humaneval, realcode, security.
  - Within each split, eligible tasks were ranked by the validated formal specification coverage (FSC) score of the Claude Code candidate, cut into five equal-count groups, and one task drawn per group. Every fifth of each split's difficulty distribution is represented.
  - Placeholder references (`Post ... := True`) and tasks from experiment 100's pool were excluded.
- Descriptive spread in the current packet:
  - Python source: 18 to 129 non-blank lines per task (median 42).
  - Reference `theorem`/`lemma` declarations: 2 to 36 per task (median 5). The references are the current ones, not byte-identical to the historical set-N references (`current_gold_matches_historical: false` for all 25 tasks).
  - Candidate `theorem`/`lemma` declarations per file: GPT-6 Astra 7 to 40 (median 11); Claude Fable 5.1 9 to 65 (median 25); Gemini 4 Argon 10 to 57 (median 29); Grok 4.7 12 to 83 (median 27).
- Limitation: the difficulty strata come from an earlier system's score (Claude Code under an older instruction), not from these four agents; they balance task difficulty, not file quality. No file was chosen by content or score (`four_agent_amendment.rule`).

## 4. Agents: four frontier vendors, with a known confound

- One file per task from each of GPT-6 Astra (Codex), Claude Fable 5.1 (Claude Code), Grok 4.7 (Grok CLI) and Gemini 4 Argon (Antigravity).
- The Astra files are historical outputs under instruction version 5; the others are native runs under later instructions. Agent differences are confounded with instruction version and harness (`four_agent_amendment.caveat`, `native_amendment`), and within Claude with two output caps (19 files under a 16k-token cap, 6 under 64k) and later-attempt substitutions (`NATIVE_ATTEMPTS_AMENDMENT_11-16-2026.json`).
- Blinded file names are not balanced across agents: Grok is `agent_4.lean` in 17 of 25 tasks (the files added for the fourth agent took the last slot) and Gemini is `agent_2.lean` in 12. Names cannot change for packets already sent; randomizing the within-task row order (section 2) keeps presentation order from tracking the agent.

## 5. Splits for judge training: these ratings are evaluation-only

- Brando, 10-07-2026: "Set N is evaluation-only: no set-N rating builds, selects or tunes a judge" ([legacy plan](../../../research_artifacts/09_human_rating_collection/legacy_veribench/human_round/PLAN_setN_rating_round.md)).
- The experiment 02 [priority plan](../../02_design_a_judge_that_predicts_human_ratings_0_to_5_start_06Nov2026/PRIORITY_2_VS_4_11-09-2026.md) keeps the inherited collection as evaluation-only (N_eval) and asks for disjoint T, A and H identity sets for training, validation and test.
- So this round is the held-out test: a complete crossing here is what the evaluation needs. Training and validation ratings for methods 2 and 4 must come from other tasks (and, for strict separation, other agents and raters), under a prospective amendment.

## Open decisions for Brando

1. Reorder the 28 unsent Sheets into task blocks with a shared 5-task core and rotated agent order (section 2), and whether to do the same for Yegor, Sri and Nikil while they have 0 responses.
2. Where the training/validation tasks come from (section 5).
3. Ratings per file: aim for at least 3 to 5 raters per file for stable per-file human rating distributions (the target of the RPS/TVD metrics); record each rater's prior exposure to set N (`A1`, `T01` and `T05` rated set-N sheets before).

## Light QA (11-17-2026)

One review round by Gemini 4 Argon (`gemini-4-argon-high`, Antigravity CLI), read-only; Codex GPT-6 Astra was the first choice but hit its usage limit. Prompt and review: [research_artifacts/qa/design_check_items_crossing_11-17-2026/](../../../research_artifacts/qa/design_check_items_crossing_11-17-2026/). All numbers verified except the sent count (now 3, fixed); its task-switching and file-name findings were re-derived deterministically and added above.
