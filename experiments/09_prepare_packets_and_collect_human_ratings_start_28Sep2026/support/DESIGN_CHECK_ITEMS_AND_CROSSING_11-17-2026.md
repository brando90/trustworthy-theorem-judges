# Design check: which files raters get, and whether the design is crossed (11-17-2026)

**TLDR:** All 32 raters get the same 100 files (25 tasks x 4 frontier agents), so the round is fully crossed over tasks (T), agents (A) and humans (H) if raters finish. Each rater's row order is shuffled, so partial completion gives a sparse crossing; a shared first block would protect it. The 25 tasks were drawn stratified by benchmark set and difficulty, and they are the evaluation-only set N.

Brando's questions (chat, 11-17-2026): did we select a diversity of difficulties and splits/types, and should everyone rate the same files so results can be split by T, A and H?

## 1. Same files for everyone: yes

- Source: the 32 `ratings/*__native_main_*.csv` snapshots of the live Sheets (form version 6).
- All 32 Sheets list the same set of 100 `item_id`s: 1 distinct item set, 100 items each.
- The 100 files are 25 tasks x 4 agents, one file per task-agent cell (`sealed/RATABLE_COHORT_100_NATIVE.json`, `expected_artifacts` 100, `expected_tasks` 25).
- So the intended data are a complete T x A x H array (25 x 4 x number of raters), the design that allows splitting and variance-component estimates by task, agent and rater.

## 2. Partial completion: the crossing is sparse early

- Row order differs per rater: Brando's Sheet (`A1`) is in task order; every other Sheet keeps its earlier shuffled order with the added files inserted at seeded random positions (`row_order` in `build_full_team_packets.py`).
- Overlap of the first 20 rows between pairs of raters (496 pairs): mean 4.0 files, minimum 0, maximum 10. All 100 files appear in someone's first 20 rows; the most-shared file is in 15 raters' first 20.
- Consequence: if raters stop early (the email says "do as many as you can"), most files get few ratings and few files get many, which weakens per-file agreement and rater-effect estimates.
- Option, not adopted: give every rater the same first block in the same order (for example 20 files = 5 tasks x 4 agents, one task per benchmark set), then each rater's own shuffle for the remaining 80. This guarantees a fully crossed core even under partial completion, at the cost of order effects on the core being shared (counterbalance by rotating agent order within each task). It changes row order in live Sheets: Sri (`T05`) and Nikil (`V02`) already have theirs, and any change needs Brando's decision and a recorded amendment.

## 3. Tasks: stratified by benchmark set and difficulty

- The 25 tasks are set N, identical to the stratified sample drawn by `draw_human_round_sample.py` (seed 20260929; task lists compared file by file: 25 of 25 match). Rule ([C1 sampling, legacy README](../../../research_artifacts/09_human_rating_collection/legacy_veribench/human_round/README.md)):
  - 5 tasks from each VeriBench V1 split: easy, cs, humaneval, realcode, security.
  - Within each split, eligible tasks were ranked by the validated formal specification coverage (FSC) score of the Claude Code candidate, cut into five equal-count groups, and one task drawn per group. Every fifth of each split's difficulty distribution is represented.
  - Placeholder references (`Post ... := True`) and tasks from experiment 100's pool were excluded.
- Descriptive spread in the current packet:
  - Python source: 18 to 129 non-blank lines per task (median 42).
  - Reference theorem statements: 2 to 36 per task (median 5).
  - Candidate theorem statements per file: GPT-6 Astra 7 to 40 (median 11); Claude Fable 5.1 9 to 65 (median 25); Gemini 4 Argon 10 to 57 (median 29); Grok 4.7 12 to 83 (median 27).
- Limitation: the difficulty strata come from an earlier system's score (Claude Code under an older instruction), not from these four agents; they balance task difficulty, not file quality. No file was chosen by content or score (`four_agent_amendment.rule`).

## 4. Agents: four frontier vendors, with a known confound

- One file per task from each of GPT-6 Astra (Codex), Claude Fable 5.1 (Claude Code), Grok 4.7 (Grok CLI) and Gemini 4 Argon (Antigravity).
- The Astra files are historical outputs under instruction version 5; the others are native runs under later instructions. Agent differences are confounded with instruction version and harness (`four_agent_amendment.caveat`, `native_amendment`).

## 5. Splits for judge training: these ratings are evaluation-only

- Brando, 10-07-2026: "Set N is evaluation-only: no set-N rating builds, selects or tunes a judge" ([legacy plan](../../../research_artifacts/09_human_rating_collection/legacy_veribench/human_round/PLAN_setN_rating_round.md)).
- The experiment 02 [priority plan](../../02_design_a_judge_that_predicts_human_ratings_0_to_5_start_06Nov2026/PRIORITY_2_VS_4_11-09-2026.md) keeps the inherited collection as evaluation-only (N_eval) and asks for disjoint T, A and H identity sets for training, validation and test.
- So this round is the held-out test: a complete crossing here is what the evaluation needs. Training and validation ratings for methods 2 and 4 must come from other tasks (and, for strict separation, other agents and raters), under a prospective amendment.

## Open decisions for Brando

1. Adopt a shared first block (section 2) for the 29 unsent raters, and whether to reorder Sri's and Nikil's Sheets if they have not started.
2. Where the training/validation tasks come from (section 5).
