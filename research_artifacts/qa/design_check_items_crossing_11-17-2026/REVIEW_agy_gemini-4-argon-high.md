1. CLAIM VERIFICATION (RE-DERIVED FROM DATA)

- Item sets & counts: VERIFIED. All 32 `ratings/*__native_main_*.csv` files use Form v6 headers and contain the exact same 100 `item_id`s (1 distinct item set) corresponding to 25 tasks x 4 agents in `sealed/RATABLE_COHORT_100_NATIVE.json` (`expected_artifacts: 100`, `expected_tasks: 25`).
- Row order & first-20 overlap: VERIFIED. `A1` is in task order; the other 31 raters preserve their 75-file random item order with 25 new items hash-inserted (`build_full_team_packets.py:238-247`). Across all 496 rater pairs, first-20 overlap has mean 3.996 (4.0), min 0, max 10; all 100 items appear in at least 2 raters' first 20 rows (max 15).
- Sent raters count ("Sri (`T05`) and Nikil (`V02`) already have theirs"; "29 unsent raters"): WRONG. `sealed/SENT_100.json` and `build_full_team_packets.py:609-613` show 3 non-A1 raters were sent packets (`T05`, `V02`, and `T02` Yegor at `2026-11-17T23:09:05Z`), plus `A1` (self-sent), leaving 28 unsent raters.
- Task stratification, seed & Set N match: VERIFIED (with gold-file caveat). The 25 Python task files match `legacy_veribench/human_round/sample/packet/R01..R25` and `sample_setN/packet/N01..N25` 25/25 byte-for-byte, drawn with seed `20260929` (5 tasks per VBV1 split: `easy`, `cs`, `humaneval`, `realcode`, `security`; 5 equal-count Claude Code FSC strata per split; excluding experiment 100's 25 tasks, 5 security siblings, and `Post := True` placeholders). However, 0/25 gold reference `.lean` files match historical Set N byte-for-byte (`current_gold_matches_historical: false`).
- Line & declaration counts: VERIFIED. Python source non-blank lines: 18–129 (median 42). Reference `theorem`/`lemma` declarations: 2–36 (median 5). Candidate `theorem`+`lemma` declarations: GPT-6 Astra 7–40 (median 11), Claude Fable 5.1 9–65 (median 25), Gemini 4 Argon 10–57 (median 29), Grok 4.7 12–83 (median 27) (if counting `theorem` only: Gemini 8–43 median 23; Grok 8–83 median 21).
- Agent confounds & evaluation-only status: VERIFIED. Astra uses prompt v5 (`historical_codex_astra`), whereas Fable, Grok, and Gemini use v8 in native harnesses (`RATABLE_COHORT_100_NATIVE.json`). Set N is locked as evaluation-only (`PLAN_setN_rating_round.md:118`, `PRIORITY_2_VS_4_11-09-2026.md:65-69`).

2. DESIGN ASSESSMENT & RECOMMENDATIONS

- Task/agent diversity & confounds: Stratification across 5 splits x 5 difficulty quintiles is sound for task diversity, though equal split sampling (5 each) overrepresents `cs` (~20 pool tasks) vs `security` (~450), requiring split-reweighted population estimates. Agent comparisons are confounded not only by prompt (v5 vs v8) and harness, but also by within-Claude cap changes (19 files under v2 16k-token cap, 6 under v3 64k cap) and multi-attempt selection (`NATIVE_ATTEMPTS_AMENDMENT_11-16-2026.json`).
- Per-item shuffling hurts workload and within-task crossing: Because the 31 non-A1 Sheets shuffle individual files rather than task folders, working top-down causes a median of 97 task switches across 100 rows (range 90–99 vs 24 for `A1`). In their first 20 rows, raters must read 12–18 distinct Python/reference tasks (median 15) and complete all 4 agents for a median of 0 tasks (max 1). At 20–40 min/task (`legacy_veribench/human_round/README.md:83`), 100 files take ~15–25 hours, making partial completion the norm.
- Shared first block & what the doc misses: Recommend adopting a task-grouped design (all 4 agents per task consecutive) starting with a shared 20-file core (5 tasks = 1 per split, spanning strata 1–5) for the 28 unsent raters, and reordering `T02`/`T05`/`V02` if their Sheets still have 0 responses. Counterbalance both task order and agent order across raters so fatigue does not bias specific tasks/agents, aim for >=3–5 raters per file for stable empirical distributions (`p-hat_i` in TVD/RPS), and track prior rater exposure (`A1`, `T01`, `T05` had earlier Set N sheets; 8 raters received warm-up sheets).

3. NUMBERED FINDINGS

1. [High] Unblocked per-item shuffling causes severe context-switching and zero complete tasks early.
   Evidence: `ratings/*__native_main_*.csv` (31 non-A1 raters have median 97 task switches per 100 rows; first 20 rows span median 15 tasks with median 0 complete 4-agent tasks); `build_full_team_packets.py:126-145` (`design()` task-grouping was bypassed).
   Fix: Group the 4 files of each task consecutively in every Sheet and place a shared 5-task (20-file) core block first (1 task per split across the 5 strata), rotating task-block and within-task row order across raters.

2. [Medium] Blinded filename slots (`agent_1..4.lean`) are heavily confounded with agent identity.
   Evidence: `RATABLE_COHORT_100_NATIVE.json` (`layout_additions` assigns all 15 added `native_grok_cli` files to `agent_4.lean`; overall, Grok is `agent_4.lean` in 17/25 tasks [68%] and Gemini is `agent_2.lean` in 12/25 tasks [48%]).
   Fix: Randomize the Sheet presentation order of `agent_1..4` within each task per rater so within-task order effects do not systematically penalize Grok (`agent_4`).

3. [Medium] Sent-packet count and delivered `.zip` contents are inconsistent across raters.
   Evidence: `sealed/SENT_100.json` and `BUILD_INDEX_100_NATIVE.json` (`T02` was also sent, leaving 28 unsent raters, not 29; `T05`/`V02` zips have 151 files including `START_HERE.md` instructing folder-order rating, while the other 30 zips have 150 files without `START_HERE.md` and emails instructing top-down Sheet order).
   Fix: Update the document to list `T02`, `T05`, and `V02` as sent (28 unsent), check live responses (currently 0), and align row order with task-folder order before releasing the hold.

4. [Low] Theorem count definition and gold-reference updates are unstated.
   Evidence: `RATABLE_COHORT_100_NATIVE.json` (Gemini median 29 and Grok median 27 hold only when summing `theorem` + `lemma`; `current_gold_matches_historical: false` on all 25 tasks).
   Fix: State `"theorem/lemma declarations"` and note the updated v8 gold references in Section 3.

Overall verdict: The factual claims and statistics in the design check are verified except for the sent-rater count (`T02` was also sent, leaving 28 unsent) and the unstated inclusion of `lemma` in candidate counts. Before lifting the send hold, switch the 28 unsent Sheets (and `T02`/`T05`/`V02` if still unscored) from per-item shuffling to task-grouped blocks with a counterbalanced 5-task (20-file) shared core so partial completion still yields a dense T x A x H crossing without 97 task switches per rater.
