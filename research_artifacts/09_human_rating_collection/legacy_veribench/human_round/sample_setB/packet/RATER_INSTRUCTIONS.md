<!-- TLDR: What raters in experiment 102's fresh rating round receive and how they return scores; how to score is the original rater instructions file, unchanged and not restated here. -->
# Rating round 2, set B: instructions for raters

**How to score:** follow the original rater instructions, unchanged: [`py_src/veribench_prompts/human_judgements_prompt.md`](../../../py_src/veribench_prompts/human_judgements_prompt.md), SHA-256 `b29e9cafdab10463d29b6ffdbb4700b46ead0e6023278b9b7b69d9ef0ab350af`. It is the file used in the first round (unchanged since 05-04-2026), and the packet contains a byte-identical copy, `human_judgements_prompt.md`. This page does not restate or change it; it only describes the packet and how to return your ratings.

## What you receive

- 25 task folders, `F01` to `F25`. Each holds the three kinds of file the original instructions describe:
  - `python_source/<name>.py`: the Python source;
  - `gold_lean/<name>.lean`: the gold Lean file;
  - `agent_lean/<folder>a.lean`, `<folder>b.lean`, `<folder>c.lean`: three agent Lean files, each rated separately.
- `rating_sheet.csv`: one row per agent Lean file, 75 rows.
- `FILES.sha256`: the SHA-256 of every file in the packet, so you can confirm you are reading the exact bytes that were sampled.

## How to record your ratings

1. Make your own copy of `rating_sheet.csv` and put your rater code (for example `P1`) in `rater_id` on every row.
2. On every row, enter `final_score_0_5`: the integer 0–5 score the original instructions ask you to enter in the score column (the score after any spam adjustment).
3. Everything else is optional, as the "Optional notes" in the original instructions are: `A`, `B`, `C` (Y or N), `D` (handful, dominates or N/A), `confidence` (Low, Med or High) and `rationale`. If you also want to record the "Base score (before spam adjustment)", use `base_score_0_5`.
4. If something prevents a rating (an unreadable file, for example), leave the score blank and say why in `problem_note` instead of guessing.
5. The original instructions link the first round's Google Sheet. For this round, use your copy of `rating_sheet.csv` instead; you can edit it in any spreadsheet program and export it as CSV.

## Rules for this round

- **Rate independently.** Do not discuss items, scores or impressions with the other raters until everyone has returned a sheet.
- **Stay blind.** The files do not say which system wrote them. Please do not try to find out, and do not look up this round's tasks in the VeriBench repository or its results while rating.
- **Use only your own judgment.** Do not ask an AI model, or any automated judge, to rate, summarize or pre-screen the files.
- The three agent files in a folder are in random order; rate each one on its own.
- You may split the work over several sessions. Return the filled sheet directly to Brando.

TL;DR: Score with the original instructions file, unchanged; fill `final_score_0_5` on all 75 rows of your own copy of the sheet; rate alone, blind and without AI help; return it to Brando.
