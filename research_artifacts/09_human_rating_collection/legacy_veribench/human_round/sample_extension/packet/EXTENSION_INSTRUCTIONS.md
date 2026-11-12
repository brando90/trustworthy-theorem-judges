<!-- TLDR: What raters receive in the optional second sheet of experiment 102's rating round and how to return it; scoring follows the original rater instructions, unchanged, exactly as in the main sheet. -->
# Rating round 2, optional second sheet: instructions for raters

**Rate this sheet only after you have returned the main 75-row sheet.** It is optional; a partly completed sheet is still useful.

**How to score:** exactly as in the main sheet, following the original rater instructions, unchanged: `human_judgements_prompt.md` in this packet, SHA-256 `b29e9cafdab10463d29b6ffdbb4700b46ead0e6023278b9b7b69d9ef0ab350af`.

## What you receive

- Task folders `E01`, `E02` and so on, one per row of the sheet. Each holds:
  - `python_source/<name>.py`: the Python source;
  - `gold_lean/<name>.lean`: the gold Lean file;
  - `agent_lean/<folder>a.lean`: one agent Lean file to rate.
- `rating_sheet_extension.csv`: one row per agent Lean file.
- `FILES.sha256`: the SHA-256 of every file in this packet.

Some tasks also appear in the main sheet under a different folder name, with different agent Lean files. Rate each file here on its own, and do not look back at your earlier scores.

## How to record your ratings

1. Make your own copy of `rating_sheet_extension.csv` and put your rater code in `rater_id` on every row.
2. On every row, enter `final_score_0_5`, exactly as in the main sheet.
3. Every other column is optional, as in the main sheet. If something prevents a rating, leave the score blank and say why in `problem_note`.

## Rules

- **Rate independently.** Do not discuss items, scores or impressions with the other raters until everyone has returned their sheets.
- **Stay blind.** The files do not say which system wrote them. Please do not try to find out, and do not look up these tasks in the VeriBench repository or its results while rating.
- **Use only your own judgment.** Do not ask an AI model, or any automated judge, to rate, summarize or pre-screen the files.
- Return the filled sheet directly to Brando, with the main sheet or separately.

TL;DR: Optional, and only after the main sheet: score each `E` folder's one agent file with the original instructions, fill `final_score_0_5` on every row of your own copy, rate alone, blind and without AI help, and return it to Brando.
