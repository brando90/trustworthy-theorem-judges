# Raw rating restoration — 11-11-2026

**User instruction:** Remove assistant-filled data and show the raw participant ratings as entered. Keep the separately requested actual-name first column and stable ID.

## Current data

Use [the raw rating index](../ratings/README.md). All 12 live Google Sheet tables were reread after restoration and exported directly into `ratings/`. Headers and all response cell values match their exact source ranges. Rylan, Sri and Yegor each retain all six submitted rows; every original response field also matches the pre-enrichment raw snapshots, including case, blanks and N/A.

The collection remains 15 numeric warm-up observations plus three N/A reference-issue entries. This restoration does not add ratings, change scores, revise qualification or modify assignments.

## Removed additions

- Cleared Rylan’s six assistant-estimated `minutes_spent` values and their timing notes. His originally blank cells are blank again.
- Removed the coordinator timing banner above the table and the timing header annotation.
- Removed assistant-added coursework/background notes from Rylan’s response cells. His own `None` values remain exactly as entered.
- Removed background-instruction notes from response cells in Rylan, Sri, Yegor and Brando’s forms; instructions remain on the column headers.
- Removed coordinator background/timing columns and enrichment settings from current exports and the active roster. The exporter ignores extra roster metadata and cannot reload the withdrawn timing estimates.

Names, IDs, assignment fields and header instructions remain form metadata. No score, rationale, participant problem note, participant timing value, assistance answer or attestation was invented or rewritten.

## Verification and provenance

- Native before/after readback of all 12 sheets found zero cell differences outside the explicitly cleared values/notes. Formatting, validation and other values were preserved.
- Each current CSV was parsed back and compared against the exact sheet table; all 12 matched. [Raw manifest](../ratings/RAW_MANIFEST.json) records sheet IDs, ranges, row counts and file hashes.
- All original fields in the three completed warm-up submissions match the pre-enrichment snapshots under `private/09_human_rating_collection/preparation_11-09-2026/collected/all_raters_11-11-2026/`.
- Full before/after CellData and extraction receipts remain in `private/09_human_rating_collection/preparation_11-09-2026/receipts/RAW_RESTORE_BEFORE_11-11-2026.json`, `RAW_RESTORE_AFTER_11-11-2026.json` and `RAW_TABLES_11-11-2026.json`.
- Original historical normalized imports remain untouched. Their named derivatives now live in [ratings/analysis/](../ratings/analysis), clearly labeled non-raw. Yegor’s numeric-only derivative has three rows, while his primary raw CSV has all six.
- Withdrawn estimates and prior snapshots remain audit history, never current observations. [Archived coordinator additions](audit/removed_coordinator_data_11-11-2026/README.md).

The active workflow and Codex, Claude and Cursor instructions now prohibit putting assistant-imputed response data into raw ratings. Missing responses remain missing. A conversational packet-level time estimate must not be distributed among item rows or represented as measured per-item data.
