# Collected human ratings, by person

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_human_rating_collection/RATINGS_INDEX.md>

**TLDR:** The raw rating CSVs now match the Google Sheets response tables. There are 15 numeric warm-up ratings and three N/A entries; main ratings remain blank as checked on 11-11-2026.

## Open the raw data

| Person | Raw CSV | Entries |
| --- | --- | --- |
| Brando Miranda | [Brando’s warm-up](ratings/Brando_Miranda__warmup_A1.csv) | Six blank rows |
| Rylan Schaeffer | [Rylan’s warm-up](ratings/Rylan_Schaeffer__warmup_T01.csv) | Six numeric ratings; original blank times and `None` Lean response |
| Srivatsava Daruru (Sri) | [Sri’s warm-up](ratings/Srivatsava_Daruru_Sri__warmup_T05.csv) | Six numeric ratings; his recorded times and notes |
| Yegor Denisov-Blanch | [Yegor’s warm-up](ratings/Yegor_Denisov-Blanch__warmup_T02.csv) | All six rows: three numeric ratings and three N/A reference-issue entries |

**[Every participant’s live Google Sheet and matching raw CSV](ratings/README.md).** All 12 active sheet tables are available, including blank forms and the three main sheets. The first two columns remain the requested `rater_name,rater_id`; these are verified identity metadata, not rating answers.

Response values, capitalization, spelling, blanks, N/A entries and row order are preserved. Rylan’s assistant-filled per-file timing estimates and background annotations have been removed from his sheet and current rating files. [Restoration and verification record](support/RAW_DATA_RESTORATION_11-11-2026.md). [Read Rylan’s original notes](support/RYLAN_NOTES.md).

## Current completion status

- [Who is done and what is missing](COMPLETION_STATUS.md).
- [Machine-readable collection summary](ratings/SUMMARY.json).
- [Raw table hashes and exact source ranges](ratings/RAW_MANIFEST.json).

Rylan and Sri each completed six warm-up ratings; each main assignment still has ten blank rating rows. Yegor’s three numeric and three N/A entries are preserved; his existing extra-only qualification decision is unchanged. Dilara, Allen, Don, Simon and Nikil each have six blank warm-up rows. No returned CSV was found for Slava in the earlier scoped mail searches. Brando’s six warm-up and 125 main rows are blank in the current sheet snapshot.

The primary collection still requires 250 main ratings: 20 assigned but blank and 230 not yet assigned. Brando’s ratings are additional. Warm-ups, blank forms and N/A entries are not completed main ratings. Re-exported copies are not new observations.

## Analysis and history

[Normalized analysis copies](ratings/analysis/) are separate from the raw files. The historical importer lowercases some labels and keeps only numeric rows; these derived copies must not be presented as the participant’s exact submission. The refresh script now writes there and cannot overwrite the primary raw directory.

[Original import receipts](../../private/09_human_rating_collection/legacy_veribench/human_round/private_ratings_setN/) and prior sheet snapshots remain historical evidence. Earlier name-first snapshots are superseded for current use because they included coordinator timing estimates. [Slava’s prepared CSV](support/SLAVA_CSV_NAME_FIRST_11-11-2026.md) remains unsent, with six blank response rows.

**11-11-2026 header revision:** Brando’s warm-up and main sheets and their current CSV snapshots now use full checklist questions (schema v2.3). Response cells and completion counts are unchanged. Other delivered forms remain historical pending rollout. See [revision record](support/QUESTION_HEADERS_11-11-2026.md).

**11-11-2026 descriptive paths:** Brando’s working warm-up packet, live sheet and current CSV use `warm_up_01_median`, `warm_up_02_greatest_common_divisor` and `agent_1.lean` through `agent_3.lean`. Historical item IDs, ratings and completion counts are unchanged. [Path mapping](support/WARMUP_PATHS.json) preserves provenance; older delivered packets remain unchanged.
