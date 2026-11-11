# Collected human ratings, by person

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_human_rating_collection/RATINGS_INDEX.md>

**TLDR:** The current collection contains 15 numeric warm-up ratings from Rylan, Yegor and Sri. The live-sheet check on 11-11-2026 found no additional or revised ratings; main-task submissions remain blank.

## Open the actual rating data

[Read Rylan’s notes in a formatted preview](RYLAN_NOTES.md).

Each filename includes the person's name, and each file starts with a `rater_name` column and retains the original `rater_id`. All original rating values, notes and rows are preserved. These named exports are the same observations as the canonical imports, not additional ratings.

Rylan's file also includes sourced coordinator background fields beside his name: **programming-languages coursework with Aiken**, reported by Brando on 11-11-2026. His separate Lean-specific self-report is preserved. [Background clarification](RYLAN_NOTES.md#relevant-background).

Rylan's `minutes_spent` now contains **coordinator estimates totaling 60 minutes**, allocated from his approximate one-hour report at Brando's request. Each row labels this timing source and preserves its originally blank timing value; these are not measured per-file times. [Timing breakdown and provenance](RYLAN_NOTES.md#time-estimate).

| Person who supplied the ratings | Actual data | Numeric ratings | Other entries |
| --- | --- | ---: | --- |
| Rylan Schaeffer | [Rylan's ratings — Rylan_Schaeffer__warmup_T01.csv](ratings/Rylan_Schaeffer__warmup_T01.csv) | 6 | None |
| Yegor Denisov-Blanch | [Yegor's ratings — Yegor_Denisov-Blanch__warmup_T02.csv](ratings/Yegor_Denisov-Blanch__warmup_T02.csv) | 3 | Three N/A reference-issue entries remain in the [source snapshot](../../private/09_human_rating_collection/preparation_11-09-2026/collected/all_raters_11-11-2026/warmup_T02/ratings.csv); they are not numeric ratings |
| Srivatsava Daruru (Sri) | [Sri's ratings — Srivatsava_Daruru_Sri__warmup_T05.csv](ratings/Srivatsava_Daruru_Sri__warmup_T05.csv) | 6 | None |

Open the [canonical data folder](../../private/09_human_rating_collection/legacy_veribench/human_round/private_ratings_setN/) for the original import receipts and immutable historical snapshots.

## Current completion status

- [Who is done and what is missing — checked 11-11-2026](COMPLETION_STATUS.md).
- [Machine-readable completion and duplicate check](ratings/SUMMARY.json).
- [Latest live-sheet snapshots, CSV exports and source receipts](../../private/09_human_rating_collection/preparation_11-09-2026/collected/all_raters_11-11-2026/).

Rylan and Sri finished their warm-ups; each main assignment still has ten blank rating rows. Yegor remains extra-only under the existing qualification decision. Dilara, Allen, Don, Simon and Nikil each have six blank warm-up rows. No returned CSV was found for Slava in the scoped mail searches. Brando's 125 main-task rows were also blank when checked.

The primary collection still requires 250 ratings: 20 assigned but blank and 230 not yet assigned. Brando's ratings are additional. Warm-up ratings are not main-task ratings, and the latest snapshots must not be appended as new independent observations.

## Local files

The actual CSV files are in `ratings/` beside this index. [Completion status](COMPLETION_STATUS.md). Snapshot checked 11-11-2026; canonical import receipts remain under the linked private source folder. Do not count these copies as new observations.
