# Name-first Google Sheets and matching CSV snapshots

**Historical snapshot — superseded for current raw data.** This earlier snapshot includes coordinator-added Rylan timing estimates that have since been removed. Use [the restored raw tables](../../../ratings/README.md). Preserved here only as audit history, not current participant responses.

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_human_rating_collection/support/sheet_exports/11-11-2026_name_first/README.md>

**TLDR:** The four warm-up sheets and Brando's main sheet now start with the person's actual name and stable rater ID. These are table-value snapshots of those sheets, not additional ratings.

Verified **11-11-2026**. Each CSV preserves the sheet's header and assigned rows after adding `rater_name` in column A and retaining `rater_id` in column B. Leading instruction/comment rows and unused grid cells are omitted; all rating text, blanks and nonnumeric entries are retained. Sheet formatting, notes and validation are preserved in the live files and coordinator receipts, not representable in CSV.

| Person / task | Live Google Sheet | Matching CSV | Assigned rows |
| --- | --- | --- | ---: |
| Brando Miranda — warm-up | [Open sheet](https://docs.google.com/spreadsheets/d/1VhlSsf8Fd_pD_hQySt4-Y3AHrj5e6Rd3kQFu6A59-8A/edit#gid=665730293) | [Open CSV](Brando_Miranda__warmup_A1.csv) | 6 |
| Srivatsava Daruru (Sri) — warm-up | [Open sheet](https://docs.google.com/spreadsheets/d/1G2_MbDnekGt7AwmzkSTxuv3KzPnZIIiQbdx9AiwyR8w/edit#gid=2007848459) | [Open CSV](Srivatsava_Daruru_Sri__warmup_T05.csv) | 6 |
| Rylan Schaeffer — warm-up | [Open sheet](https://docs.google.com/spreadsheets/d/1SiyDKm0b4kmoQIfBomQGgFc8CVb04Rx6ekAW1CjzFFU/edit#gid=1299686922) | [Open CSV](Rylan_Schaeffer__warmup_T01.csv) | 6 |
| Yegor Denisov-Blanch — warm-up | [Open sheet](https://docs.google.com/spreadsheets/d/1AhfJL23U47t61DinUTolwchqHKLaOtR65AFVDD-YOMI/edit#gid=1049421098) | [Open CSV](Yegor_Denisov-Blanch__warmup_T02.csv) | 6 |
| Brando Miranda — main | [Open sheet](https://docs.google.com/spreadsheets/d/1T14977K9IrUU9JoN_9jUR2uUVbvEP5EsKKl9wh06I_o/edit#gid=228912708) | [Open CSV](Brando_Miranda__setN_A1.csv) | 125 |

The first score is now K2 in Brando's sheets and K3 in the other three warm-ups. Brando's forms have 18 columns; the other three historical sheets retain their prior fields plus the name, for 16 columns. This name-only migration does not backfill assistance disclosures or attestations.

Rylan's `minutes_spent` values are coordinator allocations of his approximate one-hour total, not measured per-file times. The live sheet marks them with cell notes; CSV cannot retain those notes. See [timing sources and allocations](../../audit/removed_coordinator_data_11-11-2026/RATING_TIME_ESTIMATES.json) and use the validated named export for explicit per-row timing provenance.

The validated, named analysis exports remain in [ratings](../../../ratings). They preserve the original import selection and append coordinator provenance where present; they are not necessarily byte-identical to current live-sheet downloads. In particular, Yegor's live snapshot contains all six assigned rows, including nonnumeric reference-issue entries; his validated numeric export has three rows. Brando's blank rows are assignments, not completed ratings. Never concatenate these snapshots with the validated exports as new observations.

[Manifest with source links and CSV hashes](MANIFEST.json). Full before/after cell receipts are in the local coordinator store at `research_artifacts/09_human_rating_collection/preparation_11-09-2026/receipts/NAME_FIRST_{BEFORE,AFTER}_11-11-2026.json`. All five sheets were read back and visually inspected: names fit, and pre-existing values, notes, validation and formatting matched after shifting by one column.
