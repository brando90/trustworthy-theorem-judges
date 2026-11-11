# All participants: matching Google Sheets and CSV snapshots

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_human_rating_collection/sheet_exports/11-11-2026_all_raters_name_first/README.md>

**TLDR:** All 12 active personal Google Sheets begin with actual `rater_name`, then stable `rater_id`. These comma-separated value (CSV) snapshots have exactly the same table headers and values, checked on 11-11-2026.

| Person | Packet | Live Google Sheet | Matching CSV | Rows shown / assigned |
| --- | --- | --- | --- | ---: |
| Allen Nie | warmup | [Open sheet](https://docs.google.com/spreadsheets/d/1_SJ4MbUW-4dfl1lqmlW5tLaPEGc2ho6Pe3SKhXg0nH4/edit#gid=1303945181) | [Open CSV](Allen_Nie__warmup_T04.csv) | 6 / 6 |
| Brando Miranda | setN | [Open sheet](https://docs.google.com/spreadsheets/d/1T14977K9IrUU9JoN_9jUR2uUVbvEP5EsKKl9wh06I_o/edit#gid=228912708) | [Open CSV](Brando_Miranda__setN_A1.csv) | 125 / 125 |
| Brando Miranda | warmup | [Open sheet](https://docs.google.com/spreadsheets/d/1VhlSsf8Fd_pD_hQySt4-Y3AHrj5e6Rd3kQFu6A59-8A/edit#gid=665730293) | [Open CSV](Brando_Miranda__warmup_A1.csv) | 6 / 6 |
| Dilara Soylu | warmup | [Open sheet](https://docs.google.com/spreadsheets/d/1QkkiZYwyvcyfZXDJ0hGlkRm0k5X8YmKEcZGlmDS0vJk/edit#gid=1460779108) | [Open CSV](Dilara_Soylu__warmup_T03.csv) | 6 / 6 |
| Donald Poindexter Jr | warmup | [Open sheet](https://docs.google.com/spreadsheets/d/1d0MyfCbCuVO_vzdPtHZNRH_HInZ7gLKaA-b0yoLfkns/edit#gid=1340510292) | [Open CSV](Donald_Poindexter_Jr__warmup_T06.csv) | 6 / 6 |
| Nikil Ravi | warmup | [Open sheet](https://docs.google.com/spreadsheets/d/1PvlVc3QAu5uMBhfTOiC5Fr3ddY7B4xEou6CGfn5BLyk/edit#gid=1838342269) | [Open CSV](Nikil_Ravi__warmup_V02.csv) | 6 / 6 |
| Rylan Schaeffer | setN | [Open sheet](https://docs.google.com/spreadsheets/d/1GO7o1gVQuY7GWOb294U5So207MMtgk4QoUS9I2eY7TU/edit#gid=2141961818) | [Open CSV](Rylan_Schaeffer__setN_T01.csv) | 125 / 10 |
| Rylan Schaeffer | warmup | [Open sheet](https://docs.google.com/spreadsheets/d/1SiyDKm0b4kmoQIfBomQGgFc8CVb04Rx6ekAW1CjzFFU/edit#gid=1299686922) | [Open CSV](Rylan_Schaeffer__warmup_T01.csv) | 6 / 6 |
| Simon Obstbaum | warmup | [Open sheet](https://docs.google.com/spreadsheets/d/1nzlm6kmnjNWGKAOpSMbsN1UGNOB3XIGCxip7r8al5Eg/edit#gid=1838342269) | [Open CSV](Simon_Obstbaum__warmup_T07.csv) | 6 / 6 |
| Srivatsava Daruru (Sri) | setN | [Open sheet](https://docs.google.com/spreadsheets/d/12HDKFei5_zagDN2tqEZMvXbA51117N9Txrxbpd4HWdo/edit#gid=2141961818) | [Open CSV](Srivatsava_Daruru_Sri__setN_T05.csv) | 125 / 10 |
| Srivatsava Daruru (Sri) | warmup | [Open sheet](https://docs.google.com/spreadsheets/d/1G2_MbDnekGt7AwmzkSTxuv3KzPnZIIiQbdx9AiwyR8w/edit#gid=2007848459) | [Open CSV](Srivatsava_Daruru_Sri__warmup_T05.csv) | 6 / 6 |
| Yegor Denisov-Blanch | warmup | [Open sheet](https://docs.google.com/spreadsheets/d/1AhfJL23U47t61DinUTolwchqHKLaOtR65AFVDD-YOMI/edit#gid=1049421098) | [Open CSV](Yegor_Denisov-Blanch__warmup_T02.csv) | 6 / 6 |

Seven sheets were updated in this pass; five already used this layout. Every original cell value, formula, note, validation rule and format was compared before and after the insertion: zero differences in the retained cells. Native browser checks confirmed the seven newly updated name columns are readable at 100% zoom. Names were joined from the verified [rater roster](../../RATER_IDENTITIES.json).

Rylan and Sri's main forms show all 125 packet items, but each currently has only 10 assigned items. Showing a name on every existing item row does not enlarge that assignment. Brando has 125 main items. Historical team forms retain their other existing columns; future revised forms use the shared 18-column schema after the pilot.

Slava uses an emailed CSV route; no personal Google Sheet is recorded for him. [His current name-first CSV form](../../SLAVA_CSV_NAME_FIRST_11-11-2026.md) is prepared and unsent. Unassigned prospects have no personal form yet.

These are snapshots, not a live background mirror. The same ratings also appear in earlier snapshots and validated exports: never append them as new observations. See [collected ratings](../../RATINGS_INDEX.md), [completion status](../../COMPLETION_STATUS.md) and [import workflow](../../IDENTITY_AND_IMPORT.md). The validated analysis exports can include separately sourced coordinator metadata after the original columns; these snapshots reproduce the live tables exactly.

Rylan's `minutes_spent` values are coordinator allocations totaling an approximate hour, not measured per-item times. Preserve that provenance from [Rylan's notes](../../RYLAN_NOTES.md#time-estimate).

[Manifest with source links and SHA-256 hashes](MANIFEST.json). Full before/after cell receipts remain in the coordinator receipt store; immutable earlier snapshots remain unchanged.
