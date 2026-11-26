# Raw participant ratings

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026/ratings/README.md>

**TLDR:** Start with Brando's [100-file main packet](../rating_task_packet/main_rating_task/) or [warm-up packet](../rating_task_packet/START_HERE.md). All **33** current main Google Sheets (`A1` author plus `32` team, new co-author invitees and Vals raters; `V04` Vaibhav Mahajan added 11-17-2026) have **100** rows (`25` tasks x `4` agents; **250/3300** scored across 6 raters on 11-26-2026) with `Anyone with the link = Editor` access (the rating email went to all 32 raters on 11-17-2026, the packet as a Google Drive link). This page links all **45 Sheets** and matching raw CSV snapshots: `9` warm-up, `33` current 100-row main, and `3` historical 125-row main.

**Checked: 11-26-2026 via public CSV export.** The collection holds **15 numeric warm-up ratings, 3 warm-up `N/A` entries, and 250 numeric main-round ratings** (265 numeric ratings total across 6 active main-round raters; `T30` Max Sieb stays unverified under expired Sheets OAuth with HTTP 401 on public CSV export). Attestations: 118 `yes`, 100 `partial` (non-dropdown free text), 32 blank across 250 scored rows. All submitted values, blanks, rater row orders, and `T06` `item020`'s edited `candidate_file` cell are preserved verbatim per raw-response policy and flagged for coordinator review.

Warm-up and current main forms have the same eleven fields; since 11-17-2026 the main forms put the rationale last, named `rationale (optional)` (warm-up forms keep `rationale` before `problem_note`). Final score and the combined artificial intelligence (AI) assistance/human-rating attestation are required for new ratings. Time and confidence are requested; a one-sentence rationale is **preferred but optional**; problem notes are for issues. Names and IDs are prefilled metadata. Participant responses retain blanks, capitalization, spelling and N/A entries; assistant-estimated times and assistant-written background annotations were removed. [Rater email](https://docs.google.com/document/d/1KJQHxA-pSMxr31ZPMq8dI5bWPjnObQ2CHlQZ6g5r3f8/edit?tab=t.bmtmw71ddlms) · [Warm-up form verification and history](../support/sheet_exports/11-11-2026_final_form/README.md).


## Filtering by round: `source_label`

Every row in every CSV here (and in [analysis/](analysis/)) ends with a `source_label` column that names its round, so all data stays in one place and is easy to filter: `warm-up` (warm-up packet), `main` (current 100-file round), `historical_main` (original 125-row round, files `*__setN_*`), `May` (reserved for the May 2026 judge-paper ratings when they are imported). It is an export-only column; the raters' Sheets do not have it. Original columns, cells and row order are unchanged and nothing is dropped. Rules and allowed values: `export_columns` in [RATING_FORM_SCHEMA.json](../support/RATING_FORM_SCHEMA.json). Check or backfill with `python3 support/scripts/source_label.py check` (or `apply`), and `build_full_team_packets.py export` adds it on every refresh.

## Warm-up first

[Open Brando’s warm-up packet](../rating_task_packet/START_HERE.md).

| Person | Packet | Raw CSV | Google Sheet | Numeric ratings / displayed rows |
| --- | --- | --- | --- | ---: |
| Allen Nie | warmup | [Allen_Nie__warmup_T04.csv](Allen_Nie__warmup_T04.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1_SJ4MbUW-4dfl1lqmlW5tLaPEGc2ho6Pe3SKhXg0nH4/edit) | 0/6 |
| Brando Miranda | warmup | [Brando_Miranda__warmup_A1.csv](Brando_Miranda__warmup_A1.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1VhlSsf8Fd_pD_hQySt4-Y3AHrj5e6Rd3kQFu6A59-8A/edit) | 0/6 |
| Dilara Soylu | warmup | [Dilara_Soylu__warmup_T03.csv](Dilara_Soylu__warmup_T03.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1QkkiZYwyvcyfZXDJ0hGlkRm0k5X8YmKEcZGlmDS0vJk/edit) | 0/6 |
| Donald Poindexter Jr | warmup | [Donald_Poindexter_Jr__warmup_T06.csv](Donald_Poindexter_Jr__warmup_T06.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1d0MyfCbCuVO_vzdPtHZNRH_HInZ7gLKaA-b0yoLfkns/edit) | 0/6 |
| Nikil Ravi | warmup | [Nikil_Ravi__warmup_V02.csv](Nikil_Ravi__warmup_V02.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1PvlVc3QAu5uMBhfTOiC5Fr3ddY7B4xEou6CGfn5BLyk/edit) | 0/6 |
| Rylan Schaeffer | warmup | [Rylan_Schaeffer__warmup_T01.csv](Rylan_Schaeffer__warmup_T01.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1SiyDKm0b4kmoQIfBomQGgFc8CVb04Rx6ekAW1CjzFFU/edit) | 6/6 |
| Simon Obstbaum | warmup | [Simon_Obstbaum__warmup_T07.csv](Simon_Obstbaum__warmup_T07.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1nzlm6kmnjNWGKAOpSMbsN1UGNOB3XIGCxip7r8al5Eg/edit) | 0/6 |
| Srivatsava Daruru (Sri) | warmup | [Srivatsava_Daruru_Sri__warmup_T05.csv](Srivatsava_Daruru_Sri__warmup_T05.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1G2_MbDnekGt7AwmzkSTxuv3KzPnZIIiQbdx9AiwyR8w/edit) | 6/6 |
| Yegor Denisov-Blanch | warmup | [Yegor_Denisov-Blanch__warmup_T02.csv](Yegor_Denisov-Blanch__warmup_T02.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1AhfJL23U47t61DinUTolwchqHKLaOtR65AFVDD-YOMI/edit) | 3/6 |

Yegor’s six submitted rows include three numeric ratings and three `N/A` reference-issue entries. Blank rows are not completed observations. The warm-up packet and existing responses are unchanged.

## Current main sheets (33 Sheets, 100 files across 25 tasks)

**Form version 7 (11-18-2026):** each main Sheet and CSV has 15 columns: the 5 identifiers, then four required checklist dropdowns (F:I, before `final_score_0_5`) `A_key_gold_theorems_covered (Y/N)`, `B_gold_pre_postconditions_preserved_or_strengthened (Y/N)`, `C_obvious_theorem_spam (Y/N)`, `D_spam_handful_or_dominates (none/handful/dominates)` (rubric quick checklist A–D, followed by the version-6 response columns, with the attestation header shown as `ai_assisted_rating_attestation (AI help is allowed)`; values and rules in `support/RATING_FORM_SCHEMA.json` → `checklist_columns`). Join on `rater_id` + `item_id`.

[Open Brando's current main packet](../rating_task_packet/main_rating_task/): **100** returned/recovered frontier files across **25** tasks (`25 tasks x 4 agents`). On `11-16-2026` each Sheet gained the `25` Google rows in place (existing rows, order and any entries unchanged), was read back from `Ratings!A1:K101`, and matched its packaged `ratings.csv` exactly. Sharing is unchanged (`Anyone with the link = Editor`). Team emails are unsent Gmail drafts; live per-rater progress is in [Who is grading](../README.md#who-is-grading).

| Rater ID | Person | Raw CSV | Google Sheet (`Anyone with the link = Editor`) | Numeric ratings / displayed rows |
| --- | --- | --- | --- | ---: |
| `A1` | Brando Miranda | [Brando_Miranda__native_main_A1.csv](Brando_Miranda__native_main_A1.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1zUDr9fpUwK0IuxrSdFfBR_mOt4WwMY8-doBC6cIhIHM/edit) | 0/100 (additional author ratings) |
| `T01` | Rylan Schaeffer | [Rylan_Schaeffer__native_main_T01.csv](Rylan_Schaeffer__native_main_T01.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1fOr2oE2Fmibw9y8qDL7pMMuj6XH9luMJOMLDzIcBqo0/edit) | 0/100 (25 tasks (100 files); emailed 11-17-2026) |
| `T02` | Yegor Denisov-Blanch | [Yegor_Denisov-Blanch__native_main_T02.csv](Yegor_Denisov-Blanch__native_main_T02.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1Hpcb4NP754RDWstDkiaTR59K9AX2vXNL6IR9iXKRo-Y/edit) | 0/100 (extra_only preserved; emailed 11-17-2026) |
| `T03` | Dilara Soylu | [Dilara_Soylu__native_main_T03.csv](Dilara_Soylu__native_main_T03.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1D6Enb6IKRAZOoqhmk7bHwTqsFZ10U5dH3H3gRmJ8XPk/edit) | 0/100 (25 tasks (100 files); emailed 11-17-2026) |
| `T04` | Allen Nie | [Allen_Nie__native_main_T04.csv](Allen_Nie__native_main_T04.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1iE_2PfDe1uw4_eGJCa-YV_kj1ZodQajZQ0nxDDv5YNo/edit) | 0/100 (25 tasks (100 files); emailed 11-17-2026) |
| `T05` | Srivatsava Daruru (Sri) | [Srivatsava_Daruru_Sri__native_main_T05.csv](Srivatsava_Daruru_Sri__native_main_T05.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/163ZxKeTXqseLrmwY-b5QjqeBulinHsZAiAPo1zsJdJI/edit) | 100/100 (25 tasks (100 files); emailed 11-17-2026) |
| `T06` | Donald Poindexter Jr | [Donald_Poindexter_Jr__native_main_T06.csv](Donald_Poindexter_Jr__native_main_T06.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1l_zdHObt3_0hd0MJkIJ5btU51hxNsHKwHyBUv0cuSLg/edit) | 16/100 (25 tasks (100 files); emailed 11-17-2026) |
| `T07` | Simon Obstbaum | [Simon_Obstbaum__native_main_T07.csv](Simon_Obstbaum__native_main_T07.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1KMYUiMbL7wEvKn9KGN8KjHSca1DcYT-uZE3psSeqrq4/edit) | 0/100 (25 tasks (100 files); emailed 11-17-2026) |
| `T08` | Amy Lu | [Amy_Lu__native_main_T08.csv](Amy_Lu__native_main_T08.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1YLq64komUf0lD8fdChDYeTZS--zpulbn-XTVhLWVUlE/edit) | 100/100 (25 tasks (100 files); emailed 11-17-2026) |
| `T09` | Ethan R Lee | [Ethan_R_Lee__native_main_T09.csv](Ethan_R_Lee__native_main_T09.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1HraAoO6Cczkm2-8ec2Tj97Cuc75LIUWwRUvKgJl5bCw/edit) | 0/100 (25 tasks (100 files); emailed 11-17-2026) |
| `T10` | Ethan Hersch | [Ethan_Hersch__native_main_T10.csv](Ethan_Hersch__native_main_T10.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1QUKFbM9AQbjj3sQo7x0mQSKiWLCm8Ta_qrkeejxDZ_8/edit) | 0/100 (25 tasks (100 files); emailed 11-17-2026) |
| `T11` | Kirill Acharya | [Kirill_Acharya__native_main_T11.csv](Kirill_Acharya__native_main_T11.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1gHkqMYIZyzPJI4rRsNS4_9Dyat2B3x7HDA4YTulkr3U/edit) | 0/100 (25 tasks (100 files); emailed 11-17-2026) |
| `T12` | Rakshit Kaushik | [Rakshit_Kaushik__native_main_T12.csv](Rakshit_Kaushik__native_main_T12.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1rHhh1sCq_Trzlda3fRu-RXES9QG_M1Wb0CzP6Utj7eQ/edit) | 30/100 (25 tasks (100 files); emailed 11-17-2026) |
| `T13` | Zhanke Zhou | [Zhanke_Zhou__native_main_T13.csv](Zhanke_Zhou__native_main_T13.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/13yAF6JYrXcpSWMoGa_PZp9qqrTDllVCP47ygivEdifg/edit) | 0/100 (25 tasks (100 files); emailed 11-17-2026) |
| `T14` | Daneshvar Amrollahi | [Daneshvar_Amrollahi__native_main_T14.csv](Daneshvar_Amrollahi__native_main_T14.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1onFAX0J9uMmiMEq2t7g75lxxrfGw7B7NjnqnmzRpT_I/edit) | 0/100 (25 tasks (100 files); emailed 11-17-2026) |
| `T15` | Leni Aniva | [Leni_Aniva__native_main_T15.csv](Leni_Aniva__native_main_T15.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1Axk32oyQgk299JNEIi4M9bHcBlYPTwJrDyFXOAGnKY0/edit) | 0/100 (25 tasks (100 files); emailed 11-17-2026) |
| `T16` | Iddah Mlauzi | [Iddah_Mlauzi__native_main_T16.csv](Iddah_Mlauzi__native_main_T16.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/11CSWZi89IiLeZDfJCjeJ13VbM0AJEYiNKLpwG0JFCGo/edit) | 0/100 (25 tasks (100 files); emailed 11-17-2026) |
| `T17` | Elyas Obbad | [Elyas_Obbad__native_main_T17.csv](Elyas_Obbad__native_main_T17.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1jIk9KsjMO1A_vgTBN6-R-kB6_hww7AJrggdKiWg8daY/edit) | 0/100 (25 tasks (100 files); emailed 11-17-2026) |
| `T18` | Weston Kirk | [Weston_Kirk__native_main_T18.csv](Weston_Kirk__native_main_T18.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1ygdl8LPRna7e2m7l44iHizCWyknHuM9HPMbKstONVuE/edit) | 0/100 (25 tasks (100 files); emailed 11-17-2026) |
| `T19` | Zixiao Jolene Wang | [Zixiao_Jolene_Wang__native_main_T19.csv](Zixiao_Jolene_Wang__native_main_T19.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1vgngMlu0V-bQz19ZPks0KIkQvSRQy9ZNR3cW-F54HSE/edit) | 0/100 (25 tasks (100 files); emailed 11-17-2026) |
| `T20` | Kai Fronsdal | [Kai_Fronsdal__native_main_T20.csv](Kai_Fronsdal__native_main_T20.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/15mji6A89i4dIaVZnmnx-PqNjaeRgq53ZEOFu9kugyZc/edit) | 0/100 (25 tasks (100 files); emailed 11-17-2026) |
| `T21` | Ying Li | [Ying_Li__native_main_T21.csv](Ying_Li__native_main_T21.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1S4gFJYeoLoFNWIyAqbVxD0AdiKfAwNx0hIEFENyw31Q/edit) | 0/100 (25 tasks (100 files); emailed 11-17-2026) |
| `T22` | Shurui Liu | [Shurui_Liu__native_main_T22.csv](Shurui_Liu__native_main_T22.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1u-iS1GwIeaubBxvfOOq46WVhqUQxlQftAPn_RidZLIU/edit) | 0/100 (25 tasks (100 files); emailed 11-17-2026) |
| `T23` | Steven Dillmann | [Steven_Dillmann__native_main_T23.csv](Steven_Dillmann__native_main_T23.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1vsH0CxrabDY_8aPWlKvZUadV6U7fOsFjRVUMzt-e6T0/edit) | 0/100 (25 tasks (100 files); emailed 11-17-2026) |
| `T24` | Santiago Cuellar | [Santiago_Cuellar__native_main_T24.csv](Santiago_Cuellar__native_main_T24.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1HA8aAPI4aRXSlAZxCiygFO5mbzNydOrcqnOVjS1lftQ/edit) | 0/100 (25 tasks (100 files); emailed 11-17-2026) |
| `T25` | John Sarracino | [John_Sarracino__native_main_T25.csv](John_Sarracino__native_main_T25.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/10fnyfoqZmsL51cczGSj-k_a6s72YjHMW42NvaC3DL9g/edit) | 0/100 (25 tasks (100 files); emailed 11-17-2026) |
| `T26` | Donghyun Lee | [Donghyun_Lee__native_main_T26.csv](Donghyun_Lee__native_main_T26.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/11lvfec1IYxHCB1cucfgKb8V1eO4rAa44sAfEzU-NgfU/edit) | 0/100 (25 tasks (100 files); emailed 11-17-2026) |
| `T27` | Anka Reuel | [Anka_Reuel__native_main_T27.csv](Anka_Reuel__native_main_T27.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1M7B9cln6YiazYfncbpYj-oXujpKl6JCz4vS4W7s7X8A/edit) | 0/100 (25 tasks (100 files); emailed 11-17-2026) |
| `T28` | Max Lamparth | [Max_Lamparth__native_main_T28.csv](Max_Lamparth__native_main_T28.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1buaJ9ZcH2tpzM34j7Y-J3jdfpTeC80DXb_4nj_nTfyY/edit) | 0/100 (25 tasks (100 files); emailed 11-17-2026) |
| `T29` | Varun Raj Madan | [Varun_Raj_Madan__native_main_T29.csv](Varun_Raj_Madan__native_main_T29.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1FNdY9J873-8gOLCWM3ps0zhSQ8rcOMrY4LCVL8oZQng/edit) | 0/100 (25 tasks (100 files); emailed 11-17-2026) |
| `V01` | Slava Naprienko | [Slava_Naprienko__native_main_V01.csv](Slava_Naprienko__native_main_V01.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1ioE_bZBy4g9mQj6-xK2CVtqbzF3FJtiU-UvPYLiCkZo/edit) | 0/100 (25 tasks (100 files); emailed 11-17-2026) |
| `V02` | Nikil Ravi | [Nikil_Ravi__native_main_V02.csv](Nikil_Ravi__native_main_V02.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1iuxZBCPDm0LMSZ2iAgiB9twyHoThcQMPPOGx4eTBnGc/edit) | 1/100 (25 tasks (100 files); emailed 11-17-2026) |
| `V04` | Vaibhav Mahajan | [Vaibhav_Mahajan__native_main_V04.csv](Vaibhav_Mahajan__native_main_V04.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1J7t7N2pd19PnJTrkPq3AIHytEWmtz1HxXdVKnNCpr2g/edit) | 3/100 (25 tasks (100 files); added and emailed 11-17-2026) |

## Historical main sheets — not the current task

Preserve these original 125-row forms and snapshots. Use the current main links above for the 100-file packet. In the original round, Rylan and Sri each had ten assigned items despite their Sheets displaying 125 rows.

| Person | Packet | Raw CSV | Google Sheet | Numeric ratings / displayed rows |
| --- | --- | --- | --- | ---: |
| Brando Miranda | historical main | [Brando_Miranda__setN_A1.csv](Brando_Miranda__setN_A1.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1T14977K9IrUU9JoN_9jUR2uUVbvEP5EsKKl9wh06I_o/edit) | 0/125 |
| Rylan Schaeffer | historical main | [Rylan_Schaeffer__setN_T01.csv](Rylan_Schaeffer__setN_T01.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1GO7o1gVQuY7GWOb294U5So207MMtgk4QoUS9I2eY7TU/edit) | 0/125 |
| Srivatsava Daruru (Sri) | historical main | [Srivatsava_Daruru_Sri__setN_T05.csv](Srivatsava_Daruru_Sri__setN_T05.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/12HDKFei5_zagDN2tqEZMvXbA51117N9Txrxbpd4HWdo/edit) | 0/125 |

[Current completion status](../README.md#ratings-and-completion) · [Raw source ranges, hashes and counts](RAW_MANIFEST.json) · [Restoration record](../support/RAW_DATA_RESTORATION_11-11-2026.md)

## Derived analysis files

[analysis/](analysis/) contains separately labeled historical normalized imports. Those imports lowercase some answers and omit nonnumeric rows. They are not raw submissions and must not be counted again. `refresh_named_ratings.py` writes only those analysis exports by default, never these primary raw tables.

Original snapshots and withdrawn coordinator additions remain in the audit history. Refreshes must preserve exact response values and missingness; do not infer per-item times or fill other responses.
