# Raw participant ratings

**Current form, 11-11-2026:** all 12 live Sheets and primary raw CSVs have five prefilled identifiers plus final score, model-assistance disclosure and independent-rating attestation. Optional/recommended columns were removed. All retained scores, N/A entries, row order and assignments are unchanged; historical missing disclosures remain unknown. [Revision and preserved source data](../support/sheet_exports/11-11-2026_required_only/README.md).


**Checked: 11-11-2026.** These CSV tables match the current Google Sheets response values exactly. Names and IDs are prefilled identity metadata. Participant responses, blanks, capitalization, spelling, and N/A entries are unchanged. Rylan’s assistant-estimated times and assistant-written background annotations have been removed.

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
| Brando Miranda | setN | [Brando_Miranda__setN_A1.csv](Brando_Miranda__setN_A1.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1T14977K9IrUU9JoN_9jUR2uUVbvEP5EsKKl9wh06I_o/edit) | 0/125 |
| Rylan Schaeffer | setN | [Rylan_Schaeffer__setN_T01.csv](Rylan_Schaeffer__setN_T01.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/1GO7o1gVQuY7GWOb294U5So207MMtgk4QoUS9I2eY7TU/edit) | 0/125 |
| Srivatsava Daruru (Sri) | setN | [Srivatsava_Daruru_Sri__setN_T05.csv](Srivatsava_Daruru_Sri__setN_T05.csv) | [Open sheet](https://docs.google.com/spreadsheets/d/12HDKFei5_zagDN2tqEZMvXbA51117N9Txrxbpd4HWdo/edit) | 0/125 |

Yegor’s warm-up contains all six submitted rows: three numeric ratings and three `N/A` reference-issue entries. Empty sheets are included for convenience; blank rows are not completed observations. Rylan and Sri each have ten assigned main items even though their sheets display 125 rows.

[Current completion status](../COMPLETION_STATUS.md) · [Raw source ranges, hashes and counts](RAW_MANIFEST.json) · [Restoration record](../support/RAW_DATA_RESTORATION_11-11-2026.md)

## Derived analysis files

[analysis/](analysis/) contains separately labeled historical normalized imports. Those imports lowercase some answers and omit nonnumeric rows. They are not raw submissions and must not be counted again. `refresh_named_ratings.py` writes only those analysis exports by default, never these primary raw tables.

The original sheet snapshots and withdrawn coordinator additions remain in the audit history. New collection refreshes must preserve exact response values and missingness; do not infer per-item times or fill other responses.

**Combined attestation, 11-11-2026:** all 12 live sheets and current raw CSVs now contain the final score plus one AI-assisted rating attestation. Scores and identifiers are unchanged; every new attestation remains blank. Earlier ratings are not evidence of AI use. Pre-change responses and readback are preserved in `support/sheet_exports/11-11-2026_combined_attestation/` (relative to the experiment root).
