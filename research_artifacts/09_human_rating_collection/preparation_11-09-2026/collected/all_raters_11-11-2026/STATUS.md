# Human-rating collection status — 11-11-2026

**TLDR:** Twelve live Google Sheets were checked and saved privately. No new or revised numeric ratings were found: 15 warm-up ratings match existing imports; the delivered main assignments remain blank.

| Person | Warm-up | Main assignment / next missing work |
| --- | --- | --- |
| Rylan Schaeffer | 6/6 numeric ratings; already imported; qualified | 0/10 assigned ratings, folders N17 and N21 |
| Srivatsava Daruru (Sri) | 6/6 numeric ratings; already imported; qualified | 0/10 assigned ratings, folders N01 and N23 |
| Yegor Denisov-Blanch | 3 numeric ratings plus 3 N/A reference-issue entries; already imported | Preserve existing extra-only decision; no primary assignment |
| Dilara Soylu | 0/6 | Warm-up pending |
| Allen Nie | 0/6 | Warm-up pending |
| Donald Poindexter Jr | 0/6 | Warm-up pending |
| Simon Obstbaum | 0/6 | Warm-up pending |
| Nikil Ravi | 0/6 | Warm-up pending |
| Slava Naprienko | No returned CSV found in scoped mail searches | Email return route, not a Google Sheet; completion unverified |
| Brando Miranda | Historical warm-up sheet 0/6 | Personal full packet 0/125; author ratings are additional |

## What is missing

The inherited primary collection requires 250 ratings: two independent qualified ratings for each of 125 candidate files. The four delivered folder slots account for 20 assigned ratings, all currently blank. Another 46 folder slots (230 ratings) have not been assigned in the preserved delivery ledger. Pending volunteers' historical capacity is not a renewed commitment. No participant has a completed main assignment in the checked sheets.

Jacob and Mo declined; Bo and Sanmi are excluded from recruitment. Unassigned prospects are not counted as missing submissions. No reminders were sent, and the hold on team dispatch remains in force.

## Saved evidence and duplicate handling

- [SUMMARY.json](SUMMARY.json): counts, per-sheet sources and comparison records.
- [sheet_snapshots.json](sheet_snapshots.json): exact returned range values and metadata for all 12 sheets.
- Each packet/rater subfolder contains ratings.csv and SOURCE_RECEIPT.json, including source URL, range, last-modified time and CSV hash.
- [SEARCH_RECEIPT.json](SEARCH_RECEIPT.json): sheet inventory and scoped mail-search metadata. Mail searches included Slava's known address, participant attachments since 10-01-2026, and Slava/name/round keywords; no returned rating attachment was found. This is not proof that no offline work exists.
- Duplicate keys are round/packet + rater identity + item identity. Revisions replace an observation's current version rather than create another independent observation. Across the checked sources there are 15 numeric observations matching existing imports, zero new keys, zero revised scores and no previously imported scores missing from their source.
- Existing canonical imports remain under [the canonical private store](../../../legacy_veribench/human_round/private_ratings_setN/); the exact resolved paths are recorded in each source receipt. No canonical import or qualification was changed.
- Warm-up observations and N/A entries stay separate from main-task ratings. Blank cells are missing, never zero scores. No judge fitting, selection or sealed-test analysis was performed.

All files remain in the repository's ignored private collection area. This is collection evidence, not a fresh validation dataset.
