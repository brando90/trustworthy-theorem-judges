# Rater names, stable IDs and collection workflow

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_human_rating_collection/support/IDENTITY_AND_IMPORT.md>

**TLDR:** Brando fills his existing Google Sheet normally. Its `A1` code identifies Brando Miranda; collected exports show both the name and ID. Names are for people, IDs are stable keys, and hiding a rater's own name is not a scientific requirement.

## Your sheet is correctly identified

- Person: **Brando Miranda**.
- First column: `rater_name`, prefilled as **Brando Miranda**.
- Second column: stable `rater_id`, prefilled as **A1**.
- [Personal Google Sheet](https://docs.google.com/spreadsheets/d/1T14977K9IrUU9JoN_9jUR2uUVbvEP5EsKKl9wh06I_o/edit#gid=228912708&range=K2), titled **VeriBench set N rating sheet - rater A1 (Brando)** when checked on 11-11-2026.
- The first required score is `K2`, under `final_score_0_5`. No name or ID needs to be edited by the rater.
- The current raw table is [ratings/Brando_Miranda__setN_A1.csv](../ratings/Brando_Miranda__setN_A1.csv), starting with `rater_name,rater_id,...`. Its response cells are blank in the current snapshot; the file does not imply completed ratings.

The coordinator's roster and personal-sheet configuration bind A1 to this exact person and spreadsheet. [RATER_IDENTITIES.json](RATER_IDENTITIES.json) records the display-name mapping for exports. Never infer a person's identity from a score or rely only on a typed display name.

## Why there were codes and hidden names

The original privacy choice is explicit in experiment 02's [Identity splits and assignment](../../02_probabilistic_ordinal_judge/README.md#identity-splits-and-assignment), item 4, and the workshop paper's [reporting section](../../../paper_latex/AAAI_2027_Evaluation_AI_Scientists/08_controls_reporting.tex). They describe restricted identity storage and opaque analysis IDs. They do not claim that hiding a participant's own name in their sheet improves rating accuracy or judge validity.

Keep these distinct:

| Practice | Purpose | Current collection decision |
| --- | --- | --- |
| Stable rater ID | Join assignments, revisions and repeated observations without relying on spelling; preserve rater splits and dependence | Keep alongside the name |
| Hiding rater names in coordinator files | Privacy/release choice, not a demonstrated accuracy improvement | Superseded for the named collection artifacts by Brando's 11-11-2026 instruction; keep them tracked and readable |
| Hiding solver/model identities from raters | Reduce brand or reputation cues while judging the candidate artifact | Preserve the packet's blinded candidate identities |
| Keeping other people's scores out of an independent rating session | Avoid copying or anchoring to another rater's judgment | Preserve independent rating; document prior exposure when relevant |
| Anonymous workshop submission | Venue review format | Separate from collection file naming |

Codes plus a retained name lookup are pseudonyms, not irreversible anonymization. No new rater-anonymization step is needed for this collection. This clarification does not open sealed test data or change the prospective study's train/test assignments.

## Name-first contract for every participant

Active personal Google Sheets and current comma-separated value (CSV) forms start with `rater_name,rater_id`. Prefill each existing item row with the roster-verified person name; keep IDs stable for joins and duplicate detection. Apply this to blank forms and CSV-only participants as well as completed sheets. A CSV table snapshot reproduces its source sheet's headers, row order and cell values; separate normalized analysis exports retain only verified identity metadata in addition to the historical imported fields. No response enrichment is allowed in raw tables. Never infer identity from ratings or overwrite responses to enforce formatting.

[All 12 active sheets and exact current raw tables](../ratings/README.md) were verified on 11-11-2026. Adding a name to a displayed row does not create a new assignment or observation. Keep raw imports and delivered archives immutable; prepare future revisions with the shared schema. Related VeriBench and judge repositories point here rather than maintaining competing rosters or collection workflows.

## From Google Sheets to the experiment folder

This is a coordinator-run collection sync, **not a live background mirror**. Google Sheets saves the rater's work immediately; the local experiment files update when collection is run.

1. Fetch the correct personal sheet using the recorded sheet ID. Preserve a timestamped raw snapshot, source metadata and hash. Save the exact header and item-row values in person-first CSV files directly under `ratings/`, with `RAW_MANIFEST.json` recording source ranges and hashes. Keep case, spelling, blanks and all N/A rows unchanged; compare the parsed CSV back to the sheet table. Verified names and IDs are the only prefilled identity metadata. Never insert inferred timings, background, confidence, rationales or attestations into raw response cells; conversational context and analysis belong in separate notes. Preserve historical snapshots as history, not current raw data.
2. Validate rater identity, packet/item mapping, assigned folders and allowed rating values. Keep blank scores missing, preserve reference-issue notes and retain revision history. Match observations by round/packet, rater ID and item ID; a refresh is not another independent rating.
3. Save validated imports. The inherited importer handles historical schemas. Brando's renamed `agent_file01` / `Files_To_Rate01` schema must be reconciled against the preserved packet identity mapping before any historical-ID analysis; do not blindly feed renamed item IDs into the legacy template or guess a mapping. Naming exports does not replace this validation.
   The active importer now preserves submitted metadata columns, including `model_assistance` and `independent_rating_attestation`, rather than discarding them against a legacy header. It warns on missing new-form disclosures and flags `no`/`unsure` attestations for review while retaining the rating. Older submissions without these fields retain their original meaning; missing is not an affirmative attestation or evidence of no assistance.
4. If normalized analysis copies are needed, run the identity-labeling step from the repository root:

   ```bash
   python3 experiments/09_human_rating_collection/support/scripts/refresh_named_ratings.py
   ```

   It reads already imported files from the canonical import directory, joins [RATER_IDENTITIES.json](RATER_IDENTITIES.json), places `rater_name` first and `rater_id` second, verifies an already-present name against the roster, and writes person-first filenames under `ratings/analysis/`. It refuses an output directory resolving to the primary `ratings/` folder. An unknown or mismatched rater, malformed row or duplicate item stops the batch before output. Normalized-input columns and values are preserved. This is not raw-data recovery: the historical importer already changed some capitalization and omitted Yegor’s N/A rows. The exporter does not load coordinator background or timing estimates. Leading sheet-comment rows remain readable if the new name column shifts the comment into column B. A manifest records source and named-export hashes. It performs no live download, qualification decision or score analysis.

5. Refresh `RATINGS_INDEX.md`, `COMPLETION_STATUS.md` and the collection summary from the same snapshot; verify the named export manifests, then commit and push the named collection artifacts. The name-enrichment command alone does not refresh completion status.

Verified on 11-11-2026: the 12 primary CSVs match the exact restored sheet tables, and all original fields in Rylan, Sri and Yegor’s six-row submissions match pre-enrichment raw snapshots. The three normalized analysis exports reproduce their unchanged historical normalized inputs plus names. Synthetic checks cover A1 naming, zero versus missing scores, repeated export, wrong/unknown identity and duplicate items. No synthetic scores were written into real rating files or Google Sheets.
