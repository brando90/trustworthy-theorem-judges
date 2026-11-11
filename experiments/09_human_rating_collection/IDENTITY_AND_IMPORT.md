# Rater names, stable IDs and collection workflow

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_human_rating_collection/IDENTITY_AND_IMPORT.md>

**TLDR:** Brando fills his existing Google Sheet normally. Its `A1` code identifies Brando Miranda; collected exports show both the name and ID. Names are for people, IDs are stable keys, and hiding a rater's own name is not a scientific requirement.

## Your sheet is correctly identified

- Person: **Brando Miranda**.
- Stable `rater_id`: **A1**, already present in the rating rows.
- [Personal Google Sheet](https://docs.google.com/spreadsheets/d/1T14977K9IrUU9JoN_9jUR2uUVbvEP5EsKKl9wh06I_o/edit#gid=228912708&range=J2), titled **VeriBench set N rating sheet - rater A1 (Brando)** when checked on 11-11-2026.
- The first required score is `J2`, under `final_score_0_5`. No name or ID needs to be edited by the rater.
- Once scores are imported, the named export will be `ratings/Brando_Miranda__setN_A1.csv`, starting with `rater_name,rater_id,...`. This is a future output, not a claim that Brando has completed ratings.

The coordinator's roster and personal-sheet configuration bind A1 to this exact person and spreadsheet. [RATER_IDENTITIES.json](RATER_IDENTITIES.json) records the display-name mapping for exports. Never infer a person's identity from a score or rely only on a typed display name.

## Why there were codes and hidden names

The original privacy choice is explicit in experiment 02's [Identity splits and assignment](../02_probabilistic_ordinal_judge/README.md#identity-splits-and-assignment), item 4, and the workshop paper's [reporting section](../../paper_latex/AAAI_2027_Evaluation_AI_Scientists/08_controls_reporting.tex). They describe restricted identity storage and opaque analysis IDs. They do not claim that hiding a participant's own name in their sheet improves rating accuracy or judge validity.

Keep these distinct:

| Practice | Purpose | Current collection decision |
| --- | --- | --- |
| Stable rater ID | Join assignments, revisions and repeated observations without relying on spelling; preserve rater splits and dependence | Keep alongside the name |
| Hiding rater names in coordinator files | Privacy/release choice, not a demonstrated accuracy improvement | Superseded for the named collection artifacts by Brando's 11-11-2026 instruction; keep them tracked and readable |
| Hiding solver/model identities from raters | Reduce brand or reputation cues while judging the candidate artifact | Preserve the packet's blinded candidate identities |
| Keeping other people's scores out of an independent rating session | Avoid copying or anchoring to another rater's judgment | Preserve independent rating; document prior exposure when relevant |
| Anonymous workshop submission | Venue review format | Separate from collection file naming |

Codes plus a retained name lookup are pseudonyms, not irreversible anonymization. No new rater-anonymization step is needed for this collection. This clarification does not open sealed test data or change the prospective study's train/test assignments.

## From Google Sheets to the experiment folder

This is a coordinator-run collection sync, **not a live background mirror**. Google Sheets saves the rater's work immediately; the local experiment files update when collection is run.

1. Fetch the correct personal sheet using the recorded sheet ID. Preserve a timestamped raw snapshot, source metadata and hash.
2. Validate rater identity, packet/item mapping, assigned folders and allowed rating values. Keep blank scores missing, preserve reference-issue notes and retain revision history. Match observations by round/packet, rater ID and item ID; a refresh is not another independent rating.
3. Save validated imports. The inherited importer handles historical schemas. Brando's renamed `agent_file01` / `Files_To_Rate01` schema must be reconciled against the preserved packet identity mapping before any historical-ID analysis; do not blindly feed renamed item IDs into the legacy template or guess a mapping. Naming exports does not replace this validation.
   The active importer now preserves submitted metadata columns, including `model_assistance` and `independent_rating_attestation`, rather than discarding them against a legacy header. It warns on missing new-form disclosures and flags `no`/`unsure` attestations for review while retaining the rating. Older submissions without these fields retain their original meaning; missing is not an affirmative attestation or evidence of no assistance.
4. Run the name-enrichment step from the repository root:

   ```bash
   python3 experiments/09_human_rating_collection/scripts/refresh_named_ratings.py
   ```

   It reads already imported files from the canonical import directory, joins [RATER_IDENTITIES.json](RATER_IDENTITIES.json), adds `rater_name` as the first column and writes person-first filenames under `ratings/`. An unknown or mismatched rater, malformed row or duplicate item stops the batch before output. Original columns and values are preserved. A manifest records source and named-export hashes. It performs no live download, qualification decision or score analysis.

5. Refresh `RATINGS_INDEX.md`, `COMPLETION_STATUS.md` and the collection summary from the same snapshot; verify the named export manifests, then commit and push the named collection artifacts. The name-enrichment command alone does not refresh completion status.

Verified on 11-11-2026: name enrichment reproduces the three existing named exports without changing any original fields. Synthetic checks cover A1 naming, zero versus missing scores, repeated export, wrong/unknown identity and duplicate items. No synthetic scores were written into real rating files or Google Sheets.
