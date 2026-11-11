# Human-rating task preparation and collection

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_human_rating_collection/README.md>

**TLDR:** This is the active home for preparing and collecting human ratings of formal specification coverage, with inherited packets and collection records preserved. The current preparation record supplies revised deadlines and individual drafts; collaborator dispatch still requires review of the recipient-specific text and an explicit send instruction.

## Do Brando's warm-up first

[Brando's six-file warm-up packet, personal Google Sheet and instructions](BRANDO_WARMUP.md). Complete this practice set before the full 125-file packet.

**Current form revision, 11-11-2026:** [one shared warm-up/main form](RATING_FORM_GUIDE.md), with [model-assistance disclosure and an attestation](FORM_AMENDMENT_11-11-2026.md). Brando's two live sheets use this revision; the team queue remains held for his pilot and revised-text review. Dispatch agents must read the amendment before using older prepared emails or packets.

**Names first for everyone, 11-11-2026:** all 12 active personal Google Sheets now start with `rater_name,rater_id`, including unanswered forms. [Open every live sheet and its matching CSV snapshot](sheet_exports/11-11-2026_all_raters_name_first/README.md). Seven additional sheets were updated; five already used this layout. Every original cell value, note, validation and format was verified unchanged. New forms use the 18-column schema; historical team forms retain their other existing columns. The same name-first rule applies to future participants and CSV-only submissions.

[Name-first rollout and cross-project rule receipts](NAME_FIRST_ROLLOUT_11-11-2026.md).

[Slava's name-first CSV warm-up](SLAVA_CSV_NAME_FIRST_11-11-2026.md) is prepared and unsent; he uses the emailed CSV route. It contains six blank rows and is not collected rating data.

## Open the collected ratings

**Start here: [ratings by person — names and actual CSV files](RATINGS_INDEX.md).**

[How your Google Sheet becomes a named rating file, and why IDs are retained](IDENTITY_AND_IMPORT.md).

- [Actual rating CSV files](ratings/).
- [Current completion status: who is done and what is missing](COMPLETION_STATUS.md), checked **11-11-2026**.
- [Original import receipts](../../private/09_human_rating_collection/legacy_veribench/human_round/private_ratings_setN/).

The ratings, named index and completion status are directly in this experiment folder on this Mac. The CSV filenames and first column show each person's name; the original IDs, ratings and notes are preserved. These named exports are the same observations as the existing imports, not additional observations. The rating files, named index and completion status are tracked in Git, as requested on 11-11-2026.

## Ownership and scope

**Sole coordinating chat:** [Prepare human grading task](codex://threads/01a1a8f9-dcb7-7381-9368-91d6e51faffd). Read the [11-09-2026 coordination record](COORDINATION_11-09-2026.md) before collection, dispatch or practical judge-development work. It consolidates the former Best human-rating judge chat without dropping its evaluator or unfinished methods 2 and 4 work.

Brando moved this task from VeriBench on **11-09-2026**. Maintain the collection instructions, packet preparation, approved email, assignment tracking, delivery receipts and collection status here. VeriBench V1's separate direction is formal specification coverage checked by a prover, with artificial intelligence guiding proof search; this move does not change that scorer.

The [prospective probabilistic-judge design](../02_probabilistic_ordinal_judge/README.md) remains the methodology for a new collection. The inherited **set N** (the previously prepared frontier-output rating round) has its own fixed materials, assignment rules and exposure history. Moving it does not turn its outputs or ratings into the prospective study's fresh training, validation or test data.

**Required reading for every collection/dispatch agent:** [judge formulations 2 and 4](JUDGE_FORMULATIONS_11-09-2026.md), with the original photos and transcriptions. Formulation 2 develops a judge using training correlation; formulation 4 uses a proper probabilistic training loss. Preserve individual ratings so both can be studied; validation-based selection (1 versus 3) is a distinct intervention. This note does not change participant instructions or dispatch authorization.

## Current delivery status — 11-09-2026

**Prepared materials are available; collaborator dispatch is a separate action.** See the [current preparation record](PREPARATION_11-09-2026.md) rather than the old email for the live schedule and individual drafts.

- The preparation record states a preferred finish of **11-13-2026** and final deadline of **11-15-2026**, superseding the historical 11-06-2026 date without rewriting delivered archives.
- The original approved email names the coordinator's personal sheet and full assignment. The new individual drafts propose the necessary recipient-specific changes; their text approval and dispatch are still separate from this migration.
- Existing participant records, assignments, returned sheets and delivery receipts moved without changing their contents. New roster decisions and dispatch preparation are recorded separately under `private/09_human_rating_collection/preparation_11-09-2026/`; use that active preparation record instead of treating the imported historical roster as current.
- The renamed packet has **25 task folders and 125 candidate files**. The team builder creates a separate blank answer sheet while preserving candidate, Python and reference bytes. A successful archive build does not establish recipient-specific delivery readiness.
- All seven recipient sheet-permission checks are complete; the eighth return route is private CSV by email. The private review freezes eight exact recipient messages and original attachment hashes. Team text/send approval and human completion remain outstanding; access verification did not inspect sealed ratings or establish completion.

## Files

```text
09_human_rating_collection/
├── README.md
├── MIGRATION.json
├── PREPARATION_11-09-2026.md
├── CKPT_human_rating_collection.md
├── scripts/
│   ├── verify_preparation.py
│   ├── make_team_packet.py
│   └── legacy/
│       ├── assign_setN_folders.py
│       ├── import_rating_sheet.py
│       ├── make_rater_zip.py
│       ├── packet_release.py
│       └── score_warmup.py
└── tests/test_collection.py
```

### Private materials

This repository is public. The following coordinator paths are ignored, not publication destinations:

| Material | Coordinator path, relative to this repository |
| --- | --- |
| Original renamed delivery, unchanged | `private/original/` |
| Existing team archives, unchanged | `private/team-folder-01.zip`, `private/team-all-folders.zip` |
| Frozen local coordination documents, packets and sealed materials | `private/09_human_rating_collection/legacy_veribench/human_round/` |
| Pinned committed source, packet-release records and private sheet bindings | `private/09_human_rating_collection/upstream_source/` |
| Active preparation, roster, individual drafts and dispatch queue | `private/09_human_rating_collection/preparation_11-09-2026/` |
| Imported participant records, assignments, submitted sheets and delivery receipts | `private/09_human_rating_collection/legacy_veribench/human_round/private_ratings_setN/` |
| Coordinator's original delivery and personal records | `private/09_human_rating_collection/legacy_veribench/human_round/private_A1/` |
| Exact approved email | `private/09_human_rating_collection/legacy_veribench/human_round/RATER_TASK_EMAIL_LOCKED_11-04-2026.md` |
| Complete file-by-file transfer hashes | `private/09_human_rating_collection/migration_receipt.json` |

The imported `PLAN_setN_rating_round.md` records dated decisions, not the current schedule. Follow [PREPARATION_11-09-2026.md](PREPARATION_11-09-2026.md) for the newer schedule and preparation; preserve the original email's approval history and the localized-assistance wording. Keep delivered archives unchanged; any later approved delivery is a new version with a new receipt. Named collected ratings and completion records are authorized for Git tracking in this experiment; private correspondence, consent and sealed data remain outside public Git.

## Build a team packet

From `~/trustworthy-theorem-judges`:

```sh
python3 experiments/09_human_rating_collection/scripts/make_team_packet.py \
  private/original private/team-folder-01-new.zip --folders 1 --rater T01
```

Use a new output filename and the intended person's verified rater ID (`T01` is Rylan Schaeffer); omit `--folders` for all folders. Omitting `--rater` creates an unassigned template, not a recipient-ready form. The builder checks the original delivery manifest and every included file, preserves the scoring rubric apart from its personal-sheet instruction, and includes `START_HERE.md`, `Rating_Instructions.md`, `ratings.csv` and `FILES.sha256`. It does not send anything or modify a delivered packet.

**Keep the sheet layouts distinct.** This builder's renamed `agent_file*.lean` items are not the inherited `Nxx`/`Wxx` item identifiers. The utilities under `scripts/legacy/` serve the inherited sheets only; do not pass a renamed team answer sheet to that importer or infer its item mapping. Preserve explicit item mappings when reconciling later deliveries.

## Current inherited utilities

The local VeriBench checkout was older than its remote branch. The active utilities therefore retain the committed implementation at `b292c277e176`, while the original local files remain separately preserved. Their inputs come from the matching pinned tree under `private/09_human_rating_collection/upstream_source/experiments/102_rescore_vbv1_paper_fsc_with_validated_judge_rewrite_tmlr_icml/`; `upstream_source/SOURCE_RECEIPT.json` records its revision and hashes. Its private working-directory links resolve to the single imported participant-record store, not duplicate records.

- Assignment retains `--keep` for already-delivered folders; the assignment utility requires NumPy.
- Import retains emailed comma-separated value (CSV) submissions, delivery-route and personal-sheet checks, coordinator-only `--all-folders`, and reference-issue handling. Coordinator sheet identifiers live only in private configuration.
- Warm-up qualification retains amendment C17: the first task (`W01`) determines qualification; the six-file result is a sensitivity, not the qualification verdict. Sealed-key verification, leave-one-expert-out targets, and explicitly permitted missing nonqualifying items remain intact.
- `packet_release.py` verifies release status, packet hashes and the existing reference-acceptance record before packet building or warm-up scoring. Relocation does not grant release approval.
- The inherited recipient builder now refuses to overwrite an existing archive. Use a new output directory for a new delivery; its filename and receipt keep the inherited format.

## Migration and historical consumers

[The public transfer receipt](MIGRATION.json) distinguishes the local snapshot revision from the active utility revision and records utility hashes and verification. The complete private inventory preserves **1,290 files** byte-for-byte, including local coordination changes that were not yet committed in VeriBench. No candidate, reference, rating, score or assignment was changed by relocation.

- The four collection utilities and their packet-release helper now run here; VeriBench's former command paths redirect to these implementations.
- VeriBench's tracked historical packet snapshots and analysis code remain in place because the simulated-rater, judge-transfer and Certification Judge analyses still consume them. They are not a second active collection workflow.
- The two former ignored private working directories in VeriBench are compatibility links to the new private store, not duplicate copies. The collection owner maintains those links until the inherited analysis consumers are updated; remove them only after checking those consumers. The exact paths are in the private migration receipt.
- Prospective generation and the old paper rescoring are not moved or resumed. No sealed rating analysis, model inference or proof search is part of this migration.

## Verification

```sh
python3 -m unittest discover -s experiments/09_human_rating_collection/tests -v
python3 scripts/check_project.py
git diff --check
```

The tests use synthetic packets and submissions, including the current assignment, import, release and qualification rules. When the coordinator's original packet is available, they also verify a real archive build without submitting ratings. Both pinned packet releases and the sealed-key digest were checked separately without scoring real raters. The migration preserves the inherited qualification and assignment algorithms; it does not validate their suitability for the prospective study.
