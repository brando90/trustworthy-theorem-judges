# Light QA review — human-rating form v5 preparation (11-11-2026)

**Reviewer:** Claude Fable 5.1, effort max (requested opposite-company round; one round, no re-review).
**Scope:** uncommitted diff in `trustworthy-theorem-judges` (38 modified files plus two untracked paths under `experiments/09_human_rating_collection/support/`), `private/09_human_rating_collection/preparation_11-09-2026/{CURRENT_PREPARATION.json,DISPATCH_QUEUE_FORM_V5.json,REVIEW_TEAM_EMAILS_FORM_V5.md}` and `packets/FormV5/MANIFEST.json` with its thirteen archives.
**Not done, by instruction:** no messages or emails sent, no Google Sheets edited, no Lean/Python payload or rubric threshold touched, no commit or push, no extra reviewers.

**TLDR:** No blocking defect. Raw data, packets and dispatch materials verify exactly against their receipts. I fixed four small documentation/test leftovers (listed below). Two low-severity wording decisions remain for Brando.

## Verdict

**PASS with minor fixes applied.** The change set is internally consistent and dispatch-safe: thirteen FormV5 packets preserve the pinned scientific bytes and ship blank eleven-column forms with only the recipient's own sheet link; the eight previews are hash-pinned, unsent, and addressed per the roster; the twelve raw CSVs equal the read-back sheet cells and the restored participant context equals the pre-removal snapshots. Remaining items are wording choices, not correctness problems.

## Deterministic checks run

| Check | Result |
| --- | --- |
| `python3 -m pytest experiments/09_human_rating_collection/support/tests -q` | 33 passed, 7 subtests (before and after my edits) |
| `python3 scripts/check_project.py` | passed (design, mirrored instructions, source hashes, style, paper inputs) |
| `git diff --check` | clean |
| `cmp AGENTS.md CLAUDE.md` | identical |
| Packet verifier (`/tmp/qa_tj/verify_formv5b.py`, my script) over all 13 FormV5 archives | no problems |
| Raw-manifest verifier (`/tmp/qa_tj/verify_raw.py`) over 12 CSVs | all hashes, row counts, 15 numeric and 3 N/A counts match |
| Relative links in every changed Markdown file | all resolve |
| Dictionary scan of changed prose and the eight previews | no misspellings; participant text (`divsor`) preserved verbatim as required |

## What was verified (evidence)

- **Packets (13).** Source and output SHA-256 equal `MANIFEST.json`; queue `attachment_sha256` equals the manifest. Every `.lean`/`.py` member is byte-identical to the pinned source archive after the `WARMUP_PATHS.json` descriptive-path mapping (10 files per warm-up, 14/16 per set-N subset, 177 for Brando's full packet). Rubric text outside `## Output format` is byte-identical to the source; no `## Current form headers` residue. `RATING_FORM_GUIDE.md` in every archive equals the repo copy. `ratings.csv` has exactly the eleven schema columns, the verified name and ID on every row, all six response cells blank, and row counts 6/10/125 as recorded. `task_folder` and `candidate_file` match the live-sheet CSV for every row (0 mismatches, including the 10-of-125 set-N subsets for Rylan and Sri). Only the recipient's own sheet URL appears; Slava's archive has none. No `YOUR_RATING_SHEET.txt`, no email draft, `FILES.sha256` complete and correct, no stale "fill only / two fields / required-only / model_assistance / lean_familiarity" wording.
- **Dispatch queue and previews (8).** Body and header files hash-match `DISPATCH_QUEUE_FORM_V5.json`; each body appears verbatim in `REVIEW_TEAM_EMAILS_FORM_V5.md`. `To` addresses equal `ROSTER.csv` and the 11-09 verified manifest; BCC lists the three required inboxes; `new_message` true; `send_authorized` false in `CURRENT_PREPARATION.json`. Sheet links equal the `RAW_MANIFEST.json` spreadsheet ID for the same rater and packet. Greetings and subjects are unchanged from the 11-09 previews. The rubric filename named in the emails (`human_judgements_prompt.md`) exists in all eight attachments. Rylan N17+N21 and Sri N01+N23 match `ASSIGNMENT_delivered.csv`.
- **Raw data (12 CSVs).** Hashes equal `RAW_MANIFEST.json` and `SUMMARY.json`; 15 numeric warm-up scores, 3 N/A rows, every attestation blank, no main scores. The three set-N CSVs changed only by appending four blank columns (first seven columns byte-identical to HEAD). In `after.json` the read-back `formattedValue` grid equals each CSV header and body, with no extra non-blank rows. Restored context equals the pre-removal snapshots whose hashes are pinned in `restoration_sources.json`, and agrees with the earliest October imports: Rylan's six notes were always in `problem_note`; Sri's times 4,2,2,4,5,5 (sum 22) and `high` confidences; Yegor's `Medium`/`N/A` is the real sheet spelling (the legacy import lowercased it to `med`). Columns B:D are hidden in all 12 sheets; attestation validation is strict `yes/no/unsure`; confidence validation is non-strict `low/medium/high`, so historical `Medium` and `N/A` survive; the obsolete row-1 instruction on the Dilara, Allen and Don sheets was deleted and no stale wording remains in header notes.
- **Public hygiene.** No email addresses in the new public exports; `private/` is git-ignored; AGENTS.md, CLAUDE.md and the Cursor mirror agree with the eleven-column decision; no stale seven-column statements outside dated history folders.
- **Concurrent edits.** `support/CKPT_human_rating_collection.md`, `support/IDENTITY_AND_IMPORT.md` and `support/SLAVA_CSV_NAME_FIRST_11-11-2026.md` changed at 12:33–12:34 during this review; their diffs are consistent with the rest (F2 score cell, eleven columns, FormV5 links).

## Findings

| # | Severity | File:line | Finding | Status |
| --- | --- | --- | --- | --- |
| 1 | Medium | `private/RATE_TODAY.md:3,10,15` | Brando's pilot guide linked `experiments/09_human_rating_collection/BRANDO_WARMUP.md` and `.../RATING_FORM_GUIDE.md`, which moved to `support/` and `rating_task_packet/` (both links were broken), and told him to score at cell J2 although every live sheet now has `final_score_0_5` in column F. | Fixed: links repointed, J2→F2, added the FormV5 replacement packet beside the frozen original. |
| 2 | Medium | `private/09_human_rating_collection/preparation_11-09-2026/README.md:5-7` | The coordinator README still presented the 11-09 drafts, original attachments and "sheet at J2" as the review set; a reader starting there could dispatch superseded texts despite `CURRENT_PREPARATION.json`. | Fixed: added a "Current version — 11-11-2026" block pointing to the FormV5 review, queue, manifest and pilot packet; older sections kept as history. |
| 3 | Low | `experiments/09_human_rating_collection/support/sheet_exports/11-11-2026_final_form/README.md:9` | "Restored verbatim" did not say that historical checklist answers (A–D), base scores and Lean-familiarity labels were deliberately not restored (not form columns) and live only in the pre-removal snapshots and analysis copies; `after.json` stores `expected` scores as JSON numbers, so a naive equality against the text CSVs fails for the three restored warm-ups even though the read-back cells match exactly. | Fixed: two sentences added. |
| 4 | Low | `experiments/09_human_rating_collection/support/tests/test_form_revision.py:57` | Test still named `test_required_only_submission_preserves_scoring_sections` after the helper became `current_form_rubric`. | Fixed: renamed to `test_current_form_rubric_preserves_scoring_sections`; 33 tests pass. |
| 5 | Low | `experiments/09_human_rating_collection/rating_task_packet/EMAIL_INSTRUCTIONS_V0.md:1-18` | The packet-folder email draft is now addressed "Hi Brando" with subject "VeriBench human-rating task", a shortened AI paragraph, and the signature block and "Brando (drafted with …)" sign-off removed. The eight FormV5 previews keep the approved prose, subjects and signature. AGENTS.md still calls this file the approved email template. | Open, Brando's call: either restore the sign-off/signature so the template matches the previews and the shared email rule, or label the README row as a pilot-only note. Not edited (his editable text). |
| 6 | Low | `experiments/09_human_rating_collection/support/RATING_FORM_SCHEMA.json:19-27` | `rationale` is listed under both `recommended` and `optional` to encode "preferred but optional"; the test pins this. Harmless unless a consumer treats the lists as disjoint. | Open, informational. |
| 7 | Low | `experiments/09_human_rating_collection/support/scripts/legacy/import_rating_sheet.py:181-189` | Minutes accept numbers and ordered ranges (hyphen or en dash) but reject free text such as `~10` or `5 min` with a whole-import error. Consistent with the guide's "e.g. 10 or 5-10"; the coordinator should expect to ask the rater rather than invent a value. | Open, informational. |
| 8 | Info | Sheets (after.json) | `final_score_0_5` carries no data validation; that is required so `N/A` entries remain enterable. | No change. |

## Files changed by the reviewer

1. `experiments/09_human_rating_collection/support/tests/test_form_revision.py` — test method rename only.
2. `experiments/09_human_rating_collection/support/sheet_exports/11-11-2026_final_form/README.md` — two sentences appended to the restoration paragraph.
3. `private/09_human_rating_collection/preparation_11-09-2026/README.md` — new "Current version — 11-11-2026" pointer block after line 3.
4. `private/RATE_TODAY.md` — two link targets, J2→F2, one added packet link.

No rating value, packet archive, receipt, schema, rubric, Lean/Python file or Google Sheet was changed.

## Remaining for the parent

- Decide finding 5 (email template sign-off) and, if desired, note findings 6–7 in the schema or import docs.
- Re-run `python3 -m pytest experiments/09_human_rating_collection/support/tests -q`, `python3 scripts/check_project.py` and `git diff --check` before landing (all passed here after my edits).
- Dispatch remains blocked on Brando's pilot, approval of the exact FormV5 texts and an explicit send instruction, as every status file states.
