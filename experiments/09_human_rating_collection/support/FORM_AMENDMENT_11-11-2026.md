# Common rating form and assistance disclosure

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_human_rating_collection/support/FORM_AMENDMENT_11-11-2026.md>

**TLDR:** The current warm-up/main form has 18 columns, with the verified `rater_name` first and stable `rater_id` second, including model-assistance disclosure and a human-rating attestation. This is a pilot form revision; preserve historical responses and review the revised team materials after his six-item practice run.

## Verified inconsistency and correction

The full sheet had 13 columns, ending at `problem_note`. The warm-up had 15, adding `minutes_spent` and `lean_familiarity`. On 11-11-2026 both were updated in place to the same ordered 17-column schema (the earlier revision; now superseded by the name-first amendment below). Existing identity, item and score cells were not rewritten. Header notes explain required/recommended/optional fields. Attestations are blank, with `yes`, `no` and `unsure` choices. No response was supplied on a rater's behalf.

The common [rater guide](../RATING_FORM_GUIDE.md) encourages localized model assistance while keeping the comparison, score and rationale human-authored. The score, assistance disclosure and attestation are required for new completed forms. Time and Lean familiarity are recommended; the intermediate checklist, confidence and written explanations remain optional to record. The scoring rubric remains unchanged. This supersedes the prior warm-up wrapper's mandatory timing wording for this new revision, not for historical records.

## What people actually left blank

Counts below come from the current named exports, checked on 11-11-2026. They describe the 15 numeric warm-up observations, not a new collection or a live refresh.

| Rater | Numeric scores | Confidence | Rationale | Problem note | Per-file minutes | Lean familiarity |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Rylan Schaeffer | 6 | 0 | 0 | 6 | 0 | 6 |
| Srivatsava Daruru (Sri) | 6 | 6 | 6 | 1 | 6 | 6 |
| Yegor Denisov-Blanch | 3 | 3 | 3 | 0 | 0 | 3 |

All 15 numeric rows also have the A–D checklist and base score. Yegor's three additional nonnumeric reference-issue rows remain in the raw snapshot; this table is not a claim that he ignored those items. Optional blank notes are not defective ratings. Historical assistance and attestations are unknown unless separately documented; do not backfill defaults or retroactively reject scores for a field that did not exist.

Brando supplied a WhatsApp exchange in which Rylan estimated the six-item warm-up took “Like an hour?” and said “Lean is rough.” Record this as an approximate retrospective total, not six measured ten-minute durations. Brando's subsequent question about model assistance has no answer in the supplied excerpt. The private preparation source stores the verbatim excerpt. [Screenshot and provenance](assets/form_revision_11-11-2026/SOURCE.json) preserve the column inconsistency.

## How to decide whether extra fields help

First complete Brando's six-item pilot and collect short feedback about time and confusing fields. That checks usability; it cannot establish that rationales or confidence improve judge accuracy. Keep the core score observations even when optional fields are absent.

Later compare judges trained with and without training-set rationales under the same task/rater/solver splits, capacity, search budgets and validation selection. Freeze the comparison before opening held-out outcomes; use the existing ranked probability score primary metric and shared secondary panel. Do not give a judge a held-out human rationale, score, confidence or assistance disclosure as an input to predicting that same human rating. Such information would leak the target or change the task.

Confidence and assistance are descriptive metadata unless a separate weighting or exclusion rule is declared prospectively. Do not select only confident or unassisted ratings after seeing which judge benefits. Model assistance changes the annotation condition and may introduce shared model influence; retain model/tool and help-type disclosures, mark historical conditions separately, and report the target as human ratings under the stated assistance policy. An attestation is a self-report, not proof of independence.

## Dispatch and collection

- Apply the same schema and guide to every newly revised warm-up/main packet; the packet sizes must not define different forms.
- Brando's two live sheets are the pilot. Other participants' already-delivered sheets and responses remain intact while he tries it. The prepared team queue stays held and its old text is historical, not ready for dispatch under this amendment.
- Before team dispatch, revise the intended recipients' sheets and attachments with this schema, verify the exact text and links, and obtain the existing required text/send approval. Preserve delivered archives and receipt hashes; create versioned replacements.
- Preserve new metadata through imports and named exports. Count repeated exports by round, rater and item, never as new observations. Missing legacy metadata remains missing.
- Follow-up drafts ask why optional fields were skipped and request approximate timing and assistance details without requesting rerating or revealing other people's scores. Sri filled the requested timing/confidence/rationale fields, so his wording asks about burden rather than alleging missing work.

## Subsequent feedback and simplification proposal

**Background wording clarification, 11-11-2026:** Brando requested more detail than “some.” Keep the same 17 columns, but `lean_familiarity` now accepts a brief free-text account of Lean activities, approximate amount/recency, and separately related coursework or other proof assistants. Request it once in the first item row, not six or 125 times. The common guide and Brando's warm-up/main sheet notes use the same question; Rylan, Yegor and Sri's warm-up header/first-background-cell notes also carry it, preserving all existing answers. Historical labels remain valid historical data, not inferred experience. The importer preserves descriptive text; differing entries prompt a warning rather than discarding ratings. Delivered archives remain immutable; regenerate any future delivery from the updated guide/schema. No feedback email is sent by this clarification.

Brando's 11-11-2026 follow-up reports that Rylan took a programming-languages course with Aiken. This background is recorded separately from Rylan's original Lean-specific self-report in the rater profile, named export and live-sheet notes. Brando has already asked Rylan about skipped fields via WhatsApp; the duplicate email draft was cancelled. Brando subsequently clarified that he did not request these feedback emails. All three drafts are cancelled, their recipients are cleared, and none was sent. Do not request approval again or send them; further feedback outreach needs a new explicit request.

The once-per-rater background clarification above is now applied. Remaining recommendations for a later form revision, not yet applied: collect approximate total time once per packet. Keep per-artifact score, assistance disclosure and optional short reasoning/problem notes. Retain the attestation; consider whether it can be a packet-level declaration covering all included ratings rather than repeated text. Keep the checklist in the instructions and make its intermediate answers optional to record; confidence should remain optional unless a specific analysis needs it. Preserve existing columns/data while Brando tries the six-item pilot and waits for feedback. This proposal does not change the required responses. The name-first amendment below adds one prefilled identity column only.

## Name-first identity amendment, 11-11-2026

Brando requested that the live Google Sheets and CSV files start with each rater’s actual name. The current [18-column form schema](RATING_FORM_SCHEMA.json) places `rater_name` first and `rater_id` second. Names come from the verified roster; IDs remain the assignment and deduplication keys. The four warm-up sheets and Brando’s main sheet receive this identity-only layout change; existing answers and notes move one column right without being rewritten. The score moves from J to K, and Lean background from O to P. Historical team forms retain their other existing fields until the broader form rollout; adding the name does not backfill assistance or attestations.

Prospective personal packet builds prefill both name and ID. Unassigned team templates can still be built, but recipient-specific builds use `--rater` to bind a verified name. Import and export code accepts the name-first header and shifted leading comment rows; a submitted name that conflicts with the roster is flagged rather than silently replaced. Raw imports and delivered ZIP archives stay unchanged.
