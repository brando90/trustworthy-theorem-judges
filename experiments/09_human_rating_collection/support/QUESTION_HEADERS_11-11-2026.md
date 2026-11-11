# Full checklist questions in rating forms

**TLDR:** On 11-11-2026 Brando authorized replacing bare A–D headers with their exact rubric questions, keeping scoring unchanged and preserving original packets.

## Instruction files participants receive

- `START_HERE.md`: packet navigation.
- `human_judgements_prompt.md` (warm-up) or `Rating_Instructions.md` (main): scoring rubric. The repository's [warm-up rubric](../rating_task_packet/human_judgements_prompt.md) is a text copy from the user-supplied original ZIP (trailing whitespace removed; original archive unchanged); use the current guide for field names and submission route.
- [RATING_FORM_GUIDE.md](../rating_task_packet/RATING_FORM_GUIDE.md): current field requirements and full checklist questions, included in revised packets.
- `ratings.csv`: generated from [RATING_FORM_SCHEMA.json](RATING_FORM_SCHEMA.json), with headers identical to the corresponding live sheet.

The original questions use “gold,” meaning reference. Only displayed header labels changed; criteria, 0–5 scores, spam deductions and tie-break rule remain the same. New rubric copies retain the original text and append a legacy-label crosswalk. Existing rubric template-copy links are superseded by the guide and personal sheet instructions.

## Scope and provenance

Brando’s warm-up and main pilot sheets were updated in F1:I1. Both corresponding current raw CSVs were refreshed from verified live values. All 6 warm-up and 125 main response rows are unchanged. Other participants’ already-delivered sheets, archives and historical snapshots remain under their recorded versions pending rollout; future forms use v2.3. No messages were sent.

[Before/after tables, preserved CSVs and packet hashes](sheet_exports/11-11-2026_question_headers/) record the change. The original ZIPs and FormV2 ZIPs remain untouched. New FormV3 ZIPs are in the existing private packet directory; the experiment README links the current warm-up. Candidate, reference and Python bytes were verified unchanged. Packet CSVs match the live pilot tables, including row order. The builder now sorts numbered filenames naturally so the main CSV follows its existing sheet order.

## Mandatory consistency check

Before dispatch, compare exact headers and order across the intended participant’s live sheet, packet CSV and shared schema; verify question text, options and required/optional status against the guide. Version replacements and record hashes. Import by field name, accepting historical A–D aliases without rewriting raw responses. AGENTS.md, CLAUDE.md and Cursor rules carry this requirement.

Verification: 30 collection tests and project/design checks passed; paper built without unresolved references or overfull boxes. Both live sheets were visually checked; only checklist column widths were increased for readable wrapping.
