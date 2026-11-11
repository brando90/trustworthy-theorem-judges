# Filling in your human-rating sheet

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_human_rating_collection/RATING_FORM_GUIDE.md>

**TLDR:** The warm-up and main task use the same columns and instructions; only the assigned items differ. For each completed item, enter your final score, disclose any model assistance and answer the attestation.

Form revision: **11-11-2026**. This guide updates the sheet fields and assistance instructions; it does not change the 0–5 scoring rubric or any candidate/reference file. Use the personal Google Sheet linked in your email and `YOUR_RATING_SHEET.txt`, rather than a sheet-copy link in an older rubric. If your email instead assigns a CSV return route, fill the included CSV and email it back; it uses the same columns.

1. Read the folder's Python source and the gold-reference theorem statements.
2. Read each candidate in `agent_lean`. Use the accompanying scoring rubric to compare statement coverage, not proofs. Make the final comparison and score yourself.
3. Fill the matching row in your sheet. Google Sheets saves automatically; save your CSV if that is your assigned route. Keep the prefilled identifiers unchanged and leave unfinished scores blank.

| Fields | What to enter |
| --- | --- |
| `final_score_0_5` — required | Your whole-number score from 0 to 5. |
| `model_assistance` — required disclosure | Write `none`, or the model/tool name and a short description of the localized help, such as `Claude: explained Lean notation`. Using a model is optional. |
| `independent_rating_attestation` — required response | Choose `yes`, `no` or `unsure`. Choose yes only if the statement below is true. Leave blank until you answer. |
| `minutes_spent` — recommended | Approximate minutes for the file, including shared folder-reading time in its first file. Leave blank if unknown; do not invent a time. |
| `lean_familiarity` — recommended | `none`, `some` or `fluent`; repeat the same answer for each row. |
| Checklist A–D and `base_score_0_5` — optional to record | Use the rubric's checklist and spam adjustment when deciding your score. You do not have to transcribe every intermediate answer. |
| `confidence` — optional | `low`, `med` or `high`. |
| `rationale` — optional | A short explanation in your own words. |
| `problem_note` — optional unless a problem prevents rating | Note confusing instructions or a reference problem. Give a small concrete example when possible. |

## Model assistance is encouraged for localized help

You are encouraged to use artificial intelligence (AI) for localized help understanding Lean concepts, a particular theorem, or a specific point you are unsure about. You may also work without AI. Do not ask a model to do the whole rating task, perform the final comparison for you, choose your score, or write your rating rationale. You remain responsible for the final rating.

The attestation is:

> I certify that I did not ask a model to do the full rating task for this file. I made the comparison and chose the final score myself.

Answer honestly. A `no` or `unsure` response prompts clarification; it is not silently converted to `yes`. No one else should fill this answer for you.

Rate independently, without consulting other raters' scores. If a genuinely incorrect reference prevents a rating, leave the score blank, explain the issue in `problem_note` and email Brando. Follow the rubric's existing handling of reasonable reference conventions and uncertainty.

Please aim for **Friday, 11-13-2026**; **Sunday, 11-15-2026** is the final deadline. Email questions to Brando; email is preferred.
