# Email to raters

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026/rating_task_packet/EMAIL_INSTRUCTIONS_V0.md>

**TLDR:** Brando's current best rater email (11-17-2026) is first, verbatim; the earlier placeholder template for the warm-up and main task is kept below it. Fill the bracketed placeholders per recipient; send nothing until Brando approves the exact text and says to send.

Placeholders and routing per recipient:

- `[FIRST NAME]`: the rater's first name (one person per email).
- `[TASK]`: `warm-up` or `main rating task`.
- `[NUMBER OF FILES]` and `[NUMBER OF TASK FOLDERS]`: counts from that rater's personal Sheet (for example `6` files in `2` task folders for the warm-up, or `100` files in `25` task folders for the full-team main packet).
- `[PERSONAL SHEET LINK]`: that rater's own Google Sheet URL only (`Anyone with the link = Editor`). If their personal Sheet will not open, they can reply to the rating email with the filled `ratings.csv` attached (or send it to `brando9@stanford.edu` / `brandojazz@gmail.com`).
- `[PREFERRED DATE]` and `[FINAL DATE]`: written as `Weekday, MM-DD-YYYY` (for the 100-file full-team batch: `Thursday, 11-19-2026, 6pm PT` preferred and `Sunday, 11-22-2026` final).
- **Routing:** send as a new email from `brandojazz@gmail.com` with that recipient's packet `.zip` attached; blind-copy (BCC) `brando.science@gmail.com`, `brandojazz@gmail.com` and `brando9@stanford.edu`; use visible CC only on request; include no chat `TLDR` line in the rater email.

## Current draft: Brando's best so far (11-17-2026)

Brando's own text, recorded verbatim on 11-17-2026 ("best so far"). Editable source: [Google Doc, tab "Draft v2 (rubric link)"](https://docs.google.com/document/d/1KJQHxA-pSMxr31ZPMq8dI5bWPjnObQ2CHlQZ6g5r3f8/edit?tab=t.bmtmw71ddlms). The sheet link shown is Brando's own (`A1`); each recipient gets their own personal Sheet link. Not yet applied to the 31 team Gmail drafts, and nothing is sent: the team-email hold is unchanged.

```text
Hi <Person Name>,

Attached is your theorem correctness & coverage rating packet. Your sheet lists the files in your own order; please work from the top down and do as many as you can, even a few help.

Your personal rating sheet:
https://docs.google.com/spreadsheets/d/1zUDr9fpUwK0IuxrSdFfBR_mOt4WwMY8-doBC6cIhIHM/edit

What to do:

1. Unzip the attachment and read START_HERE.md.
2. In each task folder, compare the agent's theorem statements (agent_lean/) with the reference statements (gold_lean/) and score how well they cover the reference: theorem statements only, not proofs (if present).
   1. Use the rubric in human_judgements_prompt.md
      1. [https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026/rating_task_packet/human_judgements_prompt.md]
3. For each file enter a score from 0 to 5.
   1. A one-sentence rationale in your own words is welcome but optional, and RATING_FORM_GUIDE.md explains every column.
   2. Please choose the score yourself. You are allowed to use AI –ideally mostly for Lean or localized questions. Don’t feed the whole task to an agent and ask it to do it for you please.
   3. If models/agents give you options and you choose one, that is the type of thing we want to measure!


Please your first round by finish by 6pm Pacific on Thursday, 19-Nov--2026 if you can. Filling it in as you go works too!

Feel free to email me or DM with any questions.

Regards, Brando
```

## Earlier template (11-12-2026; superseded by the draft above)

### Email

Subject: VeriBench human-rating [TASK]: closes [PREFERRED DATE]

Hi [FIRST NAME],

[OPTIONAL PERSONALIZED OPENER — co-author invite / weekend request / Karpathy & Rylan ML data advice]Your VeriBench [TASK] packet is attached: [NUMBER OF FILES] agent files in [NUMBER OF TASK FOLDERS] task folders. Your sheet lists them in your own order; please work from the top down and do as many as you can, even a few helps.

Your personal rating sheet:
[PERSONAL SHEET LINK]

1. Unzip the attachment and read START_HERE.md, RATING_FORM_GUIDE.md and human_judgements_prompt.md.
2. In each task folder, compare the agent's theorem statements in agent_lean/ with the reference statements in gold_lean/, using python_source/ for context. Rate formal specification statement coverage, not proofs.
3. For each file listed in your sheet, enter final_score_0_5 (whole number 0–5) and ai_assisted_rating_attestation (yes, no or unsure; if you rated a short file personally without AI, enter no and write "rated personally without AI" in problem_note). Please estimate minutes_spent and confidence (low, medium or high). A one-sentence rationale is preferred but optional; use problem_note for issues.

Your sheet saves automatically, so there is nothing to send back (if your sheet will not open, reply to this email with your filled ratings.csv attached). Leave unfinished scores blank.

Use artificial intelligence (AI) for localized help understanding Lean notation, a concept or a specific point. Make the final comparison and choose the score yourself; do not ask a model to rate the file or write your rationale. Rate independently. If an incorrect reference prevents a rating, leave final_score_0_5 blank, add a problem_note and email me.

If you have both a warm-up and a main rating task, finish the warm-up first.

Please finish by [PREFERRED DATE] if possible ([FINAL DATE] is the final deadline).

P.S. Feel free to email me with any questions. Email is preferred for questions! Happy to clarify anything!

Brando (drafted with Antigravity)
-----
Brando Miranda
Ph.D. Student
Computer Science, Stanford University
EDGE Scholar, Stanford University
brando9@stanford.edu
website: https://brando90.github.io/brandomiranda/
