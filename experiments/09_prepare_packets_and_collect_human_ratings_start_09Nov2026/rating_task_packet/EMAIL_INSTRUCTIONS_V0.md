# Email to raters

**TLDR:** One email for both the warm-up and the main rating task. Fill the five bracketed fields for each recipient. Nothing is sent until Brando approves the exact text and says to send.

Fields to fill per recipient:

- `[FIRST NAME]`: the rater's first name.
- `[TASK]`: `warm-up` or `main rating task`.
- `[NUMBER OF FILES]` and `[NUMBER OF TASK FOLDERS]`: counts from that person's Sheet, for example six files in two folders for the warm-up.
- `[PERSONAL SHEET LINK]`: that person's own Sheet only.
- `[PREFERRED DATE]` and `[FINAL DATE]`: written as weekday, MM-DD-YYYY. The earlier 11-13-2026 and 11-15-2026 dates were never sent and need replacing.

## Email

Subject: VeriBench human-rating [TASK]: closes [FINAL DATE]

Hi [FIRST NAME],

Your VeriBench [TASK] packet is attached: [NUMBER OF FILES] agent files in [NUMBER OF TASK FOLDERS] task folders.

Your personal rating sheet:
[PERSONAL SHEET LINK]

1. Unzip the attachment and read START_HERE.md, RATING_FORM_GUIDE.md and human_judgements_prompt.md.
2. In each task folder, compare the agent's theorem statements with the reference statements, using the Python source for context. Rate statement coverage, not proofs.
3. For each file listed in your sheet, enter your final 0–5 score and answer the AI-assisted-rating attestation. Please estimate minutes spent and confidence. A one-sentence rationale is preferred but optional; use problem_note for issues.

Your sheet saves automatically, so there is nothing to send back. Leave unfinished scores blank.

Use artificial intelligence (AI) for localized help understanding Lean notation, a concept or a specific point. Make the final comparison and choose the score yourself; do not ask a model to rate the file or write your rationale. Rate independently. If an incorrect reference prevents a rating, leave the score blank, add a problem note and email me.

If you have both a warm-up and a main rating task, finish the warm-up first.

Please finish by [PREFERRED DATE] if possible; [FINAL DATE] is the final deadline.

P.S. Feel free to email me with any questions. Email is preferred for questions! Happy to clarify anything!

Brando (drafted with Claude)
-----
Brando Miranda
Ph.D. Student
Computer Science, Stanford University
EDGE Scholar, Stanford University
brando9@stanford.edu
website: https://brando90.github.io/brandomiranda/
