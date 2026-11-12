# What to enter for each file

Your name (`rater_name`) and file path (`candidate_file`) are prefilled. The internal person key (`rater_id`), item key (`item_id`) and folder (`task_folder`) are also prefilled; they are hidden in Google Sheets and retained in CSVs. Keep these five fields unchanged.

| Column | What to enter |
| --- | --- |
| `final_score_0_5` — required | Your final whole-number score, 0–5, after the rubric and spam adjustment. |
| `ai_assisted_rating_attestation` — required | `yes`, `no` or `unsure` in response to the statement below. |
| `minutes_spent` — requested estimate | Rough minutes for this file, e.g. `10` or `5-10`. Include shared folder-reading time once, with its first file. |
| `confidence` — requested | `low`: substantial uncertainty; `medium`: some uncertainty; `high`: confident in your comparison. |
| `rationale` — **preferred but optional** | One sentence explaining the main coverage or missing guarantee behind your score. Your own words are enough. |
| `problem_note` — if needed | A confusing or incorrect reference, file or instruction; give a small counterexample if possible. Otherwise leave blank. |

**Attestation:** “I used AI for localized assistance. I personally compared the specifications and chose the final score; I did not delegate the rating task to AI.”

Use artificial intelligence (AI) for localized help with Lean notation, a concept or a specific point. You must make the comparison and choose the score yourself; do not ask a model to rate the file or write your rationale. Rate independently without consulting other people's ratings. Answer the attestation honestly; `no` or `unsure` prompts clarification.

If a reference is incorrect and prevents a defensible score, leave the score blank, explain in `problem_note`, and email brandojazz@gmail.com. A blank is not a zero. If you can rate despite an ambiguity, give your score and explain the ambiguity. The checklist and base score are reasoning steps in the rubric, not extra columns to fill.

Use the personal Google Sheet linked in START_HERE.md. Submit the included `ratings.csv` only if your invitation explicitly assigns the CSV route. Missing historical context stays unknown; nobody fills it on a rater's behalf.
