# Start here: rating VeriBench Lean files (set N)

**What you do:** for each agent Lean file in this packet, give **one score from 0 to 5** saying how well its theorem statements cover the reference's theorem statements. Proofs do not matter.

## Steps

1. **Make your rating sheet (1 minute):** open https://docs.google.com/spreadsheets/d/1HhHqWLjWo7-dDORBBdQF6klOXua3boknpkfKHEjledc/copy and click "Make a copy". Type your name in the `rater_id` column of the rows you fill.
2. **Read the rules once (5 min):** `human_judgements_prompt.md`. Same instructions as the May round, unchanged; ignore its own Google Sheet link and use your copy from step 1.
3. **Rate every folder in this packet** (`N01/`, `N02/`, ...). Each folder is one task:
   - `python_source/*.py`: the Python program the agents had to formalize.
   - `gold_lean/*.lean`: the reference Lean file. Its theorem statements are what "full coverage" means.
   - `agent_lean/`: five agent files, blinded and in random order.

   For each agent file, find the gold theorem statements, check whether the agent states the same, an equivalent or a stronger property, and run the checklist:
   - A: are the key gold theorems covered?
   - B: are the gold pre/postconditions kept or strengthened?
   - C: is there theorem spam?
   - D: if so, a handful or does it dominate?

   Then give the 0-5 base score and the spam adjustment from the rules file. Unsure between two scores? Take the lower one.
4. **Fill one row per file in your sheet,** only for the folders in this packet (leave the other rows empty): `final_score_0_5` is **required**; everything else (A-D, base score, confidence, rationale, problem_note) is optional but helpful.
5. **Hand it in by sharing:** in your sheet click Share and add **brandojazz@gmail.com** as a Viewer. That's all: sharing the sheet is how you submit it. Please don't edit it afterwards.

## Good to know

- **Time:** roughly 1-2 hours per folder (an estimate; long files are normal).
- **Deadline:** please share your sheet within two weeks of receiving this packet; the round closes on Fri 11-06-2026.
- **No Lean expertise needed:** you compare theorem statements; you never write or check proofs.
- **Your sheet is saved when you share it:** that snapshot is your submission, so finish all your folders before sharing. If you need to change something afterwards, email brandojazz@gmail.com instead of editing.
- **Questions:** brandojazz@gmail.com.

**Rules:** rate on your own, no AI tools, don't discuss items with other raters until everyone is done. Long files are normal: skim for `theorem`/`lemma` statements first.
