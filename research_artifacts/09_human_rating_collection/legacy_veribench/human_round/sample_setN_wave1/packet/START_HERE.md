# Start here: rating VeriBench Lean files (set N)

**What you do:** for each agent Lean file, give **one score from 0 to 5** saying how well its theorem statements cover the reference's theorem statements. Proofs do not matter. Write the score in `rating_sheet.csv`.

## Steps

1. **Read the rules once (5 min):** `human_judgements_prompt.md`. Same instructions as the May round, unchanged.
2. **Open your first folder**, e.g. `N01/`. Each folder is one task:
   - `python_source/*.py`: the Python program the agents had to formalize.
   - `gold_lean/*.lean`: the reference Lean file. Its theorem statements are what "full coverage" means.
   - `agent_lean/N01a.lean`, `N01b.lean`, …: agent files, blinded and in random order (up to five; some folders have fewer).
3. **For each agent file:** find the gold theorem statements, check whether the agent states the same, an equivalent or a stronger property, and run the checklist:
   - A: are the key gold theorems covered?
   - B: are the gold pre/postconditions kept or strengthened?
   - C: is there theorem spam?
   - D: if so, a handful or does it dominate?

   Then give the 0-5 base score and the spam adjustment from the rules file. Unsure between two scores? Take the lower one.
4. **Fill one row per file** in `rating_sheet.csv`: put your name or initials in `rater_id`. `final_score_0_5` is **required**; everything else (A-D, base score, confidence, rationale, problem_note) is optional but helpful.
5. **Return** the sheet by email to Brando. Rate only the folders you were assigned.

**Rules:** rate on your own, no AI tools, don't discuss items with other raters until everyone is done. Long files are normal: skim for `theorem`/`lemma` statements first.
