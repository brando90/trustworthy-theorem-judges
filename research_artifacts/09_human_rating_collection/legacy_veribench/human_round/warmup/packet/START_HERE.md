# Start here: the warm-up set (about 30-45 minutes)

**What this is:** six short agent Lean files from an earlier rating round, in two task folders (`W01`, `W02`).
Everyone on the panel rates the same six files first. It is practice with the real instructions, and it shows
how each person uses the 0-5 scale. Rate exactly as you will rate your task folders afterwards.

## Steps

1. **Make your rating sheet (1 minute):** open https://docs.google.com/spreadsheets/d/1RvThrKclH0bfPmi0A94LOkebnX9JWS_Wyr3vEswbbRw/copy and click "Make a copy".
   Type your name in the `rater_id` column.
2. **Read the rules once:** `human_judgements_prompt.md`. Ignore its own Google Sheet link; use your copy from step 1.
3. **For each folder (`W01`, then `W02`):**
   - read the Python program in `python_source/`;
   - read the reference Lean file in `gold_lean/`: its theorem statements are what "full coverage" means;
   - rate each agent file in `agent_lean/` (three per folder) on statement coverage only, not proofs:
     the A-D checklist, a 0-5 base score, the spam adjustment, and the lower score when unsure.
4. **Fill one row per file in your sheet:**
   - `final_score_0_5` is required;
   - `minutes_spent`: roughly how many minutes that file took you (include reading time for the folder in its first file);
   - `lean_familiarity`: `none`, `some` or `fluent` (same value on every row);
   - everything else (A-D, base score, confidence, rationale, problem_note) is optional but helpful.
5. **Hand it in by sharing:** in your sheet click Share and add **brandojazz@gmail.com** as a Viewer. That's all:
   sharing the sheet is how you submit it. Please don't edit it afterwards.

## Good to know

- **No Lean expertise needed:** you compare theorem statements; you never write or check proofs.
- **Your sheet is saved when you share it:** that snapshot is your submission, so finish before sharing. If you
  need to change something afterwards, email brandojazz@gmail.com instead of editing.
- **Next:** after you share the warm-up, your task folders (set N) arrive within a working day.
- **Questions:** brandojazz@gmail.com.

**Rules:** rate on your own, with no AI tools, and do not look up earlier ratings of these files.
Do not discuss the files with other raters until everyone is done.
