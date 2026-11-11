# Start here: the warm-up set (about 30-45 minutes)

**Updated 10-11-2026: ready to rate.** The reference files were corrected. Lean now checks every reference theorem and test (no `sorry` is left), the false greatest-common-divisor theorem in `warm_up_02_greatest_common_divisor` was fixed, and the median reference states its empty-list convention. The references now contain proofs; you can skip them, because only statements are rated. If you already started, keep your entries, but re-check your `warm_up_02_greatest_common_divisor` scores against the updated reference.

The files `agent_1.lean`, `agent_2.lean` and `agent_3.lean` are anonymous submissions within each task. The sheet’s `item_id` retains its historical code for matching records; use `task_folder` and `candidate_file` to find the file.

**What this is:** six short agent Lean files from an earlier rating round, in two task folders (`warm_up_01_median`, `warm_up_02_greatest_common_divisor`).
Everyone on the panel rates the same six files first. It is practice with the real instructions, and it shows
how each person uses the 0-5 scale. Rate exactly as you will rate your task folders afterwards.

## Steps

1. **Open your rating sheet:** the link is in `YOUR_RATING_SHEET.txt`, next to this file. It is shared with you
   as an editor and already has your rater code filled in. Type straight into it; it saves as you go.
2. **Read the rules once:** `human_judgements_prompt.md`. Ignore its own Google Sheet link; use your sheet from step 1.
3. **For each folder (`warm_up_01_median`, then `warm_up_02_greatest_common_divisor`):**
   - read the Python program in `python_source/`;
   - read the reference Lean file in `gold_lean/`: its theorem statements are what "full coverage" means;
   - rate each agent file in `agent_lean/` (three per folder) on statement coverage only, not proofs:
     the A-D checklist, a 0-5 base score, the spam adjustment, and the lower score when unsure.
4. **Fill one row per file in your sheet:**
   - `final_score_0_5` is required;
   - `minutes_spent`: roughly how many minutes that file took you (include reading time for the folder in its first file);
   - `lean_familiarity`: `none`, `some` or `fluent` (same value on every row);
   - everything else (A-D, base score, confidence, rationale, problem_note) is optional but helpful.
5. **That's it:** when every row has a final score, you're done. There is nothing to copy, share or send; we
   read your sheet directly. Please don't change it after you finish; if you need to, email brandojazz@gmail.com.

## Good to know

- **No Lean expertise needed:** you compare theorem statements; you never write or check proofs.
- **Your sheet is personal:** it is shared only with you, so please don't forward the link. If Google asks you to
  request access, switch to the Google account named in `YOUR_RATING_SHEET.txt`.
- **Next:** once all six rows have a final score, your task folders (set N) arrive within a working day.
- **Questions:** brandojazz@gmail.com.


## Assistance and reference problems

You may ask an artificial intelligence (AI) tool a localized question about Lean syntax, notation, types or library behavior, using only the small snippet needed to explain the question. For example: “What does `∀ x, P x → Q x` mean?” or “How does list indexing work in Lean?”

Do not upload or paste a complete reference or agent Lean file, a whole task folder, or a sequence of snippets that reconstructs one. Do not ask a model to perform the rating task: comparing an agent with the reference, deciding which properties are covered, proposing a score, or writing your rating rationale. The final comparison, score and rationale must be your own. Review an explanation critically; a model answer is not evidence that the code is correct.

Rate independently, keep the system identities and other people's ratings hidden, and do not discuss particular items with other raters before the round closes. If you use a tool, briefly note the kind of localized help in `problem_note`; do not paste private conversations or model-generated ratings into the sheet.

Specifications of real code are often ambiguous, for example what to return on an empty list when the Python raises an error. When a reference picks a reasonable convention for such a case, rate with your own judgment and note your reasoning in `rationale`; some variation between raters is expected. Only if something is actually incorrect (a reference theorem that is false, or one that contradicts the Python on an input the Python accepts) put the smallest concrete example in `problem_note`, leave that score blank and email brandojazz@gmail.com. Every reference was checked on 10-11-2026, so we don't expect this.

This replaces the blanket “no AI tools” rule in the recruitment email and packet wrappers. The original May scoring rubric, score scale, blind ordering, candidate files and reference files are unchanged. The old and newly clarified assistance conditions must be distinguished in the collection record.
