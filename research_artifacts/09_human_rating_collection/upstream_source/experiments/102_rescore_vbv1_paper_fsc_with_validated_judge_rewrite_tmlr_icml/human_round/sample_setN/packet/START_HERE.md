# Start here: rating VeriBench Lean files (set N)

**Updated 10-11-2026: ready to rate.** The reference files were corrected. Lean now checks every reference theorem and test (no `sorry` is left), and references whose Python raises an error on some input state the convention they use instead. The references now contain proofs; you can skip them, because only statements are rated. `N17` also includes the two reference files it imports, in `gold_lean_dependencies/`; they are context only and are not rated.

**What you do:** for each agent Lean file in this packet, give **one score from 0 to 5** saying how well its theorem statements cover the reference's theorem statements. Proofs do not matter.

## Steps

1. **Open your personal rating sheet:** the link is in `YOUR_RATING_SHEET.txt`, next to this file. It already has your rater code; type straight into it.
2. **Read the rules once (5 min):** `human_judgements_prompt.md`. Same instructions as the May round, unchanged; ignore its own Google Sheet link and use your personal sheet from step 1.
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
5. **Finish in your personal sheet:** it saves as you go. There is nothing to copy, share or send back. Email Brando when a reference problem prevents a rating.

## Good to know

- **Time:** roughly 1-2 hours per folder (an estimate; long files are normal).
- **Deadline:** please finish your sheet within two weeks of receiving this packet; the round closes on Fri 11-06-2026.
- **No Lean expertise needed:** you compare theorem statements; you never write or check proofs.
- **Your sheet saves automatically:** finish all your folders before marking it complete. If you need to change something afterwards, email brandojazz@gmail.com instead of editing.
- **Questions:** brandojazz@gmail.com.


## Assistance and reference problems

You may ask an artificial intelligence (AI) tool a localized question about Lean syntax, notation, types or library behavior, using only the small snippet needed to explain the question. For example: “What does `∀ x, P x → Q x` mean?” or “How does list indexing work in Lean?”

Do not upload or paste a complete reference or agent Lean file, a whole task folder, or a sequence of snippets that reconstructs one. Do not ask a model to perform the rating task: comparing an agent with the reference, deciding which properties are covered, proposing a score, or writing your rating rationale. The final comparison, score and rationale must be your own. Review an explanation critically; a model answer is not evidence that the code is correct.

Rate independently, keep the system identities and other people's ratings hidden, and do not discuss particular items with other raters before the round closes. If you use a tool, briefly note the kind of localized help in `problem_note`; do not paste private conversations or model-generated ratings into the sheet.

Specifications of real code are often ambiguous, for example what to return on an empty list when the Python raises an error. When a reference picks a reasonable convention for such a case, rate with your own judgment and note your reasoning in `rationale`; some variation between raters is expected. Only if something is actually incorrect (a reference theorem that is false, or one that contradicts the Python on an input the Python accepts) put the smallest concrete example in `problem_note`, leave that score blank and email brandojazz@gmail.com. Every reference was checked on 10-11-2026, so we don't expect this.

This replaces the blanket “no AI tools” rule in the recruitment email and packet wrappers. The original May scoring rubric, score scale, blind ordering, candidate files and reference files are unchanged. The old and newly clarified assistance conditions must be distinguished in the collection record.
