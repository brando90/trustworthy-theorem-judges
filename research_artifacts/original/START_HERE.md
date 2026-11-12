# Start here: Brando’s VeriBench human ratings

**Updated 10-11-2026: ready to rate.** The reference files were corrected. Lean now checks every reference theorem and test (no `sorry` is left), and references whose Python raises an error on some input state the convention they use instead. The references now contain proofs; you can skip them, because only statements are rated. `Files_To_Rate17` also includes the two reference files it imports, in `gold_lean_dependencies/`; they are context only and are not rated.

**What you do:** for each agent Lean file in this packet, give **one score from 0 to 5** saying how well its theorem statements cover the reference's theorem statements. Proofs do not matter.

## Steps

1. **Open your personal rating sheet:** the link is in `YOUR_RATING_SHEET.txt`, next to this file. It already has your rater code; type straight into it.
2. **Read the rules once (5 min):** `Rating_Instructions.md`. The scoring rules are unchanged from the May round; the sheet link points to your personal sheet.
3. **Rate all 25 task folders in this packet.** Start with task 1 (folder `Files_To_Rate01/`), then task 2 (`Files_To_Rate02/`), and continue in numeric order. Each folder is one task:
   - `python_source/*.py`: the Python program the agents had to formalize.
   - `gold_lean/*.lean`: the reference Lean file. Its theorem statements are what "full coverage" means.
   - `agent_lean/`: five agent files, blinded and in random order.

   For each agent file, find the gold theorem statements, check whether the agent states the same, an equivalent or a stronger property, and run the checklist:
   - A: are the key gold theorems covered?
   - B: are the gold pre/postconditions kept or strengthened?
   - C: is there theorem spam?
   - D: if so, a handful or does it dominate?

   Then give the 0-5 base score and the spam adjustment from the rules file. Unsure between two scores? Take the lower one.
4. **Match each file to the same filename in your sheet**, for example `agent_file01.lean`, and fill one row per file, only for the folders in this packet (leave the other rows empty): `final_score_0_5` is **required**; everything else (A-D, base score, confidence, rationale, problem_note) is optional but helpful.
5. **Finish in your personal sheet:** it saves as you go. There is nothing to copy, share or send back. Email Brando when a reference problem prevents a rating.

## Good to know

- **Time:** roughly 1-2 hours per folder (an estimate; long files are normal).
- **Deadline:** please finish your sheet within two weeks of receiving this packet; the round closes on Fri 11-06-2026.
- **No Lean expertise needed:** you compare theorem statements; you never write or check proofs.
- **Your sheet saves automatically:** finish all your folders before marking it complete. If you need to change something afterwards, email brandojazz@gmail.com instead of editing.
- **Questions:** brandojazz@gmail.com.


## Assistance and reference problems

You may use artificial intelligence (AI) for localized help with parts of the rating task. You may not have AI do the whole rating task for you. For example, you can ask for help understanding a particular theorem or checking a specific point you are unsure about, rather than asking AI to rate all the files for you. You remain responsible for the final rating.

Rate independently, keep the system identities and other people's ratings hidden, and do not discuss particular items with other raters before the round closes. If you use a tool, briefly note the kind of localized help in `problem_note`; do not paste private conversations or model-generated ratings into the sheet.

Specifications of real code are often ambiguous, for example what to return on an empty list when the Python raises an error. When a reference picks a reasonable convention for such a case, rate with your own judgment and note your reasoning in `rationale`; some variation between raters is expected. Only if something is actually incorrect (a reference theorem that is false, or one that contradicts the Python on an input the Python accepts) put the smallest concrete example in `problem_note`, leave that score blank and email brandojazz@gmail.com. Every reference was checked on 10-11-2026, so we don't expect this.

This replaces earlier, more restrictive descriptions of AI assistance. The scoring rubric, score scale, blind ordering, candidate files and reference files are unchanged.
