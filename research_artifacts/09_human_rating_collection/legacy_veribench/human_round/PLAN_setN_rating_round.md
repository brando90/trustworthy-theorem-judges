<!-- TLDR: The working plan for rating set N under amendments C14-C15 (10-07-2026): who does what and when, from Brando's timed A1 folders on Thu 10-08 through Friday's rater assignment, the warm-up, two ratings per file and the 11-06-2026 close, with ready-to-send drafts for the team reminder and the Vals vendor request. -->
# Set N rating round: the plan

**Doc link:** <https://github.com/brando90/veribench/blob/main/experiments/102_rescore_vbv1_paper_fsc_with_validated_judge_rewrite_tmlr_icml/human_round/PLAN_setN_rating_round.md>

**TL;DR:** Every set-N file gets two independent ratings from qualified raters: 25 task folders × 2 = 50 folder assignments, about 60–110 rater-hours in total (unmeasured until Brando times N01–N03). Team volunteers do the warm-up plus 2–3 folders each, about 3–7 hours. Vals' paid vendor raters cover the rest. Rules: [C14](../PROTOCOL_AMENDMENT_C14.md) (what is in set N) and [C15](../PROTOCOL_AMENDMENT_C15.md) (two ratings, warm-up, assignment, close).

## Rater email delivery protocol (Brando, 11-04-2026)

These instructions govern new task emails and Brando's preview cycle; older email drafts below remain historical. Brando approved and locked the email on 11-04-2026: [exact approved template](RATER_TASK_EMAIL_LOCKED_11-04-2026.md). Only the recipient's name in the greeting may change; any other edit requires his approval. This latest decision supersedes earlier personalization instructions below.

- After each email correction from Brando, send him the complete revised email with the actual packet attached, in the form a rater would receive. Do not substitute a checklist, a link to an old email, or a forwarded message attachment for the task email and packet.
- Send a fresh message, not a reply or forward: omit reply/thread identifiers and In-Reply-To/References headers. Keep the normal task subject; do not add revision numbers or change subjects merely to defeat Gmail's automatic conversation grouping. Brando accepted automatic grouping on 11-04-2026.
- Begin simply: “Your VeriBench rating packet is attached.” Omit editing history about clearer filenames, renamed sheet rows, or unchanged ratings.
- Include the recipient's own sheet link, assigned folders and filenames, instructions, and verified deadline. Brando's 25-folder/125-file assignment and personal sheet must not be copied into other raters' emails unless those are actually their assignments.
- Include this assistance wording: “You may use artificial intelligence (AI) for localized help with parts of the rating task. You may not have AI do the whole rating task for you. Asking for help understanding a particular theorem, checking a specific point, or learning Lean concepts is fine. You remain responsible for the final rating.”
- Use this exact closing note: “P.S. Feel free to email me with any questions. Email is preferred for questions! Happy to clarify anything!”
- Do not include TLDR-end, project tags, Snapshot blocks, or other chat-only summaries in rater emails, including previews sent to Brando.
- Brando identified the final email on 11-04-2026, Gmail message `1a1a90917caab0d0`. The exact text is saved in the locked template linked above. Only the greeting name is variable. Approval locks the template; it does not instruct immediate team delivery.
- Before delivery, check spelling, recipient, personal sheet link, assignment, deadline, attachment identity and current approved wording. After sending, verify the sent message and attachment once. Preserve blinded materials and existing scientific release requirements.

Preview evidence: Gmail message `1a1a907d07b15ef1` was sent with the actual packet and no reply headers. Its review-number subject preceded Brando's clarification accepting Gmail grouping. The approved final preview, `1a1a90917caab0d0`, uses the ordinary task subject and contains the original packet attachment.

## Status (10-07-2026 evening)

- **Final packet: ready** (10-08-2026 ~04:45 UTC, commit `9efb78a12`), at `human_round/sample_setN/`. It has 125 files, 25 per system, none missing; 93 are byte-identical to wave 1 and 32 are new (Kimi K3 25, re-sends 7). A1 had rated nothing in wave 1, so A1 rates the final packet directly and needs no addendum sheet.
- **Replies.** Yes: Rylan, Yegor, Dilara. No: Mo. No reply yet: 22 recipients, plus Simon (who needs about a week's notice).
- **Ready now.**
  - C15 is fixed.
  - The warm-up packet is built: `human_round/warmup/packet/`, six short May files with known expert scores.
  - A1's private copy of the final packet and A1's sheet: `human_round/private_A1/setN_final_packet/` and `human_round/private_A1/setN_final_A1_rating_sheet.csv` (125 rows, git-ignored).

## The numbers

| Item | Count | Time |
|---|---|---|
| Set-N task folders | 25, up to 5 files each | 1–2 h per folder (estimate; A1 measures it on 10-08) |
| Ratings per file | 2, from different qualified raters (A1 extra) | |
| Folder assignments | 50 | about 50–100 h |
| Warm-up, everyone | 6 short files | about 30–45 min |
| Team volunteer | warm-up + 2–3 folders | about 3–7 h |
| Vendors (Vals-arranged) | the remaining ~35 folder assignments | about 40–70 h, e.g. 5 raters × 7 folders |

## Thursday 10-08

**Brando, in this order:**
1. **Done 10-08 09:41 PDT:** team reminder sent (Gmail `1a11c63e1ca626ed`).
2. **Done 10-08 09:41 PDT:** vendor request emailed to nikil@vals.ai (Gmail `1a11c63f12adbf9e`), asking Vals to recruit graders on the Lean Zulip. Paste his answer into the chat.
3. **About 2 hours, in the morning while fresh:** rate N01–N03 as A1, timed.
   - Use the final packet copy `human_round/private_A1/setN_final_packet/` and your sheet `human_round/private_A1/setN_final_A1_rating_sheet.csv`. Say "open N01" and the agent opens the folder in Cursor.
   - Put `folder minutes: NN` in the `problem_note` of each folder's last row.
   - Try Fold All (Cmd+K then Cmd+0) on one file, and note whether reading only the theorem statements helped.
   - No AI tools while rating. Turn Cursor Tab off.
4. **Optional, 30–45 minutes:** take the warm-up yourself (`human_round/warmup/packet/START_HERE.md`). You are the pilot for everyone else, so flag anything unclear. Skip it if you rated these May files yourself.

**Agent:**
- **Done 10-08 ~04:45 UTC:** built, checked and committed the final packet (`9efb78a12`); set up A1's private copy and sheet; pinged Brando.
- **Assignment script: done 10-08** (`scripts/assign_setN_folders.py`, self-tested). On Friday it runs on the real roster: replies plus Nikil's numbers.
- **Delivery: decided 10-08 (C15 item 11, packet v3).** The packet is self-contained: `START_HERE.md` links the template's `/copy` URL, the rater types their name, rates, and submits by sharing their copy with brandojazz@gmail.com as Viewer. Each rater's zip holds only their assigned folders. **Brando must set both templates to "Anyone with the link: Viewer"** (the agent is not allowed to grant that).
- **Replies.** Tally replies from the recruitment thread.

## Friday 10-09 (replies due)

- **Agent:** tally replies and Nikil's numbers, run the assignment, and show Brando the plan: who gets the warm-up, the expected folder counts, and the dates.
- **Brando:** approve the plan and say "send".
- **Agent:** emails each team rater the warm-up packet and sends the vendors' packets through Nikil.

## Week of 10-12, and on

1. **Warm-up sheets come back.** The agent scores each within a day (`scripts/score_warmup.py`).
   - **Qualified raters** (mean absolute difference ≤ 1.0 point) get their folders within one working day. Each sheet is due two weeks after delivery.
   - **Non-qualified raters** may still rate folders as extra ratings. They are thanked either way.
2. **Brando continues A1** at his own pace; all of A1 must be done before close.
3. **Close:** every folder has two qualified ratings, or **Fri 11-06-2026**, whichever is first. Nobody sees any agreement statistic or FSC value before close.
4. **After close:**
   - commit all sheets and keys;
   - unblind;
   - run `scripts/analyze_human_round.py` with C5, C7, C8 and C15's additions;
   - report in `../results.md`.

## Rules for everyone

- Rate alone, without AI tools, and don't discuss files until every sheet is in.
- Raters never see judge scores, system names or other raters' sheets.
- Sheets live in the git-ignored `human_round/private_ratings_setN/` until close.
- Everyone gets randomly assigned folders from the same pool. Nobody gets "easier" folders.
- Nothing is sent to anyone without Brando's "send".

## Drafts

**A. Team reminder.** Reply on the 10-05 recruitment thread, from brandojazz@gmail.com, to Monday's recipients plus simon@obstbaum.eu, with Bcc unchanged:

> Hi all,
>
> A few people asked whether you need to know Lean. You don't write or check any proofs. You compare theorem statements: does the agent's file state the same (or stronger) properties as the reference Lean file, which is in every folder? If you can read a typed function signature and basic logic (∀, →, ∧), you can do this.
>
> We've also made it lighter. Each file now needs two ratings instead of three, and more raters are joining, so the load per person is smaller. Everyone starts with the same short warm-up set (six short files, about 30–45 minutes), then rates 2–3 task folders (roughly 1–2 hours each; I'm timing it myself this week).
>
> If you haven't replied yet, a yes or no by Friday 10-09 would really help, even for a couple of folders. Thanks!
>
> Brando (drafted with Claude)

**B. Vendor request to Nikil (Slack):**

> Thanks Nikil, super helpful! We'd love their help with VeriBench.
>
> The task: compare an AI agent's Lean theorem statements against a reference Lean file and give a 0–5 coverage score. There are no proofs to check. It's blinded, with a CSV sheet. Everyone starts with a 30–45 min warm-up set that has known expert answers. We need about 35 task folders rated, roughly 1–2 hours each, so about 40–70 hours in total over two weeks, starting next week.
>
> A few questions:
> 1. How many of them could join, and roughly how many hours each?
> 2. Can they see outputs from the internal pre-release model? Vals approved it for our raters; I want to confirm for your contractors.
> 3. Anything I need to arrange for contracts or payment?
> 4. Should packets go through you, or directly to them?

## Decisions already made (C15), and what is still open

- **Decided.** Two ratings per file; one warm-up for everyone, cutoff 1.0 point; random whole-folder assignment, with one team and one vendor rater per folder where possible; vendors see the internal model's files only after Vals confirms in writing; close on 11-06-2026.
- **Decided (Brando, 10-07-2026).** Set N is evaluation-only: no set-N rating builds, selects or tunes a judge (option A). Judge selection comes later, from a separate pool on other tasks (option C), and both judges are then scored once on set N (C15 item 10).
- **Open.**
  - Whether to add 25 extra Fable/Astra tasks: only if vendor capacity is large, decided by a separate amendment (C16) before any generation.
  - Whether to add a proof-folding tip to the rater instructions: decided after A1's timing.
