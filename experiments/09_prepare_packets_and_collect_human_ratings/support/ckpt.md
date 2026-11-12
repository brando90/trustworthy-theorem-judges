# Handoff: clear rating instructions and synchronized forms

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_prepare_packets_and_collect_human_ratings/support/ckpt.md>

**TLDR:** Resume this chat's instruction/form consistency work using the current eleven-column contract. Preparation is complete for the existing main packets; the next sequence is Brando's trial ratings, instruction review, preparation of the Sri/Yegor/Brando first batch, then explicit approval to send.

Created: 11-11-2026 22:23 PST
Last updated: 11-11-2026 22:24 PST

## Goal

- Make the human-rating task understandable and keep participant instructions, CSV forms and Google Sheets consistent, while preserving the rubric, original packets and actual responses.
## What ran

- This handoff re-read current repository records, schema, private preparation state and assembly receipts; checked saved form row counts and final manifest hashes. No live Sheet refresh, generation, human rating or message delivery was performed for this handoff.
- Repository base: `9af5c0e`. Earlier form cleanup, descriptive names, synchronized Sheets and context-field restoration are already landed; do not repeat them.
## Results

- Frozen main inventory: 54 returned files / 25 tasks; 85 planned task/configuration combinations, 31 missing outputs. Saved main forms: Brando 54, Rylan 4, Sri 4; all scores blank at this check.
- Current target: 108 independent ratings, eight assigned and blank, 100 unassigned; Brando's 54 are additional. Warm-up snapshot: 15 numeric ratings and three N/A entries. These are inventory/status counts, not statistical evidence of sufficiency.
## Stuck / blocked

- Dispatch awaits Brando's trial, instruction review and explicit send instruction. Yegor's main assignment, packet and exact email remain unprepared. Other recipients are held.
## Next steps

- [p 10/10] Read current state and preserve the collection owner's work; exact starting commands are below. Resume the ordered checklist, not an old dispatch queue.
## Brando to-do

- Grade a few files, describe confusing instructions, then review the concrete first-batch text and explicitly approve sending. Completing all 54 main files is not a prerequisite.

## Ownership and what this handoff transfers

This is the handoff for the chat that simplified the warm-up forms and synchronized the instructions, CSVs and Sheets. It does not silently replace the separate collection coordinator or the paper/sizing owner.

- [Prepare human grading task — sole owner](codex://threads/01a1a8f9-dcb7-7381-9368-91d6e51faffd) owns packet assembly, assignments, generation records and dispatch. Its durable record is [CKPT_human_rating_collection.md](CKPT_human_rating_collection.md). Read its latest state before overlapping work. If Brando explicitly transfers that ownership too, retain one writer and record the transfer.
- [Recover rating-data estimates](codex://threads/01a1cc5b-af60-77d1-8f1e-2207b1f121d1) owns the sizing and related paper/navigation work. Do not duplicate those studies as part of form cleanup.
- Send another chat a message only with Brando's authorization. Every authorized informational message must say: **“FYI only—continue your current task. No action, reply, or duplicate work needed.”** An FYI is not a new assignment.
- Keep this requested handoff in `support/`; the existing collection checkpoint remains the coordinator's operational record. Do not add a competing top-level overview or edit the coordinator's checkpoint concurrently.

## Read these current sources

Repository: `/Users/brandomiranda/trustworthy-theorem-judges`.
Current collection: `experiments/09_prepare_packets_and_collect_human_ratings/`.
The former public `09_human_rating_collection` path and its temporary alias are retired. The private preparation directory intentionally retains that historical name.

1. [Collection overview and latest first-batch decision](../README.md).
2. [Warm-up instructions](../rating_task_packet/START_HERE.md), [main instructions](../rating_task_packet/main_rating_task/START_HERE.md), [unchanged scoring rubric](../rating_task_packet/human_judgements_prompt.md), [field guide](../rating_task_packet/RATING_FORM_GUIDE.md).
3. [Shared schema](RATING_FORM_SCHEMA.json), [form amendment](FORM_AMENDMENT_11-11-2026.md), [response import rules](IDENTITY_AND_IMPORT.md).
4. [All personal Sheets and saved CSVs](../ratings/README.md), [raw manifest](../ratings/RAW_MANIFEST.json), [summary](../ratings/SUMMARY.json).
5. [Coordinator details and provenance](COORDINATOR_README.md), [judge-methodology context](JUDGE_FORMULATIONS_11-09-2026.md).
6. Local private authority: `private/09_human_rating_collection/preparation_11-09-2026/CURRENT_PREPARATION.json`. This records `send_authorized: false` and the current three-person sequence. Keep private recipient correspondence and candidate-to-system mappings private.

## Current form contract; earlier simplification is superseded

```text
rater_name,rater_id,item_id,task_folder,candidate_file,final_score_0_5,ai_assisted_rating_attestation,minutes_spent,confidence,rationale,problem_note
```

- The first five fields are prefilled. Show the name and full candidate path; hide B:D in Sheets. Retain those internal matching keys in CSVs; hiding was not deletion.
- Score and combined attestation are required for new completed ratings. Time and confidence are requested. Rationale is preferred but optional; problem notes are conditional on an issue.
- The combined attestation states: “I used AI for localized assistance. I personally compared the specifications and chose the final score; I did not delegate the rating task to AI.” Allowed answers: `yes`, `no`, `unsure`.
- Localized AI help is required prospectively under the current amendment; humans do the comparison, choose the score and write any rationale. Historical assistance remains unknown unless actually recorded. Never prefill an attestation.
- Checklist questions, base score, spam adjustment and choosing the lower score when unsure remain reasoning steps in the rubric. There is no separate base-score or A–D response column. Their removal did not change the scoring rule.
- Earlier 7/8-column required-only layouts and older 17/18-column forms are historical. Brando later restored time, confidence, rationale and problem notes. Preserve that latest decision.
- Exact field names, order, meaning, options and required/optional status must match across instructions, builders, packet CSVs and live Sheets. Values preserve case, spelling, blanks, N/A and row order. Never estimate a participant response.

## Ordered next steps

1. **[p 10/10] Resume from evidence.** Refresh project/shared instructions, inspect Git state, and read the sources above. Determine whether Brando has already done his trial or the coordinator has advanced. The checkpoint contains saved observations, not a background synchronization. Read current Sheets when verifying new answers; never overwrite later responses with these blank snapshots.
2. **[p 10/10, after the trial] Review the actual participant experience.** Collect Brando's confusion points and tighten only the wrapper/entry instructions and field explanations as needed. Preserve scoring criteria, scale, spam adjustment and uncertainty rule exactly. Keep the full rubric available. Record any wording revision and preserve the previous packet; do not imply unchanged assistance conditions across historical rounds.
3. **[p 10/10, collection owner] Complete the first batch for Sri, Yegor and Brando.** Sri's four-file main packet and Brando's 54-file main packet are prepared. Prepare Yegor's assignment, personal Sheet, packet and exact message using the frozen actual cohort. His existing extra-only designation stays in force; first-batch membership does not qualify him or count him toward the independent target. Choose a concrete assignment from current records; if that requires a new qualification decision, expose that precise decision instead of silently changing status.
4. **[p 10/10] Verify every participant surface together.** Check all active warm-up forms/templates and the affected current main forms against the shared schema; compare exact Sheet readbacks with corresponding raw CSVs and packaged forms by field name. Verify readable paths and hidden internal keys, correct personal links/editor access, instructions/guide agreement, stable item identities and unchanged scientific-file hashes. Shared structure must match; each person's answers and assigned subset remain their own.
5. **[p 10/10] Freeze a concrete reviewable first-batch release.** Create versioned replacement archives only if content changed. Save archive/manifest hashes and exact recipient-specific email bodies. Refresh current raw manifests, summary and overview together. Make CURRENT_PREPARATION point at the actual three-person queue, not the preserved eight-person queue. Keep Rylan and everyone else held. Ask Brando to approve the final exact text and explicitly send only after preparation is complete.
6. **[p 10/10, after explicit send] Deliver and verify once.** The authorized collection owner sends the approved recipient-specific packets and verifies delivery. Record actual sent version, recipient, time and receipt; do not treat prepared drafts, Sheets or attachments as delivered. Follow current email routing rules without exposing other people's personal Sheet links or anonymous system keys.
7. **[p 9/10, as responses arrive] Collect exact responses.** Export fresh bounded Sheet tables, preserve raw answers and source receipts, validate identities/paths/scores by field name, and update the raw manifest, summary and named completion table. Keep blanks, N/A and reference issues distinct from zero. Keep normalized analysis exports separate; copies and repeat exports are not additional ratings.
8. **[p 8/10, subsequent collection] Finish the independent allocation.** Reconcile the remaining 100 slots with eligible, willing raters under existing qualification/task-boundary rules and the current recipient hold. Target two distinct qualified raters per artifact. Brando's author ratings and Yegor's extra-only ratings are separate. Do not expand outreach or send beyond the approved first batch without authorization.
9. **[p 7/10, separate owner] Hand completed data to the judge study with provenance.** Preserve evaluation-only use, task/solver/rater splits, reference and assistance versions, exposure history and missingness. The sizing chat owns sample-size proposals; 108 is collection workload, not a sufficiency guarantee. A prospective training study needs its own resolved protocol. No new solver campaign is part of this form handoff.

## Frozen facts and pitfalls

- Warm-up: six historical single-call Claude 3.7 Sonnet candidates, three each for median and greatest common divisor. Descriptive folders are `warm_up_01_median` and `warm_up_02_greatest_common_divisor`; anonymous filenames are `agent_1.lean`, etc. Brando has seen other warm-up answers, so his warm-up is coordinator practice, not an independent blinded submission.
- Main actual pool: 25 historical native Codex/GPT-6 Astra (xhigh), 19 new native Claude Code/Claude Fable 5.1 (max), ten historical Terminus 2/Grok 4.7. Pi/Gemini 3.8 Flash (high) returned zero captured required-path submissions in 25 attempts. All 50 new attempts terminated. Missing outputs are not human score zero. Different historical/new conditions prevent treating this as a causal harness comparison.
- Original main packet: 125 files / 25 tasks / five Terminus 2 configurations. Preserve it as history; it is not the current default. Likewise the earlier 85-file/170-rating plan is not the final returned inventory.
- Native preparation root: `private/09_human_rating_collection/preparation_11-09-2026/native_harness_packet_11-11-2026/`. Final manifests: `finalization/RATABLE_COHORT.json`, `finalization/EXCLUSIONS.json`; personal bundles: `builds/native_heavy_terminal_v1/{A1,T01,T05}/`.
- Rechecked at handoff: cohort SHA-256 `8463f6c846839c78fccf8102f3672ff94a20562dba7871b13d81e8cca693de22`; exclusions SHA-256 `a14cfa52ead4917f5a24b88672d05f3a38b490ce39a8c5c217729891b3d024e5`. Each of the three saved assembly receipts says `BUILT_SHEET_MATCHED_NOT_SENT`, `release_ready: true`. That is saved verification, not a new live read or permission to send.
- The coordinator checkpoint still contains some older next-step language (complete all six warm-ups; use the eight-person queue). Its latest sequencing paragraph, collection README and CURRENT_PREPARATION supersede that language. Preserve history; reconcile only current guidance when owning the next edit.
- `verify_preparation.py` checks the historical 125-file/eight-draft preparation. Passing it alone does not validate the new three-person release. Use the native builder and current assembly/readback receipts for current packets.
- No automatic Sheet-to-CSV background mirror exists. Record when each snapshot was actually checked.
- The previously requested dates were 11-13-2026 preferred and 11-15-2026 final. Re-check their relevance before drafting after those dates.
- Keep one editable participant home in `rating_task_packet/`, raw responses in `ratings/`, and scripts/tests/history here in `support/`. No extra one-link text files or top-level status/index duplicates.

## Exact starting commands and verification

```bash
cd /Users/brandomiranda/trustworthy-theorem-judges
git fetch origin
git status --short
cat experiments/09_prepare_packets_and_collect_human_ratings/README.md
cat private/09_human_rating_collection/preparation_11-09-2026/CURRENT_PREPARATION.json
python3 scripts/check_project.py
git diff --check
```

Inspect `support/scripts/native_packet_generation/build_packet.py --help` before preparing a new personal packet. It accepts the frozen cohort, a new private output directory, verified rater name/ID, personal Sheet URL and optional assigned task IDs. Its `verify-sheet` subcommand accepts `--build-dir` and `--sheet-readback`; inspect the expected readback format before supplying a fresh export. Keep source-to-system joins private and preserve the frozen display layout, including intentional gaps after exclusions.

Use connected Sheets tools for exact table reads/writes and read back edits. Scripts are under `support/scripts/`, tests under `support/tests/`. Verify only relevant changes; no need to rerun generation to change wording. Commit only owned files, inspect the exact staged diff, fetch/reconcile and push to `main`. A shared-index race previously included this chat's staged changes in another owner's commit; use scoped commits and inspect status immediately before landing.

## Copy-ready takeover prompt

```text
Continue the rating-instructions and form-consistency task in /Users/brandomiranda/trustworthy-theorem-judges. Read AGENTS.md and experiments/09_prepare_packets_and_collect_human_ratings/support/ckpt.md first, then re-check the current README, schema and private CURRENT_PREPARATION.json.

Treat the checkpoint as a handoff, not authorization to overwrite the separate collection coordinator's work. Resume the ranked next steps within this chat's scope and preserve one writer for packet/assignment/dispatch changes. The latest sequence is Brando's trial ratings, instruction review, preparation of the Sri/Yegor/Brando first batch, then his explicit approval to send. The eleven-column contract supersedes the earlier required-only form.

Keep the rubric unchanged, synchronize instructions/CSV/Sheets, preserve original archives and exact human responses, and keep the workspace uncluttered. Verify current facts before claiming completion. Do not substitute historical queues or planned candidate counts for the current release. Update this checkpoint with progress and give Brando a short concrete status. Any authorized FYI must tell the other agent to continue its task and require no action or reply.

TL;DR: Continue the clear, synchronized human-rating workflow using repository and Sheets tools; produce verified matching forms and reviewable first-batch materials while preserving the explicit send hold.
```

## Log

- 11-11-2026 22:23 PST — Created the requested handoff from the current repository/private preparation records and saved receipts; preserved the coordinator's checkpoint and all participant data. No new agent launched or messages sent.

- 11-11-2026 22:24 PST — Checkpoint links and formatting verified; all 66 project tests passed.
