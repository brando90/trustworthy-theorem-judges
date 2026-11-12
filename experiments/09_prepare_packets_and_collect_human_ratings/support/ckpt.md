# Handoff: finish human-rating packets and collection

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_prepare_packets_and_collect_human_ratings/support/ckpt.md>

**TLDR:** Take over the complete packet-preparation and collection task. The current 54-file pool is built; next are Brando's trial ratings, instruction review, preparation of the Sri/Yegor/Brando first batch, exact-text approval, dispatch and collection. This checkpoint incorporates the form-consistency handoff; the successor has not yet been identified or verified.

Created: 11-11-2026 22:23 PST
Last updated: 11-11-2026 22:29 PST

## Goal

- Finish a clear, verified human-rating workflow: Brando tries it, instructions are reconciled, the first three-person batch is approved/sent, then raw responses and remaining assignments are collected with provenance.
## What ran

- This handoff re-read current repository records, schema, private preparation state and assembly receipts; checked saved form row counts and final manifest hashes. No live Sheet refresh, generation, human rating or participant email delivery was performed for this handoff; an authorized FYI informed the form helper.
- Repository base: `9af5c0e`. Earlier form cleanup, descriptive names, synchronized Sheets and context-field restoration are already landed; do not repeat them.
## Results

- Frozen main inventory: 54 returned files / 25 tasks; 85 planned task/configuration combinations, 31 missing outputs. Saved main forms: Brando 54, Rylan 4, Sri 4; all scores blank at this check.
- Current target: 108 independent ratings, eight assigned and blank, 100 unassigned; Brando's 54 are additional. Warm-up snapshot: 15 numeric ratings and three N/A entries. These are inventory/status counts, not statistical evidence of sufficiency.
## Stuck / blocked

- Dispatch awaits Brando's trial, instruction review and explicit send instruction. Yegor's main assignment, packet and exact email remain unprepared. Other recipients are held.
## Next steps

- [p 10/10] Record successor ownership, verify current state and resume the ordered checklist below, not an old dispatch queue.
## Brando to-do

- Grade a few files, describe confusing instructions, then review the concrete first-batch text and explicitly approve sending. Completing all 54 main files is not a prerequisite.

## Ownership and what this handoff transfers

Brando asked the sole collection coordinator to save its remaining work for a different agent. This checkpoint now covers packet preparation, instruction/form consistency, assignments, reviewable emails, authorized delivery and raw-response collection. It incorporates the form helper's checkpoint from commit `31fd5c7`; its useful guidance is retained below.

- Outgoing coordinator: [Prepare human grading task](codex://threads/01a1a8f9-dcb7-7381-9368-91d6e51faffd). After publishing this handoff, it stops collection writes. The successor is not yet named; a saved prompt does not prove takeover. The successor must record its chat ID and first useful verified action here and in the existing private preparation record before becoming the sole writer.
- [Earlier collection checkpoint](CKPT_human_rating_collection.md) preserves operational history and prior receipts. This `ckpt.md`, the collection README and `CURRENT_PREPARATION.json` lead for the latest sequence. Older eight-person dispatch commands are superseded.
- [Rate warm-up Lean files](codex://threads/01a1cc2c-210b-79d1-bafe-39c7ef1080f5) helped with forms and the personal task. [Recover rating-data estimates](codex://threads/01a1cc5b-af60-77d1-8f1e-2207b1f121d1) owns sizing and its related paper/navigation work. Preserve those owners; do not launch duplicate studies.
- Authorized informational coordination says: **“FYI only—continue your current task. No action, reply, or duplicate work needed.”** An FYI is not a new assignment. Do not claim that another chat has accepted work without evidence.
- All 50 new solver attempts are finished; there is no active generation or watcher to resume. Existing solver budgets and scientific limits remain frozen. A future separately authorized experiment is distinct from finishing this collection.

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

## Personal entry points and concrete first-batch preparation

| Person | Current task | Live Sheet |
| --- | --- | --- |
| Brando | [Warm-up instructions](../rating_task_packet/START_HERE.md), six files | [Warm-up Sheet](https://docs.google.com/spreadsheets/d/1VhlSsf8Fd_pD_hQySt4-Y3AHrj5e6Rd3kQFu6A59-8A/edit) |
| Brando | [Main instructions](../rating_task_packet/main_rating_task/START_HERE.md), 54 files | [Main Sheet](https://docs.google.com/spreadsheets/d/1zUDr9fpUwK0IuxrSdFfBR_mOt4WwMY8-doBC6cIhIHM/edit) |
| Sri | Prepared four-file main packet | [Main Sheet](https://docs.google.com/spreadsheets/d/163ZxKeTXqseLrmwY-b5QjqeBulinHsZAiAPo1zsJdJI/edit) |
| Yegor | Existing six-file warm-up; main packet not yet prepared | [Warm-up Sheet](https://docs.google.com/spreadsheets/d/1AhfJL23U47t61DinUTolwchqHKLaOtR65AFVDD-YOMI/edit) |

The private preparation root is `/Users/brandomiranda/trustworthy-theorem-judges/private/09_human_rating_collection/preparation_11-09-2026/`. Under it:

- `ROSTER.csv` and `ASSIGNMENT_delivered.csv` govern identity, qualification and delivered assignments. T02/Yegor currently has `qualified=no`, `current_status=extra_only`, with no delivered main rows. Do not relabel that record based on his inclusion in the first batch.
- `drafts/NativeMainV1/EMAIL_A1_BODY.txt`, `EMAIL_A1_HEADERS.json`, `EMAIL_T05_BODY.txt`, `EMAIL_T05_HEADERS.json` are starting drafts, not approved new first-batch text. There is no T02 equivalent yet.
- A practical **proposed**, not assigned, Yegor pilot is the same two tasks/four available files as Sri: `realcode_set__20_html_escape` and `realcode_set__31_statistics_quantiles`. It gives overlap and a manageable pilot; keep it additional under the existing designation unless Brando changes qualification. Check his existing context before finalizing.
- Create one versioned three-person review and queue after checking the actual packets, then point `CURRENT_PREPARATION.json` to them. Preserve the old eight-person review/queue as history. Reconcile source drafts after Brando's instruction feedback.
- Use the normal subject and a new message, not a reply to an old thread. Gmail may group messages automatically. The user explicitly excludes chat TLDR/status text from rater emails. Preserve the approved signature and routing, including the three Brando BCC copies. Verify editor access before sending; share only the recipient's own Sheet.
- Final first-batch delivery requires Brando's approval of the exact text and explicit send instruction. A Sheet access grant, prepared archive or `release_ready: true` is not delivery or send authorization. The previous run-completion self-email is already verified in `receipts/NATIVE_PACKET_RUN_DONE_11-11-2026.json`; do not resend it for this handoff.

## Frozen execution receipts and limits

Under the private native root listed above:

- `finalization/RATABLE_COHORT.json`: final 54 real files; `EXCLUSIONS.json` and `RECONCILIATION.json`: all 85 planned cells and 31 missing files.
- `builds/native_heavy_terminal_v1/{A1,T01,T05}/`: versioned archive, payload, `ASSEMBLY_RECEIPT.json`, actual Sheet readback and Sheet-match receipt. T01/Rylan remains held outside the new first batch.
- `NEW_MAIN_SHEETS.json`, `WORKING_PACKET_PROMOTION.json`, `FINAL_PREPARATION_RECEIPT.json`, `RETURNED_ARTIFACT_SCREEN.json`: current Sheet bindings, working-copy promotion and byte checks.
- `claude_code_readiness/CC_VALID_V2_FINAL_SUMMARY.json`, `PI_FINAL_EXECUTION_AUDIT.json`, `light_qa/REVIEW.md` and `light_qa/RESOLUTION.md`: execution outcomes and the completed single Claude Fable 5.2/max review with fixes. No new review round is needed for the handoff.

Archive SHA-256 values: Brando `e10a0c50a413a5ba750148c3ecba1de89a3eef5cd69f193068bde61dee7d8923`; Sri `105ec1347c817055469d65ebf09242a7c49cc84f1194c6319403e50102aee015`; Rylan `855d167f6f2db72abf6fa272d15888fada2ecb88cd089c5377a027e9cb0b71c6`. Recheck against actual receipts if building a revision; preserve these frozen prepared archives and source artifacts when creating a revision.

Pinned configurations: historical Codex 0.154.0/GPT-6 Astra/xhigh; new Claude Code 2.1.322/Claude Fable 5.1/max; historical Terminus 2/Grok 4.7/xhigh; Pi 1.5.2/Gemini 3.8 Flash/high. Claude Code's 19 files comprise 13 native completions and six retained at limits; six attempts returned no file. Pi returned zero required-path submissions: 15 attempts without a recorded infrastructure issue, eight external-service cases and two host-supervision incidents. Scratch Lean code existed; do not describe these as proof that no code was generated.

Pi accounting: 670 generation requests including retries; token-count preflights separate. Conservative total including excluded pilot/reservations was $11.63091975 against the $20 cap, not a verified invoice. Invalid environment pilots remain excluded. No further generation is needed for this handoff.

## Later scientific work, distinct from getting ratings

Formal specification coverage concerns unproved theorem/specification statements. The current collection remains evaluation-only under its existing conditions; do not silently use it for training or model selection. Preserve exposure, task/solver/rater identity, missingness, reference versions and assistance conditions. Existing 25-task coverage does not establish all-benchmark or future-agent generalization.

Methods 2 and 4 compare training correlation with a proper probabilistic training loss under matched data/capacity/search budgets. The current priority uses normalized ranked probability score for validation and primary held-out evaluation, with cross-entropy, Brier and total variation distance as additional conditions/metrics. These are methodology plans, not new results from this collection. Read the linked priority plan before study execution; the general objective-comparison experiment belongs in the sister `judges-dont-need-psychometrics-or-corr` repository. VeriBench owns the actual formal prover, and `cert-judge` is separate.

[Existing methodology companion](https://docs.google.com/document/d/1zB-gYk-zU1wToS_E_carGSRGtUcF1NgZ-jWF5t1SJws/edit). Its generation summary was previously synchronized; the latest local first-batch decision leads. Preserve other editors when making any later targeted update.

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
Take over the complete human-rating packet preparation and collection task in /Users/brandomiranda/trustworthy-theorem-judges.

Read AGENTS.md and /Users/brandomiranda/trustworthy-theorem-judges/experiments/09_prepare_packets_and_collect_human_ratings/support/ckpt.md. Verify CURRENT_PREPARATION.json and the actual files, then record your chat ID, ownership and first useful action in the existing checkpoint. The outgoing coordinator stops writes after publishing this handoff; keep one writer and preserve other agents' work.

Follow Brando's latest sequence: he grades a few files first; review the actual rater instructions using his feedback; prepare the first batch only for Sri, Yegor and Brando. Yegor's main assignment, Sheet, packet and exact email still need preparation. Keep all other recipients held. Show the exact first-batch emails for review and send only after Brando's explicit go-ahead. The old eight-person queue is not the new first batch.

Continue independent preparation while Brando grades, including the concrete remaining-rater allocation. Preserve exact raw responses, stable IDs, frozen scientific files, evaluation-only use and existing qualification records. Keep instructions, eleven-column CSV forms and live Sheets consistent. Generation and the requested light review are already finished; this task does not need them repeated. Verify new work and push scoped changes to main. Update the existing checkpoint rather than creating extra summaries.

TL;DR: Finish the three-person pilot dispatch and remaining human-rating collection from the saved checkpoint, with Brando's own grading and send decision in his hands.
```

## Log

- 11-11-2026 22:23 PST — Created the requested handoff from the current repository/private preparation records and saved receipts; preserved the coordinator's checkpoint and all participant data. No new agent launched or messages sent.

- 11-11-2026 22:24 PST — Checkpoint links and formatting verified; all 66 project tests passed.

- 11-11-2026 22:29 PST — Collection coordinator extended the existing form-helper checkpoint into the full requested manual takeover, retained historical records and verified the current first-batch facts, local links, two manifest hashes and three archive hashes. All 66 project tests passed. Successor not yet named or confirmed.
