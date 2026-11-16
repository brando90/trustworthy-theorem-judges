<!-- TLDR: Staged (not sent) plan to give the two qualified set-N raters the full 25-folder v7 packet with a fixed rating order; decisions, evidence, the void stale-v4 build, and the send steps that wait for Brando on 10-21-2026. -->
# Full set-N packet for qualified raters: staged delivery plan (10-20-2026, revision 2)

## Why
Brando, 10-20-2026: "sri said he received something tiny, so we need for sure something more serious so people give us plenty of diverse data on frontier agents." T05 (Sri) and T01 (Rylan) each received only their 2 assigned folders (T05: N01, N23 on 10-20; T01: N17, N21 on 10-13). The current plan (`ASSIGNMENT_10-20-2026_with_pending.csv`) gives every folder at most 1 rater and leaves N06, N07, N08, N09, N12, N13, N20 and N25 with none, while the design calls for 2 raters per folder (50 slots).

## Source version (revision 2)
The first build was **void**: it came from the shared checkout `~/veribench`, whose HEAD (`1469907383`) is 943 commits behind origin/main and still holds the 10-08 v4 packet. Those zips and the first Codex review are kept in `../void_stale_v4_10-20-2026/` and must never be sent. The rebuild uses origin/main `3f6549358f` (the 10-12 v7 release from experiment 114: corrected references, `N17/gold_lean_dependencies/`, localized Lean assistance). The rebuild ran `scripts/make_rater_zip.py` from that commit, with each rater's sheet and Google account: `../VeriBench_setN_T0x_full_N01-N25_v7.zip`, 181 entries, all 179 release files byte-identical to origin/main, plus `YOUR_RATING_SHEET.txt` and `FILES.sha256`. The packets raters already received are v7: Rylan's 10-13 and Sri's 10-20 zips match origin/main in every file except their own `YOUR_RATING_SHEET.txt`, so nothing delivered is affected.

## Decisions (by the A1 helper session while Brando was away; for his review on 10-21-2026)
1. **The warm-up gate stays** (Brando, 10-20: "we are doing the warmup. We already sent it. It's fine."). Only qualified raters get set-N folders: today T01 and T05. Raters who qualify later get the same full-packet email from the rating-round manager.
2. **Qualified raters get the full packet (all 25 folders) and keep their existing sheet**, which already lists all 125 files (checked: both sheets' A1:D126 equal `sheet_structure_T0x.csv`). Their two assigned folders stay required, with their original due dates. The other 23 are optional extras due Fri 11-06, the round close. The email states that it replaces START_HERE's "rate every folder" and "two weeks" lines. Unrated rows stay blank; the rating-round manager snapshots each sheet on each due date.
3. **A fixed rating order, so raters never pick folders:**
   - **Stage 1:** their own folders.
   - **Stage 2:** the other qualified rater's folders.
   - **Stage 3:** the 8 folders with no planned rater, numerically, the same order for both raters.
   - **Stage 4:** the remaining 13 folders, in a rater-specific shuffle: Python `random.Random("setN-full-packet-tail-<rater_id>")`. T01 gets N18, N16, N19, N10, N11, N05, N24, N02, N04, N22, N14, N03, N15. T05 gets N14, N05, N04, N19, N02, N03, N16, N18, N10, N15, N24, N11, N22. The shuffle spreads coverage and keeps folder from lining up with position or fatigue across raters; each stage-4 folder already has one pending planned rater.

   2-rater pairs between T01 and T05 come only as both actually finish the same folders: 0 if both stop after stage 1, 4 after stage 2, 12 after stage 3. Pairs are tracked from received ratings, never assumed.
4. **Delivery is a Drive link only.** Each zip goes to Brando's Drive and is shared as Viewer, with notification off, with the Google account the rater's sheet already uses and with the To address (T01: RylanSchaeffer@gmail.com and rschaef@cs.stanford.edu; T05: vatsava@gmail.com). Each email adds a fallback line, "switch to that account or reply". No zip is attached, because Stanford mail strips zips ("Delivery links required", `PLAN_setN_rating_round.md`).
5. **No GitHub link for raters.** The packet's repository path sits inside experiment 102, which also holds results and run records, so a link would invite browsing that could unblind system identities.
6. **The email doesn't mention the judge.** It describes the agents only as "AI agents" and doesn't say "frontier", which avoids setting capability expectations.

## Protocol record
The coordinator recorded this change as PROPOSED amendment C18 (`8dbef4c917`): primary analysis unchanged (C15), extras as pre-registered secondaries, and an order/fatigue sensitivity analysis. It takes effect only after Brando's go and a passing QA. Revision 2 changes stage 4 from numeric to a rater-specific shuffle, so the coordinator must update C18's wording to match before any send.

## Disposition of the void v4 review (Codex reviewer, 10-20)
- **A01 (three sheet routes):** v7 START_HERE already sends raters to `YOUR_RATING_SHEET.txt` (the same sheet as the email) and tells them to ignore the rubric's old link. The email now says the link is also in that file.
- **A02 (submission and freeze):** v7 has no share-to-submit step. The email adds "saves as you go, nothing to send, we take a copy on each due date, email instead of changing a finished folder".
- **A03 (required vs. optional, deadlines):** the email states required versus optional, both dates and blank-not-guess, and that it overrides START_HERE's two lines.
- **A04 (Fold All):** replaced with folding single proofs from the margin while keeping full statements and hypotheses in view.
- **A05 (protocol record, pairs, order):** C18 covers the record. The pairs wording is fixed (decision 3), and the stage-4 tail is now per-rater.
- **A06 (AI tools):** v7 permits localized Lean questions. The email adds "In Cursor, turn off Tab autocomplete while rating".
- **A07 (folder minutes):** the email defines it as the minutes the folder took, next to other notes.
- **Blinding scan:** it found zero named-system hits on the v4 agent files. The agent files are unchanged in v7, since only references, dependencies and START_HERE changed (per `FILES.sha256`); the new review repeats the scan. Candidates for a non-rater custodian: a recurring comment group (example `N01/agent_lean/N01d.lean:676`) and an external repository link at `N24/agent_lean/N24b.lean:8`, which has no named-system hit.

## Send steps (on Brando's go on 10-21-2026, in this order)
0. **C18 goes IN FORCE first.** The coordinator flips C18 (latest `49186f41b6`) from PROPOSED to IN FORCE, citing Brando's go and both QA verdicts. It also updates `human_round/RATER_INSTRUCTIONS.md` (Fable F10) and records in the CKPT that the attended Chrome route is accepted for this send (Fable F13).
1. **Re-read the sheets.** Re-read both sheets' A1:D126 and note the row count, which must be 125, in the SENT_LOG row.
2. **Stage each zip on Drive.** Send it to brandojazz@gmail.com with `scripts/send_rater_email.py --no-stanford-bcc-copy`, logging to a staging log in this folder, never the rater SENT_LOG. Then use Gmail "Add attachment to Drive" in Claude in Chrome.
3. **Share and verify.** Check the Drive `fileSize` against the local zip. Share as Viewer (notify off) through the Drive web Share dialog with both addresses in decision 4. Confirm with `get_file_permissions`, then download the file back and compare its SHA-256 with `STAGING_MAP.json`.
4. **Fill the link and send.** Fill `<DRIVE_LINK_T0x>` in `EMAIL_T0x_BODY.txt`. Run `scripts/send_rater_email.py --to <To> --subject "VeriBench set N: all 25 folders (optional extras after your two)" --body-file EMAIL_T0x_BODY.txt --rater T0x --packet setN --folders N01,...,N25 --log human_round/private_ratings_setN/delivery/v7_10-12-2026/SENT_LOG.jsonl` from an origin/main worktree, `--dry-run` first, then for real. The presend check refuses a body with no Drive link: verified 10-20, when both placeholder bodies were REFUSED and both bodies with a synthetic link passed, with BCC 4 of 4.
5. **Register the receipts.** Append both full-packet receipts from `DELIVERY_RECEIPTS.jsonl` here to `private_ratings_setN/delivery/DELIVERY_RECEIPTS.jsonl` (the importer's default), keeping the 2-folder receipts (Astra A03). Check one assigned and one extra folder with synthetic rows before the first import. Read folder minutes from the raw `problem_note`.
6. **Close out.** Update the rating-round CKPT and tell the coordinator.
