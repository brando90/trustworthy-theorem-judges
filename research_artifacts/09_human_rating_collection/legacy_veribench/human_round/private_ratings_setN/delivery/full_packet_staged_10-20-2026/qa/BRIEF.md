<!-- TLDR: Light-QA brief (Brando-requested, 10-20-2026) for the staged full set-N packet delivery to raters T01 and T05: what to check, the binding blinding limits, and the report format. -->
# Light QA brief: full set-N packet delivery to qualified raters (VeriBench experiment 102)

Brando asked on 10-20-2026 for a light QA (one review round; the dispatching session fixes the findings) of the rater email, the packets and the delivery plan before anything goes to raters. Two reviewers run this same brief independently: Claude `claude-fable-5-1` at max effort, and Codex `gpt-6-astra` at ultra effort. Nothing has been sent; the send waits for Brando on 10-21-2026. **Revision 2:** a first build and review used the stale shared checkout `~/veribench` (the 10-08 v4 packet), so both are void. Review only the v7 inputs below, and take repository files from the clean origin/main checkout `/private/tmp/claude-501/-Users-brandomiranda/68c9cfec-5c35-4317-9b89-1f03bef5e618/scratchpad/vb_v7` (commit `3f6549358f`), never from `~/veribench`.

Let `B = ~/veribench/experiments/102_rescore_vbv1_paper_fsc_with_validated_judge_rewrite_tmlr_icml/human_round/private_ratings_setN/delivery/full_packet_staged_10-20-2026`.

## Inputs
- `B/qa/DELIVERY_PLAN.md`: the decisions under review. Read it first.
- `B/qa/EMAIL_T01_DRAFT.txt`, `B/qa/EMAIL_T05_DRAFT.txt`: the exact emails. The `<DRIVE_LINK_T0x>` placeholders are filled at send time.
- `B/VeriBench_setN_T01_full_N01-N25_v7.zip`, `B/VeriBench_setN_T05_full_N01-N25_v7.zip`: what raters will download (v7 release plus each rater's `YOUR_RATING_SHEET.txt`).
- `B/qa/sheet_structure_T01.csv`, `B/qa/sheet_structure_T05.csv`: columns A-D of each rater's live sheet (rating columns not included).
- `B/qa/sent_log_T01_T05_setN.json`: what each rater was sent before (folders, sheet id, subject with due date).
- The repository packet these zips come from: `/private/tmp/claude-501/-Users-brandomiranda/68c9cfec-5c35-4317-9b89-1f03bef5e618/scratchpad/vb_v7/experiments/102_rescore_vbv1_paper_fsc_with_validated_judge_rewrite_tmlr_icml/human_round/sample_setN/packet/`. In the same experiment folder of that checkout, also read `scripts/make_rater_zip.py`, `human_round/PLAN_setN_rating_round.md`, `human_round/RATER_INSTRUCTIONS.md` and the proposed amendment C18 (`git -C /private/tmp/claude-501/-Users-brandomiranda/68c9cfec-5c35-4317-9b89-1f03bef5e618/scratchpad/vb_v7 show --stat 8dbef4c917` names its file).

## Binding limits
- **Brando is a blinded rater (A1) and reads your report, so keep it free of rating content.** Never quote or paraphrase text from any `agent_lean`, `gold_lean` or `python_source` file. Never say how well any agent file covers its reference, never propose or hint at a score, and never state or guess which system or model produced a file. For a leak, give only `path:line` and the category (for example "system-identifying text"), never the text itself.
- **Open nothing else under `private_ratings_setN/`** besides the folder `B` and its `qa/` subfolder; skip `B/void_stale_v4_10-20-2026/` too. That directory holds other raters' private ratings and scoring records. Also open no `sealed/` directory, no judge outputs and no experiment `results*` or `runs/` content. None of it is needed for this review.
- **Review only.** Write nothing except your report file: no edits, emails, Drive or Sheets actions, or git commands. The dispatching session applies the fixes.

## Checks
1. **Packet integrity.** In each zip, every file matches the zip's `FILES.sha256`. Every release file also matches the origin/main `sample_setN/packet/FILES.sha256`; the only extra file is `YOUR_RATING_SHEET.txt`, which must carry that rater's sheet link and Google account. Every folder N01-N25 has `python_source/`, `gold_lean/` (plus `N17/gold_lean_dependencies/`) and five agent files `a`-`e`. `START_HERE.md` and `human_judgements_prompt.md` are present. Apart from the top-level folder name and `YOUR_RATING_SHEET.txt`, the two zips are identical.
2. **Blinding.** Scan all 125 agent files and the zip metadata for anything that could reveal or group systems: model, vendor, agent or harness names; run ids; paths; timestamps; distinctive header or boilerplate patterns that recur across folders. Report locations only.
3. **Instructions vs. email.** Check `START_HERE.md` and `human_judgements_prompt.md` against the drafts: the score scale, the required columns, "folder minutes", the AI-assistance rule, due dates, what to submit and how the sheet is used. Flag anything contradictory or confusing for a rater who now has all 25 folders, for example text saying the packet holds only their assigned folders.
4. **Email drafts.**
   - Folder ids, sheet ids and due dates must match the sent log. Check that each date's weekday is right for 2026.
   - The rating order must follow the plan.
   - The email must be clear for a rater who knows little Lean, with nothing that could bias ratings or weaken rater independence.
   - The editor tips must be correct. In Cursor, Cmd+K opens the inline AI editor; check every tip against Cursor and VS Code.
   - Check length and tone.
5. **Sheet structure.** The 125 items in `sheet_structure_T0x.csv` must match the zip's agent files one to one.
6. **Delivery plan.** Look for anything that could leave an email without a working way to get the files:
   - Stanford mail strips zips.
   - The Drive share must go to the Google account the rater uses.
   - Every placeholder must be filled before sending.

   Then weigh the scientific risks of switching to the full packet with a fixed order (data quality, blinding, selection effects), and judge whether the order actually produces 2-rater pairs.
7. Anything else that would confuse raters or harm the data.

Severity: **CRITICAL** = could unblind, corrupt data, or leave a rater unable to get the files. **MAJOR** = likely rater confusion, or a wrong id or date. **MINOR** = polish.

## Report
Write `B/qa/REPORT_fable.md` if you are the Claude reviewer, or `B/qa/REPORT_astra.md` if you are the Codex reviewer, in this shape:

```
VERDICT: PASS | FAIL
CRITICAL_ISSUES: [int]
MAJOR_ISSUES: [int]
FIXES_APPLIED: 0
STRUCTURAL: SKIP
SUMMARY: [1-2 sentences]
```

Below the verdict, list the findings, one per line: `id | severity | file:line | issue (at most 3 sentences, no quoted packet content) | suggested fix`. Then add a "Checks run" list with the commands and counts behind each conclusion. When the report is written, end your turn.
