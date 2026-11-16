<!-- TLDR: Final light-QA result (10-20-2026) for the staged full set-N packet delivery to T01 and T05: two reviewers on the v7 inputs, every critical and major finding fixed and checked by script, and what is left for the send on Brando's go. -->
# Light QA summary: full set-N packet delivery to T01 and T05 (10-20-2026)

```
VERDICT: FIXED
CRITICAL_ISSUES: 0
MAJOR_ISSUES: 0
FIXES_APPLIED: 14
STRUCTURAL: SKIP
SUMMARY: Both reviewers verified the v7 zips byte-identical to origin/main 3f6549358f (plus each rater's YOUR_RATING_SHEET.txt) with no system-identifying text. Their 1 critical and 8 major process and protocol findings (6 distinct majors once A04/F02 are merged and F05 is folded into critical A01) were fixed in the drafts, the plan and C18 (49186f41b6) and checked by script. Per Hard Rule 3, there is no automatic re-review.
```

**Reviewers (Brando's request):**
- Codex `gpt-6-astra` at ultra effort (`REPORT_astra.md`): FAIL, 1 critical, 3 major, 1 minor.
- Claude `claude-fable-5-1` at max effort (`REPORT_fable.md`): PASS, 0 critical, 5 major, 8 minor.

Both reviewed the v7 inputs, using brief revision 2. A first build and review used the stale shared checkout (the v4 packet) and are void (`../void_stale_v4_10-20-2026/`).

| Finding | Fix | Where |
|---|---|---|
| Astra A01 (critical) and Fable F05: the primary analysis vs. C15 item 6 | C15 item 6 kept verbatim: extras from qualified non-A1 raters enter the primary as C15 states; assigned-only becomes Sensitivity 1 | C18 `49186f41b6` (coordinator) |
| A02: no collection of order or time | The email asks for "folder minutes: NN; finished MM-DD"; C18's Descriptive 3 is narrowed and labelled confounded | drafts; C18 |
| A03: the importer reads the 2-folder receipts | Send step 5 appends both full-packet receipts, with a synthetic-row check | `DELIVERY_PLAN.md` |
| A04 and F02: unchecked send route | Send through `scripts/send_rater_email.py`, with `--dry-run` first and C18 IN FORCE first. Dry run 10-20: placeholder bodies REFUSED; synthetic-link bodies pass, with BCC 4 of 4, no attachments and the correct To | `DELIVERY_PLAN.md` |
| F01: the Drive share misses T01's To address | Share with both addresses, plus a fallback line in the email | plan decision 4; T01 draft |
| F03: C18 text out of date | Tail shuffle, order stated in the email only, script route | C18 `9979d8dcbd`, `49186f41b6` |
| F04: a note addressed to the judge inside N02 and N16 references (confirmed by a count: 6 lines each, 2 of 25 references) | The email says to ignore that note and rate by START_HERE and the rules file | drafts |
| A05: receipt basenames | `../STAGING_MAP.json` maps each built name to its staged name, with the SHA-256 checked | staging folder |
| F06, F07, F08, F09 | "Nothing to mark complete"; one name for the rules file; folding tip dropped and Ctrl+\ added; Cursor Tab and indexing turned off | drafts |
| F11 | Stage 3 keeps one shared order (more early pairs); the confound is named in C18's Descriptive 3 | C18 |
| F12 and the Astra cue list | No file changes. The 7 recurring comment signatures are disclosed as a limitation; the N24b.lean:8 link is the task's own CPython source | C18 (coordinator adjudication) |
| F10, F13 | `RATER_INSTRUCTIONS.md` update and a CKPT note accepting the Chrome route, both at C18 IN FORCE | coordinator, send step 0 |

**Left for the send (10-21-2026, after Brando's go):** send steps 0-6 in `DELIVERY_PLAN.md`. These cover C18 IN FORCE, re-reading the sheets, Drive staging and sharing, comparing the downloaded hash, the script dry run and send, and the receipts.
