The consolidation of `experiments/09_human_rating_collection` passes this light quality-assurance (QA) review: no critical or major issues, seven minor ones. Nothing in the new README is false, but a few guards and caveats from the deleted files were dropped or weakened.

Reviewer: Claude Fable 5.2 (`claude-fable-5-2`), max effort, Claude Code; no files modified.

## What I checked

- **Patch scope:** the working tree equals `PATCH.diff`, only the 12 owned paths changed, and the untracked `rating_tensor_planning/` is still there.
- **Layout and mirror:** the experiment folder holds exactly `README.md`, `rating_task_packet/`, `ratings/`, `support/`; `AGENTS.md` and `CLAUDE.md` are byte-identical; `git diff --check` is clean.
- **Project check:** `python3 scripts/check_project.py` re-run gives 33 tests OK and left the worktree unchanged; all 29 protected packet/rating files match their recorded hashes.
- **Links:** every relative link and anchor in the patched files resolves, including the three new anchors (251 links in 40 files checked).
- **Counts:** the 12 raw comma-separated value (CSV) files have 11 columns each, 15 numeric ratings plus 3 `N/A`, and 0 main ratings; row counts are 6 and 125 as stated.
- **Assignments:** folders N17, N21 (Rylan) and N01, N23 (Sri) match the private delivered-assignment ledger.
- **Other consumers:** no script, JSON file or sister repository (`judges-dont-need-psychometrics-or-corr`, `cert-judge`, `veribench`, `agents-config`) references the deleted files.
- **Reading:** I compared both deleted files and the base README line by line against the new README and the import guide. Spelling was read by eye, since neither `aspell` nor `codespell` is installed.

## Findings (all minor, ranked)

Paths are relative to `experiments/09_human_rating_collection/` unless they start at the repository root.

1. **[p 7/10] The overview no longer says the 15 ratings are old data.**
   - `README.md:30` gives the count without "no new or revised ratings; all 15 match existing imports" (deleted `COMPLETION_STATUS.md:6`).
   - `README.md:47` turns "Re-exported copies are not new observations" (deleted `RATINGS_INDEX.md:31`) into "…re-exported copies are not completed main ratings", which is weaker.
   - The statement survives only in `support/IDENTITY_AND_IMPORT.md:67` and `ratings/SUMMARY.json`.
   - Fix: add the clause at line 30 and split line 47 into two sentences.

2. **[p 7/10] Slava's row blurs sent and unsent.**
   - `README.md:43` reads "Prepared CSV route; no returned CSV found in earlier scoped mail searches".
   - The missing return concerns his originally delivered warm-up. The linked form is the replacement, which `support/SLAVA_CSV_NAME_FIRST_11-11-2026.md:10` and deleted `RATINGS_INDEX.md:37` call prepared and unsent, with six blank rows.
   - Fix: "No returned CSV found for the original emailed warm-up; [replacement CSV form](…) prepared, unsent, six blank rows".

3. **[p 6/10] The entry line is Brando-specific but unlabeled.**
   - `README.md:3` links "your Google Sheet", which is Brando's warm-up Sheet, on a page listing ten people. `rating_task_packet/START_HERE.md:3` has the same link but adds "for Brando Miranda".
   - Fix: label it "Brando Miranda's warm-up Sheet", or link only `START_HERE.md`, which the project rule names as that link's home.
   - `README.md:9` ("The task you edit and give to raters") also drops "changes here are drafts until reviewed and packaged for delivery" (base `README.md:3`); restore that clause.

4. **[p 5/10] Three current statements still describe the old layout.**
   - Root `AGENTS.md:63` and `CLAUDE.md:63` say "Track the collected rating files, named index and completion status in Git directly under …", two lines below the new four-entry rule at line 61.
   - `support/COORDINATOR_README.md:33` uses the same phrase twice.
   - Its `## Files` tree (lines 55–73, stale before this patch) still shows `MIGRATION.json`, `PREPARATION_11-09-2026.md`, the checkpoint and `scripts/` at the top level.
   - Fix: reword to "rating files in `ratings/`, named completion table in the README", and replace the tree with the four entries or a pointer to `support/README.md`. Keep the two instruction files identical.

5. **[p 5/10] Root `README.md:71` has a dead anchor into this README.**
   - It links `experiments/09_human_rating_collection/README.md#current-delivery-status--11-09-2026`, which was already dead at base; the heading lives at `support/COORDINATOR_README.md:45`.
   - It is the "before sending" pointer and is outside the owned list.
   - Fix: retarget to `…/README.md#edit-or-prepare-the-task`, which now holds the dispatch gate, or to the coordinator heading.

6. **[p 4/10] Two caveats were dropped in the move.**
   - "This is collection evidence, not a fresh validation dataset" (deleted `COMPLETION_STATUS.md:37`) is in neither the README nor the new section at `support/IDENTITY_AND_IMPORT.md:60–72`. Add it after line 69.
   - "No reminders were sent" (deleted `COMPLETION_STATUS.md:25`) has no direct replacement. The nearest is `support/CKPT_human_rating_collection.md:11` ("Nothing has been sent in this revision"). Add a clause at `README.md:24` if you want it in the overview.

7. **[p 3/10] Polish.**
   - The README lacks the `**Doc link:**` and `**TLDR:**` lines that shared Rule 16 requires for rewritten documents; deleted `RATINGS_INDEX.md:6,8` had both.
   - `README.md:18` says "what to judge"; the project reserves "judge" for the model, so use "what to rate".
   - `README.md:22` says "eleven columns" and dropped "stored … internal keys hidden in Sheets" (base `README.md:14`).
   - `support/IDENTITY_AND_IMPORT.md:61–62` and `70–71` have doubled blank lines.
   - `.cursor/rules/project.mdc:29` and `:31` are two adjacent layout paragraphs; merge them.
   - `support/COORDINATOR_README.md:23` ("Start here … CSV files and Google Sheets") fits `../ratings/README.md` better, since line 30 already links the README table.

Not counted:
- Three dead links to the deleted files remain, by design, in two dated records: `support/NAME_FIRST_ROLLOUT_11-11-2026.md:13` and `support/sheet_exports/11-11-2026_all_raters_name_first/README.md:30`.
- `support/COORDINATOR_README.md:15` still says new forms use "the 18-column schema"; this predates the change.
- Both deleted files are on `origin/main` today, so any Google Doc or chat link to their GitHub pages will stop working after the push. I could not check those from here.

VERDICT: PASS
CRITICAL_ISSUES: 0
MAJOR_ISSUES: 0
MINOR_ISSUES: 7

**TLDR-end:** [ttj: human-rating collection › one-README consolidation light QA] The single-README consolidation of `experiments/09_human_rating_collection` passes with 0 critical, 0 major and 7 minor findings; counts, assignments, links, hashes and the 33-test project check all hold. Fix first the weakened "not new observations" wording (`README.md:30,47`) and Slava's row (`README.md:43`), which no longer says his replacement form is unsent.

**Snapshot:**
```
PATCH.diff sha256 8551ce51d4490d4f… == working-tree diff vs 585ce82 (12 files, +72/−102)
top level: README.md  rating_task_packet/  ratings/  support/
Ran 33 tests in 0.472s — OK · Project checks passed · worktree status unchanged by the check
links checked: 251 in 40 files
anchor ratings-and-completion / collection-evidence--11-11-2026 / current-prepared-version--11-11-2026 -> True
CSV TOTAL numeric=15 NA=3 · setN A1/T01/T05: rows=125 numeric=0 each
protected files: 29 mismatches: []
ASSIGNMENT_delivered.csv: N17,2,T01 · N21,1,T01 · N01,1,T05 · N23,1,T05
other BAD-ANCHOR README.md:71 -> …/09_human_rating_collection/README.md#current-delivery-status--11-09-2026
```