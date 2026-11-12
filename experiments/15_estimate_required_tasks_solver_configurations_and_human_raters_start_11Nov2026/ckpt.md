# Continue rating-size estimation and simplify the judge repository

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/15_estimate_required_tasks_solver_configurations_and_human_raters_start_11Nov2026/ckpt.md>

**TLDR:** Claude Code took over sizing and cleanup on 11-11-2026 and carried out the inherited continuation: stale summaries are corrected, the root `docs/` folder is gone, and the README now holds a costed allocation with three open choices for Brando. The final collection size is still undecided; experiment 09's separate owner handles the human-rating task.

Created: 11-11-2026 22:27 PST
Last updated: 11-11-2026 23:08 PST

## Goal

- Give Brando traceable T/A/H estimates, a practical recommendation, and a simpler repository with one clear home for each effort.
## What ran

- 11-11-2026 22:40 PST: Claude Code 2.1.322 (`claude-fable-5-2`, effort `max`, session `e5556c18-2c10-4562-a2ae-6978ca6b39b3`) verified revision `3932b6d` and this file's SHA-256 `2cc7953f…38eba`, then accepted sole ownership of sizing and cleanup. It does not own the collection.
- Corrected the 85-file/170-rating summaries (root README, paper README, two paper sections, rebuilt PDF); moved the three root `docs/` notes; renamed the Claude source export; landed experiment 10's receipt text; added the costed allocation with two checks in the project check.
## Results

- Current packet, rechecked against the frozen manifests: 54 returned files, 25 tasks, three represented solver configurations; 85 planned, 31 missing; target 108 independent ratings; 0 main ratings completed.
- Planning arithmetic, not a measurement (`p-val=n/a`): 25 tasks give a 95% half-width of ±0.012 for a paired ranked probability score difference in the middle case, ±0.003 to ±0.025 across cases. ±0.01 needs 37 held-out task families (3–155); ±0.005 needs 145 (11–620).
- Scenarios: 108, 212, 264 or 732 independent ratings. Minutes per main-task rating are unmeasured; the only entries are six warm-up times from one rater, median 4.
## Stuck / blocked

- Nothing blocks. A final size needs Brando's three choices and two measurements: main-task rating time, and the spread of the paired difference for the actual judges.
## Next steps

- [p 9/10] When trial ratings with `minutes_spent` reach experiment 09, run `python3 experiments/15_estimate_required_tasks_solver_configurations_and_human_raters_start_11Nov2026/scripts/costed_allocation.py --write --tables`, update the quoted hours, then `scripts/refresh_provenance_hashes.py --write`.
- [p 8/10] After Brando picks claim, precision and workload cap, write the identity-split amendment with experiment 02's owner and freeze counts before any collection.
- [p 6/10] Remove the experiment 10 worktree once Brando confirms; its recovery package is verified.
## Brando to-do

- Choose the claim, the precision and the workload cap: [three decisions](README.md#three-decisions-that-are-brandos).
- Say whether the experiment 10 worktree may be removed.
- Rate a few main-task files and enter `minutes_spent`; this is also the collection owner's first step.

## Where the answer lives

- Decision table, costed scenarios, three choices and the historical source comparison: [README](README.md). The compact comparison that used to sit here was merged into it, with its line references.
- Inputs, formulas, limits and missing inputs: [methods note](METHODS_AND_ALLOCATION.md#costed-allocation-from-existing-evidence--11-11-2026).
- Numbers: [results/costed_allocation.json](results/costed_allocation.json), written by [scripts/costed_allocation.py](scripts/costed_allocation.py). File hashes: [provenance.json](provenance.json), kept current by [scripts/refresh_provenance_hashes.py](scripts/refresh_provenance_hashes.py). `python3 scripts/check_project.py` runs both checks.

## Continuation status: the nine inherited steps

| Inherited step | Outcome on 11-11-2026 |
| --- | --- |
| 1. Establish the current state | Done. Revision, checkpoint hash and experiment 09's two frozen manifest hashes matched before any edit. |
| 2. Make current summaries agree with the packet | Done in the repository: root README, experiment index, paper README, `05_design.tex`, `09_discussion.tex` and the rebuilt eight-page PDF. The existing Google companion was corrected and read back. |
| 3. Finish clutter reduction | Done. Root `docs/` removed by three moves; root README cut from 66 to 39 lines around one tracking table; this folder's comparison now has one home. The old-to-new map is in the [archive index](../archive/README.md#root-notes-folder-source-rename-and-experiment-10-receipt--11-11-2026). |
| 4. Resolve structural questions | Decided with evidence, no move: experiment 02 stays active; archived 16, 17 and 18 stay here; `paper_latex/` and `scripts/` keep their names. Reasons are in the archive index. |
| 5. Reconcile the experiment 10 worktree | Receipt text landed after verification; a recovery package reproduces both worktree files byte-for-byte. The checkout is untouched and still registered; removal awaits confirmation. |
| 6. Turn sizing into a concrete decision | Done: three claims, three precision targets and a workload cap, with a recommendation labeled as an agent's suggestion. No existing user decision fixes any of them: every threshold in experiment 02's `config.json` is `null`. |
| 7. Build a costed allocation from valid inputs | Done from saved results only. Named missing inputs and how to obtain each are listed in the methods note. |
| 8. Use existing learning-curve evidence | Done: archived experiments 17 and 10 supply the variability and the curve. Archived experiment 07's scaling fit measures metric-estimation error for a fixed judge, so it is cited, not used for sizing. No new run. |
| 9. Verify and land | See the log line for this session. |

## Coordination

- **Sizing and cleanup owner:** Claude Code session `e5556c18-2c10-4562-a2ae-6978ca6b39b3`; its Remote Control link is in the private receipts. Former owner: Codex chat [Recover rating-data estimates](codex://threads/01a1cc5b-af60-77d1-8f1e-2207b1f121d1), which stops writing these files once the takeover is verified. Private receipts: `/Users/brandomiranda/.local/share/trustworthy-theorem-judges/claude_takeover_11-11-2026/`.
- **Collection owner:** unchanged and separate. [Experiment 09's handoff](../09_prepare_packets_and_collect_human_ratings_start_09Nov2026/support/ckpt.md) is authoritative; its successor was still unnamed at this update (`successor_chat` is `null` in the private preparation record). This session read experiment 09's files and changed none of them.
- **Latest collection sequence:** Brando's trial, instruction review, then the Sri, Yegor and Brando first batch after explicit send approval. Others are held. This is context, not authority to send mail.
- **Experiment 10 worktree:** `~/.worktrees/trustworthy-theorem-judges/paper-publication-receipt-11-10-2026`, detached at `7dc735a`, last modified 11-10-2026 09:47, no process using it. Recovery package: `experiment_10_worktree_recovery/` under the private receipts folder.
- **Do not recreate:** a root `docs/` folder, the retired `experiments/09_human_rating_collection` alias, or a source export named `claude.md` or `agents.md` (agent clients load those names as instructions).
- **Unchanged gates:** archived experiment 04 stays paused on funding and context coverage; archived experiment 08 keeps its pending parent review and three known Markdown freeze-hash discrepancies. No collection, paid inference or collaborator email is authorized by this work.
- **Private material:** source captures and the Gemini distributions export stay under `/Users/brandomiranda/.local/share/trustworthy-theorem-judges/rating_tensor_source_archive/`; the private meeting transcript stays out of public Git.
- **Model review:** the one light review requested earlier was completed before this takeover. None was requested for the costed allocation; it has deterministic checks only.

## Takeover prompt

```text
Continue the rating-size decision support in /Users/brandomiranda/trustworthy-theorem-judges. Read experiments/15_estimate_required_tasks_solver_configurations_and_human_raters_start_11Nov2026/ckpt.md and README.md in full, refresh the repository and shared instructions, and inspect Git state and active owners before editing.

The repository cleanup is finished: do not recreate a root docs/ folder or rename paper_latex/ or scripts/ without Brando's decision. The remaining work depends on inputs that did not exist on 11-11-2026. First, when experiment 09 holds participant-entered minutes_spent for main-task files, rerun scripts/costed_allocation.py --write --tables, update the hours quoted in README.md and METHODS_AND_ALLOCATION.md, and refresh provenance.json with scripts/refresh_provenance_hashes.py --write. Second, when Brando chooses the claim, the precision target and the workload cap, turn the matching scenario into a prospective identity-split amendment with experiment 02's owner, and freeze task-family, solver and rater identities and counts before any collection. Third, remove the experiment 10 worktree only after Brando confirms.

The numbers are planning arithmetic from cached-judge studies, not measurements of a future study: 37 held-out task families for a ±0.01 paired ranked probability score comparison, ranging from 3 to 155. Keep the current 54-file packet evaluation-only and its outcomes out of sizing and selection. Missing outputs are not zero ratings. Experiment 09's collection owner controls packets, assignments, Sheets and sending; no collection, paid inference or collaborator email is authorized here.

Run python3 scripts/check_project.py and git diff --check, inspect the staged diff, commit and push main, and update this checkpoint and the existing Google companion rather than creating new summaries.

TL;DR: Refresh the costed allocation when real rating times exist, convert Brando's three choices into a frozen split amendment, and leave collection to its owner.
```

## Log

11-11-2026 22:27 PST — Rechecked all three source recommendations, recorded the current 54-file collection distinction and remaining layout work, and consolidated the previous recovery checkpoint into this user-requested ckpt.md with a takeover prompt. No source export, rating, split, generation or scientific result changed.

11-11-2026 22:30 PST — Verification passed and Google comparison/recommendation links read back; checkpoint ready for user-selected takeover.

11-11-2026 22:31 PST — Cross-linked the collection coordinator's separate handoff; both successor identities remain unassigned.

11-11-2026 23:02 PST — Claude Code (`claude-fable-5-2`, effort `max`) accepted sizing and cleanup ownership at 22:40 after verifying revision `3932b6d` and the checkpoint hash, then landed the continuation in the commit that adds this line: corrected packet counts in the root README, experiment index, paper README, two paper sections and the rebuilt eight-page PDF; removed root `docs/` by three byte-preserving moves; renamed the Claude source export; landed experiment 10's receipt text with a verified recovery package; added the costed allocation, its saved result and two checks. Verified: 66 project tests, design validator, sizing and provenance checks, paper build with no overfull boxes or unresolved references, 616 local Markdown links with no new broken link (seven older ones remain in other owners' historical records, plus the frozen source export's embedded links), a dictionary check of 5,932 added words, and `git diff --check`. No rating, model call, collection file, Sheet or email was touched. Google companion update follows separately.

11-11-2026 23:06 PST — Repository work landed as `fd30d71` on `origin/main`. Updated the existing Google Q&A companion in one revision-guarded batch and read it back: the stale 85-artifact/170-rating sentence is corrected, the costed-allocation paragraph and decision links are in the sizing section, and two links to the renamed Claude export are repointed; exactly four paragraphs changed. Page layout was not rendered.

11-11-2026 23:08 PST — Companion record landed as `610d757`. This session, as the single notifier, emailed the results notice to Brando's own inboxes at 23:07 PST and verified it once; no collaborator was emailed. The private completion marker is written. Session ends with nothing running; next action is Brando's three choices.

## Historical source-recovery record

The following prior recovery/review notes are preserved as history. Their placement/status statements refer to the earlier work; the current state and archive map above supersede them.

- Date: 11-11-2026. Owner: Codex root; local-source subagent supplied the methods draft and source cross-checks.
- Home: experiment 15, assigned by Brando on 11-11-2026. Scope: recovered text/URLs and sizing methods; no new collection, training, inference experiment or protocol mutation.
- Recovered: Claude 22 messages; Gemini bounds 20; ChatGPT shared 10 + overlapping branch 10 + recent supplement nine. All identified sizing exchanges are included; no specific missing interval was established.
- Private archive: Gemini distributions 18 messages, raw captures and review logs under `/Users/brandomiranda/.local/share/trustworthy-theorem-judges/rating_tensor_source_archive/`.
- Recommendation: preserve historical 14,848 budget; Codex’s 544-rating pilot is optional and unapproved, not a user-specified count. Freeze all three identity splits before collecting; final required total remains undetermined.
- Review: one Claude Code 2.1.322 subscription session; actual response model `claude-fable-5-2`, launch effort `max`, permission mode `bypassPermissions`, no API key. Session `a4b0b3ba-c390-4a94-9437-e10f188dfb45`; exit 0. Builder model identifier was not exposed in this runtime.
- Original verdict: FIXES_REQUIRED. Root resolved six findings: corrected primary citation; changed Claude endorsement to deferral; bounded/qualified pilot rationale; separated sizing-approach names from formulations; enforced all split axes before collection; labeled computed counts.
- Gemini split citation rechecked: message 12's final paragraph and message 14 both contain 35/45/55; message 20 contains 35/40/60. This part of the reviewer concern was rejected with source evidence.
- Link follow-up: published exact snapshots of three earlier plans; two 11-05 files lack a located commit. Original VeriBench links are access-restricted. Removed unarchived Extra High claim; local private export paths are plain text in GitHub docs.
- Optional review suggestions not adopted: 17.3% density ignores distinct generation/stage records; simple chi-square variance intervals do not describe this crossed pilot; bounded-loss scope and curve-identifiability cautions were added.
- Deterministic evidence: project checks and 33 tests passed; experiment 02 design validator passed; paper build passed with no overfull boxes or unresolved references; no paper source edits, so rebuild-only PDF bytes were restored.
- Source checks: captured message bodies match after whitespace normalization; exported trailing spaces normalized for Git checks; exact snapshot blocks match source hashes; supplied attachments preserved; no secret/email/phone/consent values found in public source scan.
- Google companion: dated section added to the existing Q&A Doc; exact text, heading and three URL links read back successfully. Receipt hash is in provenance.json.
- Follow-up 11-11-2026: browser and capture comparison corrected the earlier definite-gap claim. The loading marker does not prove missing messages; no new source text or sizing decision was added. Informative FYI to the human-grading owner authorized by Brando.
- Review manifest, original findings and final file hashes are recorded in provenance.json; no automatic second review. Final staged-diff checks and publication receipt are reported in the completing chat/Git history.
- Concurrent experiment 09/instruction edits were committed by their owner as `cf9767264097b45fed8bb3c2b5d7bafbe2ce5076`; they were not staged or rewritten here.

- Reorganization, 11-11-2026: Brando assigned the sizing work to experiment 15. Preserved all four source exports and both attachments byte-for-byte; repaired live navigation and clarified that 544 was an optional Codex proposal, not a user-specified or approved count. Current collection remains in experiment 09. Eight historical folders moved into archive; active/important/pending work remains indexed. Google companion links and attribution were updated and read back; receipt is in the local source archive.
- Reorganization verification: 277 archived tracked files and six source/attachment files byte-identical; 104 current local links checked; phase-0 config/input hashes preserved; importer entry point and shell syntax valid; 33 project tests and paper build passed. The separate owner’s publication worktree is preserved, so experiment 10 remains visible pending reconciliation. No additional model-review round or scientific execution was run.
