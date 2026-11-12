# Continue rating-size estimation and simplify the judge repository

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/15_estimate_required_tasks_solver_configurations_and_human_raters/ckpt.md>

**TLDR:** The original Claude, Gemini and ChatGPT sizing passages are recovered and compared below; none establishes the required final collection size. Continue the decision support and finish repository simplification, while experiment 09's existing owner handles the human-rating task. The full takeover prompt is in this file; no second prompt/checkpoint file is needed.

Created: 11-11-2026 22:27 PST
Last updated: 11-11-2026 22:31 PST

## Goal

- Give Brando traceable T/A/H estimates, a practical recommendation, and a simpler repository with one clear home for each effort.
## What ran

- Re-read the source passages, experiment 09's current README and collection coordinator record; source-file hashes matched the existing manifest before this edit.
- Verified 66 project tests, design/source checks, paper build, passage anchors and unchanged source hashes; updated/read back the existing Google companion. Baseline main revision was 31fd5c78080b942a669cae7d0c2ff65ed1b8b7a2, with a clean working tree at inspection.
## Results

- Historical final comparison: Claude defers to 896/4/24; Gemini proposes 135/5/6–8; ChatGPT proposes 896/4/24. These are proposals, not measured sample-size requirements.
- Current collection: 54 real files on 25 tasks, three represented solver configurations; target 108 independent ratings plus Brando's additional author ratings. No completed main ratings in the inspected record.
## Stuck / blocked

- No access blocker. Final future T/A/H requires a defined claim, acceptable uncertainty, actual rater capacity and an amended split/assignment design.
## Next steps

- [p 10/10] Read the canonical state, then implement the prioritized continuation below; first command: `git -C /Users/brandomiranda/trustworthy-theorem-judges status --short`.
- [p 9/10] Finish coherent clutter reduction after checking owners and live consumers; keep frozen evidence intact and update current consumers together. No successor to this sizing task has been selected; a saved prompt is not a verified takeover.
## Brando to-do

- Try a few ratings, then review participant instructions; the collection owner controls the subsequent Sri/Yegor/Brando first batch and explicit send approval.
- Choose the future study's practical uncertainty/effect target and workload cap when the next agent presents concrete options; no 544-rating pilot has been approved.

## Compact historical source comparison

T = distinct tasks, A = fixed solver configurations, H = distinct human raters. Ratings per artifact are a separate quantity, m. Sparse assignments, dense subsets and fresh output rounds mean the workload is not generally T × A × H.

| Source | T | A | H | Proposed rating workload and exact passages |
| --- | ---: | ---: | --- | --- |
| Claude | 896 | 4 | 8–12 originally; later defers to 24 | Intermediate main stages total 7,168 + 5,120 = 12,288 (source rounds to 12,300), excluding its separate pilot/constructed slice and leaving overlap unclear. [Message 6](sources/claude.md#message-6--assistant), especially lines 151–167. [Message 22](sources/claude.md#message-22--assistant), lines 523–541, supersedes its figures in favor of the repo's 14,848-rating/24-person plan; T/A are inherited from that plan, not newly derived there. |
| Gemini | 135 | 5 | 6–8 | Final proposal claims 800–1,000 ratings, with 35/40/60 train/validation/test tasks. [Message 20](sources/gemini_argon_high.md#message-20--model-response), especially lines 1572–1597 and 1655. The claimed workload depends on unsupported automatic-zero filtering; its earlier concentration-bound arithmetic is also wrong. |
| ChatGPT | 896 | 4 | 24: eight development, sixteen audit | Final proposed budget is 14,848: 1,536 development + 10,752 fresh audit + 2,560 dense extras. [Shared-snapshot message 10](sources/chatgpt_pro.md#message-10--assistant), lines 1133–1167 and 1289–1293. It explicitly calls these starting numbers, not proven sufficient counts. Earlier five-person designs proposed 35,840 then 28,160; a 20,480 alternative also precedes the final design. |

Claude's final answer is deference to the same repository/ChatGPT plan, not independent statistical confirmation. All 896-task designs refer to the historical pinned benchmark scope. Original signed-in chat links and coverage limits are in [SOURCE_INDEX.md](SOURCE_INDEX.md); readable exports are preserved in `sources/`. Do not invent missing ChatGPT history: all identified sizing estimates were found, and no specific missing interval was established. The “Loading older messages” marker alone did not demonstrate a gap. Model labels observed at capture do not authenticate historical per-message backends.

## Recommendation now

**Complete the existing small evaluation collection before authorizing a new large study.** Follow the latest sequence: Brando grades a few files, the collection owner reviews the actual instructions with him, prepares/reconciles Sri, Yegor and Brando, and obtains the required explicit send instruction. Other prepared recipients remain held. This is a workflow trial; it is not the optional 544-rating training pilot.

The existing main pool is **25 task identities, three configurations represented by 54 returned files, and an incomplete human-rater assignment**. The current target is two independent ratings per returned file, 108 in total; Brando's up-to-54 author ratings are additional. This is a practical collection target, not a guarantee of precision or broad transfer. H is not “2”: two is ratings per artifact. Nor is H automatically three just because the first recipient batch names Sri, Yegor and Brando; qualification and author/extra-only roles differ. Keep all 85 planned task/configuration combinations and 31 missing outputs in provenance; missing submissions are not human scores of zero. The full planned solver set and the three configurations with returned artifacts are different denominators.

**For a future development/generalization study, recommend a staged allocation with a prespecified budget and precision target, not 14,848 or 800–1,000 by fiat.** First define the target claim and the task-family, solver and human populations; then resolve the task/solver/rater split amendment and identify eligible new development data. Use measured review times for staffing, and design-aware uncertainty calculations for a specified paired loss contrast. Use only eligible development information or explicitly declared external assumptions to size the future study; preserve the current collection's evaluation-only role and sealed outcomes. Distinguish fixed-system performance from unseen-solver claims. Present feasible scenarios and their assumptions before fixing counts. Neither 544 nor any other new total is adopted by this handoff.

Use [METHODS_AND_ALLOCATION.md](METHODS_AND_ALLOCATION.md) for the three distinct questions: standard errors size evaluation precision; learning-theory bounds check assumptions; learning curves study how training data improve a learned judge. Its illustrative variances and power-law coefficients are not measured for a new collection. The [archived real-rating learning curve](../archive/17_measure_judge_learning_from_4_to_20_tasks_and_more_human_ratings/README.md) is relevant existing evidence, limited to its cached judges, 25-task pool and training sizes 4–20; it does not justify extrapolating a new final sample size.

## Prioritized continuation: all suggested next steps

1. **[p 10/10] Refresh and establish the current authoritative state.** Read root `AGENTS.md`/`CLAUDE.md`, refresh the shared rules, fetch main, inspect the diff, worktrees and active owners. Read this experiment's README, source index and methods note, then experiment 09's README and support coordinator record. A later collection change supersedes the snapshot above. Preserve concurrent work and use scoped staging/commits on main.
2. **[p 10/10] Make the repository's current summaries agree with the actual packet.** At baseline 31fd5c7, root `README.md` and `paper_latex/AAAI_2027_Evaluation_AI_Scientists/README.md` still describe 85 artifacts/170 ratings as the current pending replacement. Experiment 09 now has 54 returned files/108 target independent ratings. Update current summaries from its receipts, retaining 85/170 as the original plan and 31 missing outputs separately. Check paper source and Google companion for the same distinction. Do not turn preparation counts into completed ratings or new judge results.
3. **[p 9/10] Finish clutter reduction as one coherent change.** Inventory root and active experiment entry documents, classify each as current workflow, support, unique provenance, or redundant copy, then consolidate redundant navigation into the existing README and support homes. The user still finds the repo cluttered despite the previous moves. Prefer a short current-work index and a separate archive inventory; avoid introducing new guide/index/checkpoint files. Preserve all unique content before removing redundant working copies, and verify local/Git/editor visibility separately.
4. **[p 9/10] Resolve the remaining structural questions with evidence.** Decide whether experiment 02 still needs an active implementation home or whether its human-facing methodology navigation belongs with the paper; check its current owner and consumers before moving it. Reconcile the overlapping purpose of archived 16/18 and the sister position-paper repository, and keep 17's sizing relevance and 17/18→16 code imports intact. A cross-repo transfer must publish and verify the destination before removing the source, with one canonical copy and repaired consumers. Do not move studies merely because their names resemble each other.
5. **[p 9/10] Reconcile the preserved experiment-10 worktree with its owner.** `~/.worktrees/trustworthy-theorem-judges/paper-publication-receipt-11-10-2026` was still registered at inspection. It has unique checkpoint/PDF work; preserve it until reviewed and landed or otherwise resolved by the owner. The destination is `experiments/archive/10_fit_5_judge_mixtures_to_75_outputs_pearson_vs_ranked_probability/`. Remove a temporary checkout only once unique work is preserved and its owner confirms it is no longer in use.
6. **[p 10/10] Turn the sizing question into a concrete decision.** Specify whether the goal is fixed-benchmark evaluation, prediction of new task families/solvers/raters, or development-data sufficiency. For the methods-2-versus-4 comparison, retain matched capacity/data/search budgets and common validation normalized ranked probability score (RPS); cross-entropy and total variation remain secondary. Determine the practical precision/effect target and total time/cost cap from existing user decisions; if absent, present a small set of explicit choices without pretending one is user-approved.
7. **[p 9/10] Build a costed allocation from valid inputs.** Separate T, A, H, ratings per artifact, task-family count, output rounds and observed/missing cells. Resolve the prospective identity-split amendment; measure workflow time from actual participant entries, never assistant timing guesses. Estimate variability only from authorized development data or documented external assumptions. Show uncertainty/sensitivity and per-person workload. Select a minimal feasible allocation only after its criterion is declared; do not collect until significance or reuse held-out data for selection. If data cannot support an estimate, report precisely which named inputs are missing and a bounded plan to obtain them.
8. **[p 8/10] Use existing learning-curve evidence before proposing new runs.** Read archived 07 and 17, retaining their data reuse, correlated subsets and limited solver-family caveats. No new model inference or rating collection is authorized solely by a file cleanup or this checkpoint. Any separately authorized execution inherits its declared budget, manifest and existing funding pauses.
9. **[p 10/10] Verify and land the resulting cleanup and decision support.** Check links/anchors and old-to-new mappings; preserve source exports, raw ratings, immutable receipts and freeze-bound bytes. Refresh mutable `provenance.json` navigation hashes after editing experiment 15, without rewriting historical review/capture hashes. Run project/design checks and relevant affected script tests; build the paper if its sources change. Inspect the exact staged diff for scope and secrets, then commit/push main. Update the existing Google knowledge section for substantive decisions; no duplicate companion. Finish with a concise index and concrete remaining decisions.

## Current organization and coordination

- Active top-level experiment homes are `02_design_a_judge_that_predicts_human_ratings_0_to_5`, `09_prepare_packets_and_collect_human_ratings`, and this `15_estimate_required_tasks_solver_configurations_and_human_raters`. The original `01_veribench_25_tasks_3_samples_5_raters_judge_evaluation` is archived and prominently linked.
- Cleanup commit `ad6c2dc` moved 04, 07, 08, 10 and 16–18 into the archive. `1a03b9a` removed the temporary Explorer exclusion after the old 09 alias was removed. The alias is absent; do not recreate it. [Archive inventory and mappings](../archive/README.md) preserve status and provenance.
- Archived 04 remains paused on funding/context coverage; 08 retains its pending parent review and three pre-existing Markdown freeze-hash discrepancies. A folder move did not resolve either gate. All original freeze-bound bytes were preserved.
- General objective studies 06 and 11–14 already live in `/Users/brandomiranda/judges-dont-need-psychometrics-or-corr`; no new local copies. Its migration manifest records the previous transfer. The canonical VeriBench checkout has previously had divergent/concurrent work: inspect before synchronizing, never reset it for convenience.
- Root inventory at handoff: `.cursor/`, `docs/`, `experiments/`, `paper_latex/`, `scripts/`, root README/instruction/license files and Git dotfiles. Project instructions currently pin `paper_latex/AAAI_2027_Evaluation_AI_Scientists/`; do not mechanically apply a generic bucket rename without checking that contract and every consumer. Experiment-specific data/scripts stay with their experiment; named ratings are authorized tracked artifacts.
- Outgoing collection coordinator: [Prepare human grading task](codex://threads/01a1a8f9-dcb7-7381-9368-91d6e51faffd). Other packet helper: [Rate warm-up Lean files](codex://threads/01a1cc2c-210b-79d1-bafe-39c7ef1080f5). Brando authorized informative FYIs to these chats. The collection coordinator has also handed off its task in [experiment 09 support/ckpt.md](../09_prepare_packets_and_collect_human_ratings/support/ckpt.md), stops writes after publication, and has not named a successor. Read that handoff and establish ownership before any cross-cutting move. This sizing handoff does not silently transfer packet preparation, assignments, raw imports, Sheets or sending.
- Latest collection sequence is Brando trial → instruction review → Sri/Yegor/Brando first batch after explicit send approval. Yegor's main packet/assignment/email still needs owner preparation and his extra-only status is unchanged; Rylan and others are held. This is context for the next agent, not authority to send mail.
- Private source captures and the Gemini distributions export remain under `/Users/brandomiranda/.local/share/trustworthy-theorem-judges/rating_tensor_source_archive/`. Keep the private meeting transcript out of public Git. Original source exports and user attachments remain unchanged.
- The single Claude Code Fable 5.2/max light review requested earlier was completed and its six findings addressed. Do not invent an outstanding review or automatically repeat it. Normal deterministic checks still apply.

## Takeover prompt

```text
Continue the rating-size planning and repository cleanup in /Users/brandomiranda/trustworthy-theorem-judges. Read experiments/15_estimate_required_tasks_solver_configurations_and_human_raters/ckpt.md in full, refresh the repository/shared instructions, and inspect current Git state and active owners before editing.

Brando wants a simple way to track the original 25-task × three-sample × five-rater study, the current human-rating packet, and T/A/H estimation. He still finds the repository cluttered. Complete the checkpoint's prioritized continuation: reconcile stale current summaries against experiment 09, consolidate redundant entry documents without losing unique evidence, resolve remaining ownership/layout questions coherently, and make the next collection-size decision concrete with explicit assumptions, workload and missing inputs. Preserve the paper's current project-specific home unless a coherent, authorized migration updates all consumers.

Historical T/A/H recommendations are source proposals, not requirements: Claude's last answer defers to ChatGPT's 896/4/24, Gemini proposes 135/5/6–8 with unsupported cost/exclusion assumptions, and ChatGPT's 14,848 ratings are an initial budget rather than proven sufficiency. The 544-rating idea was an unapproved Codex proposal. The current evaluation-only packet has 54 real outputs on 25 tasks and targets 108 independent ratings; re-read its current ledger because assignments and progress can change. Do not relabel missing submissions as zero ratings or evaluation data as training data.

Keep one canonical editable home for each document. Coordinate with the sole collection owner; preserve raw responses, participant edits, delivered archives, sealed splits, frozen source/experiment evidence, all funding limits and other owners' work. No new collection or paid inference is authorized by this cleanup. The first email batch remains held for Brando's trial, instruction review and explicit send approval.

Use the existing experiment 15 README for the comparison/recommendation and this ckpt.md for continuation; do not create competing summaries. Verify links, paths, manifests and affected tests, synchronize substantive knowledge to the existing Google companion, inspect the scoped staged diff, and commit/push main. Report what is finished, what remains a genuine decision, and exact paths. Ask only for information or authorization that the remaining concrete decision actually requires.

TL;DR: Finish traceable T/A/H decision support and a coherent repository cleanup using existing evidence and local/connected tools; leave verified canonical files, an updated checkpoint and a short user-facing handoff.
```

## Log

11-11-2026 22:27 PST — Rechecked all three source recommendations, recorded the current 54-file collection distinction and remaining layout work, and consolidated the previous recovery checkpoint into this user-requested ckpt.md with a takeover prompt. No source export, rating, split, generation or scientific result changed.

11-11-2026 22:30 PST — Verification passed and Google comparison/recommendation links read back; checkpoint ready for user-selected takeover.

11-11-2026 22:31 PST — Cross-linked the collection coordinator's separate handoff; both successor identities remain unassigned.

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
