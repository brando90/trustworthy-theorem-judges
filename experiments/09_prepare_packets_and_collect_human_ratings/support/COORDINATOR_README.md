# Coordinator reference: human-rating collection

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_prepare_packets_and_collect_human_ratings/support/COORDINATOR_README.md>

**TLDR:** The revised main packet is prepared and verified: 54 real candidate files across 25 tasks, with matching personal Sheets and CSVs for Brando, Rylan and Sri. It has not been dispatched; Brando's warm-up, review of the exact recipient messages and explicit send instruction remain before team delivery.

This is supporting coordinator documentation. For the actual rating task, start with [the short README](../README.md).

## Do Brando's warm-up first

[Brando's six-file warm-up packet, personal Google Sheet and instructions](BRANDO_WARMUP.md). Complete this practice set before the new main packet.

**Current form revision, 11-11-2026:** [one shared warm-up/main form](../rating_task_packet/RATING_FORM_GUIDE.md), with [combined AI-use and personal-rating attestation](FORM_AMENDMENT_11-11-2026.md), plus time, confidence, rationale and problem notes. The twelve earlier Sheets and three replacement main Sheets use the eleven-column form; the team queue remains held for his pilot and revised-text review. Dispatch agents must read the amendment before using older prepared emails or packets.

**Names first for everyone, 11-11-2026:** all personal Google Sheets, including the three replacement main forms, start with `rater_name,rater_id`. [Open every live sheet and its current raw CSV](../ratings/README.md). The earlier name-first rollout is preserved below as history. Current Sheets and CSVs use eleven columns; historical responses and removed columns remain in the source snapshots. The same name-first rule applies to future participants and CSV-only submissions.

[Name-first rollout and cross-project rule receipts](NAME_FIRST_ROLLOUT_11-11-2026.md).

[Slava's name-first CSV warm-up](SLAVA_CSV_NAME_FIRST_11-11-2026.md) is prepared and unsent; he uses the emailed CSV route. It contains six blank rows and is not collected rating data.

## Warm-up versus main-packet provenance — checked 11-11-2026

The six files rated by Rylan, Sri and Yegor are historical **Claude 3.7 Sonnet** outputs (`claude-3-7-sonnet-20250219`): two Python tasks (median and greatest common divisor), with three single-call samples per task at temperature 0.7, without a tool/compiler loop. All six current candidate files exactly match the historical experiment 100 inputs, and all six have generation receipts. The wider 75-file pool’s missing receipt concerns `binary_search__agent0`, not these warm-ups. Recent human submissions are new ratings of old candidate files, not newly generated frontier-agent outputs. Reference corrections and form revisions have their own history; they do not change the candidate-generation provenance.

Evidence: [current warm-up file hashes and path mapping](WARMUP_PATHS.json), [historical generation provenance](../../archive/01_veribench_25_tasks_3_samples_5_raters_judge_evaluation/README.md), and the original VeriBench `veribench_dataset/human_labels/calibration/generated_agents/generation_manifest.json` entries for `humaneval_47_median` and `humaneval_13__gcd`. The preserved warm-up manifest names experiment 100’s annotation-era inputs as its source.

The preserved **original main packet (set N)** contains 25 tasks × five configurations = 125 candidate files. Its final manifest (10-08-2026), under `research_artifacts/09_human_rating_collection/legacy_veribench/human_round/sample_setN/SAMPLE_MANIFEST.json`, records 25 files each for Terminus 2 with Claude Fable 5.1, GPT-6 Astra, Grok 4.7, Google’s internal frontier model, and Kimi K3. Amendment C14 identifies Terminus 2 as the harness for all five; these are not native Claude Code/Codex runs. The public composition record does not identify the Google model as Gemini 3.8, Argon or Carbon. Keep individual candidate-to-system mappings sealed. Warm-up ratings alone do not validate agreement on these frontier outputs; their main sheets remain blank in the 11-11-2026 collection snapshot.

## Why the original packet used Terminus 2 — checked 11-11-2026

**The original 125-file main packet contains no native Claude Code, native Codex or Pi outputs.** Its five configurations are frontier models running inside a shared harness; they are not five vendors' native agents. Harness choice is part of the solver configuration and limits what judge generalization this collection can demonstrate.

The recorded reason is route availability under the experiment's funding/key constraints, together with holding the harness fixed across model families. Native Claude Code + Fable 5.1 and Codex + Astra were explicitly planned in experiment 107 amendment 9, then withdrawn as `NOT_RUN`. The approved Vals route did not support those native runs, and raw provider keys were ruled out for that experiment at the time. Terminus 2 was the available shared harness used by Vals' Terminal-Bench evaluation. These are historical execution constraints, not a claim that native agents are generally unavailable today.

The decision already appears in [experiment 102 amendment C14, item 1](https://github.com/brando90/veribench/blob/main/experiments/102_rescore_vbv1_paper_fsc_with_validated_judge_rewrite_tmlr_icml/PROTOCOL_AMENDMENT_C14.md), [experiment 107's protocol, amendments 9 and 11](https://github.com/brando90/veribench/blob/main/experiments/107_vbv1_frontier_2026_agents_claude_code_fable_codex_astra_open_qwen_valkyrie/PROTOCOL.md), and especially [its paper notes, sections 2–3: harness justification and substitute-harness disclosure](https://github.com/brando90/veribench/blob/main/experiments/107_vbv1_frontier_2026_agents_claude_code_fable_codex_astra_open_qwen_valkyrie/results/PAPER_NOTES_frontier_terminus2.md#2-why-terminus-2-harness-justification). C14's old rater-count proposal is superseded by C15; this citation concerns harness composition only.

**Native and Pi artifacts exist elsewhere, but are not interchangeable with this packet:**

| Separate source | Verified inventory or run record | Why it was not part of the original packet |
| --- | --- | --- |
| VeriBench archived experiment 85, `research_archive/experiments/85_E4_vb896_agents_astra_opus5_judges_astra/` | Codex + GPT-6 Astra/xhigh: 890 nonempty local `candidate.lean` files; 896 terminal attempts, six empty | Older frozen task/source snapshot and instruction version 5; requires an explicit source/task/protocol compatibility audit before reuse |
| `vb-priv-bmg/experiments/26_local_frontier_cells_58_10-29-2026/` | Claude Code + Opus 5.5: 27 local Lean solution files | Different private-benchmark tasks and execution conditions; Fable 5.1 in this experiment is a judge, not the solver |
| `vb-priv-bmg/experiments/25_pi_qwen3coder_proxy_rerun_60_staged_10-29-2026/` | A completed 60-task Pi + Qwen3-Coder-30B-A3B-Instruct-FP8 pilot is documented | Different private tasks and a smaller proxy model; raw remote solver artifacts were not retrieved or verified in this audit |

At that historical audit stage, this targeted search did not establish a completed native Claude Code + Fable 5.1 pool suitable for set N. Coordinator/reviewer model activity is not evidence of a benchmark solver run.

**No matched VeriBench comparison establishes Terminus 2 as the best harness.** The existing paper disclosure explicitly calls it a standardized substitute. The separate runs above vary in tasks, model versions or conditions and cannot isolate harness quality. Keep the current packet intact; if native-agent or Pi generalization is a goal, prepare a separately versioned extension with explicit model/harness versions, task/source alignment and comparable budgets. That was the recommendation at the audit stage; the subsequent user decision authorized the completed versioned preparation below.

## Native-heavy replacement — user decision, 11-11-2026

**Prepared and verified, not dispatched.** Brando decided to make native agents the primary real packet, include Pi attempts, and retain fewer Terminus 2 artifacts. The final packet contains 54 returned files across the same 25 Python tasks; all 85 planned cells remain in the availability ledger, including 31 missing submissions. This replaces the original all-Terminus-2 main packet as the delivery default. The six-file warm-up, scoring rubric, eleven-column form, raw responses and delivered archives remain unchanged; the original 125-file packet is preserved.

The original allocation planned **85 artifacts and 170 independent ratings**. After all 50 new attempts ended, the actual human-rating target is **54 artifacts × two distinct qualified raters = 108 ratings**, plus Brando's 54 additional ratings. Eight independent slots are assigned and blank (four each for Rylan and Sri); 100 remain unassigned. This is workload arithmetic, not statistical sufficiency. T=25 task identities and A=4 attempted configurations, with a sparse set of 54 returned artifacts from three configurations. H is the number of distinct people in the panel, still assignment-dependent, rather than two fixed humans for every artifact.

| Configuration | Planned cells | Verified returned files | Final artifact-availability state, 11-11-2026 |
| --- | ---: | ---: | --- |
| Native Codex + GPT-6 Astra/xhigh | 25 | 25 | Historical candidates found for all 25 tasks; all Python hashes match |
| Native Claude Code + Claude Fable 5.1/max | 25 | 19 | All 25 attempts terminal; six no-file response-cap outcomes; native Claude Code 2.1.322 |
| Pi + Google Gemini 3.8 Flash/high | 25 | 0 | All 25 attempts terminal; no captured required-path submissions; native Pi 1.5.2 |
| Terminus 2 + Grok 4.7/xhigh | 10 | 10 | Subset of existing files of record, selected without outcomes |

**Final availability:** 54 real nonempty files plus 31 missing submissions account for all 85 planned cells; none are pending. Claude Code returned 13 files from native completions and six retained at execution limits (one wall-clock, two observed-output-token and three observed-total-token stops), with six no-file response-cap outcomes. Its source/model/hash audit and lexical screen of 221 visible tool calls passed. Pi ended 15 attempts without a recorded infrastructure issue, eight with external service issues and two with a host-supervision incident; these categories describe execution, not correctness. All 25 Pi sessions received the frozen instructions and matching capture paths. No required-path submission was captured; temporary Lean code elsewhere is not ruled out because full workspace snapshots were not retained. Missing files receive no fabricated human scores.

**Verified packets and forms:** Brando has 54 files/25 tasks; Rylan and Sri each have four files/their original two tasks. Each personal assembly receipt records `BUILT_SHEET_MATCHED_NOT_SENT`, `release_ready: true` and exact equality with its live Google Sheet. The independent archive audit verified all scientific bytes, manifests and stable item paths, with no detected identity/credential patterns or same-task byte duplicates. Missing item numbers are intentional: filtering missing submissions did not renumber the frozen 85-cell plan. [Open Brando's promoted main packet](../rating_task_packet/main_rating_task/START_HERE.md); [current CSV](../rating_task_packet/main_rating_task/ratings.csv). The three named `native_main` snapshots in [ratings/](../ratings/README.md) remain blank.

**Evidence:** under `research_artifacts/09_human_rating_collection/preparation_11-09-2026/native_harness_packet_11-11-2026/`, `finalization/RATABLE_COHORT.json` (SHA-256 `8463f6c846839c78fccf8102f3672ff94a20562dba7871b13d81e8cca693de22`) binds the 54-file subset; `finalization/EXCLUSIONS.json` (SHA-256 `a14cfa52ead4917f5a24b88672d05f3a38b490ce39a8c5c217729891b3d024e5`) preserves all 31 missing cells. `RETURNED_ARTIFACT_SCREEN.json` holds the independent final audit; `builds/native_heavy_terminal_v1/{A1,T01,T05}/ASSEMBLY_RECEIPT.json` holds personal packet/Sheet checks. These are inventory counts, not judge-validation results; no statistical inference or human-agreement test was run.

Pi made **670 generation requests**, including generation retries; Google `countTokens` preflights are separate HTTP calls. Its conservative total is **$11.63091975**, including the excluded setup pilot, below the **$20** ceiling: $9.69398325 completed-usage upper bound + $1.216512 unresolved reservations + $0.7204245 excluded pilot. This is conservative accounting, not an invoice. Sources: `PI_FINAL_EXECUTION_AUDIT.json` and `claude_code_readiness/CC_VALID_V2_FINAL_SUMMARY.json` under the same private root.

**Reuse audit:** the native Codex candidates are from archived VeriBench experiment 85 (Codex 0.154.0, instruction version 5, 1,800-second allowance). Twenty current corrected gold files differ from historical gold: collect new human ratings against current accepted gold, without transferring historical machine scores. The separate Claude Code/Opus 5.5 private pool (27 outputs) and Pi/Qwen3-Coder-30B private pool (60 task records) have zero exact Python matches. These scoped searches found no reusable intended Claude Code/Fable or Pi/Gemini outputs, without establishing global absence. Private source hashes and joins are in `research_artifacts/09_human_rating_collection/preparation_11-09-2026/native_harness_audit_11-11-2026/`.

**Execution and collection contract:**

1. Keep the 25 Python files and accepted 10-12-2026 gold fixed. New generation uses source-derived version-8 instructions from VeriBench commit `e7452de7a06e0d3d8b9440be2ec4f73e32d45299`, fixing version 7's invalid namespace hints without changing Python. Preserve both instruction versions and hashes. This explicitly extends a historical packet; it is not a latest-public-release run.
2. Solvers receive only their task's source/instructions and Lean 4.22.0/Mathlib environment, without gold, other candidates, human ratings or host repositories. Pin native client/image/model/effort. Native Claude Code runs with two CPUs, an 8 GB memory limit and dropped Linux capabilities; Pi uses the clean image without those resource restrictions. Input placement also differs by native client. These execution differences are retained in the manifests. New cells have one attempt, a 1,800-second allowance, and at most 40 native Claude Code turns or 40 Pi generation requests (including generation retries; separate Google `countTokens` preflights are not counted); retain failures and partial outputs. Record final token/funding caps in the execution manifest before admission.
3. Native Claude Code uses an existing subscription; observed native rate-limit events report no overage use and reject overage. No new charges are enabled. Pi uses Allen's existing VeriBench-authorized Google route, with an externally enforced $0.75 per valid task ceiling: at most $18.75 for 25 valid attempts, plus the excluded setup pilot's measured $0.7204245, below the original $20 total ceiling. Reserve the full permitted input cost plus maximum output cost before each request; incomplete usage accounting prevents another admission. Pi permits at most 65,536 input tokens and 16,384 output tokens per request. Claude Code permits at most 16,384 output tokens per response and stops after observing 1,000,000 cumulative tokens or 131,072 output tokens; those observed limits can overshoot by one response, independently of the hard time/turn limits. These are ceilings, not measured costs or permission for new charges. No new model judging is needed for packet preparation.
4. Select ten Grok tasks by sorting SHA-256 of `native-heavy-11-11-2026|<task_id>` across the 25 tasks and taking the first ten. Copy existing files of record byte-for-byte and retain isolation flags. Do not select on scores. Keep model-to-candidate mappings private; use neutral shuffled labels in the packet.
5. Preserve evaluation-only use and task-family/exposure history; these tasks do not become training data for methods 2 versus 4. Report agreement by configuration and pooled. Ten Terminus 2 artifacts support an exploratory comparison. Historical and new generation conditions differ, so this does not isolate a causal harness effect or establish transfer to every future agent.
6. Reconcile output/failure receipts before building a versioned replacement. Preserve all 85 planned cells in the availability ledger. Only real returned artifacts enter human packets; missing submissions remain explicit failures with their cause and are never replaced by fabricated files or human scores. Freeze any smaller ratable subset only after all planned attempts finish, retaining original neutral item IDs and display paths, and update sheet/packet counts together. Keep the common form, names first and blank response fields. Reconcile Rylan/Sri assignments by task identity without rewriting old responses. Update current sheet/CSV/packet links together while preserving historical sheets/snapshots. Revised exact team email text remains for Brando's review before sending.

**Preserved execution history, 11-11-2026:** the first six valid Pi attempts are retained without reruns: one request-cap failure and five infrastructure interruptions. For untouched cells, the gateway permits at most two HTTP 503 retries (5- and 15-second backoff), counting every request and reserving uncertain cost within the original ceilings. From the fifth cell onward, the response timeout is 600 seconds within the unchanged 1,800-second task limit. Timeouts are not retried. Exact per-cell versions are bound in the private condition lineage. After repeated HTTP 503 responses, new Pi admissions pause for a 30-minute cooldown, followed by one untouched task and reassessment. That seventh attempt had 39 provider requests with no external service error, reached the original 1,800-second wall limit and returned no candidate; its unfinished request retains a full cost reservation. Two of the remaining eighteen tasks started under a central two-worker Pi scheduler. A coordinator handoff then ended their host wrappers while the Docker conversations continued. A separate observer enforced both original deadlines, recovered gateway accounting and preserved the native sessions; both attempts ended at their original 40-request cap without a file. Their receipts explicitly retain this supervision incident and the incomplete host-trajectory caveat. The sixteen then-untouched tasks continued through one detached scheduler with at most four workers, independent process sessions/gateways, a shared cost ledger and CPU/memory/pressure admission checks. Per-cell conditions and caps are unchanged; no conversation was restarted and terminal attempts are not repeated. Claude Code used at most two concurrent cells from the third admission onward, then increased to four for the 17 untouched tasks after six terminal attempts and two active cells; both active clocks and every per-cell limit were preserved. Available memory and subscription allowance governed new starts. The shared Docker virtual machine has approximately 7.75 GiB memory, so execution-resource contention is an additional recorded difference. These operational amendments do not turn missing outputs into solver-quality scores.

The ten Grok baseline files have been staged and hash-verified: nine original isolation checks passed and one retained its historical flag (an unrelated provider endpoint was reachable with HTTP 401; no key or gold reference was present). The selection was fixed before metadata lookup.

**Environment correction, 11-11-2026:** the initial image accidentally included compiled benchmark modules in the project build cache, and the initial Pi process had incorrect filesystem ownership. Both first attempts are excluded as invalid setup pilots; no output from them enters the packet. The replacement immutable image `sha256:2104a4b8fe86379143a49331d79c9eecae67ab58ef73d4db05183510061bc89e` passed all 16 independent environment checks: no project source/build artifacts beyond official dependencies, an empty candidate directory, and successful nonroot Mathlib compilation without network access. Fresh valid batches use separate output roots and preserve all original receipts. Pi transport handling was amended prospectively after two service failures: at most two retries of a pre-response HTTP 503, with 5- and 15-second backoff; every retry consumes the original call, time and cost allowance, and failed reservations remain charged conservatively. Previously attempted cells are not rerun. Infrastructure exclusions and solver-budget failures are distinguished in the final availability ledger. These are environment checks, not evidence of solver correctness.

The three replacement main Sheets now contain the final blank forms: Brando 54 items, Rylan four and Sri four, preserving the latter two participants' original task identities. Exact live-Sheet/packet equality passed after filtering the missing submissions; earlier 85/eight/six-row forms survive in preparation history. Rylan and Sri retain verified personal editor access without notifications. The current primary target is 108 independent ratings: eight assigned and blank, 100 unassigned; Brando's 54 are additional. No replacement packet has been dispatched.

The two related agents received the decision as an FYI and were told to continue their tasks. Execution state is in [the collection checkpoint](CKPT_human_rating_collection.md); source manifests and run receipts live under `research_artifacts/09_human_rating_collection/preparation_11-09-2026/native_harness_packet_11-11-2026/`.

## Historical collection size and readiness — original packet, 11-11-2026

**Historical inventory below:** this subsection records the original 125-item packet. The active replacement is the native-heavy plan above.

**The main candidate inventory is complete:** 125 nonempty Lean files, five in each of 25 task folders. All 125 match their recorded candidate hashes. The manifest records 25 files and zero missing for each of the five configurations above. The current FormV5 full archive contains exactly those 125 candidates; Rylan’s and Sri’s ten-file archives contain the corresponding unchanged subsets. Their archive hashes also match the prepared manifest. The original generation handoff retains four isolation-flagged outputs; completeness does not erase those flags or establish judge validity.

**The prepared references match the corrected release:** Brando’s 25/25, Rylan’s 2/2 and Sri’s 2/2 match the pinned accepted references. `support/scripts/legacy/packet_release.py::require_release('setN')` passes the release status, acceptance-record digest and every released file checksum. Use the pinned `research_artifacts/09_human_rating_collection/upstream_source/` release, accepted on 10-12-2026; the old `legacy_veribench/.../sample_setN/packet/FILES.sha256` predates those reference corrections and is not the current reference-release authority. No candidate or reference was changed by this inventory check.

The original authorized target was **25 tasks × five solver configurations × two independent ratings per artifact = 250 main ratings**. [Amendment C15](https://github.com/brando90/veribench/blob/main/experiments/102_rescore_vbv1_paper_fsc_with_validated_judge_rewrite_tmlr_icml/PROTOCOL_AMENDMENT_C15.md) explicitly supersedes C14’s earlier three-rating proposal. Brando’s optional 125 ratings are additional, not replacements for either independent rating. At the latest collection snapshot, Rylan and Sri have ten assigned items each, all blank: 20 assigned ratings and 230 still unassigned, with zero completed main ratings. The [main collection overview](../README.md#ratings-and-completion) owns the current named status.

For tensor notation, **T** is task identities, **A** is fixed solver configurations, and **H** is the number of distinct people in the panel. Let **m** be ratings per artifact. The original design had T=25, A=5 and m=2; H is not yet fully assigned. The identity-indexed tensor is sparse, with 250 planned observed cells, because different artifacts may be assigned to different pairs of people. Calling it “25 × 5 × 2” is convenient workload arithmetic, but its last axis is two rating slots, not necessarily the same two humans throughout.

| Scope | Tasks and solver configurations | People and ratings per artifact | Rating count / status |
| --- | --- | --- | --- |
| Original frontier evaluation round | 25 tasks × five configurations; all 125 outputs present | Panel assignment unfinished; two independent ratings per artifact | 250 target; zero completed in the latest snapshot |
| Proposed training-only pilot | 32 eligible tasks × four frozen configurations; 128 artifacts | Eight development raters; three ratings normally, eight on 32 artifacts | 544 proposed; not an approved collection amendment |
| Historical full-study budget | Pinned VeriBench 1.3: 896 task identities × four configurations, plus 512 separate development generation records | Eight development and sixteen audit raters; three base ratings, eight on 512 audit artifacts | 14,848 planned; statistical sufficiency not established |

**Original recommendation, superseded by the native-heavy replacement above:** complete the existing 250-rating frontier evaluation round. Keep the [larger sizing proposals](../../15_estimate_required_tasks_solver_configurations_and_human_raters/README.md#optional-codex-pilot-proposal) separate: the current 25-task packet is not a census of the benchmark and is evaluation-only for the new objective comparison. The proposed training pilot needs eligible identities and a resolved train/validation/test split amendment; it cannot silently reuse these evaluation ratings. Final study size remains conditional on measured variability, workload and a declared precision target. The prospective four-configuration manifest is not implemented merely because this five-configuration packet exists.

Before team dispatch, finish Brando’s pilot and obtain approval of the current exact messages plus an explicit send instruction. Existing assignments can then proceed while the remaining qualified-rater assignments are filled. Candidate generation was complete for that original all-Terminus-2 packet; the native-heavy replacement above has now reconciled all 50 new attempts and retained its 54 real files.

## Open the collected ratings

**Start here: [raw ratings by person — actual CSV files and Google Sheets](../ratings/README.md).**

**Raw-data restoration, 11-11-2026:** removed assistant-filled time estimates and background annotations. Current files in [ratings/](../ratings/README.md) preserve exact response values, blanks, spelling, capitalization and all N/A rows. [What was removed and verified](RAW_DATA_RESTORATION_11-11-2026.md). Historical normalized imports are separate in [ratings/analysis/](../ratings/analysis).

[How your Google Sheet becomes a named rating file, and why IDs are retained](IDENTITY_AND_IMPORT.md).

- [Actual rating CSV files](../ratings).
- [Current completion status: who is done and what is missing](../README.md#ratings-and-completion), checked **11-11-2026**.
- [Original import receipts](../../../research_artifacts/09_human_rating_collection/legacy_veribench/human_round/private_ratings_setN).

Collected files are in `ratings/`; named data links and completion status share the experiment README. The CSV filenames and first column show each person's name; the original IDs, ratings and notes are preserved. These raw tables contain the same participant submissions, including nonnumeric entries omitted by historical numeric-only imports. They are not additional observations. The rating files and collection README are tracked in Git, as requested on 11-11-2026.

## Ownership and scope

**Sole coordinating chat:** [Prepare human grading task](codex://threads/01a1a8f9-dcb7-7381-9368-91d6e51faffd). Read the [11-09-2026 coordination record](COORDINATION_11-09-2026.md) before collection, dispatch or practical judge-development work. It consolidates the former Best human-rating judge chat without dropping its evaluator or unfinished methods 2 and 4 work.

Brando moved this task from VeriBench on **11-09-2026**. Maintain the collection instructions, packet preparation, approved email, assignment tracking, delivery receipts and collection status here. VeriBench V1's separate direction is formal specification coverage checked by a prover, with artificial intelligence guiding proof search; this move does not change that scorer.

The [prospective probabilistic-judge design](../../02_design_a_judge_that_predicts_human_ratings_0_to_5_start_06Nov2026/README.md) remains the methodology for a new collection. The inherited **set N** (the previously prepared frontier-output rating round) has its own fixed materials, assignment rules and exposure history. Moving it does not turn its outputs or ratings into the prospective study's fresh training, validation or test data.

**Required reading for every collection/dispatch agent:** [judge formulations 2 and 4](JUDGE_FORMULATIONS_11-09-2026.md), with the original photos and transcriptions. Formulation 2 develops a judge using training correlation; formulation 4 uses a proper probabilistic training loss. Preserve individual ratings so both can be studied; validation-based selection (1 versus 3) is a distinct intervention. This note does not change participant instructions or dispatch authorization.

## Current delivery status — prepared, not dispatched, 11-11-2026

**Later user clarification:** Brando grades some items first, then reviews the actual participant instructions. The first batch is Sri, Yegor and Brando only; Rylan and all other recipients stay held. Yegor’s main packet, assignment and exact email still need preparation. Preserve his existing extra-only status. The eight-person queue below is historical preparation, not the new first-batch queue; consult CURRENT_PREPARATION.json before any dispatch.

The replacement main bundles and matching Sheets are ready for review, with all response fields blank. The preferred finish remains 11-13-2026 and final deadline 11-15-2026. Brando completes his warm-up first; the coordinator then uses the revised recipient-specific messages and waits for his explicit send instruction. No collaborator dispatch is authorized merely by `release_ready: true`.

Use the native-main review and queue under `research_artifacts/09_human_rating_collection/preparation_11-09-2026/`: `REVIEW_TEAM_EMAILS_NATIVE_MAIN_V1.md` and `DISPATCH_QUEUE_NATIVE_MAIN_V1.json`. Older original-main drafts remain historical; the current FormV6 warm-ups keep their own recipient-specific records. The remaining collection work is 108 independent main ratings, including assignment of 100 slots to qualified raters, plus Brando's optional 54. No main scores have been collected in this revision.

## Historical delivery preparation — 11-09-2026

**The following is the preserved original-packet preparation record, superseded for main delivery by the native-heavy replacement above.** See the [current preparation record](PREPARATION_11-09-2026.md) for the schedule; do not send an older 125-item main draft as the replacement.

- The preparation record states a preferred finish of **11-13-2026** and final deadline of **11-15-2026**, superseding the historical 11-06-2026 date without rewriting delivered archives.
- The original approved email names the coordinator's personal sheet and full assignment. The new individual drafts propose the necessary recipient-specific changes; their text approval and dispatch are still separate from this migration.
- Existing participant records, assignments, returned sheets and delivery receipts moved without changing their contents. New roster decisions and dispatch preparation are recorded separately under `research_artifacts/09_human_rating_collection/preparation_11-09-2026/`; use that active preparation record instead of treating the imported historical roster as current.
- The renamed packet has **25 task folders and 125 candidate files**. The team builder creates a separate blank answer sheet while preserving candidate, Python and reference bytes. A successful archive build does not establish recipient-specific delivery readiness.
- All seven recipient sheet-permission checks are complete; the eighth return route is private CSV by email. The private review freezes eight exact recipient messages and original attachment hashes. Team text/send approval and human completion remain outstanding; access verification did not inspect sealed ratings or establish completion.

## Files

```text
09_prepare_packets_and_collect_human_ratings/
├── README.md              # Task links, people and completion status
├── rating_task_packet/    # Editable task and participant files
├── ratings/               # Collected responses and live-sheet links
└── support/               # Records, scripts and tests
```

### Private materials

This repository is public. The following coordinator paths are ignored, not publication destinations:

| Material | Coordinator path, relative to this repository |
| --- | --- |
| Original renamed delivery, unchanged | `research_artifacts/original/` |
| Existing team archives, unchanged | `research_artifacts/team-folder-01.zip`, `research_artifacts/team-all-folders.zip` |
| Frozen local coordination documents, packets and sealed materials | `research_artifacts/09_human_rating_collection/legacy_veribench/human_round/` |
| Pinned committed source, packet-release records and private sheet bindings | `research_artifacts/09_human_rating_collection/upstream_source/` |
| Active preparation, roster, individual drafts and dispatch queue | `research_artifacts/09_human_rating_collection/preparation_11-09-2026/` |
| Imported participant records, assignments, submitted sheets and delivery receipts | `research_artifacts/09_human_rating_collection/legacy_veribench/human_round/private_ratings_setN/` |
| Coordinator's original delivery and personal records | `research_artifacts/09_human_rating_collection/legacy_veribench/human_round/private_A1/` |
| Exact approved email | `research_artifacts/09_human_rating_collection/legacy_veribench/human_round/RATER_TASK_EMAIL_LOCKED_11-04-2026.md` |
| Complete file-by-file transfer hashes | `research_artifacts/09_human_rating_collection/migration_receipt.json` |

The imported `PLAN_setN_rating_round.md` records dated decisions, not the current schedule. Follow [PREPARATION_11-09-2026.md](PREPARATION_11-09-2026.md) for the newer schedule and preparation; preserve the original email's approval history and the localized-assistance wording. Keep delivered archives unchanged; any later approved delivery is a new version with a new receipt. Named collected ratings and completion records are authorized for Git tracking in this experiment; private correspondence, consent and sealed data remain outside public Git.

## Historical packet builder

This builder reproduces the original all-Terminus-2 packet, not the current native-heavy replacement. The active replacement uses `support/scripts/native_packet_generation/build_packet.py` after final reconciliation; exact commands are in the private preparation checkpoint.

For an explicitly requested historical build, run from `~/trustworthy-theorem-judges`:

```sh
python3 experiments/09_prepare_packets_and_collect_human_ratings/support/scripts/make_team_packet.py \
  research_artifacts/original research_artifacts/team-folder-01-new.zip --folders 1 --rater T01
```

Use a new output filename and the intended person's verified rater ID (`T01` is Rylan Schaeffer); omit `--folders` for all folders. Omitting `--rater` creates an unassigned template, not a recipient-ready form. The builder checks the original delivery manifest and every included file, preserves the scoring rubric apart from its personal-sheet instruction, and includes `START_HERE.md`, `Rating_Instructions.md`, `ratings.csv` and `FILES.sha256`. It does not send anything or modify a delivered packet.

**Keep the sheet layouts distinct.** This builder's renamed `agent_file*.lean` items are not the inherited `Nxx`/`Wxx` item identifiers. The utilities under `support/scripts/legacy/` serve the inherited sheets only; do not pass a renamed team answer sheet to that importer or infer its item mapping. Preserve explicit item mappings when reconciling later deliveries.

## Current inherited utilities

The local VeriBench checkout was older than its remote branch. The active utilities therefore retain the committed implementation at `b292c277e176`, while the original local files remain separately preserved. Their inputs come from the matching pinned tree under `research_artifacts/09_human_rating_collection/upstream_source/experiments/102_rescore_vbv1_paper_fsc_with_validated_judge_rewrite_tmlr_icml/`; `upstream_source/SOURCE_RECEIPT.json` records its revision and hashes. Its private working-directory links resolve to the single imported participant-record store, not duplicate records.

- Assignment retains `--keep` for already-delivered folders; the assignment utility requires NumPy.
- Import retains emailed comma-separated value (CSV) submissions, delivery-route and personal-sheet checks, coordinator-only `--all-folders`, and reference-issue handling. Coordinator sheet identifiers live only in private configuration.
- Warm-up qualification retains amendment C17: the first task (`W01`) determines qualification; the six-file result is a sensitivity, not the qualification verdict. Sealed-key verification, leave-one-expert-out targets, and explicitly permitted missing nonqualifying items remain intact.
- `packet_release.py` verifies release status, packet hashes and the existing reference-acceptance record before packet building or warm-up scoring. Relocation does not grant release approval.
- The inherited recipient builder now refuses to overwrite an existing archive. Use a new output directory for a new delivery; its filename and receipt keep the inherited format.

## Migration and historical consumers

[The public transfer receipt](MIGRATION.json) distinguishes the local snapshot revision from the active utility revision and records utility hashes and verification. The complete private inventory preserves **1,290 files** byte-for-byte, including local coordination changes that were not yet committed in VeriBench. No candidate, reference, rating, score or assignment was changed by relocation.

- The four collection utilities and their packet-release helper now run here; VeriBench's former command paths redirect to these implementations.
- VeriBench's tracked historical packet snapshots and analysis code remain in place because the simulated-rater, judge-transfer and Certification Judge analyses still consume them. They are not a second active collection workflow.
- The two former ignored private working directories in VeriBench are compatibility links to the new private store, not duplicate copies. The collection owner maintains those links until the inherited analysis consumers are updated; remove them only after checking those consumers. The exact paths are in the private migration receipt.
- Prospective generation and the old paper rescoring are not moved or resumed. No sealed rating analysis, model inference or proof search is part of this migration.

## Verification

```sh
python3 -m unittest discover -s experiments/09_prepare_packets_and_collect_human_ratings/support/tests -v
python3 scripts/check_project.py
git diff --check
```

The tests use synthetic packets and submissions, including the current assignment, import, release and qualification rules. When the coordinator's original packet is available, they also verify a real archive build without submitting ratings. Both pinned packet releases and the sealed-key digest were checked separately without scoring real raters. The migration preserves the inherited qualification and assignment algorithms; it does not validate their suitability for the prospective study.
