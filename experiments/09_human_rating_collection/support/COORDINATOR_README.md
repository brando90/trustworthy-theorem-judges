# Coordinator reference: human-rating collection

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_human_rating_collection/support/COORDINATOR_README.md>

**TLDR:** This is the active home for preparing and collecting human ratings of formal specification coverage, with inherited packets and collection records preserved. The current preparation record supplies revised deadlines and individual drafts; collaborator dispatch still requires review of the recipient-specific text and an explicit send instruction.

This is supporting coordinator documentation. For the actual rating task, start with [the short README](../README.md).

## Do Brando's warm-up first

[Brando's six-file warm-up packet, personal Google Sheet and instructions](BRANDO_WARMUP.md). Complete this practice set before the full 125-file packet.

**Current form revision, 11-11-2026:** [one shared warm-up/main form](../rating_task_packet/RATING_FORM_GUIDE.md), with [combined AI-use and personal-rating attestation](FORM_AMENDMENT_11-11-2026.md), plus time, confidence, rationale and problem notes. All twelve live sheets use the current eleven-column form; the team queue remains held for his pilot and revised-text review. Dispatch agents must read the amendment before using older prepared emails or packets.

**Names first for everyone, 11-11-2026:** all 12 active personal Google Sheets now start with `rater_name,rater_id`, including unanswered forms. [Open every live sheet and its current raw CSV](../ratings/README.md). The earlier name-first rollout is preserved below as history. Current Sheets and CSVs use eleven columns; historical responses and removed columns remain in the source snapshots. The same name-first rule applies to future participants and CSV-only submissions.

[Name-first rollout and cross-project rule receipts](NAME_FIRST_ROLLOUT_11-11-2026.md).

[Slava's name-first CSV warm-up](SLAVA_CSV_NAME_FIRST_11-11-2026.md) is prepared and unsent; he uses the emailed CSV route. It contains six blank rows and is not collected rating data.

## Warm-up versus main-packet provenance — checked 11-11-2026

The six files rated by Rylan, Sri and Yegor are historical **Claude 3.7 Sonnet** outputs (`claude-3-7-sonnet-20250219`): two Python tasks (median and greatest common divisor), with three single-call samples per task at temperature 0.7, without a tool/compiler loop. All six current candidate files exactly match the historical experiment 100 inputs, and all six have generation receipts. The wider 75-file pool’s missing receipt concerns `binary_search__agent0`, not these warm-ups. Recent human submissions are new ratings of old candidate files, not newly generated frontier-agent outputs. Reference corrections and form revisions have their own history; they do not change the candidate-generation provenance.

Evidence: [current warm-up file hashes and path mapping](WARMUP_PATHS.json), [historical generation provenance](../../archive/01_veribench_25_tasks_3_samples_5_raters_judge_evaluation/README.md), and the original VeriBench `veribench_dataset/human_labels/calibration/generated_agents/generation_manifest.json` entries for `humaneval_47_median` and `humaneval_13__gcd`. The preserved warm-up manifest names experiment 100’s annotation-era inputs as its source.

The separate **main packet (set N)** contains 25 tasks × five configurations = 125 candidate files. Its final manifest (10-08-2026), under `private/09_human_rating_collection/legacy_veribench/human_round/sample_setN/SAMPLE_MANIFEST.json`, records 25 files each for Terminus 2 with Claude Fable 5.1, GPT-6 Astra, Grok 4.7, Google’s internal frontier model, and Kimi K3. Amendment C14 identifies Terminus 2 as the harness for all five; these are not native Claude Code/Codex runs. The public composition record does not identify the Google model as Gemini 3.8, Argon or Carbon. Keep individual candidate-to-system mappings sealed. Warm-up ratings alone do not validate agreement on these frontier outputs; their main sheets remain blank in the 11-11-2026 collection snapshot.

## Why this packet uses Terminus 2 — checked 11-11-2026

**The current 125-file main packet contains no native Claude Code, native Codex or Pi outputs.** Its five configurations are frontier models running inside a shared harness; they are not five vendors' native agents. Harness choice is part of the solver configuration and limits what judge generalization this collection can demonstrate.

The recorded reason is route availability under the experiment's funding/key constraints, together with holding the harness fixed across model families. Native Claude Code + Fable 5.1 and Codex + Astra were explicitly planned in experiment 107 amendment 9, then withdrawn as `NOT_RUN`. The approved Vals route did not support those native runs, and raw provider keys were ruled out for that experiment at the time. Terminus 2 was the available shared harness used by Vals' Terminal-Bench evaluation. These are historical execution constraints, not a claim that native agents are generally unavailable today.

The decision already appears in [experiment 102 amendment C14, item 1](https://github.com/brando90/veribench/blob/main/experiments/102_rescore_vbv1_paper_fsc_with_validated_judge_rewrite_tmlr_icml/PROTOCOL_AMENDMENT_C14.md), [experiment 107's protocol, amendments 9 and 11](https://github.com/brando90/veribench/blob/main/experiments/107_vbv1_frontier_2026_agents_claude_code_fable_codex_astra_open_qwen_valkyrie/PROTOCOL.md), and especially [its paper notes, sections 2–3: harness justification and substitute-harness disclosure](https://github.com/brando90/veribench/blob/main/experiments/107_vbv1_frontier_2026_agents_claude_code_fable_codex_astra_open_qwen_valkyrie/results/PAPER_NOTES_frontier_terminus2.md#2-why-terminus-2-harness-justification). C14's old rater-count proposal is superseded by C15; this citation concerns harness composition only.

**Native and Pi artifacts exist elsewhere, but are not interchangeable with this packet:**

| Separate source | Verified inventory or run record | Why it is not part of the current packet |
| --- | --- | --- |
| VeriBench archived experiment 85, `research_archive/experiments/85_E4_vb896_agents_astra_opus5_judges_astra/` | Codex + GPT-6 Astra/xhigh: 890 nonempty local `candidate.lean` files; 896 terminal attempts, six empty | Older frozen task/source snapshot and instruction version 5; requires an explicit source/task/protocol compatibility audit before reuse |
| `vb-priv-bmg/experiments/26_local_frontier_cells_58_10-29-2026/` | Claude Code + Opus 5.5: 27 local Lean solution files | Different private-benchmark tasks and execution conditions; Fable 5.1 in this experiment is a judge, not the solver |
| `vb-priv-bmg/experiments/25_pi_qwen3coder_proxy_rerun_60_staged_10-29-2026/` | A completed 60-task Pi + Qwen3-Coder-30B-A3B-Instruct-FP8 pilot is documented | Different private tasks and a smaller proxy model; raw remote solver artifacts were not retrieved or verified in this audit |

This targeted search did not establish a completed native Claude Code + Fable 5.1 pool suitable for set N. Coordinator/reviewer model activity is not evidence of a benchmark solver run.

**No matched VeriBench comparison establishes Terminus 2 as the best harness.** The existing paper disclosure explicitly calls it a standardized substitute. The separate runs above vary in tasks, model versions or conditions and cannot isolate harness quality. Keep the current packet intact; if native-agent or Pi generalization is a goal, prepare a separately versioned extension with explicit model/harness versions, task/source alignment and comparable budgets. Such an extension is a recommendation, not an authorized generation run or a revision to the frozen collection.

## Current collection size and readiness — checked 11-11-2026

**The main candidate inventory is complete:** 125 nonempty Lean files, five in each of 25 task folders. All 125 match their recorded candidate hashes. The manifest records 25 files and zero missing for each of the five configurations above. The current FormV5 full archive contains exactly those 125 candidates; Rylan’s and Sri’s ten-file archives contain the corresponding unchanged subsets. Their archive hashes also match the prepared manifest. The original generation handoff retains four isolation-flagged outputs; completeness does not erase those flags or establish judge validity.

**The prepared references match the corrected release:** Brando’s 25/25, Rylan’s 2/2 and Sri’s 2/2 match the pinned accepted references. `support/scripts/legacy/packet_release.py::require_release('setN')` passes the release status, acceptance-record digest and every released file checksum. Use the pinned `private/09_human_rating_collection/upstream_source/` release, accepted on 10-12-2026; the old `legacy_veribench/.../sample_setN/packet/FILES.sha256` predates those reference corrections and is not the current reference-release authority. No candidate or reference was changed by this inventory check.

The current authorized target is **25 tasks × five solver configurations × two independent ratings per artifact = 250 main ratings**. [Amendment C15](https://github.com/brando90/veribench/blob/main/experiments/102_rescore_vbv1_paper_fsc_with_validated_judge_rewrite_tmlr_icml/PROTOCOL_AMENDMENT_C15.md) explicitly supersedes C14’s earlier three-rating proposal. Brando’s optional 125 ratings are additional, not replacements for either independent rating. At the latest collection snapshot, Rylan and Sri have ten assigned items each, all blank: 20 assigned ratings and 230 still unassigned, with zero completed main ratings. The [main collection overview](../README.md#ratings-and-completion) owns the current named status.

For tensor notation, **T** is task identities, **A** is fixed solver configurations, and **H** is the number of distinct people in the panel. Let **m** be ratings per artifact. The current design has T=25, A=5 and m=2; H is not yet fully assigned. The identity-indexed tensor is sparse, with 250 planned observed cells, because different artifacts may be assigned to different pairs of people. Calling it “25 × 5 × 2” is convenient workload arithmetic, but its last axis is two rating slots, not necessarily the same two humans throughout.

| Scope | Tasks and solver configurations | People and ratings per artifact | Rating count / status |
| --- | --- | --- | --- |
| Current frontier evaluation round | 25 tasks × five configurations; all 125 outputs present | Panel assignment unfinished; two independent ratings per artifact | 250 target; zero completed in the latest snapshot |
| Proposed training-only pilot | 32 eligible tasks × four frozen configurations; 128 artifacts | Eight development raters; three ratings normally, eight on 32 artifacts | 544 proposed; not an approved collection amendment |
| Historical full-study budget | Pinned VeriBench 1.3: 896 task identities × four configurations, plus 512 separate development generation records | Eight development and sixteen audit raters; three base ratings, eight on 512 audit artifacts | 14,848 planned; statistical sufficiency not established |

**Recommendation:** complete the existing 250-rating frontier evaluation round. Keep the [larger sizing proposals](../../15_rating_tensor_size_estimation/README.md#optional-codex-pilot-proposal) separate: the current 25-task packet is not a census of the benchmark and is evaluation-only for the new objective comparison. The proposed training pilot needs eligible identities and a resolved train/validation/test split amendment; it cannot silently reuse these evaluation ratings. Final study size remains conditional on measured variability, workload and a declared precision target. The prospective four-configuration manifest is not implemented merely because this five-configuration packet exists.

Before team dispatch, finish Brando’s pilot and obtain approval of the current exact messages plus an explicit send instruction. Existing assignments can then proceed while the remaining qualified-rater assignments are filled. Candidate generation is not the missing preparation step for this 25-task round.

## Open the collected ratings

**Start here: [raw ratings by person — actual CSV files and Google Sheets](../ratings/README.md).**

**Raw-data restoration, 11-11-2026:** removed assistant-filled time estimates and background annotations. Current files in [ratings/](../ratings/README.md) preserve exact response values, blanks, spelling, capitalization and all N/A rows. [What was removed and verified](RAW_DATA_RESTORATION_11-11-2026.md). Historical normalized imports are separate in [ratings/analysis/](../ratings/analysis).

[How your Google Sheet becomes a named rating file, and why IDs are retained](IDENTITY_AND_IMPORT.md).

- [Actual rating CSV files](../ratings).
- [Current completion status: who is done and what is missing](../README.md#ratings-and-completion), checked **11-11-2026**.
- [Original import receipts](../../../private/09_human_rating_collection/legacy_veribench/human_round/private_ratings_setN).

Collected files are in `ratings/`; named data links and completion status share the experiment README. The CSV filenames and first column show each person's name; the original IDs, ratings and notes are preserved. These raw tables contain the same participant submissions, including nonnumeric entries omitted by historical numeric-only imports. They are not additional observations. The rating files and collection README are tracked in Git, as requested on 11-11-2026.

## Ownership and scope

**Sole coordinating chat:** [Prepare human grading task](codex://threads/01a1a8f9-dcb7-7381-9368-91d6e51faffd). Read the [11-09-2026 coordination record](COORDINATION_11-09-2026.md) before collection, dispatch or practical judge-development work. It consolidates the former Best human-rating judge chat without dropping its evaluator or unfinished methods 2 and 4 work.

Brando moved this task from VeriBench on **11-09-2026**. Maintain the collection instructions, packet preparation, approved email, assignment tracking, delivery receipts and collection status here. VeriBench V1's separate direction is formal specification coverage checked by a prover, with artificial intelligence guiding proof search; this move does not change that scorer.

The [prospective probabilistic-judge design](../../02_probabilistic_ordinal_judge/README.md) remains the methodology for a new collection. The inherited **set N** (the previously prepared frontier-output rating round) has its own fixed materials, assignment rules and exposure history. Moving it does not turn its outputs or ratings into the prospective study's fresh training, validation or test data.

**Required reading for every collection/dispatch agent:** [judge formulations 2 and 4](JUDGE_FORMULATIONS_11-09-2026.md), with the original photos and transcriptions. Formulation 2 develops a judge using training correlation; formulation 4 uses a proper probabilistic training loss. Preserve individual ratings so both can be studied; validation-based selection (1 versus 3) is a distinct intervention. This note does not change participant instructions or dispatch authorization.

## Current delivery status — 11-09-2026

**Prepared materials are available; collaborator dispatch is a separate action.** See the [current preparation record](PREPARATION_11-09-2026.md) rather than the old email for the live schedule and individual drafts.

- The preparation record states a preferred finish of **11-13-2026** and final deadline of **11-15-2026**, superseding the historical 11-06-2026 date without rewriting delivered archives.
- The original approved email names the coordinator's personal sheet and full assignment. The new individual drafts propose the necessary recipient-specific changes; their text approval and dispatch are still separate from this migration.
- Existing participant records, assignments, returned sheets and delivery receipts moved without changing their contents. New roster decisions and dispatch preparation are recorded separately under `private/09_human_rating_collection/preparation_11-09-2026/`; use that active preparation record instead of treating the imported historical roster as current.
- The renamed packet has **25 task folders and 125 candidate files**. The team builder creates a separate blank answer sheet while preserving candidate, Python and reference bytes. A successful archive build does not establish recipient-specific delivery readiness.
- All seven recipient sheet-permission checks are complete; the eighth return route is private CSV by email. The private review freezes eight exact recipient messages and original attachment hashes. Team text/send approval and human completion remain outstanding; access verification did not inspect sealed ratings or establish completion.

## Files

```text
09_human_rating_collection/
├── README.md              # Task links, people and completion status
├── rating_task_packet/    # Editable task and participant files
├── ratings/               # Collected responses and live-sheet links
└── support/               # Records, scripts and tests
```

### Private materials

This repository is public. The following coordinator paths are ignored, not publication destinations:

| Material | Coordinator path, relative to this repository |
| --- | --- |
| Original renamed delivery, unchanged | `private/original/` |
| Existing team archives, unchanged | `private/team-folder-01.zip`, `private/team-all-folders.zip` |
| Frozen local coordination documents, packets and sealed materials | `private/09_human_rating_collection/legacy_veribench/human_round/` |
| Pinned committed source, packet-release records and private sheet bindings | `private/09_human_rating_collection/upstream_source/` |
| Active preparation, roster, individual drafts and dispatch queue | `private/09_human_rating_collection/preparation_11-09-2026/` |
| Imported participant records, assignments, submitted sheets and delivery receipts | `private/09_human_rating_collection/legacy_veribench/human_round/private_ratings_setN/` |
| Coordinator's original delivery and personal records | `private/09_human_rating_collection/legacy_veribench/human_round/private_A1/` |
| Exact approved email | `private/09_human_rating_collection/legacy_veribench/human_round/RATER_TASK_EMAIL_LOCKED_11-04-2026.md` |
| Complete file-by-file transfer hashes | `private/09_human_rating_collection/migration_receipt.json` |

The imported `PLAN_setN_rating_round.md` records dated decisions, not the current schedule. Follow [PREPARATION_11-09-2026.md](PREPARATION_11-09-2026.md) for the newer schedule and preparation; preserve the original email's approval history and the localized-assistance wording. Keep delivered archives unchanged; any later approved delivery is a new version with a new receipt. Named collected ratings and completion records are authorized for Git tracking in this experiment; private correspondence, consent and sealed data remain outside public Git.

## Build a team packet

From `~/trustworthy-theorem-judges`:

```sh
python3 experiments/09_human_rating_collection/support/scripts/make_team_packet.py \
  private/original private/team-folder-01-new.zip --folders 1 --rater T01
```

Use a new output filename and the intended person's verified rater ID (`T01` is Rylan Schaeffer); omit `--folders` for all folders. Omitting `--rater` creates an unassigned template, not a recipient-ready form. The builder checks the original delivery manifest and every included file, preserves the scoring rubric apart from its personal-sheet instruction, and includes `START_HERE.md`, `Rating_Instructions.md`, `ratings.csv` and `FILES.sha256`. It does not send anything or modify a delivered packet.

**Keep the sheet layouts distinct.** This builder's renamed `agent_file*.lean` items are not the inherited `Nxx`/`Wxx` item identifiers. The utilities under `support/scripts/legacy/` serve the inherited sheets only; do not pass a renamed team answer sheet to that importer or infer its item mapping. Preserve explicit item mappings when reconciling later deliveries.

## Current inherited utilities

The local VeriBench checkout was older than its remote branch. The active utilities therefore retain the committed implementation at `b292c277e176`, while the original local files remain separately preserved. Their inputs come from the matching pinned tree under `private/09_human_rating_collection/upstream_source/experiments/102_rescore_vbv1_paper_fsc_with_validated_judge_rewrite_tmlr_icml/`; `upstream_source/SOURCE_RECEIPT.json` records its revision and hashes. Its private working-directory links resolve to the single imported participant-record store, not duplicate records.

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
python3 -m unittest discover -s experiments/09_human_rating_collection/support/tests -v
python3 scripts/check_project.py
git diff --check
```

The tests use synthetic packets and submissions, including the current assignment, import, release and qualification rules. When the coordinator's original packet is available, they also verify a real archive build without submitting ratings. Both pinned packet releases and the sealed-key digest were checked separately without scoring real raters. The migration preserves the inherited qualification and assignment algorithms; it does not validate their suitability for the prospective study.
