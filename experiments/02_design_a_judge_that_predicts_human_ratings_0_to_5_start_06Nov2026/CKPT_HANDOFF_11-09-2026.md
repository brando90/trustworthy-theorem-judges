# Practical human-rating judge: sole-owner handoff

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/02_design_a_judge_that_predicts_human_ratings_0_to_5_start_06Nov2026/CKPT_HANDOFF_11-09-2026.md>

**TLDR:** Prepare human grading task is the sole coordinator for human-rating collection and the practical judge using formulations 2 and 4. This handoff preserves the implemented evaluator and the user's newly authorized existing-data comparison; no new empirical fit was started by the outgoing coordinator.

## Current state

- Updated: 11-09-2026, 12:18 PM America/Los_Angeles.
- Sole coordinator: [Prepare human grading task](codex://threads/01a1a8f9-dcb7-7381-9368-91d6e51faffd), in trustworthy-theorem-judges.
- Outgoing coordinator: [Best human-rating judge: correlation vs proper loss](codex://threads/01a1b4c5-657e-7043-9b4f-69f936c55fdf); its replacement title is owned by the receiving coordinator.
- Ownership transfer: explicitly accepted. The receiving coordinator owns all remaining practical-judge decisions, implementation, execution, publication and collection coordination.
- Latest user instruction: continue obtaining the best judge with methods 2 and 4 using existing data while more human data are collected in parallel; keep ranked probability score (RPS) primary, cross-entropy (CE) and total variation distance (TVD) secondary, compare on identical held-out human ratings, and push the work.
- No new experiment, fitted judge, inference job or paid call was started in response to that instruction before consolidation.
- The outgoing coordinator's only current writer is this handoff. Its child inventory is read-only and is concluding; no implementation or empirical-analysis child needs adoption.
- The separately assigned TVD owner remains chat 01a1c18b-2d23-7f22-9ff8-5bc8714a0ef0; preserve its work and verify its final publication receipt rather than duplicating it.
- The historical migration owner remains chat 01a1b704-010b-7980-b6dc-236ce4224c4d in judges-dont-need-psychometrics-or-corr. Its history and private-data relocation do not start a new scientific condition.
- Before any next fit, reconcile those owners, current main, source hashes, the selected retrospective split, model family, validation rule and test-exposure disclosure.

## Completed and published work

| Deliverable | Exact revision and location |
| --- | --- |
| Practical-judge priority, ownership and methods 2/4 plan | TTJ 705bc32b1061079801d1c505c34a6b8c72cf3315; [priority plan](PRIORITY_2_VS_4_11-09-2026.md), mirrored AGENTS.md/CLAUDE.md and root README.md. Preserves concurrent history while superseding its tentative 3/4 interpretation. |
| Common offline six-probability evaluator | TTJ e2626022447eb18c033713f5878fb4b13f638476; [README](native_probability/README.md), scaffold.py and test_scaffold.py. Original 16 synthetic tests passed, including integrity, failure denominators, proper-loss identities and correlation controls. No native model transport or fitting was implemented. |
| TVD extension, separate owner | TTJ 27237a27d49b83cfdb910153b59af32e15198325, present in fetched main: adds secondary TVD, missingness bounds and prospective documentation/configuration. The metric version is native_probability_metrics_v2. Preserve completed protocols and use that owner's final verification record. |
| General-study priority | Sister repository 77977f898d72d89c7acf705e420b064310be71f7; mirrored entry files and README distinguish the practical judge from the general correlation-inferiority hypothesis. |
| Original photographs, transcription and recommendations | Sister repository f4df69159d0ee65b0b0fce0739b0ae77ef9e2cc9; paper_latex_and_notes/notes/correlation_and_loss_formulations_received_11-09-2026/. |
| Historical-study relocation pointer | TTJ fdccb703ea56acbdf0f20498d19f1ad898b044ff; experiment 06 README points to the sister repository's [migration record](https://github.com/brando90/judges-dont-need-psychometrics-or-corr/blob/main/experiments/03_exp06_ce_vs_pearson_matched_budget/MIGRATION_11-09-2026.md). |

The original evaluator checks also passed project/design validation and the unchanged paper's scratch build; the project suite had two expected skips for unavailable private fixtures. The working scientific Python with NumPy/SciPy is /Users/brandomiranda/uv_envs/no-gold-ref-judge/bin/python3; its observed SciPy version was 1.16.3. The project's existing default Python hit an architecture mismatch; arch -x86_64 /usr/local/bin/python3 ran the project checks successfully without package changes.

## Existing data that can support the next comparison

The metadata inventory resolved and hash-checked the already exposed historical dataset; it did not fit or score a new model or open the inherited fresh collection.

- Canonical private dataset: judges-dont-need-psychometrics-or-corr/experiments/03_exp06_ce_vs_pearson_matched_budget/research_artifacts/historical_exp06/cached_v1/dataset.json.
- Compatibility path: trustworthy-theorem-judges/research_artifacts/06_information_loss_vs_correlation_judge_selection/cached_v1/dataset.json. This resolves to the canonical store; do not create another uncontrolled copy.
- SHA-256: b3a05699a26d3ffd9f28e793178811219885df78319b3aa57f9d393c68724ba0.
- Immutable source: VeriBench be287d9bb2f7bd35ba6db1b8735c9ba10d00eade, experiment 100. The preserved source_hashes.json digest is 80989c4a6050c783b8b9d3d3c44a0983455c1d9f5662b293c2c9e2fd139ba9da.
- Five complete cached judge configurations, 75 artifacts and three integer 0–5 repeats per configuration/artifact; 195 expert observations. These are sampled scalar forecasts, not native probabilities of human ratings.
- Recorded configurations: H0 Sol, H0 Opus, H1 Sol, H2 Sol and H2 Opus. Model selectors are openai/gpt-6-sol-high with high effort and anthropic/claude-opus-5-5-no-fallback with maximum compute effort/adaptive thinking. Preserve each cache's actual prompt/configuration hashes; these are historical pins, not assertions of current provider availability.

| Original split | Artifacts | Tasks | Task families | Expert observations |
| --- | ---: | ---: | ---: | ---: |
| train | 30 | 10 | 9 | 78 |
| val | 15 | 5 | 5 | 39 |
| test | 30 | 10 | 9 | 78 |

The source uses the literal split label val; any conversion to validation must be explicit. Tasks are disjoint but families overlap: binary-search and heap families cross train/validation, binary-search and sorting families cross train/test, and the binary-search family crosses validation/test. All three expert columns recur across the splits. The old test has already been exposed by previous studies. Preserve this provenance; neither this split nor a new resplit establishes fresh simultaneous task/agent/rater generalization. The original split preserves the historical H1/H2 prompt-development boundary better than pretending those upstream prompts were refitted independently inside new folds.

The inherited collection in experiment 09 remains evaluation-only under its recorded protocol. The user's permission to use available data does not turn that collection into a new training pool. The receiving owner already controls collection readiness and should keep it separate from the retrospective exercise.

## Concrete continuation for the sole owner

1. Read the [priority plan](PRIORITY_2_VS_4_11-09-2026.md), the TVD-updated [evaluator](native_probability/README.md), and the sister repository's completed comparison and migration record. Reuse completed results before admitting a new condition.
2. Freeze a separately named retrospective practical-judge condition before fitting. A useful smallest extension is a common simplex-mixture family over the same cached probability representation, trained with Pearson for method 2 and RPS for method 4, using identical train rows and the same validation RPS for any hyperparameter or candidate choice. The sister repository has a stable finite-active-face Pearson solver; an RPS quadratic objective can use the corresponding cumulative-distribution design. This is a proposed implementation path, not an already frozen or executed experiment.
3. Keep representation, probability-floor policy, candidate set, information access, capacity, tie policy, optimizer checks and search budgets matched. A fitted mixture/head is not end-to-end language-model training. Do not compare an unstable Pearson softmax fit with a different successful proper-loss model as evidence about the objective alone.
4. Freeze selected models before the common retrospective test. Report RPS primary, CE/TVD secondary and the common diagnostics; compare against a train-fitted constant and unchanged cached judges. Retain failed fits and missing artifacts, and report paired uncertainty with its actual unit and limitations. Select a usable candidate on validation; do not tune the next condition to manufacture a test winner.
5. Export the fitted parameters, exact upstream judge configurations, prediction code, private reproducible forecasts and public aggregate report/checkpoint. Keep individual ratings, raw source artifacts and participant records private. Push eligible files to main and verify remote revisions.
6. Treat the coming human collection as the route to stronger independent evidence. The strict task/agent/rater split amendment, native-probability transport, new-model selection and any deployment threshold remain separate unfinished work. Existing retrospective success cannot establish those claims.

The current funding pause, scoped allowlists, existing caps, payer requirements and failed scientific gates remain binding. Local analysis of the cached data needs no new provider calls. Any new measured inference requires an eligible route and a bounded cost estimate; the Tiny/Gemini exception is not general permission for human-judge calls. The last local funding audit found no TTJ allowlist entry; recheck live state before treating that as current eligibility.

Reusable code is in the sister experiment 03's scripts/historical/mixture_models.py and scripts/ce_mixture.py. The original TTJ experiment-06 scripts/import_cached.py remains a supported historical import dependency. Weighted probability-mass-function fitting is not RPS fitting; verify the new objective and its controls separately.

## Shared checkout and writer ownership

The canonical TTJ checkout deliberately retains its older HEAD/index at 930da261613b13c345cda02c0ebb84481dc0c648. Task-owned published files were copied into it without merging shared state. At handoff inspection it showed modified AGENTS.md, CLAUDE.md and README.md plus untracked PRIORITY_2_VS_4_11-09-2026.md and native_probability/. These originate from the published priority/evaluator work; the TVD owner may be updating the same working copies. The modified experiment-06 README belongs to the migration owner and is published at fdccb70. Do not blindly stage or overwrite the shared checkout.

The TVD worktree at ~/.worktrees/trustworthy-theorem-judges/tvd-evaluation-panel belongs to that owner. The outgoing coordinator's earlier implementation and priority worktrees were removed after publication. This handoff uses a temporary detached checkout, to be removed after its push. No active local fitting worker, paid run or training process belongs to the outgoing coordinator.

## Other unfinished authorized work that must remain visible

- Tiny pilot and prover validation remain with [Run Tiny-256 Lean prover comparison](codex://threads/01a1a7d3-74f3-79c2-873f-58a7a392aaab). Last verified published state: 132 attempts finished; strict winner unresolved and full-1,024 admission uncleared. Preserve the exact Gemini HIGH/harness conditions and existing budgets; do not duplicate or restart the pilot.
- Differential testing/reference acceptance remains with [Check DT status in VeriBench](codex://threads/01a1a7da-397d-7c53-b93a-3f5d3bf1886e). Last verified acceptance overlay ff2606e05e has 10 admitted, three rejected and zero pending review. The rejected cases still need repair; do not relabel the frozen benchmark.
- The original overnight synthetic objective study and master-entailment pilot are published, but their full requested five-stage acceptance remains unverified. Published trees matched stage-02 artifacts; recorded stage-03 repair 2b34a6d and final Grok/fresh-Claude/finalizer receipts must be recovered before declaring full acceptance. No duplicate notification was sent.
- Detailed original-job ownership, budgets, receipt hashes and exact recovery paths are in the local private coordination record ~/Documents/Codex/2026-11-08/judge-overnight/CKPT_MASTER.md and JUDGE_PRIORITY_AND_EVALUATOR_11-09-2026.json. The SNAP recovery paths are /dfs/scratch0/brando9/judge-overnight-1108/{objective-study,applied-judge} and /lfs/skampere3/0/brando9/judge-overnight-1108/qa/. Existing remote jobs must be inspected and adopted, not assumed dead or duplicated.
- Use the configured Whale gateway and shared reconnect guard before any SNAP retry. Last local inspection had no reusable target master; do not infer that VPN is required, reset the cooldown or claim a remote worker is live from an old checkpoint.
- The original finalizer owns the combined-study Google companion and DONE notification. Verify its ledger before sending anything. Google synchronization for this chat's priority/evaluator update was not independently verified; the receiving collection owner has separate methodology-document work that must be preserved.

## Event log

- 11-09-2026: verified Brando's explicit consolidation request in the receiving chat, acknowledged sole-owner transfer, stopped admission of a duplicate practical-judge experiment, completed the read-only existing-data inventory and prepared this handoff for publication.

**TLDR-end:** [TTJ: practical judge handoff] Prepare human grading task now owns collection and the existing-data methods-2/4 comparison. Continue from the published evaluator and verified private dataset, keeping RPS primary, CE/TVD secondary, historical exposure explicit and other owners intact.
