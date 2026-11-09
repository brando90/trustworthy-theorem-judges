# Human-rating collection migration checkpoint

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_human_rating_collection/CKPT_human_rating_collection.md>

**TLDR:** Move the active human-rating collection from VeriBench into this experiment without changing delivered materials, opening sealed ratings, or conflating the inherited round with the prospective study.

## State

- Updated: 11-09-2026 11:15 PST.
- Historical migration owner: Pi; migration is complete. Current sole collection and practical judge coordinator: [Prepare human grading task](codex://threads/01a1a8f9-dcb7-7381-9368-91d6e51faffd), per [the 11-09-2026 ownership decision](COORDINATION_11-09-2026.md).
- Canonical task: `~/trustworthy-theorem-judges/experiments/09_human_rating_collection/`.
- Private working state: `~/trustworthy-theorem-judges/private/09_human_rating_collection/`.
- Source: VeriBench `experiments/102_rescore_vbv1_paper_fsc_with_validated_judge_rewrite_tmlr_icml/human_round/` and its collection utilities.
- Source checkout contains concurrent changes; preserve its packet/reference edits and unrelated files.
- Owned detached publication checkout: `~/.worktrees/veribench/human-ratings-move` removed after verified publication; no temporary checkout remains for this task.
- Migration: 1,290 private files transferred with matching hashes; four utility redirects and two document redirects published. Commits: trustworthy-theorem-judges `91ecc6312d71`, VeriBench `6a6f6a834c90`; both verified on `origin/main`.
- Current utilities: pinned to committed VeriBench `b292c277e176`, not the older dirty local checkout; matching private snapshot and release helper preserved. Working participant records still have one physical home.
- Preparation owner: the sole coordinating chat above owns `PREPARATION_11-09-2026.md`, `scripts/verify_preparation.py`, `private/RATE_TODAY.md`, and the private `preparation_11-09-2026/` record. The former separate methodology chat hands its work to the same coordinator.
- Delivery: the concurrent preparation record supersedes the historical deadline; revised individual drafts still require text review and an explicit send instruction.
- Scientific settings: unchanged; no solver, judge, proof search, or new ratings run.
- Verification: 17 collection tests pass, including delivered-assignment preservation, emailed submissions, release checks and C17 qualification; both real packet-release gates and the sealed-key digest match. Project and preparation checks passed; all 1,290 transfer hashes and 208 pinned-snapshot/configuration hashes match.
- Cleanup: zero new home-directory entries; global sweep retained other owners' unique work. Verification logs and small recovery records are in `private/09_human_rating_collection/migration_checks/`.
- Next: migration and packet preparation are complete; continue collection from the preparation record. All seven recipient sheet-access checks are verified. Recipient-specific text/send approval remains before collaborator dispatch; warm-up qualification and human completion remain collection work.
- Continuation: read this experiment's README and private migration receipt before touching packets or participant records.

## Event log

- 11-09-2026 preparation completion: verified all seven restricted team-sheet editors through the owner browser and retained the private CSV route. Froze eight exact messages, headers and original attachment hashes in the private review. Scoped recent-reply checks found no new matching rating replies; they do not establish sheet completion. No collaborator message or sealed rating was changed.
- 11-09-2026 manuscript coordination acknowledgment: received the VeriBench manuscript coordinator's scope notice. A publishable judge result must identify model, harness, effort, evaluator version, rubric, scale, splits, prior exposure, observed/missing denominators, uncertainty and artifact hashes. Normalized ranked probability score (RPS) is primary; cross-entropy (CE) and total variation distance (TVD) are secondary. Retrospective mixture fitting or evaluator tests do not validate a deployed semantic judge; historical paper conditions remain labeled historical and fresh replacement remains pending. The separately reported VeriBench `b67b299e77` DT overlay is not this collection or a new judge-validation result.
- 11-09-2026 manuscript follow-through: received the [published paired-paper handoff](https://github.com/brando90/veribench/blob/24bce07d14f560a65b0b3167c5b1137c1daf0cee/paper_support/public_v1_dt_11-06-2026/PUBLIC_DT_JUDGE_SYNC_11-09-2026.md) and sister TVD commit `5acfcb0`. The coordinator reports 12 publication checks and public reference acceptance of 13 accepted, zero rejected, zero pending in v2; these are that coordinator's receipts, not measurements repeated here. Both VeriBench papers retain prover-based FSC with no LLM-rating fallback. New probability-judge evidence remains a separately identified comparison unless Brando changes that choice. Private benchmark outcomes remain private.

- 11-09-2026: User explicitly requested the move to this repository's `experiments/`; inventoried legacy consumers and created a detached sparse checkout for VeriBench publication.
- 11-09-2026: Verified all 1,290 transferred file hashes and ten collection tests; detected concurrent preparation work and linked its current schedule without modifying its private roster or drafts.
- 11-09-2026: Caught older local utility versions before publication; preserved current committed implementations and their packet-release dependency, retained private sheet bindings, and passed 16 tests plus both real release gates. No real rating was scored.
- 11-09-2026: Added archive-overwrite protection; all 17 tests pass, including both real inherited packet builds in temporary directories. Reverified 1,290 original and 208 pinned-snapshot/configuration hashes, and all four redirects in both VeriBench checkouts.
- 11-09-2026 11:15 PST: Published both migration commits to `origin/main` and verified remote revisions; parsed-code comparison found only declared port adaptations, and the paper built in scratch without changing the canonical PDF. Removed the owned checkout, retained other owners' work, and preserved verification records privately. No collaborator email was sent by this migration.
