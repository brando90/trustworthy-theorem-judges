# Human-rating collection migration checkpoint

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_human_rating_collection/CKPT_human_rating_collection.md>

**TLDR:** Move the active human-rating collection from VeriBench into this experiment without changing delivered materials, opening sealed ratings, or conflating the inherited round with the prospective study.

## State

- Updated: 11-09-2026 11:15 PST.
- Owner: Pi, current human-rating collection session.
- Canonical task: `~/trustworthy-theorem-judges/experiments/09_human_rating_collection/`.
- Private working state: `~/trustworthy-theorem-judges/private/09_human_rating_collection/`.
- Source: VeriBench `experiments/102_rescore_vbv1_paper_fsc_with_validated_judge_rewrite_tmlr_icml/human_round/` and its collection utilities.
- Source checkout contains concurrent changes; preserve its packet/reference edits and unrelated files.
- Owned detached publication checkout: `~/.worktrees/veribench/human-ratings-move` removed after verified publication; no temporary checkout remains for this task.
- Migration: 1,290 private files transferred with matching hashes; four utility redirects and two document redirects published. Commits: trustworthy-theorem-judges `91ecc6312d71`, VeriBench `6a6f6a834c90`; both verified on `origin/main`.
- Current utilities: pinned to committed VeriBench `b292c277e176`, not the older dirty local checkout; matching private snapshot and release helper preserved. Working participant records still have one physical home.
- Concurrent owner: a separate session owns `PREPARATION_11-09-2026.md`, `scripts/verify_preparation.py`, `private/RATE_TODAY.md`, and the private `preparation_11-09-2026/` record; preserve that work and its publication ownership.
- Delivery: the concurrent preparation record supersedes the historical deadline; revised individual drafts still require text review and an explicit send instruction.
- Scientific settings: unchanged; no solver, judge, proof search, or new ratings run.
- Verification: 17 collection tests pass, including delivered-assignment preservation, emailed submissions, release checks and C17 qualification; both real packet-release gates and the sealed-key digest match. Project and preparation checks passed; all 1,290 transfer hashes and 208 pinned-snapshot/configuration hashes match.
- Cleanup: zero new home-directory entries; global sweep retained other owners' unique work. Verification logs and small recovery records are in `private/09_human_rating_collection/migration_checks/`.
- Next: migration complete; continue collection from the preparation record. Four recipient sheet-access checks and recipient-specific text approval remain before collaborator dispatch.
- Continuation: read this experiment's README and private migration receipt before touching packets or participant records.

## Event log

- 11-09-2026: User explicitly requested the move to this repository's `experiments/`; inventoried legacy consumers and created a detached sparse checkout for VeriBench publication.
- 11-09-2026: Verified all 1,290 transferred file hashes and ten collection tests; detected concurrent preparation work and linked its current schedule without modifying its private roster or drafts.
- 11-09-2026: Caught older local utility versions before publication; preserved current committed implementations and their packet-release dependency, retained private sheet bindings, and passed 16 tests plus both real release gates. No real rating was scored.
- 11-09-2026: Added archive-overwrite protection; all 17 tests pass, including both real inherited packet builds in temporary directories. Reverified 1,290 original and 208 pinned-snapshot/configuration hashes, and all four redirects in both VeriBench checkouts.
- 11-09-2026 11:15 PST: Published both migration commits to `origin/main` and verified remote revisions; parsed-code comparison found only declared port adaptations, and the paper built in scratch without changing the canonical PDF. Removed the owned checkout, retained other owners' work, and preserved verification records privately. No collaborator email was sent by this migration.
