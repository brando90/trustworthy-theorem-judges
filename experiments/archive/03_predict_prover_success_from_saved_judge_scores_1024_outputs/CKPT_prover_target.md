<!-- TLDR: Zero-call prover-target reanalysis, requested independent review and main publication completed; fresh model inference remains a separate pending study. -->
# Prover-target study checkpoint
Created: 11-06-2026 11:32 PST
Last updated: 11-06-2026 11:57 PST
## Goal
- Predict fixed-protocol proof success as a separate fallback research target from expert-rating prediction.
## What ran
- Protocol committed before analysis: 24c9152. Zero new measured model calls; source revision be287d9bb2f7bd35ba6db1b8735c9ba10d00eade.
- Complete 1,024-artifact reanalysis, 64/64/128 task split, four excluded-agent fits, 10,000 task-bootstrap resamples.
## Results
- Pooled test: Brier 0.107 versus constant 0.165, paired difference -0.058 [-0.087, -0.031], 512 artifacts/128 tasks, p-val=n/a.
- Retrospective only; exact target is proof-dependent historical acceptance, not semantic ground truth or fresh judge validation.
## Stuck / blocked
- New measured calls: existing funding pause excludes this experiment; no scoped key exception applies. Zero-call work completed.
- Claude Fable/max review completed: PASS, 0 critical, 2 major findings fixed. Published on origin/main at e12117f98c3b50fae32a107349afc1a9be2c08ea.
## Next steps
- Completed: reviewed study, project links and mirrored instructions published; Google findings companion updated and verified.
- Future measured study: validate a faithful statement-only target and establish an eligible funding route before the separate pilot. All 83 private files are hash-verified in canonical research_artifacts/prover_target/.
- Reproduce: see RUNBOOK.md; source blobs and split manifest are protected under research_artifacts/prover_target/.
## Brando to-do
- None for the completed zero-call study; a later paid run needs an eligible route under the existing gate.
## Log
- 11-06-2026 11:32 PST -- Completed retrospective analysis and source audit; preparing requested review.
- 11-06-2026 11:52 PST -- Fable/max review reproduced results; all findings resolved, original reviewed revision preserved privately.
- 11-06-2026 11:55 PST -- Merged origin/main while preserving protocol history; project checks and paper build passed; protected artifacts copied with hashes.
- 11-06-2026 11:57 PST -- Parent verified main publication e12117f and the dated Google companion update; canonical records preserved for checkout cleanup.
