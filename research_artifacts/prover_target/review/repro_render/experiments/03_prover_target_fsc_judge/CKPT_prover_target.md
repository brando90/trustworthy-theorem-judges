<!-- TLDR: Zero-call prover-target reanalysis completed; requested independent review and parent integration remain. -->
# Prover-target study checkpoint
Created: 11-06-2026 11:32 PST
Last updated: 11-06-2026 11:32 PST
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
- Requested Claude Fable/max review pending; parent owns main integration.
## Next steps
- [p 10/10] Run one requested review, fix findings, rerun deterministic checks.
- [p 10/10] Parent integrates owned experiment path, then worker preserves private receipts and removes its checkout.
- Reproduce: see RUNBOOK.md; source blobs and split manifest are protected under private/prover_target/.
## Brando to-do
- None for the completed zero-call study; a later paid run needs an eligible route under the existing gate.
## Log
- 11-06-2026 11:32 PST -- Completed retrospective analysis and source audit; preparing requested review.
