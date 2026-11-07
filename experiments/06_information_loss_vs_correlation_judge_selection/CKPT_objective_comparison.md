# Objective comparison checkpoint

**TLDR:** Cached-data implementation in progress; no comparison results inspected yet.
Created: 11-06-2026 (original preparation; time not recorded)
Last updated: 11-06-2026 23:08 PST

## Goal
- Compare selection objectives on the same historical held-out rating metrics.
## What ran
- Root resumed on the verified Vals/work route, GPT-6 Astra / xhigh, full access, approvals disabled (prior runtime receipt).
- Import completed: 75 artifacts, 25 tasks, 19 families, 195 expert ratings, 1,125 cached scores; zero new model calls.
- Owner: current chat; branch `codex/ttj06-cached-objectives`, worktree `~/.worktrees/trustworthy-theorem-judges/ttj06-cached-objectives`.
- Canonical private data: `private/06_information_loss_vs_correlation_judge_selection/cached_v1/` under the canonical Mac repository.
## Results
- Empirical comparison pending. All input receipt/manifests passed importer assertions.
## Stuck / blocked
- Nothing. Integer-valued float ratings are now correctly accepted; initial failed import created no dataset.
## Next steps
- Freeze protocol/code; run synthetic checks and full cached comparison on skampere3, verify terminal receipts, publish.
- Execute `scripts/run_cached.py --data <private dataset.json> --config protocol.json --out <results directory> --private-out <private resamples directory>` from this experiment.
## Brando to-do
- None for this cached analysis; new human confirmation remains separate.

## Log
Log 11-06-2026: Preserved the original image byte-for-byte and user request; created the experimental design, mathematical clarification and work-account continuation prompt.
Log 11-06-2026: Verified historical inventory (75 artifacts, 25 tasks, 195 expert ratings; five complete scalar candidates). Deterministic objective identities/counterexample pass; math_checks.json records the output. Project checks pass. No empirical selection run or overnight process has started.
11-06-2026 23:08 PST -- Adopted existing worktree, repaired numeric-type assertion, completed import; froze protocol before comparison execution.
