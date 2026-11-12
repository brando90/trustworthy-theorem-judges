# Native Pi packet generation checkpoint

**TLDR:** Finish the original 25-task cohort with at most four isolated workers. Preserve every attempt, all caps, and explicit provider-unavailable outcomes.

- Updated: 2026-11-12T04:48:40.308764+00:00
- Status: COMPLETED
- Terminal attempts: 25 / 25
- Active task IDs: []
- Untouched tasks: 0
- Valid conservative cost: $10.91049525; invalid pilot $0.7204245 separately.
- Active full-cap reservations: $0.00
- Additional outage-recovery admissions: 1 / 2
- Next recovery admission: not scheduled
- Condition: `PI_CONDITION_VALID_V9.json`; per-cell runner remains the frozen V6 snapshot.
- Receipts and trajectories: `runs/pi_valid_v3/<task_id>/`.
- Never rerun terminal tasks or treat pending tasks as zero scores.

## Final verified outcome — 11-11-2026

All 25 original attempts are terminal; no active or pending work remains. The final supervisor completed at 8:48 PM Pacific. Native Pi 1.5.2 used `gemini-3.8-flash` with high thinking throughout. There are 0 captured required-path Lean submissions. No terminal attempt was rerun, and no candidate was reconstructed from scratch code.

The [final audit](PI_FINAL_EXECUTION_AUDIT.md) and [machine-readable receipts](PI_FINAL_EXECUTION_AUDIT.json) preserve each task and its failure cause. Conservative accounting is $9.69398325 in completed-usage upper bounds plus $1.216512 in unresolved request reservations for the valid cohort; the excluded environment pilot adds $0.7204245. The combined bound is $11.63091975, below $20. These are not verified invoice charges.

The 670 counted calls are generation requests, including generation retries. Token-counting preflights are additional HTTP calls, outside that counter. The final saved-session inspection found zero occurrences of the corresponding required output filename in tool-call arguments across all 25 tasks. The earlier 18-task diagnostic preserves more detail about temporary Lean files. Whole workspace snapshots were not retained, so these findings establish zero captured required-path submissions, not that no temporary Lean code existed elsewhere.

Read-only cleanup verification at 8:50 PM Pacific found no running Docker containers and no surviving coordinator PID 91507 or recovery-observer PID 88366. Parent and finalizer received the final report and hashes. This checkpoint is complete; do not resume generation or retry any of these cells.
