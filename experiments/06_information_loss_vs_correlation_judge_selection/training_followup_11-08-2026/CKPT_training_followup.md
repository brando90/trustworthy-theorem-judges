<!-- TLDR: Resume the authorized weighted-PMF training and stable correlation comparison from this checkpoint. -->
# Training follow-up checkpoint — 11-08-2026

## State
- Status: VERIFIED; final publication and completion notification in progress.
- Goal: compare weighted-PMF training and a stable correlation baseline using existing data and identical held-out metrics.
- Canonical home: experiments/06_information_loss_vs_correlation_judge_selection/training_followup_11-08-2026.
- Owner: current Codex chat; branch codex/ttj06-weighted-training-1108.
- Owned worktree: /Users/brandomiranda/.worktrees/trustworthy-theorem-judges/weighted-training-1108.
- Local workers: stable_correlation_design implements mixture models/math; weighted_head_extension implements softmax objectives/controls. Both inherited full access, approvals disabled, and verified first reads.
- Study design: same-class globally solved mixture weighted/Pearson training, plus separately matched four-loss softmax fits.
- Manifest: 50 primary mixture fits, 900 secondary softmax fits; 1,000 paired task-family resamples with mixture refitting.
- Budget: one CPU, at most 7,200 seconds, zero new model calls/provider charges; subscription coordination usage unmeasured.
- Run COMPLETE from frozen 6e8f609: 50/50 mixture certificates, 900/900 converged softmax fits, 998/1,000 valid refit draws; two failures retained.
- Remote target: /lfs/skampere3/0/brando9/ttj06_training_1108, session codex-ttj06-weighted-training-1108.
- Access: existing skampere3 SSH master works; LFS read/write and numerical dependencies verified. AFS token renewed; scoped numerical preflight and both control suites passed.
- Next: publish verified report/checkpoint, send DONE notification, sync canonical checkout and remove owned worktree.
- Notification owner: root, start/done emails and originating chat; no worker sends duplicate notices.
- Cleanup: root removes this temporary worktree after publication and canonical/private synchronization.

## Log
11-08-2026 — Prepared isolated worktree and delegated design/implementation; paused both subtasks when Brando asked for the overall purpose.
11-08-2026 — User explicitly resumed; prepared protocol/configuration and resumed two bounded implementation subtasks.
11-08-2026 — Numerical controls passed on skampere3; AFS token recovered, scoped CPU/filesystem checks passed. No empirical fits launched yet.
11-08-2026 — Before source-freeze rebase: old merge base 0024972; fetched main 5aef572; backup branch codex/ttj06-weighted-training-1108-prefreeze. Preserve the upstream note amendment.
11-08-2026 — Published source 6e8f609 after preserving the upstream note amendment; launched named tmux once at 20:52 Pacific. First useful receipt: 50 mixture +900 softmax fits and 25 bootstrap draws completed.
11-08-2026 — Run completed in 56.288 seconds; all 2,625 forecasts independently reconstructed. Resample verification reproduced three valid draws and both certificate failures. Primary weighted-loss contrast −0.010409 [−0.061911,+0.005933], no resolved advantage.
11-08-2026 — Appended verified findings to the existing methodology Google Doc through the signed-in owner browser after the connector returned 403; readback showed the text and Saved to Drive.
11-08-2026 — Runtime receipt/probe confirms NumPy 2.2.6 and SciPy 1.17.1; added ENVIRONMENT_NOTE.md to correct the earlier dependency-summary ambiguity without changing scientific evidence.
