# Native Claude Code rating-candidate generation

**Doc link:** private execution checkpoint; parent publishes aggregate preparation status.

**TLDR:** All 25 valid native Claude Code attempts are complete: 19 nonempty candidate files and six declared response-cap/no-file outcomes. No task retakes occurred.

## Current state
- **COMPLETE** as of 11-11-2026 19:41 PST. Authoritative ledger: `VALID_V2_BATCH_STATUS.json` (`FULL_SET_TERMINAL`). No CC cells are active or pending.
- Final verified inventory: `CC_VALID_V2_FINAL_SUMMARY.json`, SHA256 `c774b5fddc9d7e98df27526ebe4f33bbedf32538edd63445c4263c1ee6315f21`.
- Valid condition: `../CC_CONDITION_VALID_V2.json`, SHA256 `d51c4322693cf133f3dfe4d10b8e831d258945680d1ef1357970dc014c06c66c`.
- Input manifest SHA256: `e7a46a58a90cc23491f3db033d7dc749616f160da0b868962a3b5d8ec1b61e29`.
- Valid outputs: `../claude_code_valid_v2/<task_id>/` (planned record, raw stream, receipt, candidate when present, derived cap disposition when applicable).
- Native Claude Code 2.1.322; `claude-fable-5-1` / max; original 1,800-second/40-turn/one-attempt/16,384-response-token controls unchanged. Total/output token thresholds are observed-response controls with possible overshoot.
- Runner SHA256 `7bff1a4ecbcd049c06ea7591edfd8cb22c058f663a555139fe0ef94723575cce`; clean image `sha256:2104a4b8fe86379143a49331d79c9eecae67ab58ef73d4db05183510061bc89e` retained for Pi and reproducibility.
- Outcomes: 13 native completions with files; six budget-stopped files (one wall, two observed-output, three observed-total); six declared per-response-cap/no-file outcomes. Candidate presence is not a Lean-validity or FSC result.
- Six no-file tasks: topological_sort, prime_fib, base32, heapsort_algorithm, edit_distance, heap_sort. Hash-bound per-cell `TERMINAL_DISPOSITION.json` preserves exact cap and pinned-provider-model evidence; raw synthetic-client-error identity booleans remain unchanged.
- Final source maps, all 25 model identities, preflight/no-mount records and all 19 file hashes verified. `VALID_V2_TRAJECTORY_AUDIT.json`: 25 terminal streams, 221 visible tool calls, zero pattern hits, zero malformed JSONL lines (lexical screen, not proof against obfuscation).
- Observed traffic: 13,683,012 total tokens / 1,965,786 generated tokens; five interrupted streams have incomplete in-flight usage. These are observed traffic sums, not a complete provider billing statement.
- Shared personal subscription weekly utilization reached 36%; no overage event. Shared usage includes other activity and is not solely attributable to this batch; native list-price estimates are not new subscription charges.
- Scheduling amendments preserved single admission ownership and active clocks: serial → two lanes → four lanes; V5 corrected declared-cap/synthetic-envelope classification. All amendment hashes appear in the final summary.
- Original invalid-image pilot remains preserved separately under `../claude_code_outputs/realcode_set__20_html_escape/`; environment-based exclusion, outside valid 25, no quality-based retake.
- CC-only egress proxy/internal network removed after verifying zero CC containers; `CC_EXECUTION_CLEANUP.json` records it. Pi containers/networks and the shared image were untouched.
- Parent owns final packet assembly, main publication/emails and old experiment-path alias cleanup after both native conditions finish. No public edits/commits were made during valid execution by this worker.

## Event log
- 11-11-2026 16:36 PST: launched frozen first cohort cell and serial25-task driver; no extra model probe.
- 11-11-2026 16:42 PST: native billing event confirms weekly18%, isUsingOverage=false, overage rejected; output-usage accounting issue reported to parent.
- 11-11-2026 16:49 PST: corrected dependency-only image and exact-user offline Mathlib preflight passed; provider usage parser regression fixture passed; waiting for corrected parent freeze.
- 11-11-2026 16:56 PST: corrected condition frozen and running; first useful source-only Lean tool action and provider usage accounting verified.

- 11-11-2026 17:25 PST: first valid HTML-escape cell ended at wall cap; 36,420-byte candidate preserved, verified Fable5.1; cell2 is-prime continued.
- 11-11-2026 17:34 PST: parent-authorized concurrency2 amendment frozen (SHA256 `015d5b1642e0ea6c3eedc02f227993e03478c515ff906bfce09b935ca61fa991`); supervisor PID68292 adopted is-prime runner PID64674 unchanged and admitted task3. Original supervisor52658 terminated without process-group signal; original condition/runner and per-cell clocks/caps unchanged. Current authoritative state remains `VALID_V2_BATCH_STATUS.json`.
- Scheduler V3 `run_frozen_batch_v3.py` owns all new admissions and holds on native quota rejection/85%weekly reserve or VM memory pressure; source-only image unchanged. `CONCURRENCY2_LAUNCH.json` and `CONCURRENCY2_AMENDMENT.json` preserve transition.
- Final provenance acceptance must refresh `audit_native_tool_trajectories.py` output `VALID_V2_TRAJECTORY_AUDIT.json`; initial terminal cell has zero pattern hits. Public09 now renamed `09_prepare_packets_and_collect_human_ratings`; old ignored local symlink is intentionally needed for frozen runner path until completion, parent owns cleanup.

- 11-11-2026 18:03 PST: parent-authorized four-lane scheduler amendment, SHA256 `3cff26fd98cbe935f0406d8c06b51f03d888ffa4f0b775dc583869d34fa74a17`, scoped to17 untouched tasks. Supervisor74612 adopted max-element71969 and topological-sort72413 unchanged; only prior coordinator68292 stopped. Original25 tasks/model/image/runner/per-cell caps preserved. Current admission guard also records Pi solver presence.

- 11-11-2026 18:16 PST: immutable budget-classification amendment SHA256 `5eeeaf477c4ad12728f70f63e7cd96fde76fd53a031a53826cf6c0935fbb1e09`; coordinator78755 adopted all3 healthy active runners unchanged. Topological-sort remains a valid declared16,384-response-token-cap no-file outcome; raw receipt unchanged, explicit synthetic client-error envelope/provider identity verified by sidecar. No retry/cap increase. SchedulerV5 resumes the14 untouched tasks at at most4 concurrent cells and continues to reject unrelated API/model failures.

- 11-11-2026 19:41 PST: all 25 valid attempts terminal; final source/model/hash/trajectory verification passed; finalizer and parent notified.
- 11-11-2026 19:44 PST: removed completed CC-only proxy/network after confirming zero solver containers; shared image and active Pi work preserved.
