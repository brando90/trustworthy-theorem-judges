# Light review: native-heavy human-rating packet implementation

**Doc link:** local private file (git-ignored, not published): `private/09_human_rating_collection/preparation_11-09-2026/native_harness_packet_11-11-2026/light_qa/REVIEW.md`

**TLDR:** One round, read-only. No spending, isolation, credential or label-blinding defect found. One open critical problem in the Pi arm (two of three valid Pi cells were ended by transient provider/transport failures and are being counted as their single attempt), two open major gaps before any cohort freeze or dispatch, and one critical defect in the originally hashed builder that the later builder already fixes. The frozen generation code does not need editing because of this review; the Pi batch is already halted and should stay halted until the decision in C1 is made.

- Reviewer: Claude Fable 5.2 (`claude-fable-5-2`), effort `max` as requested in `LAUNCH.json` (effort not measurable from inside the session). Same vendor as the Claude Code solver condition, so this is not an opposite-company review.
- Review window: 11-11-2026, 16:58 to 17:16 PST. State facts below are as of 17:14 PST (01:14 UTC 11-12-2026).
- Reviewer actions: file reads, `python3 -B` hash and join computations, the three native unit-test files (temporary directories only). No Docker, provider, Google or email action. The only file written is this one. A scratch folder outside the repository (`/tmp/ttj_light_review_scratch`) held comparison copies and is removed at the end.

## 1. Scope and reviewed hashes

The five hashes in `INPUT_HASHES.json` matched at 16:58 PST. Three of the five files changed during the review, and a new script and test appeared. Both versions were reviewed; findings say which version they apply to.

| File (under `experiments/09_prepare_packets_and_collect_human_ratings/support/`) | Hashed snapshot (reviewed in full) | Latest version reviewed | How the latest was reviewed |
|---|---|---|---|
| `scripts/native_packet_generation/build_packet.py` | `b2850752…` | `780a3a41…` (17:00:56) | full diff against the snapshot |
| `scripts/native_packet_generation/pi_runner.py` | `5ed1acd6…` (archived as `pi_runner_versions/pi_runner_valid_v3_5ed1acd6.py`) | `f4ac9b97…` (17:02:41, "V4") | full diff: diagnostics-only |
| `scripts/native_packet_generation/claude_code_runner.py` | `7bff1a4e…` | unchanged | full read |
| `scripts/native_packet_generation/finalize_cohort.py` | not in snapshot (new) | `250c02fd…` (17:09:36) | full read at `ba8ba52b…` plus diff to `250c02fd…` |
| `tests/test_native_packet_builder.py` | `79cb228b…` | `e51c01d0…` | snapshot read in full; latest run, its diff not read |
| `tests/test_native_pi_budget.py` | `57dc3a50…` | unchanged | full read |
| `tests/test_native_cohort_finalizer.py` | not in snapshot (new) | `978d0e45…` | full read |

Private files also read: `run_pi_valid_batch.py`, `run_pi_valid_remaining_v4.py` (diff), `claude_code_readiness/run_frozen_batch_v2.py`, `CC_CONDITION_VALID_V2.json`, `PI_CONDITION_VALID_V3.json`, `PI_CONDITION_VALID_V4.json`, `ENVIRONMENT_AUDIT_v2.json`, `PLANNED_COHORT_VALID_ENV_V2.json`, `PLANNED_ASSIGNMENTS.json`, `NEW_MAIN_SHEETS.json`, `inputs_and_existing/INPUT_MANIFEST.json`, the Pi task index, all four Pi gateway ledgers, three Pi receipts, and both Claude Code streams.

Tests: I ran the 20 tests in the three native test files at 17:09 PST against builder `780a3a41…`, finalizer `250c02fd…`, Pi runner `f4ac9b97…`: all pass. The coordinator reports all 53 project tests pass; I did not re-run the other 33.

## 2. Critical (open)

### C1. Pi arm: a single transient provider or transport failure permanently ends a cell, and that cell is then counted as its one attempt

**Evidence (valid Pi run, `runs/pi_valid_v3/`, 3 cells terminal, 0 artifacts):**

| Cell | Requests | Ending cause from the gateway ledger | Solver-attributable? |
|---|---|---|---|
| `realcode_set__20_html_escape` | 40 of 40 | denial `Provider request cap reached`; 40 single-command probes, no file ever written | yes, under the frozen 40-request cap |
| `easy_set__23_is_prime` | 6 | call 6: `URLError` 0.16 s after admission, no HTTP response, no usage | no |
| `security_set__…93_unsafeappentitlements` (V4 runner) | 5 | call 5: upstream HTTP 503 in phase `generate_content`, 0.6 s after admission | no |

That is 2 failures in 51 admitted generation requests. Calls in the third cell took 74 to 158 s for about 55 output tokens (about 12 s in the first cell), so the provider is degraded right now. All three receipts carry the same labels: `status: provider_error`, `native_stop_reason: error`, `artifact_status: missing`.

**Code path:**
- `pi_runner.py` (line numbers of `5ed1acd6…`; V4 is the same code shifted by +3 to +13 lines) lines 398-403 write Pi settings with `retry.enabled False`, `maxRetries 0`, provider `maxRetries 0`.
- Line 279 makes one upstream `urlopen` with no retry.
- `Budget.reserve`, lines 153-154, refuses every later request once any earlier row has no finish reason ("Earlier provider response incomplete; new admission stopped").
- So one HTTP 503 or one failed connection ends the agent, and the cell directory already holds its attempt marker (lines 333-335).
- `PI_CONDITION_VALID_V4.json` then lists the affected cell under `prior_attempted_task_ids`, and `run_pi_valid_remaining_v4.py` skips it for good. V4 added logging only.

**Why it matters:**
- The requirement is 25 fresh native Pi artifacts. At most 22 are now possible, and two of the three losses are infrastructure events, not solver outcomes.
- Stopping later admissions is not needed for budget safety in these two cases. The provider returned an explicit error or nothing, so no tokens were generated, and the row's full reservation ($0.110592) is retained anyway.
- The runner switches Pi's own retry off. If native Pi retries transient provider errors by default (not verified here), this is also a departure from the "native Pi" condition.

**Minimal fix (prospective only; new frozen condition for unstarted cells; do not edit while a batch runs):**
1. In `serve_gateway.do_POST`, retry the generation `urlopen` for the same ledger row and the same reservation at most 2 more times with backoff (for example 5 s, then 20 s). Retry only when no response has started and the failure is an explicit upstream HTTP 429/500/502/503/504 or a connect-phase error (name resolution, connection refused, TLS handshake). Record each failed try in the row. Leave model, caps, prices, wall clock and everything else unchanged. Keep the current fail-closed stop for a response that started and then broke.
2. Record a disposition rule before any further Pi outcome is seen. This needs Brando's decision because the parent authorization says no retries. Option A: keep `easy_set__23_is_prime` and `security_set__…93_unsafeappentitlements` as excluded infrastructure failures and state the Pi arm as at most 22. Option B: declare any cell whose only ending cause is an infrastructure or provider failure an invalid attempt, by the same outcome-independent logic used for the environment pilots, and re-admit it once under the amended condition, with both attempts preserved and all cost counted against the $20 ceiling (measured so far: $1.384212).
3. Do not resume Pi admissions while the provider is returning 503s and multi-minute latencies.

## 3. Major (open)

### M1. `finalize_cohort.py` files infrastructure-ended cells as ordinary missing outputs and can freeze that record permanently

- **Code (`250c02fd…`):** lines 26-28 treat Pi `provider_error` and `runner_error`, and Claude Code `INFRASTRUCTURE_INTERRUPTED`, as terminal. Lines 224-229 turn any terminal cell without a captured file into `MISSING_OUTPUT` with reason "Terminal attempt returned no captured artifact". The gateway ledger is never read.
- **Effect:** in `EXCLUSIONS.json` the request-cap cell and the two transport-failure cells would be indistinguishable (same `execution_status`, same `stop_reason: error`). A Claude Code cell interrupted before any model call would also become a missing output. `ratable_subset_available` (line 278) turns true without any explicit decision, and `freeze_json` then refuses to overwrite the frozen record.
- **Conflict with the documentation:** `COORDINATOR_README.md` step 6 says missing submissions "remain explicit failures with their cause".
- **Minimal fix:** for each missing Pi cell, read and hash `<output_dir>/gateway_ledger.json` and add `missing_cause` (`budget_cap:<denial>`, `infrastructure:<denial, phase, status>`, `timeout`, `ended_without_file`); for Claude Code derive it from `status`, `stop_reason` and `model_call_performed`. Refuse to freeze a ratable subset while any missing cell has an infrastructure cause, unless a hash-bound disposition file names that item. Add one synthetic test per cause. Do this before the first freeze.

### M2. The three prepared Google Sheets hold rows for artifacts that will not exist, and no gate compares Sheet rows with the built `ratings.csv`

- **Evidence:** `NEW_MAIN_SHEETS.json` records 85 rows for Brando (`A1`), 8 for Rylan (`T01`), 6 for Sri (`T05`). They include `native-heavy-11-11-2026__item042` → `task_11_html_escaping/agent_lean/agent_1.lean` (in `A1` and `T05`) and `…__item072` → `task_13_primality_testing/agent_lean/agent_1.lean` (in `A1`), plus the Pi row of the third cell in `A1`. All three are terminal with no file.
- **Code:** `build_packet.py` writes `ratings.csv` rows only for artifacts in the cohort, takes only `--sheet-url`, and never checks Sheet content. `start_here()` (latest lines 97-117) does not explain a skipped file number.
- **Effect if dispatched as is:** Sri's Sheet asks for 6 ratings while the packet holds 5 files, with one row pointing at a file that is absent. A score typed into that row would be an observation for a non-existent artifact. The stated counts (85 total, 170 primary, Brando 85, Sri 6) no longer hold: currently at most 82, 164, 82 and 5. Rylan's 8 are unaffected so far.
- **Minimal fix:** after the cohort freeze, regenerate each participant's rows from the built `ratings.csv`, update the three undispatched Sheets to exactly those rows, read them back, and store a row-level equality check in a new versioned Sheets record. Add a builder or verifier argument that fails when supplied Sheet values differ from the CSV rows. Add one `START_HERE` sentence when the selected tasks contain excluded items ("File numbers can skip; rate only the files listed in your Sheet"). Update the counts in the coordinator documents.

## 4. Critical in the hashed snapshot, fixed in the later builder

### S1. `build_packet.py` `b2850752…` renumbered candidate files when a cell was missing

- **Snapshot code:** lines 156-166 numbered `agent_{index}.lean` by enumerating only the artifacts present in the cohort. The snapshot had no representation for a missing output, so the only buildable cohort dropped the cell.
- **Concrete failure:** dropping the missing Pi cell of `realcode_set__20_html_escape` (`item042`, planned `agent_1.lean`) moved the Codex file (`item082`) from `agent_2.lean` to `agent_1.lean` and the Claude Code file (`item017`) from `agent_3.lean` to `agent_2.lean`, while the already-written Sheets keep `item082 ↔ agent_2.lean` and `item017 ↔ agent_3.lean`. Ratings would have been joined to the wrong solver configuration with no error.
- **Status:** fixed in `780a3a41…`. `display_layout` (lines 56-74) derives names from the full planned cohort, and `checked_display_layout` (lines 77-94) binds a filtered cohort to the hash-verified plan. Verified: the latest layout over the 85 planned cells equals all 99 prepared Sheet rows, and the new filtered-cohort test passes. Still open: a hand-made cohort without `display_layout` and without `excluded_item_ids` takes the old path, and the builder does not require `buildable: true` or a final status. Add both checks (minor).

## 5. Minor

1. **Blinding check is narrow.** The builder's tokens for the real cohort are exact product strings (`claude-fable-5-1`, `Claude Code`, `gemini-3.8-flash`, `grok/grok-4.7-xhigh`, `Terminus 2`, `Codex`, `gpt-6-astra`); `Pi` is skipped as too short; the planned configurations carry no `identity_tokens`, and the finalizer copies them unchanged. A comment such as "written by Claude" or "Gemini" in a fresh candidate would pass. Dry run on the real rubric, guide, 25 Python files, 25 references and 35 historical candidates: 0 token hits and no vendor word in any candidate. Add vendor and family stems as default tokens and scan the fresh candidates before dispatch.
2. **Claude Code limit detection.** `run_frozen_batch_v2.py:55` detects subscription or billing stops by phrase matching, and the runner does not store `rate_limit_event` status. A limit stop that matches no phrase and shows no non-pinned model would be logged as a terminal no-artifact cell and the loop would continue. Without editing frozen files: watch `rate_limit_event.rate_limit_info` in the live stream and use `claude_code_readiness/HOLD_ADMISSIONS`. Observed: status `allowed`, weekly utilization 0.18 to 0.19, `overageStatus: rejected`, `isUsingOverage: false`. Extra usage is off because the account is out of credits, not by a user switch.
3. **Running drivers depend on the untracked alias** `experiments/09_human_rating_collection` (`run_pi_valid_remaining_v4.py:13`, `run_frozen_batch_v2.py:7`). Removing it, or editing a runner, makes the per-cell hash guard raise an unhandled error and leaves `BATCH_STATUS.json` saying `RUNNING` (seen in `runs/pi/driver.log`). Keep the alias until both batches are terminal and name its cleanup owner, as the project rule requires.
4. **Guards are `assert` statements** in `claude_code_runner.py` (lines 124-156, 233-282) and both private drivers. They vanish under `python -O` or `PYTHONOPTIMIZE` (currently unset). Use explicit raises in a later revision.
5. **Claude Code egress.** The proxy allowlist includes `generativelanguage.googleapis.com` (`claude_code_runner.py:33`), which those cells do not need. The tunnel is opaque, and the solver holds the subscription grant in its environment (line 249), so deliberate out-of-band use is neither prevented nor metered. The proxy image is pinned by tag, not digest (line 114), and `run_cell` does not re-check the proxy script label. Scan of all 99 tool calls so far: 0 network or credential commands. Repeat that scan on every trajectory before finalizing.
6. **The two fresh conditions differ in container limits and input placement.** Claude Code: all capabilities dropped, 2 CPUs, 8 GB, inputs in `/workspace`, prompt on standard input (lines 246-249, 268). Pi: no such limits, inputs in the Lean project root, prompt attached as a file (`pi_runner.py` lines 365-369, 413, 449). Disclose; no harness comparison is claimed.
7. **Infrastructure failures before any model call consume the attempt marker** in both runners (`pi_runner.py` lines 333-335; `claude_code_runner.py:239`). Cover this in the C1 disposition rule.
8. **Lost ledger is counted as $0.** If the ledger copy fails (`pi_runner.py` lines 509-515), the driver records $0 for the cell (`run_pi_valid_remaining_v4.py`, `receipt.get('accounted_usd', 0)`). True spend stays bounded by the $0.75 gateway cap, but the report would understate it. Count a missing ledger at the cap and halt.
9. **Labels.** Pi `provider_error` covers cap endings and transport failures. `settle()` marks an incomplete stream `provider_cap_violation` (line 188). `invalid_pilot_receipt_sha256` in the Pi conditions is the hash of `INVALID_PI_ENVIRONMENT_PILOT.json`, not of the pilot receipt.
10. **Claude Code runner edge cases.** A final line without a newline is not parsed (lines 310-315). The captured candidate is hashed through symbolic links (lines 353-354); the finalizer now rejects such a file (lines 40-43, 198).
11. **`NEW_MAIN_SHEETS.json` contradicts itself:** `participant_permissions` says "Pending silent writer grants", `participant_access` says "VERIFIED_RESTRICTED_EDITORS_WITH_NOTIFICATIONS_DISABLED". I did not read Drive permissions. Confirm the grants produced no notification, since the requirement is no team email before approval.
12. **`RATING_FORM_GUIDE.md` names the six response fields but none of the five prefilled identifier columns.** The builder only requires the six. Decide whether the guide should list all eleven.

## 6. Verified with evidence

- **Frozen inputs and receipts.** Condition, runner, input-manifest, task-index, environment-audit, preflight, pilot-record, planned-cohort, assignment, Grok-manifest, form-schema, roster and delivered-assignment hashes all reproduce. The Pi V4 runner equals its archived copy. All 25 Python and 25 reference hashes equal the released historical packet's `FILES.sha256` and the files at their original paths, across 25 distinct historical folders. All 35 historical candidates hash-verify; 50 fresh ones are pending.
- **Deterministic joins.** The neutral item-ID rule and the ten-task Grok selection rule reproduce exactly. Task and candidate order come from SHA-256 of seed, kind and identity. Repeat builds give an identical archive hash (test).
- **Spending.** Recomputed cost equals the ledger for all four Pi ledgers. Invalid pilot $0.7204245; valid cells $0.38397525 + $0.15521625 + $0.124596 = $0.6637875; total $1.384212 of the $20 ceiling. Every settled row has total tokens = prompt + output + thinking, so no other billed category appears. The gateway admits one model and one operation, rejects cached content and non-function tools, reserves 65,536 input plus the requested output before each call, and keeps the full reservation for any incomplete response. A one-response overshoot is possible only if the provider ignores its own output limit.
- **Isolation.** Both runners assert zero host mounts and an internal-only network. The image audit passes 16 of 16 checks. Each solver directory holds exactly the instruction and the Python file (0 Lean files), and the reference folder is never copied by either runner.
- **Credentials.** The Gemini key exists only in the gateway container environment and the subscription grant only in the solver container environment; neither is written by the runners. Pattern scan of 334 private and script files: 0 hits. `private/` is git-ignored.
- **Pilots versus valid runs.** Both excluded pilots (`runs/pi`, `claude_code_outputs`) used the image with compiled benchmark modules. Their receipts are preserved, their cost is counted, and the finalizer refuses candidates under the excluded roots (test).
- **Forms.** Schema columns equal the builder's eleven. Prepared Sheet headers equal them, and all response cells are blank in the local record. `ratings/` and `rating_task_packet/` show no modification.
- **Structure.** Scripts are under `support/scripts/native_packet_generation/`, tests under `support/tests/`, evidence under `private/`; no new top-level files.

## 7. Not reviewed

- Live Google Sheets and Drive permissions (local record only).
- Docker image contents (relied on `ENVIRONMENT_AUDIT_v2.json`).
- The Gemini price table and Pi's default retry behaviour.
- `COORDINATOR_README.md` beyond a keyword pass of its native-heavy section; `README.md` and the checkpoint edits in progress.
- `RATING_FORM_GUIDE.md` beyond field-name presence.
- The diff of the latest `test_native_packet_builder.py`; the other 33 project tests.
- Claude Code cell outcomes (first cell still running) and any Pi cell after the third.
- Form V5 packets and email drafts.

## 8. Suggested order

1. Keep Pi halted; get Brando's decision on C1 option A or B; freeze the amended Pi condition for unstarted cells.
2. Fix M1 before the first cohort freeze.
3. Fix M2 and minor item 1 before any packet build or dispatch.
4. Let the Claude Code batch continue; watch its rate-limit events (minor item 2).

VERDICT: FAIL; CRITICAL_ISSUES: 1; MAJOR_ISSUES: 2; STRUCTURAL: PASS; SUMMARY: No spending, isolation, credential or label-blinding defect found, and the running Claude Code batch needs no change. Open critical: two of three valid Pi cells were ended by transient provider/transport failures (URLError; HTTP 503) because retries are off and the gateway stops all later admissions, and they are being counted as the cells' single attempts; decide the disposition and amend the Pi condition before any further Pi admission. Open major: the finalizer records such cells as ordinary missing outputs without cause, and the prepared Sheets hold rows for artifacts that will not exist with no Sheet-versus-CSV gate. The hashed builder `b2850752…` additionally had a critical file-renumbering defect that the later builder `780a3a41…` fixes (verified against all 99 prepared Sheet rows). Reviewer: Claude Fable 5.2, effort max, one round.
