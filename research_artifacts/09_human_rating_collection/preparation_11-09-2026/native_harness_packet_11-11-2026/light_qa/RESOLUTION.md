# Resolution of the single light review

**TLDR:** Implementation findings are fixed and 66 project tests pass. Generation and final packet/Google Sheet equality checks are complete; the prepared packets remain unsent. The original REVIEW.md is unchanged.

Builder/coordinator: Codex. Reviewer: Claude Fable 5.2, requested maximum effort, verified subscription CLI and actual model. This is an opposite-company implementation review; the fact that one benchmark solver is also Claude does not change the builder/reviewer roles. The first invocation reached its 35-turn limit before a verdict; the same session continued for at most eight tool turns to finish this one review. No new review round is scheduled.

| Finding | Disposition |
| --- | --- |
| C1: transient provider failures end Pi cells | Prospective condition V5 adds at most two HTTP 503 retries, with 5s/15s backoff, each counted against the original 40 provider requests, 1,800s, $0.75/cell and $20 global ceiling. V6 lengthens only the response timeout to 600s within the unchanged task limit. Existing terminal attempts remain unchanged; provider/transport failures are explicit infrastructure exclusions, not solver-quality failures. This authorized operational choice needs no repeated user approval. Unknown interrupted requests retain their full cost reservation; we do not assume no tokens were generated merely because no response arrived. |
| M1: missing causes/disposition absent | Fixed: finalizer hashes gateway evidence, records typed missing causes and requires an exact infrastructure-exclusion disposition before freezing. Tests cover request caps, HTTP errors, timeouts, missing ledgers and invalid dispositions. |
| M2: prepared Sheet rows exceed returned artifacts | All three Sheets are undispatched preparations. Parent will reconcile each with actual packet rows, preserve any intervening response, verify exact live readback and require a recorded Sheet/CSV equality gate before release. Fixed verifier records hashes/equality and keeps release_ready=false until exact readback matches. Final live reconciliation completed:54/4/4 actual rows match exactly, obsolete planned rows cleared after fresh blank-response checks; all three receipts are release_ready=true. |
| S1: subset renumbering | Fixed before any new packet build: full planned 85-cell display mapping is retained and hash-bound. Passing filtered-path regression test. |
| Minor1: incomplete identity-token scan | Fixed family/vendor checks plus specific Pi attribution phrases; no scientific-byte redaction or silent exclusions. |
| Minor2: rate-limit event monitoring | Execution owner reads actual native events, preserving allowed status/utilization/no-overage evidence and stopping new admissions on authentication/allowance errors. No account switch may reset a scientific attempt. |
| Minor3: old-path alias | Removed the temporary ignored alias after both drivers and watcher finished; all 66 project checks pass without it. The current home is 09_prepare_packets_and_collect_human_ratings. |
| Minor4: Python assertions | Actual launch uses non-optimized Python; PYTHONOPTIMIZE is unset. Frozen running runner bytes remain unchanged. Future runner hardening must be versioned rather than edited under an active frozen condition. |
| Minor5: egress/grant exposure | Retain the source-only environment boundary and native client grant mechanism. Review found no direct network/credential tool commands. Inspect every terminal trajectory for out-of-band calls before accepting its packet provenance; any anomaly stays explicit. No claim that malicious solver code is cryptographically prevented from using its own grant. |
| Minor6: resource/input differences | Disclosed in coordinator contract and conditions; this collection does not establish a causal harness comparison. |
| Minor7: infrastructure before model call | Covered by explicit missing-cause/disposition fix, with no fabricated files or scores. |
| Minor8: absent cost ledger defaults to zero | Worker added a versioned continuation-driver guard: missing ledger/accounted cost reserves the full cell cap and halts, preserving the original global ceiling. |
| Minor9: coarse native status labels | Preserve raw status; finalizer adds evidence-backed cause. Condition metadata hashes the invalid-pilot record, retained under its original key; no receipt hash substitution. |
| Minor10: terminal-stream/symlink edge cases | Finalizer rejects symlink candidates. Raw streams remain preserved for terminal evidence reconciliation; any missing/incomplete native metadata is a limitation, not inferred success. |
| Minor11: contradictory sharing metadata | Corrected NEW_MAIN_SHEETS.json. UI Notify people was unchecked; successful access updates were verified by Drive metadata for RylanSchaeffer@gmail.com and vatsava@gmail.com. No invitation email sent. |
| Minor12: identifier names absent from guide | Current guide now explicitly names the five prefilled identifiers. Field meanings/order/requirements and rubric unchanged; delivered archives preserved. |

Deterministic verification: python3 scripts/check_project.py passed all 61 tests (including 28 native-packet tests), design, mirrored instructions, source hashes, official style and paper inputs. git diff --check passed. Source hashes follow; publication receipt will be appended after landing. The continuation process ended at its bounded deadline after saving the complete review; its exit receipt is preserved. Review does not establish candidate correctness or human agreement.

## Fixed implementation hashes

- `scripts/native_packet_generation/build_packet.py`: `f6125194efb40fccf1d2809de854834f3cf25cfff45dd91e6efc02036faede8f`
- `scripts/native_packet_generation/claude_code_runner.py`: `7bff1a4ecbcd049c06ea7591edfd8cb22c058f663a555139fe0ef94723575cce`
- `scripts/native_packet_generation/finalize_cohort.py`: `d69f2480e882d8897a652f0d19e2be0990417283e24da5109b5c2307b0aaf2ae`
- `scripts/native_packet_generation/pi_runner.py`: `d2be5ac2a81b97f0f003b5bb493dacfa618f76719ff1cc73ac733c266b6d1c04`
- `tests/test_native_cohort_finalizer.py`: `10a6d092f0828e530a99cea25e998e78f80dde2221a261ca94746384dcbecc0b`
- `tests/test_native_packet_builder.py`: `916576759334a0e389cda31a40c801a3065f62177d9de2781be6d666bd9243f8`
- `tests/test_native_pi_budget.py`: `16195dd926a5b1d61b2137f6aea4766868ba59af658f46d867655c11b5649b51`

Paper build verification also passed with no overfull boxes or unresolved references; the canonical PDF did not change. Implementation landed on main as 58a6c5d; final packet release remains pending.

Follow-up implementation verification, 11-11-2026: commit `0eda12f` passed all 62 project tests, including the observed native per-response output-cap regression. Current finalizer SHA-256: `ae497447dfa00f6e465f7969ace7c1e48ed471b08f49b5c4ef1c49e212ea7664`. Ten FormV6 warm-up archives preserve scientific bytes and scoring; nine fresh live Sheet readbacks matched all 54 stored item rows exactly. Six pending warm-up email bodies are unchanged and rebound to the verified replacement archives. No email sent; main generation and final release checks remain pending.

Follow-up implementation verification, 11-11-2026, 7:34 PM Pacific: commit `8d1a550` passed all 65 project tests. Current finalizer SHA-256 is `5225ce81550da0d5defa93e2b6ec915f63d5971c9e057d7995a954880225c1fa`. Two original Pi conversations survived host-wrapper loss; hash-bound native session/model/effort/deadline/ledger evidence admits only their explicit recovered no-file outcomes, with the 40-request-cap outcome retained separately from the supervision incident. Tests reject changed starts, deadlines, effort, request/cost limits and status-bypass attempts. No extra reviewer round; final generation and release checks remain pending.

Event 11-11-2026, 7:48 PM Pacific: commit 3730b54 is pushed. The narrow Pi native length/MAX_TOKENS classification and regression test passed all 66 project checks; finalizer SHA-256 6f9113dc1d46e3ec97a42d9f81b9143f980e6e1607a894234464cd736e6c8bcb. The CC batch is fully terminal (19 real files, six no-file response caps); its final source/model/hash and 221-tool-call lexical audit passed. Pi output-path audit found no prompt/capture mismatch in 18 terminal sessions; whole workspaces were not retained. No new review round or model calls for these audits. Final packet gate remains pending seven Pi attempts.

Event 11-11-2026, final packet checks: all 50 new attempts are terminal, and the final availability ledger retains all 85 planned combinations (54 actual files,31 missing). All three ZIP payloads, manifests and blank response fields passed the independent byte audit. Actual live Google Sheet values match the corresponding 54/4/4-row CSVs exactly. Editable main packet and named raw snapshots are promoted; eight team messages are prepared and unsent. All 66 project tests passed after promotion and alias removal; no new reviewer round was run.

Publication receipt: final packet preparation pushed as 5679b6b8f42c67240fdd2a45a2699a37f08472b3; all 66 tests and paper build passed. Companion cleanup 1a03b9a is its child. Final scientific bytes and live Sheet equality are recorded in FINAL_PREPARATION_RECEIPT.json. Team packets remain unsent.
