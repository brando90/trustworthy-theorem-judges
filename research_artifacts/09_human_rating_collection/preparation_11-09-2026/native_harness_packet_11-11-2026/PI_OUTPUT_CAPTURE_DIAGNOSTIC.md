# Pi output-capture diagnostic

**TLDR:** All 18 terminal attempts received the exact frozen instruction naming the same output path captured by their runner. No capture-path mismatch was found; zero required artifacts were captured.

The machine-readable [evidence](PI_OUTPUT_CAPTURE_DIAGNOSTIC.json) binds each task’s prompt, manifest, native session and runner hash, plus exact source line references. All 18 persisted user messages contain the frozen instruction verbatim.

Recorded Lean writes are temporary `test.lean` or `scratch.lean` files, `/tmp/test_warn.lean`, or `Veribench/test.lean`. No recorded tool operation names a task’s required output filename. For example, `all_prefixes` repeatedly overwrote `scratch.lean`; its final write was a 399-character helper lemma `forIn_list_map`, and the following Lean check failed. `base32` used temporary scratch files and ended with provider `MAX_TOKENS`. Neither is evidence of a completed final artifact at a different named path.

The collector did not retain whole workspace snapshots, and the terminal containers are gone. Therefore the defensible statement is **zero captured required-path submissions**, not that no Lean text was ever written or that all possible alternate paths were exhaustively ruled out. This is a read-only audit; no candidate was reconstructed, no exclusion rule changed, and no model call was made.
