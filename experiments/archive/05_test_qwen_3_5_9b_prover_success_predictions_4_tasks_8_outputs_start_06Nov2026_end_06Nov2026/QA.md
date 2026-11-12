<!-- TLDR: One Claude Fable/max review passed with eight minor findings; all were addressed without changing frozen measurements or starting another review. -->
# Review and deterministic fixes

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/05_fresh_local_prover_target_judges/QA.md>

One requested light quality-assurance round reviewed commit `1a2c3ab4741c34870c515b494e2f723569d323c9`. Actual assistant and initialization records identify `claude-fable-5-1`; the running CLI arguments verify `--effort max` and `--dangerously-skip-permissions`, with `bypassPermissions` echoed. The server did not separately echo effort. The route was the existing Claude.ai Max subscription with API overrides removed, separate from the 46 measured local calls and their $0 provider charges.

**Reviewer verdict: PASS; 0 critical, 0 major, 8 minor findings. Builder resolution: FIXED, with no second model review.** Raw review output, prompts and scratch proofs remain private. The [sanitized receipt](sources/review_receipt.json) binds the evidence by hash.

| Finding | Resolution |
|---|---|
| Proof elaboration outside `Natural` was not disclosed in model prompts | Added [post-run protocol observations](PROTOCOL_OBSERVATIONS.md) and a conspicuous result caveat; no frozen prompt or outcome changed. |
| Temporary paths make duplicate proof requests differ | Disclosed the repeated-search distinction and exact prompt-token counts; no repeat-variance claim. |
| Three controls stop at text filtering | Identified the filter, context-hash and Lean/replay layers; recorded the reviewer's two separate raw-path checks as post-run diagnostics. |
| Counterexample authorship unclear | Explicitly stated that the builder wrote proof terms after frozen outcomes, then checked them; they remain separate diagnostics. |
| Historical v1 analyzer overwrites the consolidated report | Added a safe recomputation wrapper that redirects v1 Markdown and fixes its relative link while preserving both historical analyzers byte-for-byte. |
| Missing generation/target/projection hash checks | Verifier now checks both private file hashes and the public artifact projection, plus all source snapshots. |
| Literal narrative counts could become stale | Added exact support-count and role-count assertions before report rendering; changed receipts cannot silently retain stale prose. |
| Double space and stale checkpoint | Safe rendering fixes the double space, qualifies mechanical intervals, and updates the checkpoint. |

The reviewer independently reconstructed all generation, forecast and prover inputs, checked all 46 call receipts and chronological sealing, recomputed metrics with writes intercepted, and traced T04_G0 from source to result. Scratch Lean checks replayed a counterexample, proved candidate consistency, reproduced a frozen search failure, rejected a raw placeholder through the transitive `sorryAx` acceptance check, and rejected a definitionally equal but non-exact goal type. Those scratch checks are additional review diagnostics; they are not new preflight observations or measured inference.

Driver verification: both frozen file sets remain byte-identical; full manifest/hash/order/shared-budget checks pass; safe v1 recomputation preserves the consolidated report; full recomputation preserves numerical JSON; five in-memory corruption/stale-count checks reject altered evidence; project/design checks, paper build, spell-check and whitespace checks pass. The paper itself is unchanged. The safe wrapper is the supported entry point in the [runbook](RUNBOOK.md).

**TLDR-end:** [ttj: fresh local prover-target judges] The requested single review passed and all eight findings were resolved through additive disclosure and deterministic fixes. No frozen result was retried or changed.
