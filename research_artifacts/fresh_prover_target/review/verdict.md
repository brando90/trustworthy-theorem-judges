All evidence is in hand, and the background Lean scratch checks passed. Here is the review.

**Model identity:** Claude Fable 5.1, model id `claude-fable-5-1`, effort max, launched non-interactively with permissions bypassed, as recorded in the private review launch receipts.

## Verdict

```
VERDICT: PASS
CRITICAL_ISSUES: 0
MAJOR_ISSUES: 0
MINOR_ISSUES: 8
Reviewed commit: 1a2c3ab4741c34870c515b494e2f723569d323c9
```

The negative feasibility result is faithfully recorded. Fixed-goal transport, kernel replay, pins, caps, chronological sealing, the full eight-artifact denominator, duplicates, missingness, and the public text all check out. No file was edited; no measured inference was run.

## Minor findings

1. **Judge-facing procedure omits a namespace detail that cost two of six prover attempts.** Candidate proofs are elaborated outside `namespace Natural` with no `open`, see `conditions/nonthinking_v2/scripts/checker.py:110`, so unqualified `GoldSpec` fails. The prover prompt and both judge prompts never say this. Receipts for `prove_T01_G0_1` and `prove_T04_G0_1` died on "unknown identifier 'GoldSpec'". No outcome changes, since both unique statements have checked counterexamples, but the judges forecast a procedure with an undisclosed weakness. Fix: one sentence in `PROTOCOL.md` and the nested protocol naming the elaboration scope as part of the frozen target definition.
2. **Prover prompts are not a pure function of the statement.** The fixed-tactic error tail passed at `conditions/nonthinking_v2/scripts/run.py:242` embeds a random `candidate_*` temp path from `checker.py:117`. The duplicate pair T01_G0 and T01_G1 therefore received different prover prompts, with prompt token counts 898 and 899, and produced different proof attempts. Fix: document in the recovery protocol that the duplicate is a repeated search, not a byte-identical replay.
3. **Three filter controls never reach the kernel path.** `placeholder_rejected`, `native_oracle_rejected`, and `audit_forgery_rejected` in `scripts/target_checks.py:66-68` all stop at `proof_guard_rejected`, as `results/target_checks.json` shows. The protocol table at `PROTOCOL.md:30` lists them beside the kernel-level rejections without distinguishing the layer. My scratch run confirmed the kernel path independently rejects a raw `sorry` theorem via `sorryAx` and a definitionally-equal but unfolded goal type. Fix: label the three as filter-level in the text, and optionally record the two raw-path checks as a clearly post-hoc diagnostic.
4. **Counterexample authorship is unstated in public text.** `results.md:42` says the diagnostics "checked 2/2 counterexamples" but not that the proof terms were hand-written by the builder after outcomes, as `scripts/diagnose.py:12` reading `diagnostic_proposals.json` implies. Fix: add "proof terms written by the builder after the frozen outcomes".
5. **The v1 analyzer overwrites the consolidated report.** `scripts/analyze.py:122` writes the experiment-root `results.md`, the same file `scripts/report.py:63` produces. Running the v1 analyzer after the runbook sequence silently replaces the consolidated report. The committed `results/v1_results.md` matches the analyzer output except for a hand-edited link on line 28. Fix: point the v1 analyzer at `results/v1_results.md` with the correct relative link, and list it in `RUNBOOK.md`.
6. **Verifier gaps.** `scripts/verify_receipts.py` never checks `generation_receipt.json` and `target_receipt.json` hashes against the private files, nor the `artifact_hashes.json` projection. I checked all three by hand and they pass. Fix: add the three assertions.
7. **Hardcoded narrative numbers.** `scripts/report.py:35,37,43,49,57` embed literal counts such as "6,843", "3,157", "five statements", and "Fourteen of sixteen" instead of deriving them from `summary.json`. Correct today, but a receipt change would leave stale prose. Fix: format from the summary dictionary or assert equality.
8. **Housekeeping.** Double space at `conditions/nonthinking_v2/results.md:28`, from `scripts/analyze.py:118`. `CKPT_fresh_judges.md:4,14` still say the review is pending. The scratch directory I created under `private/fresh_prover_target/review/scratch/` is ignored and can be deleted.

Already public elsewhere, so not a finding: `sources/provenance.json` lists private-repository paths and solver names for the four tasks, but experiment 04's plan, results, and script already name them.

## Checks actually run

- **Git state.** HEAD equals the reviewed commit. Every frozen v1 file is byte-identical to c2d216b and every frozen v2 file to 0445889. `git diff --check` is clean over the experiment and routing diffs. The merge touches only one timestamp line in experiment 04. Working tree clean before and after. `private/` is ignored with zero tracked private files.
- **Project checker.** `python3 scripts/check_project.py` passed. The paper build was not run because no paper file changed.
- **Recomputation with writes intercepted.** The receipt verifier reproduces `verification.json` byte-for-byte. The v2 analyzer reproduces `analysis.json` and the nested `results.md` byte-for-byte. The report script reproduces `summary.json` and the root `results.md` byte-for-byte. The v1 analyzer reproduces its `analysis.json`; see finding 5 for its markdown.
- **Hash bindings, 22 checks, all pass.** Generation, forecast, and target receipts bind the private artifact, forecast, and target files. Launch receipts bind both public freezes and both wrappers. The v2 freeze binds the v1 freeze. Provenance binds all 21 pinned source blobs and the case manifest. Diagnostics hashes bind the private proposals and result receipts.
- **Independent input reconstruction.** All 8 generation requests equal Python source plus interface only, with no gold. All 16 forecast requests equal Python, interface, candidate, and gold, with no context module, proof, certificate, or outcome text. All 6 prover requests start with the frozen context and exact goal. Every system prompt equals its committed prompt file, with think flags and token caps as configured.
- **Receipt audit of all 46 calls.** Model, digest, seed, context size, and temperature match per request. Output counts never exceed caps. Four token-budget failures: two in the v1 thinking preflight and two J0 forecasts on T01. All forecasts finished before the seal at 23:24:08 UTC; the first prover call started at 23:24:40. v2 was frozen at 23:17:29, launched after the v1 terminal receipt at 23:18:58, and the shared elapsed time of 905.62 s, requested tokens of 49,152, and observed tokens of 9,777 recompute from receipts.
- **Lean kernel replay in a scratch directory, frozen receipts untouched.** Rebuilt trusted contexts for T04_G0 and T01_G0. Reproduced the fixed-tactic consistency rejection. Explicit witnesses prove consistency for both statements, so the operational zeros come from the false coverage half, which the replayed counterexample confirms with an identical record and candidate hash. A raw `sorry` theorem is rejected through the `sorryAx` axiom check; a defeq-but-unfolded goal is rejected with exact-type false. The pinned toolchain's `Lean.Replay.addDecl` calls the kernel `addDeclCore`.
- **Source-to-result trace, T04_G0.** Pinned Python and interface, generation receipt, statement asserting only pointwise equality of the two functions, context hash, two zero forecasts with recorded reasons, rejected tactic and model proofs with genuine Lean errors, target 0, accepted counterexample, and the matching public rows.
- **Statistics.** Valid bootstrap draws of 6,843 and 9,375 match the expected empty-draw rates for one and two observed families; the full-denominator bound formula and all baseline losses recompute; correlations are correctly unavailable under constant classes.

Next steps for the builder, graded: fix findings 1, 4, and 8 in text `[p 9/10]`; add the verifier assertions from finding 6 `[p 8/10]`; redirect the v1 analyzer output per finding 5 `[p 7/10]`; derive report numbers per finding 7 `[p 6/10]`; label filter-level controls per finding 3 `[p 6/10]`; note the duplicate-search caveat per finding 2 `[p 5/10]`.

**TLDR-end:** [ttj: fresh local prover-target judges review] Experiment 05 at commit 1a2c3ab passes the one requested cross-company review with zero critical and zero major issues; eight minor text and script fixes are listed with exact locations, all verifiable deterministically without new inference.

**Snapshot:**
```
VERDICT: PASS  CRITICAL_ISSUES: 0  MAJOR_ISSUES: 0  MINOR_ISSUES: 8
git diff --stat c2d216b HEAD -- <v1 frozen files>   (empty = identical)
git diff --stat 0445889 HEAD -- <v2 frozen files>   (empty = identical)
[IDENTICAL] experiments/05_fresh_local_prover_target_judges/results/verification.json
[IDENTICAL] .../conditions/nonthinking_v2/results/analysis.json
[IDENTICAL] .../conditions/nonthinking_v2/results.md
[IDENTICAL] experiments/05_fresh_local_prover_target_judges/results/summary.json
[IDENTICAL] experiments/05_fresh_local_prover_target_judges/results.md
PASS forecast input T04_G0 J1 == reconstruction; no context/proof/outcome leakage
[OK ] T04_G0 explicit witness Nonvacuous: accepted=True axioms=[]
[OK ] T04_G0 frozen counterexample proposal replays: accepted=True (record equal: True)
[OK ] T04_G0 RAW sorry theorem: status=kernel_replay_rejected axioms=['sorryAx']
[OK ] T04_G0 RAW defeq-but-unfolded type: typeExact=False typeDefEq=True rejected
Project checks passed: design, mirrored instructions, source hashes, official style, and paper inputs.
```
