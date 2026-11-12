<!-- TLDR: Recompute reports and audit immutable receipts; do not replay a completed model condition. -->
# Reproduction and receipt audit

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/05_fresh_local_prover_target_judges/RUNBOOK.md>

**Companion notes:** [Google Doc](https://docs.google.com/document/d/1zB-gYk-zU1wToS_E_carGSRGtUcF1NgZ-jWF5t1SJws)

The public repository contains code, prompts, model/dependency hashes, opaque artifact rows and aggregates. Exact input and proof reproduction requires authorized access to `research_artifacts/fresh_prover_target/`. Source snapshots are pinned committed blobs from the private VeriBench repositories; no dirty shared checkout file is an input. Four selected contexts reproduce their original exported hashes and reference-name inventories. Fifteen deterministic controls include faithful implication, consistency, counterexample, inconsistent-premise rejection, wrong goal, added axiom, placeholder, native oracle, forged log and proof-body invariance.

## Recompute existing reports

From the project root, with the original private receipts present:

```bash
python3 experiments/05_fresh_local_prover_target_judges/scripts/verify_receipts.py
uv run --python 3.12 --with numpy==2.4.2 --with scipy==1.17.0 python experiments/05_fresh_local_prover_target_judges/scripts/recompute.py
python3 scripts/check_project.py
git diff --check
```

The verifier checks both freezes, actual runtime files, exact request hashes and parsed probabilities, the eight-artifact/sixteen-forecast manifest, forecast sealing before model target calls, accepted-proof replay receipts and shared budgets. The analyzer makes no model call. Its intervals use four source-task families, never eight independent tasks. Missing probabilities or outcomes stay unavailable; full-denominator bounds include their possible losses.

The original failed condition's source, protocol and freeze remain in this experiment root. Its preflight gate rejected two output-token-exhausted responses, and it admitted no fresh artifact. The additive recovery is under `conditions/nonthinking_v2/`; both conditions share the original ceilings. The recovery changes thinking settings and prompts before any target outcome, and omits repeats to fit the remaining call allowance. It does not overwrite or retry the failed condition.

## Execution evidence

Each private condition has `launch.json`, `worker.json`, `run_state.json`, per-call request/stream/receipt files, `execution.log` and terminal `done.json`. The recovery's `done.json` also records elapsed time from the original start. Before every request, its runner checks combined reservations against 56 calls and 81,920 requested output tokens. Its wrapper uses the original four-hour deadline. Provider cost is zero; local compute time is measured. Ollama is loopback-only with cloud disabled and the exact installed weight digest recorded.

Do not invoke an old `run.py` to reproduce a completed study: model calls are not replayed, and proof-search timing belongs to the recorded condition. A new execution needs a separately named prospective condition and its own valid authorization, fixed denominator and budget. The preparation and target-control scripts are available for an isolated deterministic reconstruction; their generated files must not overwrite an existing frozen receipt. Retain initial failures and all subsequent condition identities.

**TLDR-end:** [ttj: fresh local prover-target judges] Recompute and verify the recorded evidence without new inference. A new run is a separate condition, not a retry of these outcomes.
