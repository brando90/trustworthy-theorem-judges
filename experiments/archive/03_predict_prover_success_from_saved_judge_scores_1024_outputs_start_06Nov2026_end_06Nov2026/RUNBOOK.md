<!-- TLDR: Reproduce the zero-call analysis from pinned restricted Git blobs, publish aggregates only, and admit no measured model calls under the current pause. -->
# Reproduction and continuation

Run from the project root. `uv` installs dependencies into its cache; it does not change system Python. The host’s default Python had an architecture-mismatched NumPy, so the completed run uses this isolated Python 3.12 environment.

```bash
uv run --python 3.12 --with numpy==2.4.2 --with scipy==1.17.0 python experiments/03_prover_target_fsc_judge/scripts/verify.py
uv run --python 3.12 --with numpy==2.4.2 --with scipy==1.17.0 python experiments/03_prover_target_fsc_judge/scripts/analyze.py --source-repo /path/to/authorized/veribench
python3 experiments/03_prover_target_fsc_judge/scripts/render_report.py
uv run --python 3.12 --with numpy==2.4.2 --with scipy==1.17.0 python experiments/03_prover_target_fsc_judge/scripts/verify.py
git diff --check
```

The analysis reads only the revision in `config.json`, validates a complete one-to-one join, snapshots source blobs under `research_artifacts/prover_target/source/`, and writes aggregate JSON plus source hashes. It does not make model calls, change source data or use individual human ratings. Exact task split identities remain in `research_artifacts/prover_target/split_manifest.json`; only its hash is public. Source access is required for independent reproduction. Public aggregates alone are not enough to re-run the analysis.

The initial protocol is commit `24c9152`, before this statistical analysis. Source aggregate counts were already read, so no prospective-registration claim is made. Results are reproducible under fixed versions/seed; small floating-point differences across numerical libraries may occur.

## Future measured pilot

1. Resolve source extraction and adapter faithfulness with an immutable elaborated goal and independent satisfiability certificate. Retain original candidate and reference hashes. Do not admit the old name-only correspondence check as sufficient.
2. Validate the fixed-goal checker with positive, negative, inconsistent-premise, gold-proof leakage, wrong-goal, missing-obligation and forged-audit controls. Run deterministic controls first. Preserve source 117’s failed gate and any new failed gate; repairs are a new condition.
3. Select eligible solver/prover/judge systems from relevant measured evidence; record exact models, harness, effort, version, tools, seed distribution, context/time/token limits and repair count. This experiment has not selected or run a new foundation model.
4. Prepare all 12 pilot artifacts and all 36 searches plus 12 forecast calls before admission; separate training/validation/test task families and solver identities. Keep target certificates/outcomes unavailable to the forecast judge. The prompt in `prompts/binary_forecast.md` is an unused prospective template.
5. Verify live Vals organization, secret mapping, actual payer and remaining limits, and a concrete token/cost reservation. The existing pause currently blocks this study. An eligible route or explicit scoped pause change must exist before any measured call; do not reuse experiment 168’s key exception.
6. On an eligible route, run the smallest exact-transport control batch, then the declared pilot with durable remote ownership. Keep failures and missing outcomes visible, stop new admissions on systematic transport/checker errors, and never silently replay completed attempts. Freeze a new condition before expanding.

No new recurring watcher, paid run or speculative launch is created by these instructions. The current task’s actual execution is the complete zero-call retrospective analysis, with one requested Claude Fable/max subscription review.

**TLDR-end:** [ttj: prover-target study] The commands reproduce the complete historical forecasting experiment without inference spending. Fresh prover and judge measurements require a faithful goal pipeline and an eligible existing funding route.
