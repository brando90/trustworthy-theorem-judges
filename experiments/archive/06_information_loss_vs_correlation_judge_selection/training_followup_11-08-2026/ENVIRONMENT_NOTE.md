<!-- TLDR: The measured run used NumPy 2.2.6 and SciPy 1.17.1; an earlier preflight summary listed different installed versions and is not the runtime receipt. -->
# Runtime environment clarification — 11-08-2026

The machine-recorded `results/results.json` is authoritative for the measured run: Python 3.12.3, NumPy 2.2.6 and SciPy 1.17.1. A post-run probe of `/usr/bin/python3` confirmed imports from `/lfs/skampere3/0/brando9/.local/lib/python3.12/site-packages/` with those versions.

The pre-launch `results/preflight.json` summary listed NumPy 1.26.4 and SciPy 1.11.4 from an earlier dependency probe. That summary did not establish the import resolution of the later scientific worker. It remains preserved as historical preparation evidence, with this correction; do not cite it as the executed environment. No package versions were pinned in `protocol.json`.

The worker ran both synthetic control suites inside the actual numerical process before accessing the empirical data, and stored their successful receipts in `results/results.json`. The independent reconstruction and selected-resample replay used the same observed current environment and passed. The final report uses the measured versions. No scientific source, configuration, fitted model or result was changed to address this metadata discrepancy.
