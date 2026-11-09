# Experiment07 certificate checkpoint

## Current state
- Owner: remote certificate worker; root owns inference, scoring and integration.
- Canonical home: experiments/07_master_specification_entailment/.
- Six task families, eight controls each; 48 primary forecasts planned by root.
- No measured forecast calls have been made by this worker.
- inputs.jsonl contains only opaque IDs and statement declarations.
- construction_manifest.json records proposed labels before checker compilation.
- Lean pin: leanprover/lean4:v4.22.0; observed commit ba2cbbf09d4978f416e0ebd1fceeebc2c4138c05.
- Trusted checker elaborates one proof term, checks the exact target, replays the theorem through the kernel and traverses transitive axioms.
- Certificates finalized: 18 checked positives, 18 checked negatives, six checked inconsistencies, six unsupported axiom declarations.
- Final outputs saved: labels.json, certificate_validation.json, checker_tests.json, CERTIFICATE_REPORT.md; all nine tests pass.
- Next command: python3 scripts/verify_controls.py --verify-existing --output /tmp/ttj07-certificate-replay.json.
- No GPU ownership; no provider spending; one-thread Lean compilation.
- No commits by this worker; root coordinates one shared clone and review-only branch.

## Event log
- 11-08-2026 (PST): Created deterministic construction and exact-goal kernel checker; first development compilation caught source/term layout errors before any forecasts.
- 11-08-2026 (PST): Final construction verified (60 theorem audits), nine tests passed and immutable replay reproduced all labels; inference integration handed to root.
