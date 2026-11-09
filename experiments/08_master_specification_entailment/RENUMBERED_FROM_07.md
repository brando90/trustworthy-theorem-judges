# Renumbered from 07 to 08

This folder was `experiments/07_master_specification_entailment/` on the Codex branch `codex/ttj-master-judge-overnight-1108`. Main already had `experiments/07_exp1_metrics/`, so on 2026-11-09 the branch folder was renumbered to 08 and `07_exp1_metrics` was left untouched.

| | Commit |
|---|---|
| Branch tip before the merge (old 07 folder, 81 files) | `45a148e54ef74fabc495f405e93049c4ec15a844` |
| Merge into main | `9c3f7b5e943665e9bd3ba16820e76eecdf868c8e` |
| Renumber (07 to 08, `git mv`, history kept by rename detection) | `da6cab5ea8f9ffbf51d835706457951cd4935dcd` |

Mapping: `experiments/07_master_specification_entailment/<path>` -> `experiments/08_master_specification_entailment/<path>` for all 81 files.

Check (hash compare of the git trees, 45a148e vs main): same 81 file names; 74 files are byte-identical; 7 docs differ only in the experiment number and folder path (`CERTIFICATE_PROTOCOL.md`, `CERTIFICATE_REPORT.md`, `CKPT_certificates.md`, `CKPT_forecasts.md`, `MODEL_SELECTION.md`, `README.md`, `results.md`). The old 07 versions stay in git history at `45a148e`: `git show 45a148e:experiments/07_master_specification_entailment/<file>`.

Left as `07` on purpose, because they are part of the frozen, hashed run, not references to the folder:
- `TTJ07_CERTIFICATE_AUDIT` markers inside the certificate proof bodies and `construction_manifest.json` (the checker and the recorded hashes pin these bytes).
- The `TTJ07_CHECKER_TEST_OUTPUT` environment variable name read by `scripts/test_certificates.py`.
- Temp-folder prefixes `ttj07_*` in the scripts, and the recorded outputs in `results/checker_tests.json` (a historical log of the run).
