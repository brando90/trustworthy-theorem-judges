# Current form verification — 11-11-2026

All 12 existing personal Google Sheets were migrated to the same eleven-column form and read back exactly. The current raw CSV tables match those response values. Five prefilled identity fields are followed by score, combined attestation, minutes, confidence, rationale and problem note. Internal IDs are hidden in Sheets, retained in CSVs.

- `before.json`: exact sheet metadata and cells immediately before this revision.
- `after.json`: applied requests, expected response tables, returned cells and equality checks.
- `restoration_sources.json`: original participant context, source filenames and hashes.

Rylan's six problem notes, Sri's six times/confidences/rationales and one problem note, and Yegor's six confidence/rationale entries were restored verbatim from pre-removal source snapshots. No missing answer or per-file time was inferred. Sri's recorded times sum to 22 minutes; his separately reported approximate session time was 25 minutes. Rylan reported about an hour for the session; his per-file times remain blank. Session estimates are not six new observations. The historical checklist answers, base scores and Lean-familiarity labels in those snapshots are not columns of the current form; they remain only in the dated pre-removal snapshots and the normalized analysis copies. In `after.json`, `expected` stores numeric scores as JSON numbers while the raw CSVs keep every cell as text; compare the read-back `formattedValue` cells with the CSVs for an exact check.

The 15 numeric warm-up ratings and three N/A entries are unchanged. Historical AI use remains unknown where unreported; combined attestations are blank. New instructions apply prospectively. Prior reference corrections and participants' exposure histories remain material differences between rounds; do not pool them as identical conditions.

Older dated folders are provenance, not current participant instructions. The active instructions are in `../../../rating_task_packet/`, and raw exports in `../../../ratings/`.

## Final verification

Native browser inspection covered all twelve Sheets: response columns are readable, long participant notes wrap, and the header row stays visible. The working packet and all thirteen replacement archives use the current field guide; candidate-to-sheet mappings match, and every Lean/Python file matches the accepted released source set. No references were edited or newly proved in this revision.

One requested independent light review used subscription-authenticated Claude `claude-fable-5-1` with `--effort max` and bypass permissions. Verdict: PASS with minor fixes applied. The review corrected stale coordinator links/score-cell directions and clarified source history; the parent restored the editable pilot email's established signature. Rationale's recommended/optional overlap is intentional and now documented. Time input accepts numeric minutes or ordered ranges; raw unparseable responses must be preserved and clarified, never guessed. No second model-review round was run.

The exact private review and model launch/output receipts are in `research_artifacts/qa/human_rating_form_v5_11-11-2026/` at the repository root. Team dispatch remains prepared and unsent, pending Brando's pilot, exact-text approval and explicit send instruction.
