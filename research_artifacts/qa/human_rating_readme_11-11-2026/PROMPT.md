Do one light quality-assurance review of this documentation consolidation. Requested model: Claude Fable 5.2, max effort; no model substitution. Builder owns edits in the shared checkout, so return findings rather than modifying files. Full access is enabled for inspection. No emails or additional model reviewers are part of this task.

Repository: /Users/brandomiranda/trustworthy-theorem-judges
Original base: 585ce8292ee1ba9ddeaf7271ba2ac50758ba2060
Exact reviewed patch: private/qa/human_rating_readme_11-11-2026/PATCH.diff
Owned paths list: private/qa/human_rating_readme_11-11-2026/FILES.json

User asks to declutter experiments/09_human_rating_collection. They questioned whether root README, RATINGS_INDEX.md and COMPLETION_STATUS.md all need to exist. Change combines those into ONE root README with clear packet entry point, named raw data links and dated completion table. Only root entries should be README.md, rating_task_packet/, ratings/, support/. Detailed source provenance moved into existing support/IDENTITY_AND_IMPORT.md. Active consumers and AGENTS/CLAUDE/Cursor guidance were updated. Historical dated snapshot and rollout docs retain historical paths/claims; do not flag these immutable records as current navigation. No packet, raw response, schema, Sheet, scientific payload or email authorization edits are intended. Preserve unrelated untracked experiments/02_probabilistic_ordinal_judge/rating_tensor_planning/ work.

Check for lost useful information, misleading counts or assignments, broken active links/anchors, contradictory current file-placement rules, unnecessary clutter, and wording that implies new data or sending authorization. Compare deleted files at the original base with the consolidated README/import guide. Scope is this small documentation change, not a fresh scientific review of the wider project. Existing check evidence: python3 scripts/check_project.py passed 33 tests; local-link existence, four-entry layout, instruction mirror and non-Markdown packet/rating file hashes passed. If additional deterministic checks are useful, run bounded focused checks. Keep final findings concise and cite exact file/line for actionable issues.

End with VERDICT: PASS | FAIL, CRITICAL_ISSUES: n, MAJOR_ISSUES: n, MINOR_ISSUES: n, and a concise summary. One round only; builder will fix findings and verify without another review.
