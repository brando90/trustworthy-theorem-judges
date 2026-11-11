# Required-only rating form — 11-11-2026

Brando requested removal of optional columns from participant forms and current raw data, with the scoring rubric unchanged. The active schema now has five prefilled identifiers and three responses: final_score_0_5, model_assistance and independent_rating_attestation. Both optional and recommended response columns are removed; they are not made mandatory.

All 12 live Sheets and primary ratings/*.csv tables were updated together. before.json records complete pre-change live tables and metadata; the CSV copies preserve the previous local raw files. after.json is the verified post-change live data. Every retained cell and row order matches its source. Added historical assistance/attestation cells are blank, meaning unknown, never no assistance or yes. Existing N/A scores remain N/A; their original reference-problem notes remain in this archive. No historical rating is rejected for missing metadata introduced later.

The participant rubric’s coverage definition, checklist, 0–5 base scale, spam adjustment and uncertainty rule are unchanged. Only the submission paragraph now requests the three required responses. Archived previous instruction files preserve the earlier wording. New source archives are versioned; delivered archives stay unchanged.

The pre-change tables contain 15 numeric rows with both base and final scores; the two scores are equal in all 15. This is a descriptive check of recorded values, not evidence to remove the spam-adjustment rule. No final score was edited in this change. Reference problems now go by email rather than a routine extra form column.

Future packet builders use the required-only schema and submission paragraph. Normalized historical analysis exports remain historical, separate from the primary raw tables. Current CSVs reproduce live values exactly for the retained schema.

Verification: all 12 Sheets inspected visually; 31 collection tests and project/design checks pass; paper build succeeds. Primary CSV headers, retained cells and manifest hashes checked against post-change live snapshots.
