# Combined AI-assisted rating attestation — 11-11-2026

Brando requested one required attestation instead of separate model-assistance and independence fields. New ratings use localized AI help; the human performs the comparison and selects the score. Exact wording:

> I used AI for localized assistance. I personally compared the specifications and chose the final score; I did not delegate the rating task to AI.

All 12 live Sheets were changed after fresh metadata and cell reads. The two old response columns were blank in every table. The new field is `ai_assisted_rating_attestation` with yes/no/unsure choices; it is deliberately distinct from the earlier independence-only field. Every new answer remains blank. Earlier ratings are grandfathered under their earlier conditions; no AI use was inferred.

`before.json` preserves complete bounded cell data and metadata. `after.json` records requests and verified readback. Every retained identifier/score cell, including its notes, formatting and validation, matched exactly. Current raw CSVs were exported from that readback and their hashes updated. The existing 15 numeric ratings and three N/A entries are unchanged; no observations were added. Scoring sections, candidate/reference/Python bytes and delivered archives are unchanged. Builders apply this layout to future packets. No collaborator email was sent.
