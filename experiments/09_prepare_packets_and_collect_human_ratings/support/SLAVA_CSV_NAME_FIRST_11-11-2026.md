# Slava Naprienko — prepared CSV return route

Slava uses an emailed CSV rather than a Google Sheet. This is a blank prepared form, not returned ratings or a new assignment; it adds zero observations.

- [Current eleven-column form](forms/Slava_Naprienko__warmup_V01.csv).
- [Current packet](../../../research_artifacts/09_human_rating_collection/preparation_11-09-2026/packets/FormV5/VeriBench_warmup_V01_FormV5.zip).
- [Shared field guide](../rating_task_packet/RATING_FORM_GUIDE.md).
- [Current exact email review](../../../research_artifacts/09_human_rating_collection/preparation_11-09-2026/REVIEW_TEAM_EMAILS_FORM_V5.md).

The name and stable ID are prefilled as Slava Naprienko and V01. All six answer rows remain blank. The packet uses descriptive folder/file paths, the same scoring rubric and fields as the live Sheets, and explicitly tells him to return ratings.csv by email. It is prepared and unsent; exact-text approval and a send instruction are still required.

The original delivered VeriBench_warmup_V01.zip and the earlier eighteen-column template under forms/11-11-2026_name_first/ remain immutable history. They are superseded for the next dispatch.

## Other template paths checked

- `support/scripts/revise_rating_packet.py` builds prospective personal forms with verified names first and stable IDs second; it leaves original archives unchanged.
- `support/scripts/make_team_packet.py --rater V01` prefills both identity columns when a separately authorized main assignment is prepared. Without `--rater`, its output is an unassigned template, not a ready personal delivery.
- `support/scripts/legacy/make_rater_zip.py` packages frozen scientific files and a personal-sheet pointer; it does not generate a CSV form. Its historical source templates and delivered archives were not rewritten.

The dated source snapshots, earlier packets, and earlier blank-form templates retain their original layouts as provenance. Use the current schema for new forms; do not import these prepared blank rows as completed ratings.
