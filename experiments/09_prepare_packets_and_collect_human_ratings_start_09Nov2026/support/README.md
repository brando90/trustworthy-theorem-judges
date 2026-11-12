# Supporting collection records

These files support coordination and reproducibility. **They are not required to do your ratings.** [Return to the rating task](../README.md).

- [Coordinator documentation](COORDINATOR_README.md): detailed preparation, migration and utility commands.
- [Preparation and dispatch](PREPARATION_11-09-2026.md), [current takeover checkpoint](ckpt.md), [earlier checkpoint/history](CKPT_human_rating_collection.md), and [ownership](COORDINATION_11-09-2026.md).
- [Form amendments](FORM_AMENDMENT_11-11-2026.md), [column schema](RATING_FORM_SCHEMA.json), and [verified rater identities](RATER_IDENTITIES.json).
- [Raw-response restoration](RAW_DATA_RESTORATION_11-11-2026.md) and [name-first rollout](NAME_FIRST_ROLLOUT_11-11-2026.md).
- `scripts/`: packet-building, import and collection-maintenance tools.
- `tests/`: automated checks for packet construction and rating imports; no human labeling is performed here.
- `assets/`: source images and supporting material.
- `sheet_exports/`: dated before/after snapshots and raw-response provenance; current raw data stays in [../ratings/](../ratings/README.md).
- `audit/`: withdrawn coordinator additions and provenance; never treat these as participant responses.
- `forms/`: prepared forms, including Slava’s unsent CSV route.
- `drafts/`: older draft history. Edit the current working drafts in [../rating_task_packet/](../rating_task_packet/), not here.
- [Layout move record](LAYOUT_MOVE_11-11-2026.json): old/new paths and unchanged rating-file hashes.

Keep new administrative/history documents here rather than adding them to the rating task’s top level. Scripts live in `support/scripts/`; current commands and compatibility entry points use that location. Automated software checks live in `support/tests/` and run through `python3 scripts/check_project.py` from the repository root. No email is sent by this cleanup.

- [Identity and import workflow](IDENTITY_AND_IMPORT.md): how responses reach the raw data without duplicate counts.
- [Judge formulations](JUDGE_FORMULATIONS_11-09-2026.md): study-design context for agents, not rater instructions.
- [Brando’s earlier warm-up entry point](BRANDO_WARMUP.md): coordinator-specific context and prior-exposure record; the working packet is now `../rating_task_packet/`.
