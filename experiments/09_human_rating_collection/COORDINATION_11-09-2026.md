# Single coordinator for human ratings and judge development

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_human_rating_collection/COORDINATION_11-09-2026.md>

**TLDR:** Prepare human grading task is the sole coordinating chat for this collection and the practical human-rating judge using methods 2 and 4. The former Best human-rating judge chat handed its work to that owner; ending its coordination does not mean collection or judge validation is complete.

## Ownership decision — 11-09-2026

Brando explicitly requested one owner and a `done` title for the redundant chat.

| Role | Chat | Responsibility |
| --- | --- | --- |
| Sole coordinator | [Prepare human grading task](codex://threads/01a1a8f9-dcb7-7381-9368-91d6e51faffd) | Packet preparation, recipient-specific drafts, authorized dispatch, assignments, collection, and the practical judge comparison using methods 2 and 4. |
| Handoff complete | [Done — judge work handed to human-rating task](codex://threads/01a1b4c5-657e-7043-9b4f-69f936c55fdf) | Evaluator and plans preserved; unfinished work transferred; duplicate coordination ended. |
| Separate existing implementation task | [Matched comparison and evaluation-panel work](codex://threads/01a1c18b-2d23-7f22-9ff8-5bc8714a0ef0) | Its assigned total variation distance update remains separately owned; this consolidation does not interrupt or duplicate it. |

The outgoing chat acknowledged the transfer and published its handoff in commit `9fa35f6`. Both chat titles were updated and verified on 11-09-2026. No new fitting or inference job was started by that chat before transfer. Its [judge-development handoff](../02_probabilistic_ordinal_judge/CKPT_HANDOFF_11-09-2026.md) records the implementation revisions, remaining tasks and execution state. The sole coordinator owns subsequent decisions and may delegate bounded work without creating a second coordinator. Future agents must check this record and the latest handoff before changing shared files or launching an overlapping experiment.

## Work retained by the sole coordinator

- **Human-rating collection:** follow [the preparation record](PREPARATION_11-09-2026.md) and the ignored private preparation checkpoint. Personal rating is ready. Team dispatch still needs the remaining recipient access checks, text review and explicit send instruction; qualification and outstanding assignments remain collection work. Previously delivered packets and the approved participant prose retain their existing contract.
- **Practical judge:** inherit the [methods 2 and 4 priority plan](../02_probabilistic_ordinal_judge/PRIORITY_2_VS_4_11-09-2026.md), native-probability evaluator, and the outgoing chat's remaining implementation/experiment requests. The six-category probability evaluator is preparation, not a fitted or validated new judge. Inspect the handoff and completed comparisons before launching anything.
- **Common evaluation:** normalized ranked probability score remains primary; cross-entropy and total variation distance are secondary. Preserve completed experiments' frozen protocols and compare both training objectives with the same held-out evaluation and matched budgets.
- **Data and funding:** preserve the inherited collection's evaluation-only role for the new condition, sealed ratings, prior exposure, participant privacy, and existing inference budgets. The authorized request to use existing data does not make previously inspected data fresh or release sealed ratings.
- **Project boundaries:** trustworthy-theorem-judges owns this application and collection. The sister judges-dont-need-psychometrics-or-corr project owns the general objective comparison; VeriBench owns the actual formal prover and benchmark-reference work. Historical migration ownership is not a second collection coordinator.

## Completion meaning

`Done` on the outgoing chat means **its handoff and duplicate coordination are finished**. It does not mean the human ratings are complete, the team emails were sent, or either training objective has produced a validated judge. The current preparation and judge-development checkpoints carry those unfinished tasks forward.
