# Human-rating collection

**Edit the task in [rating_task_packet/](rating_task_packet/).** This is the working folder Brando requested; changes here are drafts until reviewed and packaged for delivery.

| Working file | Why keep it |
| --- | --- |
| [START_HERE.md](rating_task_packet/START_HERE.md) | Task instructions and your personal Google Sheet link. |
| [human_judgements_prompt.md](rating_task_packet/human_judgements_prompt.md) | The actual coverage criteria, 0–5 rubric, spam adjustment and uncertainty rule. |
| [RATING_FORM_GUIDE.md](rating_task_packet/RATING_FORM_GUIDE.md) | What each sheet column means and which responses are required. |
| [EMAIL_INSTRUCTIONS_V0.md](rating_task_packet/EMAIL_INSTRUCTIONS_V0.md) | Brando’s editable invitation draft; review in chat before sending. |
| [ratings.csv](rating_task_packet/ratings.csv) | Blank local form for inspecting/editing the packet; not collected responses. |
| [warm_up_01_median/](rating_task_packet/warm_up_01_median/) and [warm_up_02_greatest_common_divisor/](rating_task_packet/warm_up_02_greatest_common_divisor/) | Actual Python, reference and six candidate files copied unchanged from the FormV3 packet. |

**Draft inconsistencies still to resolve:** the email draft says score column J; the current name-first Sheet uses K. The older START_HERE draft and rubric submission paragraph must be reconciled with the current form guide before dispatch. Their wording was preserved during this move. Use the personal Sheet linked in START_HERE.md; do not copy the historical rubric’s template. The scoring rubric itself is unchanged.

## Collection records

- [ratings/](ratings/README.md): original responses; [RATINGS_INDEX.md](RATINGS_INDEX.md): people, Sheets and data links.
- [COMPLETION_STATUS.md](COMPLETION_STATUS.md): who has finished and what remains.
- [support/](support/README.md): import procedures, study design, coordinator notes, configuration, history and software tests.
- `scripts/`: packet-building and import tools. Stable command paths are retained.

The working packet is for Brando’s coordinator practice: he has already viewed other raters’ warm-up answers. Delivered archives remain unchanged. No email is sent by editing this folder.

Folder names spell out the task. Each `agent_lean/` folder contains `agent_1.lean`, `agent_2.lean` and `agent_3.lean`. The sheet’s historical `item_id` is only a stable record key; its folder and filename columns give the current paths. See [path mapping](support/WARMUP_PATHS.json).
