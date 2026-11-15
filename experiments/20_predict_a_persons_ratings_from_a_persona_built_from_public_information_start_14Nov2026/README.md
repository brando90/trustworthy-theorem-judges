# Predict a person's ratings from a persona built from public information

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/20_predict_a_persons_ratings_from_a_persona_built_from_public_information_start_14Nov2026/README.md>

**TLDR:** Can a frontier model, told only a persona written from a person's public information, rate formal specification coverage the way that person does? Compare the persona's six rating probabilities (ratings 0 to 5) with the person's actual ratings, using Kullback–Leibler (KL) divergence and the repo's ranked probability score (RPS), against four controls. Brando is the first subject. This folder holds the problem and the design only; nothing has been run.

**Status, 11-14-2026:** Problem and design written. No persona built, no model run, no result. Brando's main-task rating sheet is still blank, so the first scoring waits for his ratings. The design thresholds below are planned values, not verified; Brando confirms them before the first run.

Requested by Brando on 11-14-2026 (voice): build a simulated persona of a person from public information (his own Google, Instagram and LinkedIn were his examples), get a probability distribution over ratings from that persona, and measure how far it is from his actual ratings, then do the same for the team. Start with the problem and experiment folder.

## Files

| File | Holds |
| --- | --- |
| [DESIGN.md](DESIGN.md) | Question, measurements, algorithm steps, controls, planned sample, decision rules, what would make it uninformative |
| [PRIVACY_AND_CONSENT.md](PRIVACY_AND_CONSENT.md) | What may be collected, what may be stored, and what needs a person's OK |

## Related work in this repository

- Rating packet and collection (what each rater, and so each persona, rates): [experiment 09](../09_prepare_packets_and_collect_human_ratings_start_28Sep2026/README.md). Brando's main sheet is [`Brando_Miranda__native_main_A1.csv`](../09_prepare_packets_and_collect_human_ratings_start_28Sep2026/ratings/Brando_Miranda__native_main_A1.csv), 54 rows, blank on 11-14-2026.
- Metric definitions (RPS, cross-entropy, total variation distance): [experiment 02](../02_design_a_judge_that_predicts_human_ratings_0_to_5_start_06Nov2026/README.md).
- First informal example: the simulated-Yegor dry run of 11-14-2026, where a frontier model acted as Yegor Denisov-Blanch on the rating packet using a short persona from public information. It tested the packet instructions. It is exploratory only (the persona was not frozen before the ratings were seen), so it is not evidence for this study. Its files are linked here once they are saved with the rating-collection records.
