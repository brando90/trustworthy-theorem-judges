# Design: persona raters from public information

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/20_predict_a_persons_ratings_from_a_persona_built_from_public_information_start_14Nov2026/DESIGN.md>

**TLDR:** Build a persona for a person from public pages, freeze it, have frontier models rate each item as that persona several times, and score the resulting rating probabilities against what the person really rated. The persona must beat controls, in particular a persona of someone else, or the experiment shows nothing. All sizes and thresholds below are planned.

**Status, 11-14-2026:** Design only. No run.

## 1. Question

Can a persona built from a person's public information predict that person's human ratings?

The rating setup is the one in [experiment 09](../09_prepare_packets_and_collect_human_ratings_start_28Sep2026/README.md): a rater compares an agent's Lean theorem statements with the gold reference statements for a Python task and gives a whole-number score `final_score_0_5` from 0 to 5.

- Person h gives rating r(h, i) for item i, an agent file.
- The persona of h gives six probabilities P(R = 0 to 5 | persona of h, item i).

How close the persona's probabilities are to the person's ratings is the measure. A persona that is only as good as a generic rater has not captured the person.

## 2. Measurements

Each person gives one rating per item, so the person's rating for an item is a single point, not a distribution. Two levels of comparison follow.

**Item level (per item, then averaged equally over the items of a person):**

| Measure | Definition | Role |
| --- | --- | --- |
| Ranked probability score (RPS) | Normalized RPS of the persona's six probabilities against the person's rating, as defined in [experiment 02](../02_design_a_judge_that_predicts_human_ratings_0_to_5_start_06Nov2026/README.md#primary-objective). Lower is better. | Primary, the repo's primary metric |
| Kullback–Leibler (KL) divergence, item level | KL(point mass at the person's rating, persona distribution) = minus the log of the persona's probability for the rating the person gave. Lower is better. | Primary, Brando's requested measure |
| Total variation distance (TVD) | 1 minus the persona's probability of the person's rating | Secondary |
| Spearman correlation | Across items, between the persona's expected rating (sum of r × P(r)) and the person's rating | Secondary |
| Pearson correlation | Same pairs | Secondary |

**Distribution level (one number per person):**

| Measure | Definition | Role |
| --- | --- | --- |
| KL divergence, distribution level | KL(Q, P̄), where Q is the histogram of the person's ratings over ratings 0 to 5 and P̄ is the persona's probabilities averaged over the same items. Both get a pseudo-count of 0.5 per bin so no bin is zero. The reverse direction is reported too. | Primary, Brando's requested measure |
| TVD, distribution level | Half the sum of absolute bin differences between Q and P̄ | Secondary |

Distribution level asks whether the persona is as harsh or lenient overall. Item level asks whether it rates the right items high and low. A persona can pass the first and fail the second, so both are reported.

Probability smoothing: P(R) from samples gets a pseudo-count of 0.5 per rating bin before any log is taken. This is fixed before the first run.

## 3. Algorithm (initial)

Run once per subject. Every model call names its harness and model; frontier models only, per the repo's rule.

1. **Fix the subject and the ratings to predict.** The subject's ratings come from experiment 09, main task only. Warm-up ratings are excluded because warm-up files are older-model outputs. The persona is built and committed before the ratings are read.
2. **Collect public information** by web search and public pages, under [PRIVACY_AND_CONSENT.md](PRIVACY_AND_CONSENT.md). Record each source as link, date, short quote and hash. Stop at 15 sources, or earlier when new searches add no new rating-relevant fact. Never open this repository or a rating sheet.
3. **Write the persona summary**, at most 400 words, each statement citing a source number: field, training, formal-methods and proof experience, views on evaluation, writing style, how demanding the person's public work suggests they are. No statement without a source; mark any inference as an inference.
4. **Freeze.** Commit the persona text, source list and hash to main, with the harness, model and date. Ratings are read only after this commit.
5. **Rate as the persona.** For each item, give a frontier model the persona and exactly what a real rater gets (the rater instructions, scoring rubric and the three item inputs: Python source, agent Lean, gold Lean). Ask for the score 0 to 5. Draw K = 10 independent samples per item. P(R | persona, item) is the sample frequencies, smoothed as in section 2. A second variant asks the model to state the six probabilities directly; it is reported next to the sampled one and not used for the decision.
6. **Score** against the person's ratings with section 2's measures, per person and pooled.
7. **Repeat** with a second frontier model rating the same frozen persona, so a result is not one model's habit. First choices: GPT-6 Astra (xhigh, Codex) and Claude Fable 5.1 (max, Claude Code); Gemini 4 Argon or Grok 4.7 where a free route exists.

Planned size for Brando: 54 items × 10 samples = 540 calls per condition per model. Five conditions (persona, rebuilt persona, name-only, generic rater, other person's persona; section 4) × two models = 5,400 rating calls, plus the persona builds. Free hardware and subscription harnesses only; no paid API without Brando's yes.

## 4. Controls

| Control | What it removes | Built how |
| --- | --- | --- |
| Generic rater | Anything a persona adds beyond a competent rater | Same prompt, with a one-line "careful computer science reviewer" in place of the persona |
| Other person's persona | Anything that is not about this person (a persona-shaped prompt, any persona-driven shift) | Another subject's frozen persona rates this person's items; average over all other available personas |
| Name-only | What the model already knows or guesses about the name, without the collected pages | The person's name and nothing else |
| Test-retest | Persona instability | The persona rebuilt from a fresh, independent run of steps 2 to 4 (new searches), then rated again; compare the two sets of probabilities and their scores. Also split the K samples in halves to measure sampling noise. |
| Rating baseline | Predicting well by guessing the common rating | A constant forecast: the pooled rating histogram of all other raters on the same items (this person left out) |
| Other human | How well one person predicts another | Where item i has a second human rating, use that human's rating as a point forecast and score it the same way; this is the ceiling to compare with |

The persona is a useful predictor only if it beats the generic rater, the other person's persona and the rating baseline. Name-only is reported to show how much comes from the model's prior knowledge instead of the collected pages.

## 5. Planned sample

- **Subject 1: Brando.** 54 main-task ratings on 25 task folders, once he has entered them. This is a pilot of one subject: an interval is reported, but no confirmatory claim rests on it alone.
- **Next subjects, one at a time,** in the order their ratings arrive and their OK is in. A subject needs at least 20 ratings to be scored alone. Raters with fewer (for example, a four-file packet) are scored only in the pooled result.
- **Pooled question:** all (person, item) pairs across the consenting subjects. The collection target in experiment 09 is 108 ratings in total, so the pooled sample is at most that unless collection grows. This is planned, not verified; the final size depends on who rates how many files.
- Uncertainty: bootstrap by task folder (items of one task are not independent), 95% intervals, for every difference between persona and control.
- Persona and control calls are paired by item, so differences are paired differences.

## 6. What counts as support, refutation, or neither

Planned, to be confirmed by Brando before the first run. The equivalence margin is an initial choice of 0.01 normalized RPS.

- **Support:** pooled, the persona's item-level RPS is below the generic rater's, the other person's persona's and the rating baseline's, each paired difference with a 95% interval below zero; and the distribution-level KL is below the generic rater's and the other person's persona's. Held for at least two rating models.
- **Partial support:** the persona beats the other person's persona and the generic rater but not the rating baseline, or the effect holds for one rating model only. This says the persona carries person-specific information that the plain base rate does not use yet.
- **Refutation:** the persona's item-level RPS difference to the generic rater and to the other person's persona has a 95% interval inside ±0.01, so a real gain is ruled out at that margin.
- **Neither:** every other outcome, including intervals wider than the margin.

A single subject (Brando) gives a first reading only. It can show whether the pipeline works and what failed, but it does not settle the question.

## 7. What would make it uninformative

- Too few ratings: under 20 for a person scored alone, or a pooled interval wider than ±0.02 normalized RPS.
- The person's ratings barely vary (almost all the same score), so any forecast near that score looks good.
- Low human test-retest or low agreement between two humans on the same items: the persona cannot beat a noisy target.
- Leakage: a source shows the person's ratings, or the model recalls the repo, the rating sheet or this study. Check the persona text and the model's sources before scoring; a leaked run is dropped and reported.
- The persona sees too little: fewer than 5 usable public sources, so the persona is close to generic.
- A persona that is persona-shaped but not person-specific: the other person's persona scores about the same as the person's own. This is the central failure to watch for.
- Retest instability: two independent persona builds give forecasts that differ by more than the persona beats the controls.
- Refusals, incomplete runs or missing items beyond 5% in any condition.
- The persona or the ratings changed after the person's ratings were read.

## 8. Reporting

Per person and pooled: all section 2 measures, every control, paired differences with intervals, sample size, rating model and harness, persona model and harness, dates, failed items. Name a person only with their OK ([PRIVACY_AND_CONSENT.md](PRIVACY_AND_CONSENT.md)); otherwise use a code. Outputs from older models are never used in this experiment's runs.
