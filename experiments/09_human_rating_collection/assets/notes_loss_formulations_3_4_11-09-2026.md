# Handwritten notes: loss formulations 3 and 4

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_human_rating_collection/assets/notes_loss_formulations_3_4_11-09-2026.md>

**TLDR:** The note conjectures that proper-loss selection or training could outperform correlation objectives and asks to compare both. It distinguishes validation-based selection (3) from training-loss optimization (4), followed by validation-based hyperparameter choice.

Source: Brando Miranda's [original photograph](notes_loss_formulations_3_4_11-09-2026.jpeg), supplied on 11-09-2026. Original path: `/Users/brandomiranda/Downloads/WhatsApp Image 2026-11-09 at 10.44.48 (2).jpeg`. See [image provenance](formulations_11-09-2026_provenance.json).

## Transcription

“But I don't think (2) is needed! I conjecture:

1) (3) + (4) gives better (eval) results (since it uses general [crossed-out text] ML knowledge, instead of a [unclear phrase about human correlations]).

2) (3) + (4) is more ‘principled’ / or … at least it's easier to think about, since it uses the (successful) framework of ML learning (not necessarily ‘contrived’ learning theory).

3)” [no text follows this third item]

**(3)**

\[
P_j^{\widehat{AI}_j}(\cdot)
=\operatorname*{argmin}_{AI_j\in\Theta}
\left\{\operatorname{Loss}\left(P_j^{\widehat{AI}_j}(\cdot),P_j^H(\cdot)\right)\right\}.
\]

Annotations: “constrained/helped by train data” \(S^{\mathrm{tr}},R^{\mathrm{tr}}\); the loss is “on val set,” \(S^{\mathrm{val}},R^{\mathrm{val}}\).

“Or what I think ppl/we do more in practice (we train, using the train set and choose hps on val w historical hps…)”

**(4)**

\[
P_j^{\widehat{AI}_j}(\cdot)
=\operatorname*{argmin}_{AI_j\in\Theta}
\left\{\operatorname{Loss}\left(P_j^{\widehat{AI}_j}(\cdot),P_j^H(\cdot)\right)\right\}.
\]

The loss is annotated with \(S^{\mathrm{tr}},R^{\mathrm{tr}}\).

“→ (4) is more similar to what we do in practice. Do a [‘pre’ inserted above] training run on ‘all the data’. So comparing to (2) feels especially important, but, in our setting with such small data, I wonder if ‘trying to approximate the test set with a val set’ would give better eval corrs.

Q: Do both experiments? Which one is the best?”

## Reading notes

“ppl” means people and “hps” means hyperparameters. The word read as “contrived” and the inserted “pre” are uncertain. The crossed-out phrase is not reconstructed. “All the data” is preserved as written; the recommendation does not interpret it as permission to train on validation or sealed test ratings. These hypotheses are not measured results.
