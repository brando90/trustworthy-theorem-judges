# Whiteboard: correlation and loss objectives

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_human_rating_collection/support/assets/whiteboard_objective_overview_11-09-2026.md>

**TLDR:** The board contrasts maximizing correlation with minimizing a distributional loss, and sketches a probability distribution over ratings. The scaling-law expression is an untested suggestion, not a fitted law for this study.

Source: Brando Miranda's [original photograph](whiteboard_objective_overview_11-09-2026.jpeg), supplied on 11-09-2026. Original path: `/Users/brandomiranda/Downloads/WhatsApp Image 2026-11-09 at 10.44.48 (1).jpeg`. Image bytes and hash are recorded in [provenance](formulations_11-09-2026_provenance.json).

## Transcription

Notation is typeset for readability. The board's left-hand side is a selected distribution, while its right-hand side uses an argmax/argmin over judges; that type mismatch is retained here and corrected in the [coordinator note](../../JUDGE_FORMULATIONS_11-09-2026.md). Dots abbreviate omitted arguments.

\[
P_j^{\widehat{AI}_j}(\cdot\mid\cdot,\cdot)
=\operatorname*{argmax}_{AI_j\in\Theta}
\left\{\operatorname{Corr}\left(P_j^{AI_j}(\cdot\mid\cdot,\cdot),P_j^H(\cdot\mid\cdot,\cdot)\right)\right\}.
\]

Below it:

\[
\operatorname*{argmin}_{AI_j\in\Theta}
\left\{\operatorname{Loss}\left(P^{AI_j},P^H\right)\right\}.
\]

The word “Loss” is underlined and labeled \(\ell\) in green.

Green expression on the left:

\[
\ell=E+A N^{-\alpha}+B D^{-\beta}.
\]

Bottom:

\[
P(\cdot\mid\hat y,y^*)\in\mathcal P^R
=\left\{p\in\mathbb R\;\middle|\;\int p(r\mid\hat y,y^*)=1,\quad p(r\mid\hat y,y^*)\geq0\right\}.
\]

The right-hand constraint is small; the visible intent is normalization and nonnegative probabilities. The integral has no clearly written differential. The set/function notation above follows the board rather than supplying missing mathematical definitions.

Below the rating argument:

\[
\{0,1,2,3,4,5\}=R,
\qquad [0,1].
\]

## Interpretation, separate from transcription

For the actual six discrete rating categories, use a probability vector \(q\in\Delta^5\), meaning \(q_r\geq0\) and \(\sum_{r=0}^{5}q_r=1\). A normalized score takes values \(\{0,0.2,0.4,0.6,0.8,1\}\); it is not a continuous density or an event probability merely because it lies in \([0,1]\). The symbols \(A,N,D\) in the proposed scaling law are not defined on the board; do not identify them with solver count, task count, or rater count without a separate model and supporting data.
