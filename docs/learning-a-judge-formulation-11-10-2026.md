# Learning a judge instead of choosing one by correlation: formulation and scaling-curve idea

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/docs/learning-a-judge-formulation-11-10-2026.md>

**TLDR:** Brando's position (voice notes 11-08-2026 and 11-10-2026): getting a judge should be a normal machine-learning problem. Fit the judge by minimizing a proper loss on training tasks, evaluate it on held-out tasks, and do not pick it by how well it correlates with humans. This note states that formulation in one place and records his scaling-curve idea. The formulation is already tested on cached ratings (experiments 10 and 11). The scaling curve is an idea and is not tested.

Source: Brando Miranda's WhatsApp voice notes of 11-08-2026 09:29 and 11-10-2026 17:35, his whiteboard and handwritten pages of 11-09-2026 ([whiteboard transcription](../experiments/09_human_rating_collection/assets/whiteboard_objective_overview_11-09-2026.md), [formulations 1 to 4](../experiments/09_human_rating_collection/JUDGE_FORMULATIONS_11-09-2026.md)). This note adds no new result.

## The formulation

For artifact \(i\) (Python source, candidate Lean file, gold reference), a judge forecasts a probability vector \(q_\theta(\cdot\mid z_i)\) over the six ratings 0 to 5. Humans give ratings \(r_{ih}\). Training loss on a set of tasks \(D\):

\[
\widehat L_D(\theta)=\frac{1}{|D|}\sum_{i\in D}\frac{1}{m_i}\sum_{h\in H_i}\ell\bigl(q_\theta(\cdot\mid z_i),r_{ih}\bigr),
\]

averaged within each artifact, then equally over artifacts.

- **Choosing by correlation (formulations ① and ②):** pick \(\theta\) that maximizes \(\operatorname{Corr}(\mu_\theta(z_i),\bar r_i)\), where \(\mu_\theta\) is the judge's expected rating and \(\bar r_i\) the human mean. Correlation ignores bias and the shape of the distribution, so many different forecasts tie.
- **Learning by loss (formulations ③ and ④):** pick \(\hat\theta\in\arg\min_\theta \widehat L_{\text{train}}(\theta)\) (④: train tasks only), or select among trained judges by validation loss (③).
- **Mixture family used so far (cached judges):** \(q_i(w,\lambda)=(1-\lambda)\sum_j w_j q_{ij}+\lambda c\), with \(w\) on the simplex over the five cached judges, \(c\) the training-marginal histogram, and \(\lambda\) from a fixed grid (experiment 10) or 0 (experiment 11).
- **Evaluation:** every judge is scored on held-out tasks, with data-dependent steps fit inside each training fold. Folds are grouped by task, so related artifacts are never split across train and test.

## The evals

- **Normalized ranked probability score (RPS), primary.** With \(Q_k=\sum_{s\le k}q_s\): \(\ell_{\mathrm{RPS}}(q,r)=\frac15\sum_{k=0}^{4}\bigl(Q_k-\mathbf 1\{r\le k\}\bigr)^2\), in \([0,1]\), lower is better. In expectation it equals a distribution-error term plus a disagreement term that no forecast can remove.
- **Cross-entropy (CE), secondary.** \(\ell_{\mathrm{CE}}(q,r)=-\log q_r\), with a probability floor of 1e-6 in experiments 10 and 11.
- **Total variation distance (TVD), secondary,** against each artifact's empirical rating histogram, averaged equally over artifacts.
- Pearson, Spearman and Kendall are diagnostics, not objectives.

Intervals: task bootstrap (10,000 draws) of paired differences; a result counts only if the 95% interval excludes 0.

## Where the evidence is so far (cached ratings, 75 artifacts, 25 tasks, 0 model calls)

- Experiment 10: validation selected the RPS-trained mixture over the Pearson-trained one, but the held-out difference is unresolved (+0.0052, 95% interval [-0.068, +0.015]).
- Experiment 11 (formulation ④, repeated task-grouped 5-fold CV): the CE-trained mixture has RPS 0.1367 vs 0.1496 for equal weights and 0.1829 for the constant. Its CE ties equal weights and is worse than the constant.

## Idea, not tested: a scaling curve for learning a judge

If learning a judge is a learning problem, its held-out loss should fall with the amount of training data, so we can fit a learning curve and use it to size the next human-rating round. Brando's whiteboard form is \(\ell=E+A N^{-\alpha}+B D^{-\beta}\); its symbols \(N\) and \(D\) were not defined on the board. Experiment 07 fitted that form to the estimation error of a fixed judge's nRMSE (varying tasks \(n\) and raters per artifact \(k\)). That is a different quantity. The idea here is a curve of the held-out RPS of a learned judge against the number of training tasks, and separately against ratings per artifact. Nothing has been run for it. The only data are 25 tasks and 75 artifacts, so such a curve would be noisy.

## Learning bounds

Brando said (Fathom call 11-07-2026, [notes](https://github.com/brando90/judges-dont-need-psychometrics-or-corr/blob/main/paper_latex_and_notes/notes/fathom_call_11-07-2026/notes.md)) that the idea came from trying to work out, with a learning bound, how many human-rated pairs are needed. A derived bound is not in this repository. The only bound-like statement here is that small excess expected RPS bounds the Wasserstein-1 distance (`paper_latex/AAAI_2027_Evaluation_AI_Scientists/04_objective.tex`).
