# Mathematical interpretation of the handwritten note

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/06_information_loss_vs_correlation_judge_selection/MATH_AND_NOTE.md>

**TLDR:** The note motivates comparing objectives, but ordinary Brier loss already recovers the true distribution in population. The weighted population distance is different from plugging one observed rating into both its weights and target.

Source: Brando's attached handwritten page, saved byte-for-byte in ignored private storage; image SHA-256 `c76657091ffb2e6515ad6bb4565dacc66e7fd8368ad2681a058d399c6bc21443`. The following is a mathematical transcription and interpretation, not a claimed verbatim transcription of every handwritten word. Crossed-out and uncertain margin text is not reconstructed as a quotation.

The legible equations are:

    BS(x_tilde, q_hat) = sum_x (1{x=x_tilde} - q_hat(x))^2
                       = (1-q_hat(x_tilde))^2 + sum_{x != x_tilde} q_hat(x)^2
    WeightedDiv(p || q_hat) = sum_x p(x) (p(x)-q_hat(x))^2
    argmin_{q_hat in simplex(X)} WeightedDiv(p || q_hat)
    q_hat(x) >= 0; sum_x q_hat(x) = 1

The prose asks whether the weighted version removes the explicit penalty on unobserved categories, whether it would converge more slowly or at all, and whether normalization plus repeated sampling is enough to recover the true distribution. The note also asks whether this has a theorem. Here x is a rating category; it should be renamed r in code to avoid confusing it with input Python x_input.

## Brier and forward KL

For R~p on six categories and a fixed normalized forecast q:

    E[sum_r (q_r-1{R=r})^2] = sum_r (q_r-p_r)^2 + 1-sum_r p_r^2.
    E[-log q_R] = H(p) + KL(p || q).

Both population risks are uniquely minimized by q=p. The per-observation Brier terms for unobserved categories are not a defect: averaging them over observations yields squared distance to p plus a q-independent constant. CE and forward KL are equivalent optimization criteria for fixed targets, not two independent treatments. Reverse KL is different and is especially problematic with sparse empirical targets containing zeros.

Population identification is not a finite-sample, misspecified-model or optimization guarantee. Different proper scores can select different best approximations within a restricted candidate family. Better log loss need not give better Brier, and neither guarantees better correlation. Pearson is invariant to positive affine transformations; rank correlations are invariant to strictly increasing transformations that preserve ties. Consequently high correlation does not establish correct levels or probabilities.

## The weighted proposal

For a known population p, D_p(p,q)=sum_r p_r(p_r-q_r)^2 has unique minimum q=p on the probability simplex. Proof: its nonnegative terms give value zero at p; any other zero-loss q agrees with p wherever p_r>0. Those coordinates already sum to one, forcing all remaining q_r to zero. Thus zero weights outside the support do not destroy uniqueness on the simplex. This does not prove a convergence rate; rare categories receive little weight and optimization can be poorly conditioned.

But setting p_hat to a one-hot observation e_R in this same expression gives only (1-q_R)^2. This is NOT generally a proper multiclass scoring loss. Example: p=(0.6,0.3,0.1), q=(2/3,1/3,0). Expected loss at q is 0.3, below the 0.324 at q=p. Under the full Brier loss, q=p is better: 0.54 versus about 0.555556. This distinction is absent in the binary special case, where the one-term loss is half the usual two-category Brier loss.

An empirical p_hat from many independent ratings can converge to p, and minimizing its weighted distance can be consistent under suitable assumptions. With only two or three raters per artifact, however, plugging that noisy p_hat into both weights and target is not the same estimator as averaging a proper score over ratings. Compare it explicitly rather than assuming equivalence. Independence assumptions also need scrutiny when the same raters score many artifacts.

TVD and weighted PMF distance against an empirical human histogram measure agreement with that histogram. Their values are affected by sparse human sampling. A plot of two marginal score histograms can match perfectly while item-level scores are reversed; all primary comparisons must retain artifact pairing and conditional inputs.
