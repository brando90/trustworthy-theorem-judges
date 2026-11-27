# Rank score and the held-out RPS interval (11-27-2026)

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/30_rank_next_human_ratings_by_judge_ensemble_uncertainty_and_power_curve_for_the_held_out_rps_gain_start_27Nov2026/derivation/active_selection_and_rps_power_11-27-2026.md>

**TLDR:** The rank score uses six logged judge distributions and the count of ratings, not the rating values. The task bootstrap of ranked probability score (RPS) does not shrink once those histograms stop moving, so extra ratings on the same 20 tasks leave the upper bound at +0.002. The planning extrapolation crosses at 23 tasks.

**Date:** 11-27-2026. Typeset PDF: [active_selection_and_rps_power_11-27-2026.pdf](active_selection_and_rps_power_11-27-2026.pdf).

## What this shows and what it does not show

The rank score orders the next human ratings. It is not a trained judge. RPS compares two distributions on $\{0,1,2,3,4,5\}$. The cumulative logit behind the forecast uses a linear shift of four scalar features. It does not see an arbitrary function of the Lean file, and the power curve does not refit it.

The task bootstrap resamples tasks and keeps each histogram fixed. More draws from the current histograms do not push the upper endpoint below 0. The figure of 23 tasks holds the 20-task point estimate fixed and scales only the gap to the upper endpoint by $\sqrt{20/m}$. It is not a measured interval and not a certification.

## Rank score

Six members, equal weight. Member $k$ has distribution $q^{(k)}$ and expected score $\mu_k=\sum_{r=0}^{5} r\, q^{(k)}_r$. Disagreement $D$ is the sample standard deviation of the six expected scores. $\bar q$ is their mean. $H(\bar q)$ is the Shannon entropy of $\bar q$ in nats, divided by $\log 6$. The rank score is

$$S = D + H(\bar q)\,(1-\bar q_5) + \frac{0.5}{1+n}.$$

$n$ is the number of ratings so far. The rating values do not enter. On the measured list the top 25 new artifacts are 21/61 fives and the bottom 25 are 66/70 fives. Spearman of $S$ with the five-rate is $-0.617$. That check is not an input to $S$.

## Ranked probability score

With cumulative sums $P_{\le t}$ and $Q_{\le t}$,

$$\mathrm{RPS}(P,Q)=\frac{1}{5}\sum_{t=0}^{4}\Big[(Q_{\le t}-P_{\le t})^2+P_{\le t}(1-P_{\le t})\Big].$$

The second term does not depend on the forecast, so it cancels in the paired difference against the set-aware constant. The paired estimand is the mean over test artifacts of RPS(judge) minus RPS(constant). On the 445-rating snapshot that mean is $-0.035133$, with task-bootstrap interval $[-0.076366,+0.002010]$.

## Why more ratings on the same tasks do not close the gap

A bootstrap draw samples the 20 tasks with replacement and recomputes the mean of the per-artifact paired RPS, counting a repeated task again. The interval is the 2.5 and 97.5 percentiles of 10,000 draws. If new ratings are drawn from the current histogram $P$, the expected new histogram is $P$, and the interval returns to the current one as the added count grows. The measured forward curve, through 2,240 synthetic ratings, stays within 0.0008 of $+0.002010$.

## Extrapolation

$$U(m)=\Delta_{20}+(U_{20}-\Delta_{20})\sqrt{20/m},$$

with $\Delta_{20}=-0.035133$ and $U_{20}=+0.002010$. Then $U(22)=+0.000281$ and $U(23)=-0.000497$. Subsamples of these 20 tasks have interval widths that track $1/\sqrt{m}$ (coefficient of variation of width times $\sqrt{m}$ is 0.019). The formula still assumes a new task would have the same paired RPS. Three more tasks at the current depth of 176/20 ratings are about 26 ratings only under that assumption.
