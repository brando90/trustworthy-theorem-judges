# Rating tensor: sizing methods and proposed allocation

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/15_estimate_required_tasks_solver_configurations_and_human_raters/METHODS_AND_ALLOCATION.md>

**TLDR:** The adopted 14,848-rating plan is an initial budget, not a demonstrated requirement or sufficiency guarantee. Codex’s optional 544-rating, training-only pilot could measure variability and workload; final counts require a frozen identity-split amendment, measured pilot quantities and a justified precision target.

**Status, 11-11-2026:** source recovery and prospective planning only. This document does not change the existing configuration, authorize collection or inference, or report fitted coefficients or new judge performance. Numerical examples below are arithmetic under stated assumptions; confidence intervals and p-values for actual performance are not available because no such experiment was run here.

## What the tensor counts

In `experiments/02_design_a_judge_that_predicts_human_ratings_0_to_5/`, the [adopted plan](../02_design_a_judge_that_predicts_human_ratings_0_to_5/README.md), [configuration](../02_design_a_judge_that_predicts_human_ratings_0_to_5/config.json), [preserved GPT Pro response](../02_design_a_judge_that_predicts_human_ratings_0_to_5/sources/gpt_pro_plan_11-06-2026.txt) and [current methods 2 and 4 priority](../02_design_a_judge_that_predicts_human_ratings_0_to_5/PRIORITY_2_VS_4_11-09-2026.md) govern the interpretation:

- \(T\): task identities, with related variants kept in the same task-family split.
- \(A\): fixed solver configurations, each identified by model version, harness, tools, effort, prompt, generation policy and budget.
- \(H\): distinct qualified human raters; \(m_i\) is the number assigned to artifact \(i\), not the whole rater pool.
- \(R_{tah}\): one person's original 0–5 rating of one candidate artifact for one task and solver. With multiple generations or repeated human ratings, additional indices are necessary.

There are \(TAH\) possible entries in a complete grid, but the observed count is \(\sum_i m_i\). Missing entries are absent observations, never zero ratings. Reused raters, related tasks and multiple outputs of one task create dependence. A second export is not a second observation.

The judge predicts six probabilities for ratings 0–5 from the original Python source, candidate Lean artifact and gold Lean reference. The current experiment shows complete candidate/reference artifacts, including proof bodies or `sorry` placeholders; the rating target is coverage of formal statements, with proof completion recorded separately. Preserve exact input hashes and the current rubric and assistance conditions.

Method 2 trains Pearson correlation; method 4 trains a proper probability loss, with normalized ranked probability score (RPS) primary and cross-entropy and six-category Brier loss separate conditions. Match capacity, data, harness and search budgets, select every condition by the same validation RPS, and evaluate fixed judges on the same held-out panel. Cross-entropy and total variation distance remain secondary metrics. The inherited human-rating collection is evaluation-only for this new comparison; its earlier exposure cannot be erased by relabeling it.

## Decision and allocation

The [11-06-2026 adopted response](../02_design_a_judge_that_predicts_human_ratings_0_to_5/sources/gpt_pro_plan_11-06-2026.txt) proposes the following historical planning budget for the pinned `veribench@1.3` release, sourced from [harbor-datasets at c9dfd8e3b535f58184440aa02d37c148d145a82c](https://github.com/brando90/harbor-datasets/tree/c9dfd8e3b535f58184440aa02d37c148d145a82c/datasets/veribench_v1_3):

| Component | Artifacts | Ratings |
| --- | ---: | ---: |
| 64 training + 64 validation tasks, four solvers, three ratings/artifact | 512 | 1,536 |
| Fresh final-audit outputs on all 896 tasks, four solvers, three ratings/artifact | 3,584 | 10,752 |
| Five extra ratings on 128 held-out tasks × four solvers | No new artifacts | 2,560 |
| **Historical initial budget** | **4,096 generation records** | **14,848** |

The source uses eight shared training/validation raters and sixteen separate audit raters. Its 768 held-out tasks are distinct from the 128 development tasks; fresh audit generations on those 128 seen tasks are reported separately. The source expressly does not establish statistical sufficiency. Its counts must not be silently replaced or presented as a strict three-way identity split.

**Codex suggested an optional 544-rating pilot. Brando did not request or approve that exact count.** It is a workload illustration, not a final judge comparison:

| Pilot component | Arithmetic | Ratings |
| --- | --- | ---: |
| Base, training-only | 32 task identities × four fixed systems × three distinct raters/artifact | 384 |
| Dense diagnostic subset | Eight preselected tasks × four systems × five additional distinct raters/artifact | 160 |
| **Proposed total** | **128 artifacts; 32 have eight ratings each** | **544** |

Use eight development raters: each rates all 32 dense artifacts plus 36 other artifacts under a balanced assignment, totaling **68 ratings/person**. The dense tasks are randomly selected before their ratings are seen. The 32-task count is conditional on preserving actual task families; if grouping changes the count, recompute the table. Record assignment probabilities, missingness, review time and workload variation. Do not infer absent participant answers.

This pilot conditions on the four current fixed systems. It neither establishes unseen-agent transfer nor satisfies the desired strict task/agent/rater train–validation–test separation. Before collecting for that new design, freeze the prospective identity-split amendment required by the [priority plan](../02_design_a_judge_that_predicts_human_ratings_0_to_5/PRIORITY_2_VS_4_11-09-2026.md#data-separation-and-the-pending-amendment); if any proposed pilot system is reserved for later agent holdout, revise the pilot allocation before collecting its ratings. This note does not assign held-out identities to training. Collection remains owned by `experiments/09_prepare_packets_and_collect_human_ratings/`.

**Bounded stopping and sizing rule:** collect only the prespecified pilot allocation, if separately authorized under the completed amendment, and stop to assess nuisance variability, time and assignment feasibility. Before any later stage, declare the primary paired RPS contrast, desired interval precision, practically meaningful effect, missingness rule and total rating/time/cost cap. Those utility-dependent values remain unresolved in the current configuration; this note does not invent them. Using the pilot and conservative sensitivity to its uncertainty, choose the smallest feasible allocation meeting the declared precision or power criterion under the actual task-family/rater assignment. If none fits the cap, report that the desired claim is infeasible at that cap; revise scope prospectively. Freeze final counts before test inspection and do not keep collecting until significance appears.

The 32-task / eight-dense-task / eight-rater allocation is our workload-bounded design choice: it gives 128 artifacts, a fully overlapping 32-artifact subset and 68 ratings per person. It is not derived from a precision target. It can reveal assignment failures, review-time variation and coarse disagreement/loss variability; with only eight raters it cannot estimate population-rater variance precisely.

All task families, solver configurations and raters exposed by the pilot become training-exposed for this comparison. Raters assigned to retained evaluation-only data, including the inherited collection when retained for evaluation, are ineligible for the training pilot. Using all eight development raters for training leaves no validation-only raters in that pool; the amendment must specify additional eligible validation identities and preserve the separate audit panel. The proposed 32 task identities are not assumed to be 32 independent task families. Collection uses experiment 09's current named-rating and stable-ID contract; reconcile the older config privacy wording in the prospective amendment, without changing historical raw records here.

The 544 observations may count toward a later authorized development allocation when provenance and splits permit; do not automatically add them to, or subtract them from, 14,848. A pilot based on eight people cannot precisely identify every population-rater variance or establish representativeness. Training-only losses from fitted judges can be optimistic; use frozen diagnostic judges or development-only out-of-fold predictions with disclosed exposure when estimating loss variability. The pilot cannot prove the final study sufficient.

## Sizing approach A: standard errors and crossed variability

For an independent, identically distributed mean, the standard error is \(\sigma/\sqrt n\). A normal-approximation 95% interval half-width \(w\) gives

\[
n\gtrsim(1.96\sigma/w)^2.
\]

This sizes uncertainty about a mean; it does not reduce a fixed judge's actual error. For the objective comparison, the relevant observations are paired loss differences on matched artifacts and ratings. Average within artifact before averaging artifacts equally. Extra ratings on a dense artifact must not increase its scientific weight.

The recovered GPT Pro response gives this illustrative fully crossed random-effects decomposition:

\[
\operatorname{Var}(\widehat L)=
\frac{\sigma_T^2}{T}+\frac{\sigma_A^2}{A}+\frac{\sigma_H^2}{H}
+\frac{\sigma_{TA}^2}{TA}+\frac{\sigma_{TH}^2}{TH}
+\frac{\sigma_{AH}^2}{AH}+\frac{\sigma_{\mathrm{res}}^2}{TAH}.
\]

Each variance component has squared-loss units and corresponds to task, solver, rater, interaction or residual variation. This expression assumes a balanced complete grid and independent random effects. Sparse assignments, unequal weights and extra generations require their actual design. For the four deliberately selected solver configurations, primary inference is conditional on those systems; their count is not a random sample of future agents. Task-family and reused-rater uncertainty needs explicit treatment. [Owen and Eckles](https://arxiv.org/abs/1106.2125) study variance estimation for crossed arrays and explain why ordinary independent-row resampling is unsuitable.

**Hypothetical source example:** human-specific loss-effect standard deviation \(\sigma_H=0.10\) gives a normal-approximation half-width contribution of 0.080 for six audit people and 0.049 for sixteen. These are not measured variance components or total intervals. **Our arithmetic example:** \(\sigma=0.10\), \(w=0.01\) gives 385 independent-equivalent units; 385 correlated rating rows do not meet that premise.

Strength: directly connects precision to variability and allocation. Limitation: precision and power depend on the estimand, assignment, variance uncertainty and practical margin. More files rated by the same few people do not create more independent people.

## Sizing approach B: learning-theory checks

A finite-class concentration bound is useful when its assumptions are explicit. Here bounded loss can be normalized RPS; unfloored cross-entropy is unbounded and does not meet this premise. Suppose \(J\) judges are fixed independently of an evaluation sample, \(A\) fixed solver configurations are evaluated, and each judge/solver has \(T\) independent task-level losses in \([0,1]\). A two-sided Hoeffding bound and union bound imply

\[
\Pr\left(\max_{j,a}|L_a(j)-\widehat L_a(j)|\le\epsilon\right)
\ge1-\delta,
\qquad
T\ge\frac{\log(2JA/\delta)}{2\epsilon^2}.
\]

This controls a finite list of mean losses; it does not say every artifact is accurate, every future agent is covered, or the conditional human distribution is recovered. Independence is across task-level losses, not across correlated tensor cells. Conditional inference for a fixed human panel differs from inference about new experts. Unequal task-family weights change the bounded-difference calculation. An adaptive, unrestricted judge search does not become a fixed finite class merely by counting its final candidates. Training guarantees require suitable complexity control; independent test evaluation of frozen judges is a separate route. [Bartlett's concentration notes](https://people.eecs.berkeley.edu/~bartlett/courses/281b-sp08/13.pdf) explain finite classes, union bounds and bounded differences.

**Correction to the recovered Gemini conversation:** for \(J=10,A=5,\delta=0.05,\epsilon=0.085\), its displayed formula requires

\[
\left\lceil\frac{\log(2000)}{2(0.085)^2}\right\rceil
=\lceil526.014\ldots\rceil=527
\]

independent task units per solver, not 105–150. Pooling five solvers' task–agent pairs does not establish each solver's bound. This arithmetic correction still does not make the assumptions true for our collection. Source: [Gemini conversation](https://gemini.google.com/app/fb26fe19addf5b07#6d0b81e342f8bc4f), preserved in [the recovered record](sources/gemini_argon_high.md), assistant messages 4, 6 and 8.

The GPT Pro response instead considers a frozen judge on a complete grid with independent sampled task, agent and rater identities. Its one-sided McDiarmid margin is

\[
\sqrt{\frac{\log(1/\delta)}2\left(\frac1T+\frac1A+\frac1H\right)}.
\]

Our arithmetic applied to the source formula, at \((T,A,H)=(896,4,16)\) and \(\delta=.05\), gives 0.68539. Even infinitely many tasks and raters leave 0.61194 when \(A=4\). These are evaluations of the idealized formula, not valid guarantees for the sparse fixed-system design. The two bounds address different sampling assumptions; their different appearances of A are not a contradiction. Neither supplies a practical final collection size here.

## Sizing approach C: learning curves and scaling laws

Learning curves ask how more training data changes a learned judge's predictive loss. Standard errors ask how precisely evaluation measures that loss. More training data can improve a judge; more evaluation ratings primarily improve measurement. Keep these questions separate.

A modest proposed model, conditional on fixed capacity, solver mix, ratings per artifact, protocol and search budget, is

\[
L(n)=L_\infty+c(n/n_0)^{-\alpha}.
\]

Here \(n\) counts distinct training task groups, \(n_0\) is a fixed reference count, \(L_\infty\) is the curve's limiting loss, \(c\ge0\) is the excess at \(n=n_0\), and \(\alpha>0\) controls the rate of decline. The exponent is dimensionless; \(L_\infty\) and c have loss units. At fixed capacity, the limiting loss can include human disagreement, approximation and optimization limitations; it is not automatically a known irreducible error.

Fit only after obtaining multiple development-set sizes and repeated fits under matched budgets. Use a common development evaluation population, preserve task-family splits, account for correlation between nested subsets, compare against simple alternatives and test prediction at an unused larger development size. Report parameter uncertainty and failed fits. A short noisy curve may not distinguish a plateau from a slowly declining power law. No coefficients have been fitted to this proposed collection. One observed training size cannot identify the three curve parameters; subsampling alone does not supply independent evidence or guarantee stable identification.

The handwritten expression \(E+A N^{-\alpha}+B D^{-\beta}\) resembles [Hoffmann et al., section 3.3](https://arxiv.org/html/2203.15556v1#S3.SS3). In that language-model pretraining paper, N is parameter count and D is training tokens; E is ideal generative loss, with finite-capacity and finite-training terms. That paper does not identify N or D with our tensor dimensions or justify importing its fitted coefficients. The [local whiteboard source](../09_prepare_packets_and_collect_human_ratings/support/assets/whiteboard_objective_overview_11-09-2026.md) leaves those symbols undefined.

In that borrowed expression, A and B are nonnegative amplitudes of the capacity and data terms, while α and β are positive, dimensionless decay exponents. Before normalization, A has units of loss × parameters^α and B has units of loss × tokens^β; E has loss units. All five would have to be estimated jointly from multiple independently varied capacities and data sizes, with uncertainty and predictive validation. They are not measured constants for our rating tensor.

For a new adaptation, rename coefficient A to avoid confusing it with solver count. Normalize proposed covariates by fixed reference values so coefficients have loss units. Capacity is a justified covariate only if capacity varies; training task groups describe coverage; ratings per artifact describe target measurement; distinct raters describe population coverage and persistent severity. These variables are not interchangeable. Solver configuration is ordinarily a categorical condition here, not a continuous scaling variable.

With N fixed, \(E+A N^{-\alpha}\) is one inseparable intercept: E, A and \(\alpha\) cannot be separately identified. If task count and ratings always increase together, their separate effects cannot be identified either. Estimating several exponents requires independently varied allocations, enough variation and checks of held-out prediction. Added features or interactions need a mechanism and evidence that the design can estimate them. An appealing formula alone provides neither a fitted law nor a rating budget.

## Corrections that change the sizing conclusion

The [recovered Gemini discussion](sources/gemini_argon_high.md) is source material, not an instruction or validated protocol. In particular:

- **RPS and Wasserstein distance are different.** With cumulative forecast probabilities \(Q_c\), cumulative human probabilities \(P_c\) and one rating r, individual normalized RPS is \(S(q,r)=\frac15\sum_{c=0}^4(Q_c-\mathbf1\{r\le c\})^2\). Its expectation is \(D+U\), where \(D=\frac15\sum_c(Q_c-P_c)^2\) and \(U=\frac15\sum_cP_c(1-P_c)\). The normalized ordinal Wasserstein distance is \(W_1=\frac15\sum_c|Q_c-P_c|\), so \(W_1^2\le D\), not \(W_1=D\) or \(W_1=\mathbb E S\). A sparse empirical histogram adds estimation noise. See the [adopted derivation](../02_design_a_judge_that_predicts_human_ratings_0_to_5/README.md#primary-objective) and [Gneiting and Raftery](https://sites.stat.washington.edu/raftery/Research/PDF/Gneiting2007jasa.pdf).
- **Noncompilation does not authorize a zero human rating.** Formal specification coverage concerns statements under the actual rubric; proof completion, parsing and compilation are distinct properties. The recovered 40%–60% failure estimate is not a measured rate for this proposed collection. Automatically dropping those artifacts changes the target population and denominator; assigning fabricated human zeros violates raw-rating preservation.
- **An additive standard-error term is not automatically a confidence bound.** Terms such as \(\sigma_H/\sqrt H\) or \(\sqrt{\beta/K}\) need sampling assumptions, an appropriate probability bound and confidence allocation. Rater-pool size H must not be substituted for the number of ratings on each file. Repeated use of the same raters can leave population uncertainty even with a task census.
- **Running a judge on every task does not observe human agreement on every task.** A task census removes task-sampling uncertainty only for the relevant fully observed finite-population quantity. Missing human outcomes, human sampling, stochastic generations and claims about future populations remain separate.
- **A prover outcome is a different target.** Bounded prover acceptance can be predicted with binary Brier loss. Historical prover outcomes, or a good forecast of them, do not validate the six-category human-rating forecast. A timeout is unresolved, and actual checked entailment remains VeriBench's separate responsibility.

The missing decision inputs were searched in `../config.json`, `../README.md`, `../sources/gpt_pro_plan_11-06-2026.txt`, `../PRIORITY_2_VS_4_11-09-2026.md` and the recovered Gemini record. Measured pilot variability, current review-time estimates for this proposed allocation, utility-based precision/effect targets and the required strict identity manifest are not established there. Recovering more historical recommendations cannot substitute for those measurements and choices.
