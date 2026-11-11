# Earlier local rating-size plans — exact source snapshots

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/02_probabilistic_ordinal_judge/rating_tensor_planning/sources/earlier_local_plans.md>

**TLDR:** Three earlier plans are preserved below without correcting their text. They are historical recommendations under different targets and assumptions, not the current protocol or newly verified results.

Captured 11-11-2026. Each START/END block preserves the source text verbatim; relative links still refer to the original VeriBench directory, not this bundle. The original header links are retained as evidence, including unavailable ones. Use SOURCE_INDEX.md and the current methods note for interpretation.

## Snapshot: RATING_TENSOR_SAMPLE_SIZE_11-04-2026.md

Original local path: `/Users/brandomiranda/veribench/experiments/ideas/leave_one_agent_out_fsc_judge_validation_on_human_ratings/RATING_TENSOR_SAMPLE_SIZE_11-04-2026.md`. Immutable Git object 01f639c1f2242cdef3b977715d91a7c978ea7fcd. SHA-256: `f3b4c4414ce08e7d4689eed0ebe6fcac05017153c8eb31826307d9093d830633`.

<!-- START RATING_TENSOR_SAMPLE_SIZE_11-04-2026.md -->
# How many tasks, solver systems and human raters for VeriBench judge validation?

**Doc link:** <https://github.com/brando90/veribench/blob/codex/human-rating-note-11-04-2026-8fa1104e/experiments/ideas/leave_one_agent_out_fsc_judge_validation_on_human_ratings/RATING_TENSOR_SAMPLE_SIZE_11-04-2026.md>

**TLDR:** For pooled agreement, 100 held-out tasks × five solver systems × two qualified raters per output is a useful 1,000-rating design. For a claim about the worst of five systems, budget 200–250 tasks (2,000–2,500 ratings); 250 is the stronger candidate if we want roughly a 90% chance of estimating the worst correlation within 0.10 in both illustrative scenarios. These are planning calculations, not a change to the approved 25-task round or evidence that the judge passes.

[Google study-design companion](https://docs.google.com/document/d/1qmc9ezrx7N-7Y9uohC7kW59WblaO30mvJ1jVBzykQg0/edit?usp=drivesdk) · [original question](assets/handwritten_rating_tensor_11-04-2026.md) · [arithmetic and figure script](scripts/size_human_rating_study.py) · [synthetic survey script](scripts/simulate_worst_solver_precision.py) · [calculated values](results/rating_tensor_planning_11-04-2026.json) · [simulation results](results/worst_solver_accuracy_11-04-2026.json).

## 1. What is counted

T is the number of held-out Python tasks. A is a fixed panel of solver configurations, each supplying one output for each task. H is the pool of distinct qualified non-author raters; r is the number assigned to each output. The human tensor R[t,a,h] is sparse: T × A × H possible entries, T × A × r observed entries under complete collection. If a solver produces multiple independent attempts, add a generation index. K denotes independent executions of the judge on one fixed output.

A=5 tests the five specified systems. Five models in one harness do not establish transfer to untested harnesses or all future agents. Two independent human ratings permit a human–human comparison. Use a balanced, connected whole-folder assignment: rotate pairs, compare the same systems on the same tasks, and distribute task types across raters. The current packet remains 25 × 5 × 2. Brando's ratings are additional.

## 2. Task count changes precision, not the judge

For an independent, approximately bivariate-normal pair per task, Fisher's Pearson approximation is tanh(atanh(c) ± 1.96/√(T−3)), where c is the anticipated correlation. It is a planning proxy, not the final interval for tied ordinal Spearman ranks. At c=0.65, a single solver has a typical 95% interval [0.343, 0.832] at 25 tasks, [0.520, 0.751] at 100, and [0.562, 0.723] at 200. The widths are 0.489, 0.231 and 0.162: four times as many tasks roughly halve sampling error.

For pooled planning only, an exchangeable cluster approximation is n_eff ≈ T A/[1+(A−1)κ]. κ is the within-task correlation of contributions to the estimator; it is not the correlation between the raw human scores. At T=100 and illustrative κ=0.5, A=1, 3, 5 and 10 yield 100, 150, 167 and 182 effective pairs. At c=0.65 the corresponding widths are 0.231, 0.187, 0.177 and 0.170. Doubling the number of solvers from five to ten buys little precision here; add solvers for scientific coverage. Within a particular solver the sample size is still T.

For A=5 and κ=0.5, a pooled width of 0.20 calls for about 80 tasks if c=0.65 but 192 if c=0.30. With strong dependence κ=0.9 the respective counts rise to 122 and 294. These κ values are sensitivity assumptions. The earlier project's own two-scenario simulation gave mean task-bootstrap widths about 0.13–0.19 at T=100; the toy formula and that simulation make different assumptions.

![Planning intervals for rank agreement and signed bias](results/rating_tensor_precision_11-04-2026.png)

Figure assumptions: the left panel uses the Pearson approximation and κ=0.5 for pooling. The right panel uses a balanced assignment and the two standard deviations in section 5. Curves describe hypothetical precision; they do not score the judge.

## 3. Direct check with ordinal scores: how close is the estimated correlation?

The [project's simulation](../../102_rescore_vbv1_paper_fsc_with_validated_judge_rewrite_tmlr_icml/results/C15_panel_size_and_warmup.md) supplies two plausible score distributions. The new sensitivity check fixes five system offsets at (−1, −0.5, 0, 0.5, 1) times the scenario's system scale. Each simulated study draws 20 persistent rater tendencies (standard deviation 0.06), assigns two different raters to each whole task folder, and rounds each rating to 0–5. A separate 200,000-task synthetic population approximates each system's target Spearman correlation against the average of two sampled qualified raters. Each design has 1,000 independently simulated studies. No current rating or judge value was read.

| Tasks | Human ratings | Worst-solver root mean squared estimation error: spread / bunched | Chance worst-solver estimate is within 0.10: spread / bunched |
|---:|---:|---:|---:|
| 25 | 250 | 0.169 / 0.217 | 49.7% / 32.6% |
| 100 | 1,000 | 0.068 / 0.090 | 87.5% / 73.6% |
| 165 | 1,650 | 0.053 / 0.067 | 94.1% / 86.5% |
| 200 | 2,000 | 0.050 / 0.065 | 95.6% / 87.2% |
| 250 | 2,500 | 0.044 / 0.058 | 97.4% / 91.5% |

The simulated population's pooled / worst correlations were 0.663 / 0.566 with spread scores and 0.287 / 0.187 with bunched scores. Adding tasks estimates those values more accurately; it does not raise them. In the bunched scenario the true worst value is below a hypothetical 0.45 floor, so a reliable study should not say it clears the floor. The minimum of several noisy estimates is typically downward biased, particularly in small studies.

At T=250 the 95% Wilson intervals for Monte Carlo sampling error in the within-0.10 rates are 96.2–98.2% and 89.6–93.1%, respectively. These quantify simulation repetition error, not uncertainty about the real study or coverage of its confidence intervals.

## 4. A separate question: can every solver clear a useful floor?

Illustrate a **proposed**, stronger single claim: the minimum of the five correlations exceeds 0.45. The current protocol's pooled point criterion of 0.45 is not already such a per-system confidence-bound requirement. Take true worst correlation 0.65 as a good-judge scenario, not an estimate for the new solvers.

For each solver the Fisher-scale gap is atanh(0.65)−atanh(0.45)=0.291. To make the one global claim, require every one-sided 95% lower bound to exceed 0.45. This intersection test has at most 5% false acceptance when at least one solver is below or at the floor, provided each component bound has its claimed coverage. To get at least 90% joint power without assuming independence between solvers, aim for ≤2% miss probability per solver (5 × 2% = 10%). Then T ≈ ceil[3+((1.645+2.054)/0.291)²]=165. For five separately interpretable simultaneous one-sided bounds, a conservative Bonferroni version uses 2.326 in place of 1.645 and needs 231 tasks.

| Assumed weakest true correlation | Tasks: one global all-five claim | Tasks: five simultaneous bounds |
|---:|---:|---:|
| 0.55 | 769 | 1,077 |
| 0.60 | 318 | 445 |
| 0.65 | 165 | 231 |
| 0.70 | 97 | 135 |

These are conservative sufficient counts under a Pearson planning approximation, not empirical powers for ordinal Spearman or for the complete validation protocol. A correlation near the floor is intrinsically expensive to distinguish from it. Values beyond the available task pool require revising the claim, target population or precision target.

## 5. Raters per file versus total rater pool

On the old 45 complete items (15 tasks), the three primary experts' single-rater absolute-agreement intraclass correlation was 0.633. Using the classical equal-reliability, independent-error model, reliability of a mean of r raters is r q/[1+(r−1)q]. This gives 0.633, 0.775, 0.838 and 0.896 for r=1, 2, 3 and 5. If a fixed judge's correlation with the underlying human target were 0.80, the corresponding observed Pearson correlations against the noisy rater mean would be about 0.636, 0.704, 0.732 and 0.757. That is less human measurement noise, not a change in the judge. The third rating costs 50% more than two for a much smaller gain than the second rating. These are illustrative projections, not an exact attenuation correction for Spearman.

To generalize mean bias to a qualified-rater population, persistent severity cannot be averaged away by giving more files to the same two people. Under a balanced additive model use SE(mean bias) ≈ √(s_task²/T+s_rater²/H). Assume s_task=0.09 at five outputs and two ratings per output (close to 0.035√25/1.96 from the existing spread-scenario bias interval) and an additional persistent s_rater=0.05 on the 0–1 scale. This is a sensitivity case: variance-component estimates on the old common items are 0.023 for the three experts and 0.144 for all five raters mixed, estimated standard deviations. Neither is a precise estimate for a fresh qualified panel.

At T=100, the 95% half-width is 0.072 for H=2, 0.036 for H=10, 0.028 for H=20 and 0.023 for H=40. If the true bias is +0.05, the probability that the full 95% interval lies inside ±0.10 is approximately 26%, 78%, 94% and 99%, respectively. The proposed full-interval requirement is stronger than checking a point estimate. With H=20, T=100 and true bias +0.181 like the old test, the probability of incorrectly clearing this criterion is essentially zero in the model. The old test means were 0.653 judge and 0.472 human.

For a 90% chance of demonstrating acceptable bias when true bias is +0.05, the active-boundary approximation requires SE ≤ (0.10−0.05)/(1.96+1.282)=0.0154. At T=200 this gives H≥13 if s_rater=0.05 but H≥51 if s_rater=0.10. Thus 20 qualified raters is an illustrative design point, not a statistical constant. Larger, balanced pools reduce the burden per person as well; at T=250 there are 500 folder assignments, averaging 25 folders per person at H=20 or 10 at H=50. Unequal work reduces the effective rater pool (H_eff=1/Σw_h² for workload shares w_h).

## 6. Judge variability and the decision

Variation across *different* tasks reflects the range of outputs. Random variation on the *same* output requires repeat executions of the frozen judge. Human rater count does not change that variation. For a fixed file, even under independent normal repetitions, three observations give a 95% interval for the underlying standard deviation from 0.52 to 6.28 times the observed standard deviation; ten give 0.69 to 1.83 times. Real scores are bounded and tied, so this is a scale illustration. The deployed ensemble's three calls per member are ingredients of one six-call score. Reuse historical raw repeats for component stability; repeat the complete procedure on a prespecified subset if the uncertainty of its aggregate score is the target.

Keep the evaluation fresh, blinded and task-disjoint from selection. Use identical, meaningful Python/reference/candidate inputs for humans and judge; never use the test ratings to tune the judge or pick the sample size. Report pooled, per-system, worst-system and within-task rankings; mean absolute error, signed bias, human–human agreement and judge repeatability. Existing level tolerances on the 0–1 scale are mean absolute error ≤0.15 and |bias|≤0.10; the second-human reading compares the lower confidence bound of judge–human minus human–human rank correlation with −0.10. The old frozen protocol still governs the current packet. For a future expansion, prespecify any stronger interval-based gates, evaluate their **joint** power and interval coverage under plausible scorer, rater, missingness and ceiling effects, then freeze the design. A failure or an inconclusive result is an informative outcome.

## Sources

[Original test receipt](../../100_karpathy_recipe_tc_judge_search_human_train_val_test/results/TEST_RECEIPT.json) · [qualified-rater protocol and human comparison](../../102_rescore_vbv1_paper_fsc_with_validated_judge_rewrite_tmlr_icml/PROTOCOL_AMENDMENT_C15.md) · [per-system thresholds](../../102_rescore_vbv1_paper_fsc_with_validated_judge_rewrite_tmlr_icml/PROTOCOL_AMENDMENT_C7.md) · [Fisher transformation](https://online.stat.psu.edu/stat505/Lesson05) · [average-rater reliability](https://pubmed.ncbi.nlm.nih.gov/28342902/) · [equivalence bounds](https://pmc.ncbi.nlm.nih.gov/articles/PMC5502906/) · [crossed rater and item dependence](https://doi.org/10.1214/12-AOAS547) · [standard deviation intervals](https://itl.nist.gov/div898/software/dataplot/refman1/auxillar/sdconfli.htm).
<!-- END RATING_TENSOR_SAMPLE_SIZE_11-04-2026.md -->

## Snapshot: FULL_BENCHMARK_FIXED_PANEL_11-05-2026.md

Original local path: `/Users/brandomiranda/veribench/experiments/ideas/leave_one_agent_out_fsc_judge_validation_on_human_ratings/FULL_BENCHMARK_FIXED_PANEL_11-05-2026.md`. Local working file; embedded GitHub main URL returned 404 on 11-11-2026. SHA-256: `203ccc1b0be888422bea42165c67e4765f151b7cf8133cdf81093002d1d2aaf3`.

<!-- START FULL_BENCHMARK_FIXED_PANEL_11-05-2026.md -->
# Human panel for all VeriBench tasks and four named solvers

**Doc link:** <https://github.com/brando90/veribench/blob/main/experiments/ideas/leave_one_agent_out_fsc_judge_validation_on_human_ratings/FULL_BENCHMARK_FIXED_PANEL_11-05-2026.md>

**TLDR:** For veribench@1.3, plan for 896 task folders, four named solver configurations, 64 completing qualified raters and two independent human ratings per output. This is 3,584 files and 7,168 human ratings. Each rater commits to 28 four-file folders. The primary endpoints are within-solver correlation with the human ratings and within-file repeat variance of the frozen judge.

[Google study notes](https://docs.google.com/document/d/1zB-gYk-zU1wToS_E_carGSRGtUcF1NgZ-jWF5t1SJws/edit) · [Published package at its pinned revision](https://github.com/brando90/harbor-datasets/tree/c9dfd8e3b535f58184440aa02d37c148d145a82c/datasets/veribench_v1_3) · [Benchmark-size accounting in the paper](https://openreview.net/pdf/2accae7bf4d97dbd20b9f0dd716156be8f105d6f.pdf).

The new handwritten pages describe the [fixed human panel](assets/handwritten_fsc_conditional_ratings_11-05-2026.md) and [conditioning inputs](assets/handwritten_fsc_conditional_inputs_11-05-2026.md). Each transcript links to the original photograph.

### What is fixed

Use all 896 Python task IDs from the scored release veribench@1.3 at package commit c9dfd8e3b535f58184440aa02d37c148d145a82c. Pin one solver configuration for each of Claude Code, Codex, Gemini and Grok. Model version, harness, instructions, tools and budget identify each configuration. Freeze one candidate per task and solver, along with the Python and Lean gold reference actually shown to both experts and judge. Retain every task–solver cell and report any missing output or invalid reference separately, with the valid-pair denominator. Separate any inputs used to develop the judge when reporting agreement on previously unseen tasks. The 896-task number includes 460 SecuritySet files in 230 safe/vulnerable pairs.

The ideal reference-free target is $p^{\mathrm{judge}}_j(r\mid y_{\mathrm{pred}},x_{\mathrm{input}})$. Here $r$ is a rating from 0 to 5, $x_{\mathrm{input}}$ is the Python task, and $y_{\mathrm{pred}}$ is the solver’s Lean output. The judge assesses whether the candidate states the guarantees the task calls for.

For this study use $p^{\mathrm{judge}}_j(r\mid x_{\mathrm{input}},y_{\mathrm{pred}},y^*)$, where $y^*=y_{\mathrm{gold\_ref}}$ is the gold Lean reference. This applies to a single human, a human panel or an AI judge. The Python source gives the behavior to formalize and, where present, docstrings or examples that describe the intended behavior. The judge scores how completely the candidate’s theorem statements cover the reference guarantees for that task. Equivalent or stronger statements count, and proofs are ignored. If the implementation, documented intent and gold reference appear to conflict, flag the specific discrepancy for review separately from the coverage rating. These three inputs match the [implemented judge](../../100_karpathy_recipe_tc_judge_search_human_train_val_test/JUDGE_EXPLAINER.md).

For a fixed panel of H named experts, the human distribution is the fraction of panelists assigning each rating under the rubric if each person gives a fixed answer. With stochastic rerating it is the equal mixture of their rating distributions. The AI distribution is induced by independent complete runs on the same inputs. Below, z denotes the triple (Python source, candidate Lean output, gold Lean reference), and p_H and p_J abbreviate the respective distributions. Correlation with experts and small judge variance operationalize the ranking and repeatability goal. A requirement that p_H and p_J be close for every file is stronger. For instance two humans can give a file 2 and 4, while the judge always returns their mean of 3.

### Recommended allocation

| Quantity | Count | Reason |
|---|---:|---|
| T, distinct tasks | 896 | Census of the selected release |
| A, solver configurations | 4 | Direct coverage of every requested system |
| H, qualified completing raters | 64 | Balanced staffing with a commitment of 28 four-file folders per person |
| r, independent human ratings per file | 2 | Two-expert consensus and direct individual-expert comparisons |
| Planned files | 3,584 | 896 × 4 |
| Human ratings | 7,168 | 896 × 4 × 2 |
| Folder assignments | 1,792 | Each of 896 task folders goes to two distinct raters |
| Proposed judge repeats K | 2 complete scores per file | 7,168 complete judge evaluations to estimate the mean within-file variance for each solver |

Schedule 28 rounds with 32 different rater pairs per round. Use different partners across rounds, blinded agent identities and randomized task folders spread across benchmark subsets. Each of 64 people then rates 112 files. A possible staffing schedule is four folders per person per week over seven weeks. This is a proposed commitment. The [existing volunteer plan](../../102_rescore_vbv1_paper_fsc_with_validated_judge_rewrite_tmlr_icml/human_round/PLAN_setN_rating_round.md) asked for only two to three folders in total. With a ten-folder ceiling a minimum of 180 people must complete their assignments. With a three-folder ceiling the minimum is 598. Count confirmed capacity after qualification. Freeze the named panel and the procedure for recording attrition before collection. Report any resulting gaps or panel changes.

### What the study can establish

Compute Spearman rank correlation across tasks separately for each of the four solvers against the mean of the two assigned human ratings. Report all four values and the lowest. To address agreement with one panelist, also report the correlation against a randomly designated individual rating with balanced representation. The two-rating mean is a noisy reference for a full-panel mean. Correlation with that reference defines the primary operational target directly. The frozen 896 files per solver form a census. For that fixed target, uncertainty concerns the random rater assignments, human scores if stochastic and judge runs. For a future-task inference, specify the task distribution separately and respect task-family dependence such as security pairs. With one frozen solver output per task the study covers that output and its judge repeats. Independent solver generations introduce a separate source of variation.

For solver a, define V_a as the mean over its 896 files of Var(J | z). With independent complete scores J₁ and J₂ on each file, the mean of (J₁ − J₂)²/2 is unbiased for V_a, even if each file has a different variance. Two full runs are the minimum for this estimate. Prespecify a practically small bound β on the chosen score scale and a correlation floor before examining the evidence. Compare upper confidence bounds on V_a to β and lower bounds on correlation to the floor for all four, accounting for the simultaneous claim and the balanced rater design. The confidence widths depend on the observed repeat noise and margins. K=2 provides limited evidence about variance on any single file. If there are serious consequences to instability on one file, prespecify a tail or worst-file target and allocate more independent repeats to that question. Historical per-component passes and repeats of the deployed aggregate are different quantities.

### How T, A and H enter

For a fixed file and threshold event such as “rating at least 4”, write the panelists’ 0/1 responses as y_h. For r distinct raters sampled uniformly without replacement from H, the variance of their mean is (1 − r/H) S²/r, with S² the finite-panel variance using denominator H−1. T and A do not enter this within-file formula. Observations on other files inform this file only through an assumed model connecting files.

For example, with H=64 and r=2, the other 62 ratings are unobserved. Without a model, the range of panel fractions that are consistent with those two observations has width 62/64. Measuring that fixed panel’s empirical rating distribution exactly on every file requires 64 × 3,584 = 229,376 human ratings, assuming one fixed response per person per file. Extra tasks can improve a task-population estimate, but increasing T cannot force p_J to approach p_H on a particular file. If the goal is prospective distributional fidelity, prespecify the probability distance, tolerated error and confidence level before sizing within-file human ratings and complete judge repeats. The choice of four named solvers directly defines the covered set. It does not require treating software products as randomly drawn from a population of future families.

This recommendation is a proposed expansion. It supplies a staffing budget and a way to measure both endpoints. Numerical evidence for acceptance comes from the actual scores.

### When correlation is the right selection objective

The [first page](assets/handwritten_fsc_selecting_a_judge_11-05-2026.md) and [second page](assets/handwritten_fsc_ordinal_rating_objective_11-05-2026.md) ask two distinct questions. The intended deployment is ranking outputs by expert-rated formal specification coverage, subject to a limit on random score changes on identical inputs. The probability mass function over 0–5 also lets us state a stronger question about matching the frequencies of all six ratings.

**Select for ranking.** Write $z_{ta}=(x_t,\hat y_{ta},y_t^*)$. For a candidate judge configuration $c$, let $s_{cta}$ be its scalar deployed rating, including its frozen aggregation, and $\bar h_{ta}$ the mean of the two assigned qualified ratings. Compute $\hat\rho_a(c)=\mathrm{Spearman}_t(s_{cta},\bar h_{ta})$ across tasks for each fixed solver. Use the smallest of the four correlations because the requirement applies to each solver. Prespecify how to handle ties and report a correlation as undefined if the scores on an axis are constant. If the judge is repeated, prespecify whether the deployed score is a single complete execution or an average. For single-execution deployment, one can estimate per-execution correlation using prespecified repeats rather than silently validating an average.

On validation, select $\hat c=\arg\max_{c:\max_a \widehat V_a(c)\le\beta}\min_a\hat\rho_a(c)$, where $V_a$ averages within-file variance over that solver’s tasks. The maximization returns the judge configuration. Minimizing $1-\min_a\hat\rho_a$ gives the same choice. If no candidate clears the variance constraint, report that outcome. The final test separately assesses whether the frozen candidate’s correlation and repeat variance clear prespecified practical thresholds with appropriate confidence bounds. If the application compares solver leaderboard means, add a paired comparison across agents on the same tasks. Per-agent correlations can stay high even if agent-specific score offsets reverse a leaderboard comparison.

**If predicting a human rating distribution becomes the aim.** A consistent two-point upward shift can yield perfect Spearman correlation and zero repeat variance. For example, three files with deterministic human ratings (1,2,3) and deterministic judge ratings (3,4,5) have exactly those properties and disagree on every file. For ordered ratings 0–5, the ranked probability score (RPS) against an individual expert rating $h$ is the sum over thresholds $u=0,\ldots,4$ of $(F_c(u\mid z)-\mathbf{1}\{h\le u\})^2$, optionally divided by five. Here $F_c$ is the cumulative rating probability. At each threshold the expected squared loss equals $(F_c-F_H)^2+F_H(1-F_H)$, so the expected loss is minimized at the human distribution. One can compare probability predictions by averaging this loss over files and held-out individual expert ratings without reconstructing the entire human distribution for each file. If the only available evidence for judge probabilities consists of independent complete runs, the ordinary empirical two-draw distribution gives a biased estimate of the infinite-run forecast’s score. A fair ensemble estimate at each threshold uses $(I_1-I_h)(I_2-I_h)$, with $I_i=\mathbf{1}\{J_i\le u\}$ and $I_h=\mathbf{1}\{h\le u\}$. Conditional independence of the two complete runs given the file and human observation makes its expectation equal to the desired squared loss. With only two runs it can be noisy. The operational target of small judge variance can conflict with reproducing human disagreement. [Gneiting and Raftery on proper scoring rules](https://sites.stat.washington.edu/raftery/Research/PDF/Gneiting2007jasa.pdf) · [Ferro on fair scores from finite ensembles](https://empslocal.ex.ac.uk/people/staff/ferro/Publications/ferro2013.pdf).

**Which sample goes where.** Develop prompts on training tasks, select a frozen finalist on validation tasks and use sealed test ratings once. Keep all outputs, raters’ scores and judge repeats for a Python task in the same split. Group closely related variants, including security pairs, together. Using external, task-disjoint training and validation data and preserving all 896 as genuinely untouched inputs would permit a full-benchmark test. Where historical or new selection has used some of those tasks, give both the descriptive full-census result and the clean held-out result with its actual denominator. The 896-task budget covers the whole release; the split determines the size of the independent test. The historical two-scenario precision calculation covered five fixed solvers and a different rater setup. The present four-solver census and roster are coverage and workload choices. Neither that prior calculation nor two repeats establishes power for a particular joint pass criterion without specifying thresholds, plausible effects and margins.
<!-- END FULL_BENCHMARK_FIXED_PANEL_11-05-2026.md -->

## Snapshot: CONDITIONAL_RATING_AGREEMENT_AND_TRANSFER_11-05-2026.md

Original local path: `/Users/brandomiranda/veribench/experiments/ideas/leave_one_agent_out_fsc_judge_validation_on_human_ratings/CONDITIONAL_RATING_AGREEMENT_AND_TRANSFER_11-05-2026.md`. Local working file; embedded GitHub main URL returned 404 on 11-11-2026. SHA-256: `dcd5cce1e057d55c60cbbb2a45c786fb7cefb14f7b23514bc74733e63e1b9d5a`.

<!-- START CONDITIONAL_RATING_AGREEMENT_AND_TRANSFER_11-05-2026.md -->
# What would show that the VeriBench judge reproduces expert ratings?

**Doc link:** <https://github.com/brando90/veribench/blob/main/experiments/ideas/leave_one_agent_out_fsc_judge_validation_on_human_ratings/CONDITIONAL_RATING_AGREEMENT_AND_TRANSFER_11-05-2026.md>

**TLDR:** If the target is the distribution of expert ratings conditional on the same file, select the judge for probabilistic accuracy on held-out individual ratings. Keep worst-solver rank agreement for the ordering decision and assess repeatability of what is actually deployed. The proposed census of 896 tasks and four named solvers requires 7,168 human ratings at two per file. A separate pilot must size the sealed test for the chosen practical margin.

[Study Q&A](https://docs.google.com/document/d/1zB-gYk-zU1wToS_E_carGSRGtUcF1NgZ-jWF5t1SJws/edit) · [Prior fixed-panel and correlation design](FULL_BENCHMARK_FIXED_PANEL_11-05-2026.md) · [Earlier rank-precision simulations](https://github.com/brando90/veribench/blob/01f639c1f2242cdef3b977715d91a7c978ea7fcd/experiments/ideas/leave_one_agent_out_fsc_judge_validation_on_human_ratings/RATING_TENSOR_SAMPLE_SIZE_11-04-2026.md). This is a proposed design for the clarified objective. No new human or AI agreement was measured.

## The question a correlation can answer

For a frozen input z = (original Python source, candidate Lean output, gold Lean reference), the two rating laws are P_J(r | z) and P_H(r | z). Choosing the best of several judges for expert-like ordering is a legitimate decision objective. On validation, calculate Spearman correlation **across tasks separately for each solver** between the deployed scalar score and the blinded human consensus, then choose the candidate with the largest minimum across the available validation solvers. Human–human agreement on the same files tells the reader how closely a second person reproduces another rater’s ordering. Neither correlation identifies a conditional probability law. A comparison of solver leaderboard means is another decision and should be evaluated directly with paired task differences.

Consider two equally weighted files on each of which experts give 0 or 5 with equal probability. Judge A also gives each score with equal probability on each file. Judge B always gives the first file 0 and the second file 5. Assume independent human and judge draws conditional on a file. For **both** judges, an unlabeled pooled scatterplot puts one quarter of the pairs at each of (0,0), (0,5), (5,0), and (5,5). Every pooled joint moment agrees; the conditional distributions differ. For threshold probabilities over normalized scores, the root mean squared discrepancy is 0 for A and 0.5 for B. B has zero repeat variance. The example also separates stable output from representing expert disagreement.

![Exact two-file example](results/pooled_scatter_and_conditional_ratings_11-05-2026.png)

## A direct measure on the 0–1 scale

Let F_J(u | z) be the judge probability that a score is at most u. Define F_H similarly. For fixed solver a, average the integral ∫₀¹(F_J(u | z) − F_H(u | z))² du over its target task files; call this D_a. It is zero exactly when the two distributions agree on all positively weighted files of a finite benchmark. Small average D_a allows some files to have large errors. The square root is a root mean squared probability gap averaged over tasks and uniformly weighted cutoffs on the normalized scale. If both outputs take only 0, 0.2, …, 1, the integral is the average over the five nontrivial ordinal cutoffs. The deployed judge averages member medians and can emit intermediate scores, so use the full integral or the union of supports with interval-width weights. The equal-spaced score scale is explicit. If consequences differ by cutoff, choose weights before selection. Matching means or a few moments discards distinctions. On six fixed levels, the first five moments plus normalization theoretically determine all six probabilities, but estimating five moments separately from two ratings per file is uninformative.

**Select on observed expert ratings.** Against one independent human score h, the continuous ranked probability score integrates (F_J(u | z) − 1{h ≤ u})². Its expected value equals the integrated squared discrepancy plus ∫F_H(1−F_H)du, a human-disagreement term shared by candidates on the same files. Thus minimizing this loss for a fixed solver recovers the human law in expectation when the candidate class can represent it. When comparing different solvers, their human-disagreement terms can differ. For a literal worst-solver discrepancy objective, estimate D_a or excess loss against the common human reference within each solver before taking the maximum. Taking the maximum of raw probabilistic losses asks a different question. On validation, minimize worst-solver discrepancy subject to any prespecified ranking/operational-stability requirements. Where selection sees three families only, minimize over those three. Freeze the choice before evaluating the fourth. [Proper scoring rules](https://doi.org/10.1198/016214506000001437)

For a judge that only produces sampled scalar scores, two independent complete outputs J₁,J₂ on the same input allow a fair estimate of its probabilistic loss against h: (|J₁−h|+|J₂−h|−|J₁−J₂|)/2. Average this over individual experts and files. A naive two-draw histogram creates sampling bias in the unadjusted score. With two human scores H₁,H₂ also drawn independently from the target expert population, an estimate of D_a averages the four cross-distances |J_i−H_j|, then subtracts half of each within-pair distance |J₁−J₂| and |H₁−H₂|. For simple uniform sampling of two distinct people without replacement from a fixed panel of M deterministic raters, multiply the human within-pair subtraction by (M−1)/M. Use the actual split or subgroup panel size and the true assignment design. Nonuniform team/vendor pairing, unknown repeat effects within an individual, or population claims require their own weighting, assumptions or data. A finite-sample discrepancy estimate may be negative; base inference on D and transform suitable nonnegative bounds for display. Raw proper-loss comparisons against individual experts do not require estimating a full per-file human histogram. [Fair ensemble scores](https://doi.org/10.1002/qj.2270) · [Energy distance](https://www.sciencedirect.com/science/article/pii/S0378375813000633)

**Judge randomness versus expert uncertainty.** If random executions themselves define P_J, demanding near-zero variance can conflict with matching a genuinely divided panel. A separately frozen judge that forecasts the six human rating probabilities could return the same forecast and scalar summary reliably on repeated executions even for a contentious file. Such an output would define a new judge condition. A scalar score alone is not a distribution forecast unless its law across complete runs is explicitly the quantity intended. Kullback–Leibler divergence (or log loss against a human draw) is justified for a probabilistic forecast if support is handled. With two sampled judge scores per file, unobserved categories create artificial zero probabilities, log loss can be infinite, and a penalty for an unseen true category does not reward placing the alternative mass on adjacent ordinal values. A finite-order cumulative score is easier to interpret here.

## A concrete split and a sample-size calculation

One feasible internal allocation for veribench@1.3 is shown below. Counts are planning targets, subject to keeping actual related task groups intact. Every split can still collect all four systems for the descriptive census under access controls.

| Split | Python tasks | Dedicated qualified raters | Human ratings with 4 solvers × 2 |
|---|---:|---:|---:|
| Training | 280 | 20 | 2,240 |
| Validation | 168 | 12 | 1,344 |
| Sealed test | 448 | 32 | 3,584 |
| Total | 896 | 64 | 7,168 |

Each person completes 28 four-file folders (112 ratings). Pair raters at random subject to balanced loads within each split; keep task variants such as safe/vulnerable pairs together and stratify task groups by benchmark subset. Keep all outputs and ratings of a task within its task split. Before choosing families, audit every judge candidate’s prior human-data, prompt and solver-family exposure. For one frozen judge and a feasible transfer test: develop on two families, allow a third in validation and reserve **every output, example and rating of the fourth family** until after freeze. Evaluate all four on the new test tasks and new raters. Only the fourth-family × test-task × test-rater block is held out simultaneously along the three axes. One held-out family is evidence about that family. If all four genuinely qualify as unseen because selection was entirely external, report all four as such. Leave-one-family-out runs answer a different question about the *selection procedure* across four fits. The per-file primary human reference and the rate of missing outputs should be reported by solver. A total of 64 completers comes from workload arithmetic; 32 test raters do not establish representativeness of every kind of expert. The intended expert population, qualification rules and sampling route determine that claim.

The earlier 250-task calculation assessed worst-solver Spearman estimation in two simulated scenarios. Power for this new endpoint needs the new endpoint’s variability. For an illustration, suppose acceptance is D_a < 0.04 for all four solvers, the true largest D_a is 0.01 and the task-level standard deviation of its estimator is 0.15. Those three numbers are illustrative choices. A conservative simultaneous one-sided normal approximation for four reported upper bounds has z_(1−.05/4)=2.241; allowing at most .10/4 probability of missing per solver gives z_(1−.10/4)=1.960. Effective independent units per solver ≈ ceil[((2.241+1.960)×0.15/(0.04−0.01))²] = 442. At standard deviation 0.10 it is 197; at 0.20 it is 785. These are assumptions about independent equivalent units, not sample-size guarantees. The same reviewers score many files, related tasks reduce independence, and correlation plus repeatability criteria can change joint power. The proposed 448 raw test tasks are only a starting allocation.

Use a task-disjoint pilot with the exact planned rater and judge-repeat design (reuse eligible existing data). Estimate paired task-level variances and rater variation while keeping the final test sealed. Simulate the crossed assignment, selection, ties, plausible distribution shifts, missingness, and all frozen acceptance decisions. Increase the effective test sample, ratings per file, number of rater identities, or number of complete judge repeats according to the uncertainty that limits the decision. Increase **distinct held-out families** if transfer across families limits the claim. Set a minimum useful difference from unconditional and simple heuristic baselines and an absolute tolerance based on what would change a scientific or leaderboard decision. A statistical test of exact equality is poorly matched to practical equivalence.

## What to show a reviewer

Before opening the sealed scores, publish or timestamp the target, task groups and held-out families, margins, selection rule, inclusion rules, repeated-score procedure and planned intervals. Show per-solver results and the simultaneous lower rank and upper discrepancy bounds, conditional agreement by score range, missing counts and judge repeatability. Account for repeated raters and clustered tasks according to the actual population target. Distinguish finite-benchmark census summaries from transfer to future tasks. Report how far the AI lies from human–human rank agreement on the exact same files. The previous [second-human comparison](../../102_rescore_vbv1_paper_fsc_with_validated_judge_rewrite_tmlr_icml/PROTOCOL_AMENDMENT_C15.md) specified a rank-difference margin of −0.10; this does not set the new distributional tolerance.

Compare at least a train-only unconditional human-category-frequency predictor and a simple coverage heuristic on the same test files. Show gold/reference, vacuous and wrong-task controls and worked disagreements. For the practical claim about using the judge to compare solvers, report every paired difference of system means with uncertainty and identify any reversal against expert means or any comparison too close to resolve. A sufficient conclusion states the actual estimand, family, task and rater coverage, uncertainty and margins met or missed. A synthetic illustration or a held-in result is not a judge validation outcome.

[Source for the exact illustrative figure](scripts/illustrate_conditional_rating_agreement.py) · [Existing judge inputs and controls](../../100_karpathy_recipe_tc_judge_search_human_train_val_test/JUDGE_EXPLAINER.md).
<!-- END CONDITIONAL_RATING_AGREEMENT_AND_TRANSFER_11-05-2026.md -->
