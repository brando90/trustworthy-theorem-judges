# Probabilistic ordinal judges of formal specification coverage

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/02_probabilistic_ordinal_judge/README.md>

**TLDR:** Predict the conditional distribution of expert ratings with a six-category probability forecast, select the judge by ranked probability score, and evaluate fresh outputs with separate task, agent, and human holdouts.

**Status, 11-06-2026:** Planned methodology; new human ratings, judge selection, and final results are pending. The counts below are an initial budget, not a demonstrated sufficiency guarantee or a completed preregistration.

This repository studies artificial intelligence (AI), agent, and large language model (LLM) judges of formal specification coverage (FSC). VeriBench's separate direction is a prover judge, with AI guiding proof search; this study does not implement that migration or report new prover results. Historical scalar LLM-judge evidence is a baseline, not evidence that the new probabilistic judge works.

The accepted design comes from the user's [shared planning conversation](https://chatgpt.com/share/6aee2147-9648-83e8-9ea5-685a565ffe54). This document makes the planned data collection and analysis explicit. It supersedes earlier human-count proposals for this experiment.

**Rating-count source recovery, 11-11-2026:** [Original Claude, Gemini and ChatGPT text, links and sizing decision](rating_tensor_planning/README.md) compare standard errors, learning theory and scaling laws. The historical budget below remains unchanged; the new 544-rating pilot is a prospective proposal, not an executed amendment.

## Target and measurement

For each candidate artifact, use the same triple for humans and the judge:

\[
z=(x_{\mathrm{input}},y_{\mathrm{pred}},y^*),
\qquad r\in\{0,1,2,3,4,5\}.
\]

Here, the inputs are the Python source, candidate Lean output, and gold Lean reference. FSC concerns coverage of the required formal specifications, meaning theorem statements without their proofs; proof completion is a separate property. A reference can be incomplete or wrong, so agreement with reference-assisted humans is not itself a proof of semantic correctness.

Define the human target as the probability mass function

\[
p^*(r\mid z)=\Pr(\text{a qualified expert assigns }r\text{ to }z)
\]

under the specified rubric and expert sampling population. The initial judge interface explicitly elicits a structured six-probability vector, rather than deriving it from token likelihoods or repeated scalar answers. The judge returns six nonnegative probabilities \(q_\theta(r\mid z)\) that sum to one. Its expected normalized score is \(\sum_{r=0}^5 r q_\theta(r\mid z)/5\). Preserve the probability vector and each individual human rating; do not reduce disagreements to one consensus rating.

The target is agreement **conditional on the same artifact**, then averaged across artifacts. Pooled rating histograms can match perfectly while the judge swaps every high and low rating. Repeated stochastic scalar outputs from an LLM are not automatically predictions of human disagreement. This six-probability output is a new experimental condition.

## Primary objective

For \(Q_c=\sum_{r=0}^c q_r\), use the normalized ranked probability score (RPS):

\[
S(q,r)=\frac15\sum_{c=0}^4\left(Q_c-\mathbf1\{r\le c\}\right)^2\in[0,1].
\]

Let \(P_c\) be the true cumulative human probabilities. Then

\[
\mathbb E_{R\sim p^*}S(q,R)
=\underbrace{\frac15\sum_c(Q_c-P_c)^2}_{\text{conditional distribution error}}
+\underbrace{\frac15\sum_cP_c(1-P_c)}_{\text{human disagreement}}.
\]

Thus, minimizing expected RPS targets the entire conditional rating distribution; its unrestricted optimum is \(q=p^*\). On the normalized rating scale, the Wasserstein distance is \(W_1(q,p^*)=\frac15\sum_c|Q_c-P_c|\), and \(W_1^2\) is at most the excess expected RPS. This justifies the objective, not a claim that any chosen judge achieves it. Proper scoring rules are established methodology ([Gneiting and Raftery, 2007](https://sites.stat.washington.edu/raftery/Research/PDF/Gneiting2007jasa.pdf)).

For artifact \(i\) with \(m_i\) assigned raters, optimize

\[
\widehat L(\theta)=\frac1n\sum_{i=1}^n\frac1{m_i}\sum_h S(q_\theta(z_i),r_{ih}).
\]

Average ratings **within each artifact first**, then average artifacts equally. The dense subset must not gain extra weight merely because more raters rate it. With complete task-agent coverage, this also weights the four agents equally. Missing artifacts require an explicit missingness analysis rather than an unnoticed change in weights.

## Initial data collection budget

Use all **896 tasks of `veribench@1.3`**, with the dataset source pinned to [`harbor-datasets@c9dfd8e3b535f58184440aa02d37c148d145a82c`](https://github.com/brando90/harbor-datasets/tree/c9dfd8e3b535f58184440aa02d37c148d145a82c/datasets/veribench_v1_3). Verify the manifest and file hashes before collection. This is a fixed benchmark claim, not a claim about every future programming task.

| Design element | Planned allocation |
|---|---:|
| Task identities for training / validation / held-out test | 64 / 64 / 768 |
| Required solver configurations | 4: Claude Code, Codex, Gemini, Grok |
| Distinct qualified raters | 24: 8 for training/validation, 16 for final audit |
| Base ratings per artifact | 3 distinct randomly assigned raters |
| Dense diagnostic subset | 128 randomly selected held-out test tasks, all 4 solvers |
| Ratings per dense artifact | 8 total, including its 3 base ratings |
| Solver outputs per task-agent pair in each collection stage | 1 initially |

The four names specify required systems, not exact reproducible configurations. Pin model version, harness, tools, effort, prompt, budget, generation seed policy, and failure policy before generating outputs. They are four deliberately selected systems, not four independent random draws from a population of all agents.

| Collection stage | Distinct solver artifacts | Human ratings |
|---|---:|---:|
| Training + validation: 128 tasks × 4 agents | 512 | 512 × 3 = 1,536 |
| Final audit: 896 tasks × 4 agents | 3,584 | 3,584 × 3 = 10,752 |
| Five extra ratings on 128 × 4 final-audit artifacts | 0 | 512 × 5 = 2,560 |
| **Total** | **4,096** | **14,848** |

The final audit uses **fresh generations**, including on the 128 tasks seen during training or validation. Those 512 final-audit artifacts must have different generation records from the 512 training/validation artifacts, even if a deterministic solver happens to produce identical bytes. Report the 128 seen-task/fresh-output results separately from the 768 held-out-task results.

Balanced assignment gives **192 ratings per training/validation expert** and **832 ratings per final-audit expert**. These are rating counts, not measured time commitments. Measure minutes per review and fatigue effects during the pilot. The dense subset supplies better distribution diagnostics; eight ratings do not reveal the exact population distribution for an artifact.

## Identity splits and assignment

1. Group related task identities before splitting. In particular, related security variants stay together; never split individual rating rows or near-duplicate artifacts across training, validation, and test. Preserve exact 64/64/768 counts only if grouping permits them; otherwise amend the design and recompute its budget before inspection of test results.
2. Recruit the 8 training/validation experts and 16 final-audit experts as disjoint pools from the declared qualified population. Record qualifications, recruitment frame, exclusions, and nonresponse privately. The final-audit raters supply no ratings for judge selection.
3. Assign 3 different raters per artifact at random with balanced workload and overlap, without solver identity or other raters's ratings visible. Give 5 additional distinct audit raters each dense artifact. Record assignment probabilities and the random seed. Dense tasks are selected randomly from the 768 held-out tasks before seeing their ratings.
4. Use opaque rater identifiers in analysis. Keep names, emails, consent records, payment information, raw ratings, and sealed task assignments in private storage. Public release needs a separate consent and data-release decision. This is a prospective privacy/release policy, not a claim that name-hiding improves accuracy. For the inherited collection in experiment 09, Brando authorized tracked names and individual ratings on 11-11-2026; use its [identity and import workflow](../09_human_rating_collection/support/IDENTITY_AND_IMPORT.md). Stable IDs remain alongside display names; solver blinding and sealed test access are separate.
5. Use the same instructions and byte-identical Python/candidate/reference contents for humans and the judge. The main study shows both raters and the judge the complete candidate and reference artifacts, including proof bodies or `sorry` placeholders; proof completion is recorded separately. Keep original ordinal ratings; normalized scores are derived by dividing by 5.

The tensor is sparse: 24 distinct raters does **not** mean 24 ratings on every artifact. Retain an assignment table rather than filling absent cells with zero. People are reused across artifacts, so those ratings are dependent.

## Training, selection, and transfer

Fit candidate judges on the 64 training tasks, then select using artifact-weighted mean validation RPS on the 64 validation tasks. Record every candidate, prompt iteration, input choice, and score-mapping fit. Human-group cross-validation within the eight training/validation raters may guide selection; it does not replace the separate audit pool. Repeatedly inspected validation results are selection evidence, not independent test evidence ([Cawley and Talbot, 2010](https://www.jmlr.org/papers/v11/cawley10a.html)).

Run five procedures:

- **Main judge:** train and select using all four agents' training/validation outputs.
- **Four leave-one-agent-out judges:** for each target agent, train and select using only the other three agents' outputs. Exclude target-agent outputs and ratings from both training and validation, including prompt examples and human rationales used to construct that fit. Evaluate on the target agent's 768 held-out tasks with final-audit raters.

The four transfer procedures reuse the collected final-audit ratings; they do not require four extra human rounds. This tests whether the **judge training/selection procedure** transfers to each excluded configuration. It does not establish that the main judge trained on all four generalizes to every future agent. Record prior experiment and pretraining exposure; a leave-one-agent-out split cannot erase historical exposure to that model family.

Before opening final ratings, fix judge versions, analysis code, endpoints, treatment of failed/missing calls, all thresholds, and the number of repeats. Evaluate the final test once. Later changes are new conditions requiring fresh test evidence for clean claims.

## Analysis and criteria

**Evaluation panel clarification, 11-09-2026:** normalized ranked probability score (RPS) remains the primary held-out metric and the common validation criterion. Cross-entropy (CE) and total variation distance (TVD) are secondary evaluation metrics for every training objective, alongside the full [methods 2 and 4 panel](PRIORITY_2_VS_4_11-09-2026.md#shared-held-out-evaluation-metrics). This prospective clarification does not change completed protocols or results.

CE averages `-ln(q_i(r))` over the individual ratings within each artifact and then equally across artifacts. TVD averages `(1/2) sum_r abs(q_i(r) - p_hat_i(r))` equally across artifacts, where `p_hat_i` is the artifact's empirical human rating distribution. Both are lower-is-better metrics. TVD ranges from 0 to 1 and is a sparse-rating distribution diagnostic; it is not total variation distance mutual information (TVD-MI), a proper individual-rating loss, or an estimate that removes finite-rater noise. The [offline evaluator](native_probability/README.md) reports TVD with full-denominator missingness bounds; they do not replace confidence intervals or a prespecified missingness policy.

Report artifact-weighted mean RPS and paired differences against: (1) a constant human-rating distribution estimated on training ratings, (2) a fixed rubric/reference-assisted judge, (3) a correlation-selected judge, and (4) the RPS-selected judge. Also include a non-LLM theorem-count baseline: clip candidate/reference statement-count ratio to [0,1], multiply by five, and distribute probability linearly between the adjacent integer rating categories (all mass at five for a ratio of one). A reference with no countable statements is an invalid baseline input. Fix the counting rule in the pilot. Use matched artifacts and record unequal model-call budgets. The correlation-selected and RPS-selected conditions must search the same candidate set with matched information access and search budget to isolate the selection objective. Historical scalar judges are not automatically probability forecasts: either compare scalar metrics alone or define and record a probability-output conversion as a new baseline condition.

Report separately: all 896 final-audit tasks; the 128 seen tasks with fresh outputs; the 768 held-out tasks; each agent; and each of the four transfer procedures. Show counts, failures, missingness, and 95% intervals. If claiming all four systems meet a criterion, use simultaneous uncertainty statements for those four claims.

Raw RPS contains irreducible human disagreement. A three-vote histogram is also noisy. For a threshold \(c\), let \(X_h=\mathbf1\{r_h\le c\}\). Under independent draws from the declared expert population,

\[
\widehat D_c=(Q_c-\bar X)^2-\frac{s_X^2}{m}
\]

is unbiased for \((Q_c-P_c)^2\), where \(s_X^2\) uses denominator \(m-1\). Average across thresholds and artifacts. Individual corrected estimates can be negative; do not clip them before averaging. For a **fixed finite panel** of \(H\) raters with simple random sampling without replacement, use the corresponding finite-population correction \((1-m/H)s_X^2/m\) instead. Balanced assignment may require design-specific variance calculations. The chosen estimand and sampling assumptions must accompany the result.

Use uncertainty procedures that respect task groups and reused raters under the actual sparse assignment. Fix the task/rater resampling or model-based analysis and check its behavior using pilot data before test inspection; do not bootstrap individual rating rows as if independent. Report an analysis conditional on the fixed panel separately from a population-of-experts analysis. With only 16 audit raters, population inference can remain imprecise. The four named agents stay fixed in the primary analysis ([Owen and Eckles, 2012](https://arxiv.org/abs/1106.2125)).

Secondary diagnostics are Pearson correlation, Spearman correlation, Kendall tau-b, mean absolute error, and signed mean bias of expected normalized judge rating minus mean normalized human rating, with both means. Compare human-human agreement on matched artifacts. Keep model-call instability separate from predicted human disagreement: repeated probability vectors and their expected ratings need their own standard deviations and repeat counts.

Success margins, minimum improvement over baselines, maximum distribution error, maximum repeat variability, and maximum failure rate are **not yet chosen**. Set them from the intended use and a pilot that excludes final-audit raters and test tasks. The planning config records these as `null`; no pass/fail conclusion is available.

## Semantic validity checks

Before scoring, specify expected changes under controlled edits and establish the relationship with checked implications or counterexamples where possible:

| Controlled edit | Expected FSC response |
|---|---|
| Remove a necessary specification obligation | Lower coverage |
| Narrow a precondition to exclude required inputs | Lower coverage of the required domain |
| Use a semantically equivalent specification | Similar coverage |
| Add irrelevant or vacuous statements | No meaningful increase |
| Supply an incomplete or faulty reference | Detect/report the discrepancy where possible |
| Change only proof completion, preserving statements | Similar coverage |

Keep these controls separate from the randomly sampled audit and report their denominators. Numeric tolerances and control counts are pending pilot decisions. Independently inspect reference defects; matching experts who share a defective reference does not establish correct FSC. Before broad collection, trace one artifact from generation through extraction, human display, judge input, probability parsing, and score computation; bind every step by content hashes. Check valid probability vectors, scale mapping, and expected responses to positive, negative, and literal-instruction controls. Include a rating-in-prompt reproduction check: supply an artificial known rating, then verify that the output parser and normalization reproduce it. This pipeline test is excluded from semantic performance estimates and the test set.

## Why these counts, and what they cannot guarantee

The 64/64 training/validation tasks are a starting allocation for selecting a pretrained judge. The 768 held-out tasks preserve task coverage for the final estimate. Three ratings support an estimate of the proper loss; the additional dense ratings support conditional-distribution diagnostics. The larger number of distinct raters addresses human variation that repeated work by the same few raters cannot remove. Use pilot variance, learning curves, overlap, and workload to revise the allocation **before** final test inspection.

As an illustration only, a human-specific loss-effect standard deviation of 0.10 gives a normal-approximation 95% half-width contribution of \(1.96(0.10)/\sqrt{16}\approx0.049\), versus approximately 0.080 for six raters. This is one hypothetical variance component, not a measured total interval. More ratings improve precision; they cannot make a biased or semantically wrong judge correct.

A fully crossed independent-identities bound or a formula in the product \(TAH\) is not a sample-size guarantee for this sparse study. Four deliberately selected systems, related tasks, and reused raters violate a naive independent-rating calculation. Claims are limited to the specified benchmark, evaluated solver configurations, and justified expert population. New model versions and new populations need prospective evaluation.

## Files and next collection steps

```text
02_probabilistic_ordinal_judge/
├── README.md                  # Design and analysis contract
├── config.json                # Planned counts and unresolved choices
├── scripts/validate_design.py # Deterministic count/consistency check
└── sources/                   # Byte-exact accepted plan and provenance
```

Run `python3 experiments/02_probabilistic_ordinal_judge/scripts/validate_design.py` from the repository root. It checks this planned allocation; it does not run judges, generate ratings, or establish readiness to launch.

Coordinate preparation and collection through [`experiments/09_human_rating_collection/`](../09_human_rating_collection/README.md); its inherited packets do not replace this prospective design. Next, create the private task-group manifest and rater assignment from these counts, run the training/validation pilot, set the remaining margins and budgets, and record a dated protocol amendment before collecting final-audit ratings. Each artifact record needs task/group/split IDs, stage, agent configuration ID, generation ID, Python/candidate/reference hashes, rubric hash, and judge-input hash; each rating needs its artifact ID, opaque rater ID, pool, ordinal value, timestamp, and assignment record. Each prediction needs probabilities, parsed status, judge/prompt/version IDs, repetition ID, cost receipt, and input hash. The final analysis must be reproducible from these records without exposing identities or sealed ratings in this public repository.

The adopted plan is preserved verbatim in [sources/gpt_pro_plan_11-06-2026.txt](sources/gpt_pro_plan_11-06-2026.txt), with [hash and source provenance](sources/provenance.json). A dated adoption summary is also in the [Google methodology notes](https://docs.google.com/document/d/1zB-gYk-zU1wToS_E_carGSRGtUcF1NgZ-jWF5t1SJws).

The separate [prover-target study](../03_prover_target_fsc_judge/README.md) applies a binary proper loss to acceptance by a specified proof-search procedure. It can proceed without human ratings for that operational target, but does not establish the human-rating agreement studied here.
