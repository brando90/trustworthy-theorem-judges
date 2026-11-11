# Formal Judge Design — ChatGPT source bundle

**Doc link:** <https://chatgpt.com/c/6aecd8ba-8cd0-83e8-abbd-9b2df24689b2>

**TLDR:** Recovered source text, not an approved protocol.

**Captured:** 11-11-2026. The shared snapshot is complete as displayed (10 messages); it is not the complete later conversation. The related branch begins mid-conversation and supplies 10 available messages. The connector supplement supplies nine recent messages. Both live chats showed "Loading older messages…" without recovering the missing interval. The older adopted source calls the model **GPT Pro**; exact historical backend is unverified. Historical per-message effort is unverified. Some original rendered tables are malformed around unescaped vertical bars; no missing cells were reconstructed. Equations and actual anchor URLs are preserved; unresolved citation-chip IDs in the connector supplement do not imply recovered URLs. Image bytes, tool traces and interactive widgets are outside this text export.

# Shared snapshot — 10 displayed messages

Source: <https://chatgpt.com/share/6aee2147-9648-83e8-9ea5-685a565ffe54>

## Message 1 — user

image(20261105-195936).pngImageimage(20261105-195951).pngImage

How does this change your thinking?

I also need a final recommendation for how many human's H we'd need, agents A we'd need (ideally we need it to at least work for top 4 frontier agents eg CC, codex, gemini, grok) and def all tasks for a fixed benchmark (like veribench)

## Message 2 — assistant

Yes—these notes change the statistical target enough that I would revise my recommendation. My final recommendation is: five fixed human experts, the four solver systems you named, and every task in the fixed benchmark. Collect two independent solver outputs per task–agent pair: one for development and one for an untouched final audit.

Have all five experts independently rate every output. That gives you:
\(\boxed{|H|=5,\qquad |A|=4,\qquad |T|=\text{all benchmark tasks},\qquad K=2.}\)
Here \(K\) counts independent solver outputs, not repeated calls to the judge.

| Decision | My recommendation |
| --- | --- |
| Human panel | Five fixed, qualified experts |
| Solver systems | Claude Code, Codex, Gemini, Grok, each as a precisely specified configuration |
| Tasks | Every task in a versioned VeriBench release |
| Development data | One output from each solver on every task |
| Final audit | A fresh output from each solver on every task |
| Human coverage | All five experts rate each output |
| Total generated outputs | (8 |
| Total human reviews | **(40 |

For illustration, a 170-task benchmark would require 1,360 generated outputs and 6,800 human reviews, including 680 outputs in the final audit. I’m using 170 as an example, not asserting that it is the size of your current version.

Five is my practical panel-size recommendation. It is not a theorem that five humans are sufficient to represent all possible experts. Your new formulation makes a more precise and achievable claim: reproduce the rating distribution of these five experts, then test how accurately the judge does so.

## 1. What changes in my thinking

Your strongest new idea is:
\(p_H(r\mid x)\approx p_{\mathrm{AIJ}}(r\mid x),\)
where \(H\) is a fixed set of humans.

That gives us an operational target. I would make four changes to the previous proposal.

### First: preserve the human distribution as the primary target

Previously, I emphasized adjudicating human ratings into a reference score. For your revised objective, keep each expert’s independent rating and make their distribution the primary target.

Adjudication remains useful for resolving factual mistakes and determining whether an acceptance is substantively wrong. But replacing the original ratings with a consensus label would erase the disagreement you now want the judge to predict.

This distinction has precedent in work on learning from annotator disagreement, although that literature does not itself establish performance for formal-specification judging. [ACL Anthology](https://aclanthology.org/2022.tacl-1.6/?utm_source=chatgpt.com)

### Second: use a fixed-benchmark experiment

You want the judge to work on all tasks in this benchmark. Consequently, those tasks can appear in both development and evaluation.

What must be held out for the main test is the new candidate submission and its human ratings.

For example, the judge may encounter VeriBench task 37 during development. In the final audit, it evaluates a newly generated specification for task 37. That directly tests the capability you care about: judging another submission for a known benchmark task.

A separate held-out-task experiment would address transfer beyond the fixed benchmark. It is useful later, but it is not necessary to make your first claim precise.

### Third: four agents are sufficient to define the requested scope

I would revise my earlier suggestion of six solver systems to the four systems you actually want covered.

You do not need additional agents merely to claim performance on these four. You do need to measure performance separately for each one.

“Agent” should mean a complete configuration:
\(a=(\text{model version, agent software, tools, instructions, budget, settings}).\)
Claude Code and Codex identify agent systems; Gemini and Grok also need specified execution environments. Record the exact configurations so that the results refer to reproducible systems.

### Fourth: human disagreement becomes something to reproduce

The judge should predict that experts disagree when they do disagree.

That changes what “small variance” should mean. You want a stable estimate of the human rating distribution, while allowing that distribution itself to have substantial spread.

## 2. Define the fixed-panel target precisely

I would write the judged item as
\(z_{tak}
=
\left(
x_t,\;
s_{tak},\;
g_t,\;
e_{tak},\;
\mathcal U
\right),\)
where:

- \(x_t\) is the task, including the original source and description.
- \(s_{tak}\) is solver \(a\)’s \(k\)-th submitted artifact.
- \(g_t\) is the gold reference.
- \(e_{tak}\) is relevant checking evidence.
- \(\mathcal U\) is the rating rubric.

Your observation that the gold reference is missing from the notation is correct. I would include it explicitly. If the reference is already a deterministic part of the task, omitting it can be harmless shorthand mathematically; the actual evaluation protocol should still give humans and the judge the necessary reference information.

Fix the five experts’ identities, the reference version, the rubric, and their weights. Fixing only the number five leaves the target ambiguous because different panels can judge differently.

For a categorical rating scale, define
\(p_H(r\mid z)
=
\frac{1}{5}
\sum_{h=1}^{5}
\mathbf 1\{r_h(z)=r\}.\)
For numerical ratings, the corresponding object is the empirical distribution placing weight \(1/5\) on each expert’s score.

Once all five experts have rated an artifact, its observed five-person distribution is fully known. There is no uncertainty from having sampled only part of that panel.

There are nevertheless three distinct targets:

| Target | What five ratings establish |
| --- | --- |
| The five experts’ recorded ratings on this artifact | The complete observed panel distribution |
| How those same experts would rate it on another occasion | An estimate; blind repeat ratings can reveal instability |
| How a broader population of experts would rate it | A small panel observation; broader claims require a sampling argument |

For the first VeriBench study, I recommend the first target, with rerating stability reported separately.

## 3. Two claims in the notes need correction

### Increasing \(A\) does not recover the human population

The handwritten line involving \(A\to\infty\) does not follow.

More agents provide more kinds of submissions. They do not provide more human perspectives on an already specified submission.

If you meant convergence toward a broader human population’s rating distribution, that would require additional, appropriately sampled humans, along with assumptions about representativeness.

For the fixed-panel target you now propose, there is no need to take that limit. The five-person panel is the chosen reference population.

### Increasing \(T\) does not automatically make the judge correct

More labeled tasks or submissions can help learn the mapping
\(z\mapsto p_H(\cdot\mid z).\)
Success still depends on whether the judge can represent that mapping, whether the training procedure learns it, and whether the examples cover its failure modes.

Also, a fixed finite benchmark has a fixed number of tasks. Once all tasks are included, the main expandable dimension is new submissions for those tasks.

This is why I would add \(K\), the number of independent solver generations, to your tensor:
\(Y_{takh}
=
\text{expert }h\text{’s rating of output }k
\text{ from agent }a\text{ on task }t.\)
Your original \(T\times A\times H\) tensor implicitly contains only one submission per task–agent pair. The extra generation dimension is necessary for separating development from a meaningful new-submission test.

## 4. Predict a distribution directly—and measure the right variance

Suppose three panelists consider a specification adequate and two consider it inadequate.

The observed panel distribution is
\(p_H(\text{adequate}\mid z)=0.6,\qquad
p_H(\text{inadequate}\mid z)=0.4.\)
A judge can return that probability vector consistently on every call. Its returned estimate is stable, while the human distribution it predicts remains uncertain.

That is the behavior I would aim for.

I would distinguish:

| Quantity | Desired behavior |
| --- | --- |
| Spread of the predicted human ratings | Match the panel’s spread |
| Error in the predicted distribution | Small |
| Variation in the returned probability vector across repeated judge calls | Small |
| Uncertainty in the reported evaluation statistics | Quantified |

Repeated stochastic LLM scores are not automatically samples from the human distribution. The judge needs to learn or calibrate its distribution predictions against the human labels.

### Your ICC observation is useful, but “we can’t beat it” is too strong

Human disagreement can create irreducible error when predicting a particular person’s next vote. But it does not prevent a judge from correctly predicting the distribution of votes.

A judge can also predict the panel’s mean more accurately than a single panel member does. Thus, human–human agreement is a useful comparison, rather than a universal upper bound on every judge metric.

For categorical ratings, this is especially clear through the normalized Brier loss:
\(L(q,r)=\frac12\|q-e_r\|_2^2,\)
where \(q\) is the predicted probability vector and \(e_r\) represents the observed category. Averaging over the full panel gives the exact identity
\(\frac1H\sum_h L(q,r_h)
=
\underbrace{\frac12\|q-p_H\|_2^2}_{\text{distribution prediction error}}
+
\underbrace{\frac12\left(1-\|p_H\|_2^2\right)}_{\text{panel disagreement}}.\)
The second term remains even when \(q=p_H\). It should not be interpreted as judge error. The Brier score is a strictly proper scoring rule: its expected loss is minimized by predicting the target distribution. [sites.stat.washington.edu](https://sites.stat.washington.edu/raftery/Research/PDF/Gneiting2007jasa.pdf?utm_source=chatgpt.com)

### My choice of distribution metric

For ordered numerical FSC ratings, I would use Wasserstein-1 distance, after normalizing scores to \([0,1]\):
\(d(z)
=
W_1\!\left(
q_\theta(\cdot\mid z),
p_H(\cdot\mid z)
\right).\)
It accounts for how far apart the rating values are. Moving probability from 0.8 to 0.9 is a smaller discrepancy than moving it from 0.1 to 0.9.

Keep the existing rating scale. For training, use a proper distributional loss: Brier for categorical ratings, or a ranked probability score/CRPS for ordered or continuous ratings. Proper scoring rules provide a principled way to train and evaluate predicted distributions. [stat.uw.edu](https://stat.uw.edu/research/tech-reports/strictly-proper-scoring-rules-prediction-and-estimation-revised?utm_source=chatgpt.com)

This also avoids a problem with total variation on continuous ratings: a smooth predicted distribution and a five-point empirical distribution can have total variation distance one despite placing their mass at numerically close scores.

## 5. Why I recommend exactly five humans

I recommend five total panel members, with all five rating every artifact.

The reasons are practical:

- Five provides several expert perspectives on each specification.
- The complete panel distribution is directly observed.
- You can inspect which disagreements are systematic rather than losing them in a majority vote.
- You can perform leave-one-expert-out analyses and compare three-person subpanels against the five-person panel.
- The cost is already substantial once you cross every task with four agents and separate development from testing.

For this particular distributional objective, I prefer that design to three ratings from a rotating pool of eight or ten people. A rotating design can estimate useful quantities, but it leaves the full panel distribution unobserved on each artifact. Computing a nonlinear discrepancy against an incomplete histogram then requires additional statistical care.

The five-person choice defines an interpretable reference panel. It does not establish that every five-person panel is accurate or representative.

The reviewers need competence in Lean and the relevant program semantics. The rubric, gold references, and checking evidence should receive review before the final audit. Have experts score independently before discussing disagreements.

Keep two records where necessary:

- The independent ratings used for distribution matching.
- The subsequent evidence-based resolution of substantive errors.

A model that perfectly reproduces a shared human mistake has achieved panel agreement, but the formal-specification claim still needs the semantic checks discussed earlier.

## 6. The study I recommend running

Use the following two rounds.

| Round | Outputs | Human reviews | Purpose |
| --- | --- | --- | --- |
| Development | (4 | T | ) |
| Untouched final audit | (4 | T | ) |
| Total | **(8 | T | )** |

All tuning happens in the development round. You can subdivide or cross-validate within that round for model selection. Keep every artifact’s five ratings together when splitting data.

After development, fix the judge, rubric, checking budget, and acceptance policy. Generate the audit outputs with fresh contexts under the same specified solver protocols. Report exact output overlap if it occurs; repeated identical outputs provide limited evidence about handling different submissions.

Every task–agent pair should be accounted for, including generation failures and unusable specifications.

### Why two rounds are my main recommendation

One round used for both developing and evaluating the judge would provide an overly optimistic assessment. Two rounds give you a direct new-submission test while keeping annotation cost lower than a mandatory three-round study.

A distinct development/calibration/audit workflow is also valid. If you choose that workflow, use three outputs per task–agent pair and budget \(60|T|\) reviews. I would start with the two-round design, with all selection completed before the final audit.

For the hypothetical 170-task case:

- Each expert reviews 1,360 artifacts across both rounds.
- The panel completes 6,800 reviews in total.
- The final audit contains 170 outputs from each of the four solvers.

A “review” here can contain all rubric scores and the supporting rationale; it is not merely clicking one label. Measure the time per review before scheduling the annotation effort.

## 7. Where \(H\), \(A\), and \(T\) now enter the mathematics

The fixed scope changes the role of the axes.

### \(H\) defines the panel target

For the fully observed five-person histogram, you do not obtain an additional factor of five independent artifacts by having five ratings.

The main artifact sample count is
\(\text{tasks}\times\text{agents}\times\text{independent outputs},\)
rather than that number multiplied by \(H\).

Increasing \(H\) changes the panel and the target distribution. If you instead estimate a wider human population’s distribution, then human-sampling error becomes a separate term that can decrease with more humans.

### \(A\) has two different effects

More agents contribute more observations to an overall mixture of systems.

But you want the judge to work for each of the four named systems. Extra observations from Codex do not replace missing evidence about Grok. Consequently, report per-agent results and control uncertainty across all four claims.

### \(T\) provides complete benchmark coverage

Including every task removes uncertainty about which benchmark tasks were selected. It does not exhaust the possible submissions an agent can produce for a task.

The remaining generalization question is:

How well does the judge match this panel on new outputs from these configurations, over these fixed tasks?

That is a much more specific target than generalization to arbitrary new tasks, agents, and humans.

### A concrete audit bound

Let \(N=|T|\), \(A=4\), and let \(R\) be the number of audit outputs per task–agent pair. In my recommended first study, \(R=1\).

Define
\(Z_{tak}
=
W_1(q_\theta(\cdot\mid z_{tak}),p_H(\cdot\mid z_{tak}))
\in[0,1].\)
Let \(\mathcal R_a\) be agent \(a\)’s expected discrepancy on fresh outputs, averaged uniformly over all benchmark tasks. Its audit estimate is
\(\widehat{\mathcal R}_a
=
\frac1{NR}
\sum_{t=1}^{N}\sum_{k=1}^{R}Z_{tak}.\)
Conditional on the fixed judge, task set, configurations, and reference-rating function, independent output generations give the simultaneous bound
\(\boxed{
\mathcal R_a
\le
\widehat{\mathcal R}_a
+
\sqrt{\frac{\log(A/\delta)}{2NR}}
\quad\text{for every }a,
}\)
with probability at least \(1-\delta\). This follows from Hoeffding’s inequality and a union bound; identical distributions across tasks are unnecessary, but independence and the stated fixed scope matter. [people.eecs.berkeley.edu](https://people.eecs.berkeley.edu/~bartlett/courses/281b-sp08/13.pdf?utm_source=chatgpt.com)

If human rerating introduces additional randomness or dependence, that needs to be included in the reference model rather than silently treating the recorded panel distribution as an unchanging function.

For the hypothetical \(N=170\), \(R=1\), and 95% confidence, the conservative additive margins are:

| Claim about fresh outputs | Margin above the observed discrepancy |
| --- | --- |
| Overall four-agent average | 0.0469 |
| Each agent, simultaneously across all four | 0.1135 |

These are deliberately conservative bounds. They illustrate why a panel-size recommendation and a claim of sufficiently small error are different decisions. The observed errors determine whether the judge passes a chosen tolerance; sharper bounds can sometimes provide more informative intervals.

Under the same fixed-scope assumptions, the overall estimator’s variance is
\(\operatorname{Var}(\widehat{\mathcal R})
=
\frac{1}{N^2A^2R}
\sum_{t,a}\sigma_{ta}^2
=
\frac{\overline{\sigma^2}}{NAR},\)
where \(\sigma_{ta}^2\) measures discrepancy variation over new outputs for that task–agent pair.

This is the relevant version of your \(\sigma/\sqrt n\) intuition. There is no automatic additional \(1/H\) factor for five complete ratings of the same artifact.

The broader crossed random-effects model from my previous answer is useful when generalizing over sampled tasks, agents, and raters. With those sets deliberately fixed, this conditional analysis is more directly aligned with your goal.

## 8. “All tasks” needs two explicitly different claims

I would evaluate every task and show every task’s results. There are nevertheless different strengths of conclusion:

| Claim | What is required |
| --- | --- |
| Every benchmark task is represented | The complete task × four-agent audit |
| The judge matches the panel on every audited artifact within a tolerance | Check the maximum discrepancy over all audited artifacts |
| Average performance on future outputs is good for each solver | Per-agent risk estimates and confidence bounds |
| Future-output performance is good separately for every task–agent pair | Substantial repeated-output evidence per pair, or stronger structural assumptions |
| Every possible future specification will be judged correctly | A much stronger formal or restricted-domain guarantee |

My recommendation covers every task and directly measures every audited artifact. It also supports an aggregate fresh-output analysis for each solver.

A small average discrepancy alone would not establish that every audited task passed. Therefore, report both:
\(\widehat{\mathcal R}_a
\quad\text{and}\quad
\max_{t,k}Z_{tak}.\)
For a stronger statistical guarantee on the future expected error of every task–agent pair, one conservative sufficient condition is
\(R\ge
\frac{\log(NA/\delta)}{2\epsilon^2}.\)
For the illustrative 170-task benchmark, four agents, \(\delta=0.05\), and additive tolerance \(\epsilon=0.10\), this bound requires 476 audit outputs per pair. That is a conservative sufficient count, not a necessary lower bound. It demonstrates how much stronger a uniform future-output guarantee is than evaluating one new submission on every task.

I would make the initial study’s claim explicit and narrower, while retaining the complete per-task results so failures cannot be hidden.

## 9. What I would require before calling the judge successful

For the first study, I would preregister the following evaluation:

- Primary metric: average normalized Wasserstein-1 discrepancy against the five-person panel, reported separately for all four agents.
- Complete-task assessment: maximum discrepancy and a list of every artifact exceeding the chosen tolerance.
- Score calibration: bias of the judge’s expected score relative to the panel mean.
- Repeatability: variation in returned distributions when the same artifact is judged repeatedly.
- Substantive failures: incorrect acceptance of vacuous, restricted-domain, or otherwise inadequate specifications, evaluated using evidence-based review.
- Automatic decision rate: how much work the judge resolves without human escalation.

As a practical starting tolerance, I would target mean \(W_1\le0.05\) for each solver on the normalized scale—an average rating displacement of at most five points on a 100-point scale. This is a proposed evaluation target, not a consequence of choosing five humans. A stronger claim requires the relevant upper confidence bound to meet that target as well.

Choose a separate maximum-error tolerance before the final audit if you want to claim agreement on every audited artifact. Any exceptions should remain visible.

One correction to the previous answer’s numerical example: 299 error-free accepted cases was a single-population certificate. If you later want a separate “under 1% error among automatic acceptances” claim for each of four solvers, simultaneously at 95% confidence, a simple Bonferroni-adjusted zero-error plan requires 437 independently audited accepted cases per solver. That is a separate acceptance-risk audit, with its own sampling assumptions. [itl.nist.gov](https://www.itl.nist.gov/div898/software/dataplot/refman2/auxillar/exacbino.htm?utm_source=chatgpt.com)

### The research claim I would aim to establish

We evaluate a distributional specification judge against a fixed panel of five experts. Development and evaluation cover every task in the benchmark and four specified solver configurations. Evaluation uses independently generated submissions withheld from judge development. We report distributional agreement, score bias, repeatability, substantive acceptance errors, and per-task exceptions separately for each solver.

That claim is concrete, useful, and supported by a feasible experimental design. It leaves room for later studies of additional experts, new solver versions, and unseen benchmarks.

## TL;DR

Use five fixed experts, four fixed solver configurations, and every task. Have all five experts rate two independent outputs per task–agent pair: one for development and one for an untouched audit. Total: \(40|T|\) human reviews.

Your new notes improve the target by making it the fixed panel’s conditional rating distribution. Preserve disagreement, predict that distribution directly, and separately measure how stable the judge’s estimate is. Five defines the panel; the final audit establishes how well the judge matches it. Report results for each solver and every task, with stronger guarantees tied to explicit error tolerances and sampling assumptions.

## Message 3 — user

summarize. Include how your "equation"/bound lead to that conclusion an explicitly what T, A, H (sizes) are.

## Message 4 — assistant

Recommended sizes: \(|H|=5\) experts, \(|A|=4\) agents, and \(|T|=N\), where \(N\) is every task in the fixed VeriBench version.

Important clarification: the bound does not derive “five humans.” Five is a practical choice of reference panel. Four agents and all tasks come from your requested scope. The bound determines how much independent testing supports an accuracy claim.

## What the symbols mean

| Symbol | Meaning | Recommended size |
| --- | --- | --- |
| \(T\) | Set of benchmark tasks | ( |
| \(A\) | Set of fixed solver configurations | ( |
| \(H\) | Fixed expert panel | ( |
| \(m\) | Fresh test outputs per task–agent pair | Initially 1; increase for tighter bounds |

The original two-output proposal was one development output plus one test output, so \(m=1\).

## The bound—and what it actually implies

Let \(\widehat{\mathcal E}_a\) be the judge’s measured average disagreement with the panel for agent \(a\), using a distribution-distance metric normalized to \([0,1]\).

With a fixed judge/reference protocol and independent test generations, simultaneously for every agent, with confidence at least \(1-\delta\):
\(\boxed{
\mathcal E_a
\le
\widehat{\mathcal E}_a
+
\underbrace{\sqrt{\frac{\ln(|A|/\delta)}{2|T|m}}}_{\text{uncertainty margin}}
}\)
This follows from Hoeffding’s inequality plus a union bound over agents. [people.eecs.berkeley.edu](https://people.eecs.berkeley.edu/~bartlett/courses/281b-sp08/13.pdf?utm_source=chatgpt.com)

Why no \(H\) in the denominator? All five ratings together define one submission’s panel distribution. They are not five independent submissions.

### Concrete example: \(N=170\), four agents, 95% confidence

| Test outputs per task–agent pair | Conservative uncertainty margin |
| --- | --- |
| \(m=1\) | 0.114 |
| \(m=6\) | 0.046 |

To require a margin no larger than \(\eta\), choose
\(m\ge
\left\lceil
\frac{\ln(4/0.05)}{2N\eta^2}
\right\rceil.\)
For \(N=170\) and \(\eta=0.05\), this gives six test outputs per pair, plus the development output.

A five-point uncertainty margin is not a five-point error guarantee: the upper error bound is measured error + margin.

## TL;DR

Five experts, four agents, every task. The two-output design is a starting study. For a conservative five-point audit margin on a 170-task example, use one development output plus six test outputs per task–agent pair. The bound determines testing precision; observed errors determine whether the judge is trustworthy.

## Message 5 — user

coworker said:

```
[11/5/26, 1:37:01 PM] Brando Miranda Garay: summarize. Include how your "equation"/bound lead to that conclusion an explicitly what T, A, H (sizes) are.
[11/5/26, 1:37:26 PM] Ultimate Brando9 Scalable Coworker: Summary of the two pasted answers and my pick (my suggestion; I haven't checked their numbers).

My bound, from before:
gap ≈ √(σ_T²/|T| + σ_A²/|A| + σ_H²/|H|)

With a fixed benchmark and named agents:
•⁠  ⁠Tasks and agents are the whole population, so the |T| and |A| terms drop out.
•⁠  ⁠Only the human term is left.
•⁠  ⁠Score error ≈ √(0.25 / (tasks × raters per file)).
•⁠  ⁠For a claim per agent, add the Hoeffding term √(ln(A/δ) / (2·N·R)). N is the number of tasks, R is fresh outputs per task, and A is the number of agents, which is the union-bound factor.

Sizes:

Codex
T (tasks): 896
A (agents): 4
H (humans): 64, 2 ratings per file (7,168 ratings)

ChatGPT Pro
T (tasks): all (example 170)
A (agents): 4
H (humans): 5, all rate every output, 2 rounds

My pick, stage 1
T (tasks): 896
A (agents): 4
H (humans): as many as you can recruit, 2 per file

My pick, stage 2
T (tasks): 256 (Tiny-256) or your 125 files
A (agents): 4
H (humans): 5 to 8, all rate every file

Why that conclusion:
•⁠  ⁠Stage 1: error ≈ √(0.25/(896×2)) ≈ 0.012. It answers whether the judge ranks like experts, for each agent.
•⁠  ⁠Stage 2: error ≈ √(0.25/(256×5)) ≈ 0.014 on the benchmark score. Per agent, with 1 fresh output per task, the Hoeffding margin is √(ln(4/0.05)/512) ≈ 0.09. It answers whether the judge matches the whole rating distribution, scored with W1.
•⁠  ⁠Full distribution on all 896 tasks with 5 raters is about 36,000 reviews over two rounds. That is why it goes on a subset.

TLDR-end: [VeriBench judge] T=896 or 256, A=4, H=2 per file for ranking plus 5-8 for distribution; error ≈ 0.01 to 0.09.
```

It's equation seems simpler to understand. It has the 3 letter explicitly (and independence). Might be wrong though? Does it change your mind of what the recommendation should be?

## Message 6 — assistant

Their equation is a useful model of sampling uncertainty, but they are using it to support stronger claims than it establishes. It does change my recommendation about annotation cost: use fewer ratings during development, while preserving a complete-panel final audit if you want distribution matching assessed on every task.

Taking 896 as the task count in their plan, I would keep:
\(\boxed{|T|=896,\qquad |A|=4,\qquad |H|=5\text{ fixed experts}.}\)
The main correction is to distinguish how accurately we have measured a gap from how small that gap actually is.

## 1. What their simpler equation actually means

Their expression
\(\sqrt{
\frac{\sigma_T^2}{|T|}
+
\frac{\sigma_A^2}{|A|}
+
\frac{\sigma_H^2}{|H|}
}\)
can describe the standard error of an average under a model with independent, additive task, agent, and human effects. More elaborate designs require interaction and residual terms.

A clearer interpretation is:
\(\boxed{
\text{measured judge–human gap}
=
\text{actual gap}
+
\text{sampling noise}.
}\)
Their square-root expression describes the size of the sampling noise.

For example, a judge could consistently overscore humans by 0.30. With enough data, you could estimate that 0.30 gap extremely precisely. A tiny standard error would establish that the judge is reliably wrong.

Shared task and rater effects also matter when deciding which observations are independent; treating every rating as an independent observation can give misleading uncertainty estimates. [arxiv.org](https://arxiv.org/abs/0712.1111?utm_source=chatgpt.com)

### Do the task and agent terms disappear?

For a census of the fixed tasks and agents, their population-selection uncertainty disappears. That part of the coworker’s reasoning is reasonable.

But other uncertainty remains:

- Which humans rate each submission.
- Which submission a stochastic agent generates.
- Which tasks receive full-panel assessment when you examine only 256 of 896.
- Whether the human rating protocol is stable.

In particular, sampling 256 tasks from 896 reintroduces task-sampling uncertainty for the full-benchmark estimate.

## 2. Their numerical calculations need different interpretations

### The 0.012 calculation can be valid

For a fixed set of outputs, two appropriately randomized human ratings per file can estimate the average human benchmark score quite precisely.

Indeed,
\(\sqrt{\frac{0.25}{896\times2}}
\approx0.0118.\)
That can be a valid conservative standard error under the relevant rating-sampling assumptions.

It does not, by itself, establish that:

- The AI judge agrees with humans.
- The judge ranks the four agents correctly.
- Each submission’s human rating distribution is accurately known.

Ranking requires examining the human-supported differences between agents and whether the judge reproduces those differences.

### The 0.014 calculation does not establish distribution-matching precision

For full-panel distribution evaluation, each artifact produces one quantity:
\(W_1(\text{judge distribution},\text{panel distribution}).\)
Five ratings define the panel distribution; they do not create five independent artifacts.

Thus, with 256 evaluated artifacts per agent, a generic worst-case standard error for their average bounded \(W_1\) loss is
\(\frac{0.5}{\sqrt{256}}=0.03125,\)
before a finite-population correction. For a random sample of 256 from 896 fixed artifacts, the corresponding worst-case correction brings this to approximately 0.0264, under simple random sampling.

The claimed 0.014 comes from counting the five human votes as though they supplied five independent units for that distribution-level calculation.

Consequently, their final “error ≈ 0.01 to 0.09” combines different quantities: a standard error for a human mean and a confidence-bound margin for judge error.

### Two votes also give a noisy distribution target

Suppose the full panel’s binary ratings are
\([0,0,1,1,1].\)
A perfect judge predicts 60% probability of rating 1. Its true discrepancy from the panel is zero.

If you compare that prediction against only two randomly selected panelists, the apparent distribution can differ substantially. In this example, the expected apparent \(W_1\) error is 0.24, despite the judge being perfect against the complete panel.

That is why two ratings are useful for estimating aggregate scores, but require care when evaluating per-file distribution matching.

## 3. Separate panel size from ratings per file

These are different quantities:

| Symbol | Meaning |
| --- | --- |
| ( | T |
| ( | A |
| ( | H |
| \(m\) | Number of those people rating each artifact |

The coworker’s first proposal has \(|H|=64\), but \(m=2\).

For fixed artifacts, if each file receives a uniformly random subset of \(m\) members of the same fixed panel, independently across files, a useful per-agent bound is
\(\boxed{
\operatorname{SE}(\text{estimated panel mean})
\le
\sqrt{
\frac{|H|-m}{|H|-1}
\frac{1}{4|T|m}
}.
}\)
This explicitly distinguishes the roster from the reviews per file. For 64 panelists, two ratings per file, and 896 tasks, it gives approximately 0.0117, consistent with their 0.012 calculation.

When all panelists rate every artifact, human-subsampling uncertainty disappears. Human disagreement remains part of the observed target.

Neither five nor 64 humans follows automatically from these equations. Five defines the reference panel I recommend. A larger panel can serve a broader human-population goal, but that requires a different justification.

Also, moving from a 64-person target in stage 1 to a five-person target in stage 2 changes the human standard. I would use the same fixed five experts throughout.

## 4. My revised recommendation

Because you emphasized all tasks, I would economize during development and retain full-panel assessment of every final-audit output.

| Phase | Design | Human reviews |
| --- | --- | --- |
| Development: broad coverage | All \(896\) tasks × 4 agents × 2 randomly assigned members of the fixed five-person panel | 7,168 |
| Development: complete-panel subset | Random 256 tasks × 4 agents × the remaining 3 panelists | 3,072 |
| Final audit | Fresh outputs on all 896 tasks × 4 agents × all 5 panelists | 17,920 |
| Total |  | 28,160 |

This reduces the original 35,840 reviews while preserving a complete five-person distribution for every final-audit submission.

The 256-task subset should be random or use documented stratified sampling. A convenience subset such as Tiny-256 or your existing 125 files supports conclusions about that subset unless its selection supports broader inference.

Freeze the judge before the final audit and use fresh outputs. Keep individual human ratings independent.

A cheaper alternative uses the broad-two-plus-complete-five-on-256 design in both rounds, costing 20,480 reviews. That can estimate benchmark-average distributional agreement with appropriate sampling. It does not observe the complete panel distribution on every final-audit artifact.

## 5. With 896 tasks, the earlier bound supports one audit output per pair

For normalized distribution error, a fixed judge and reference protocol, and independent test generations, the simultaneous one-sided bound across all four agents is
\(\mathcal E_a
\le
\widehat{\mathcal E}_a
+
\sqrt{
\frac{\ln(|A|/\delta)}
{2|T|R}
},\)
where \(R\) is fresh audit outputs per task–agent pair. This follows from Hoeffding’s inequality and a union bound. [people.eecs.berkeley.edu](https://people.eecs.berkeley.edu/~bartlett/courses/281b-sp08/13.pdf?utm_source=chatgpt.com)

Using
\(|T|=896,\quad |A|=4,\quad R=1,\quad \delta=0.05\)
gives an additive margin of
\(\boxed{0.0495}.\)
So the six-test-output example I gave for 170 tasks is unnecessary for that same five-point margin when there are 896 tasks. One fresh audit output per pair suffices for this particular conservative margin.

The actual upper error bound remains observed error + 0.0495. This is an average fresh-output claim for each agent, not a guarantee for every possible submission.

## TL;DR

Their equation is useful for precision, but it does not bound judge accuracy by itself. Their 0.012 calculation can support estimation of an average human score; their 0.014 calculation does not establish full-distribution agreement.

My revised recommendation is 896 tasks, four agents, five fixed experts, with sparse development ratings and complete five-person ratings on every fresh final-audit output: 28,160 reviews total. With 896 tasks, that final audit yields the earlier conservative 0.0495 uncertainty margin per agent, simultaneously across all four.

## Message 7 — user

image(20261105-222124).pngImageimage(20261105-222128).pngImage

sorry I think I made a small typo in my notation...it should have been (for either pdf judge, ai or human) p^{judge}_j(rating | y_pred, x_input) so given the question x_input the (ideal) judge should be able to give a score/rating for weather y_pred is "good" (in our case formal spec coverage, ie if y_pred has a complete set of unproven theorems/formal specs). This formulation would/could avoids the "anchoring" bias of a gold reference. But since I don't actually know how to do that I will change the notition to actually use some gold reference (because afaik, it does bias it to that specific answer but at least it also increases the correctness/validity of the rating/score given by the AI judge).
So
p^{judge}_j(rating | y_pred, y*)
weather judge is a human, collection of humans, or AI judge.
y* = gold reference y = y_gold_ref.

Actually including x (x_input) too all 3 is likely the best cuz x_input is the original source code to check/formalize -- so likely has the right intention (which the user might just want to translate or catch a bug if it has one)

p^{judge}_j(rating | x_input, y_pred, y*)

----

Ok given now all the context...is this correlation approach optimization justified?

PS: and the current suggestions you gave me for T, A, H sizes too?

## Message 8 — assistant

Your corrected formulation is appropriate. Optimizing a judge against human ratings is justified; correlation alone is insufficient for the distribution-matching goal you’ve written down. I would change the primary optimization objective and keep correlation as a secondary metric.

For the study sizes, I would retain all benchmark tasks, four fixed agent configurations, and a fixed panel of five experts—with the qualification that five humans is a practical panel choice, not a sample size proved sufficient by the bound.

## 1. Your corrected conditioning makes sense

Write
\(z=(x_{\mathrm{input}},y_{\mathrm{pred}},y^*),
\qquad
q_\theta(r\mid z)=p_j^{\mathrm{AI}}(r\mid z),\)
where \(\theta\) identifies the judge’s model, prompt, and other settings. Both humans and the AI should receive the same inputs and a fixed grading rubric.

Including the reference supplies useful evidence, but whether it increases correctness is an empirical question. It can also encourage both humans and the AI to favor one particular formalization. I would therefore grade coverage of the reference’s semantic obligations, allowing alternative equivalent formulations.

Also, source code establishes existing behavior; if it contains a bug, it does not by itself establish intended behavior. The rubric must specify whether the task is faithful translation, specification of intended behavior, or bug detection. A complete set of unproven specifications can receive full coverage credit; proof completion is a separate criterion.

## 2. Why correlation is insufficient

If your objective were only to rank submissions, correlation would be a reasonable optimization proxy. Your stated objective is stronger:
\(q_\theta(\cdot\mid z)\approx p_H(\cdot\mid z).\)
Two counterexamples show the difference.

Perfect correlation can coexist with incorrect scores.

| Across three submissions | Submission 1 | Submission 2 | Submission 3 |
| --- | --- | --- | --- |
| Human mean score | 0 | 0.5 | 1 |
| AI mean score | 0.5 | 0.75 | 1 |

Pearson correlation is 1, but mean absolute error is 0.25. The AI systematically overgrades weaker submissions.

Correct means can coexist with an incorrect rating distribution.

Suppose humans assign either 0 or 1 with equal probability, while the AI assigns probability 1 to a rating of 0.5. Both distributions have mean 0.5, but:

- Human rating variance is \(0.25\); the AI’s predicted rating variance is \(0\).
- Their Wasserstein distance \(W_1\) is \(0.5\), on a scale whose maximum is 1.

Across submissions, an AI could predict every human mean correctly while making this kind of distributional mistake.

A notation correction in your photograph: maximizing correlation requires \(\arg\max_\theta \operatorname{Corr}\), or minimizing \(1-\operatorname{Corr}\). The optimizer returns the selected configuration \(\hat\theta\), from which you obtain \(q_{\hat\theta}\).

## 3. The objective I recommend—and its mathematical justification

For numerical ratings normalized to \([0,1]\), I recommend CRPS, a proper scoring loss for predicted rating distributions. It compares the predicted probability of falling below each rating threshold with the observed human rating. Proper scoring rules are designed so that the correct distribution minimizes expected loss. [sites.stat.washington.edu](https://sites.stat.washington.edu/people/raftery/Research/PDF/Gneiting2007jasa.pdf?utm_source=chatgpt.com)

Let \(F_q(u\mid z)\) be the predicted cumulative distribution. Then
\(\mathrm{CRPS}(q,r)
=
\int_0^1
\left(F_q(u\mid z)-\mathbf 1\{r\le u\}\right)^2du.\)
Use this training objective:
\(\boxed{
\hat\theta
=
\arg\min_\theta
\frac{1}{n_{\mathrm{train}}}
\sum_{i\in D_{\mathrm{train}}}
\frac{1}{m_i}
\sum_{h\in H_i}
\mathrm{CRPS}\!\left(q_\theta(\cdot\mid z_i),r_{ih}\right)
}\)
Here:

- \(i\) identifies a candidate artifact: a task, agent, and output run.
- \(H_i\subseteq H\) contains the humans assigned to that artifact.
- \(m_i=|H_i|\) is the number of ratings for it.
- Averaging within each artifact first prevents artifacts with more ratings from automatically receiving more weight.

### Why this objective targets what you want

For a human rating distribution \(p_H\), the excess expected CRPS satisfies
\(\underbrace{
\mathbb E_{r\sim p_H}\mathrm{CRPS}(q,r)
-
\mathbb E_{r\sim p_H}\mathrm{CRPS}(p_H,r)
}_{\text{excess loss above the correct human distribution}}
=
\int_0^1(F_q-F_H)^2du.\)
This is zero exactly when the distributions match. The human-disagreement component of the loss cancels. [sites.stat.washington.edu](https://sites.stat.washington.edu/people/raftery/Research/PDF/Gneiting2007jasa.pdf?utm_source=chatgpt.com)

Furthermore, by Cauchy–Schwarz on \([0,1]\),
\(\boxed{
W_1(q,p_H)^2
=
\left(\int_0^1|F_q-F_H|du\right)^2
\le
\int_0^1(F_q-F_H)^2du.
}\)
That is the objective-to-goal connection: reducing excess CRPS controls distributional discrepancy. Correlation does not provide that implication.

This justifies the objective, not a guarantee that a particular prompt optimizer will find a sufficiently good judge. That still requires an independent audit.

For development, two uniformly randomly assigned raters from the same five-person panel provide an unbiased estimate of the panel-average proper loss, for a fixed judge. They do not reliably reconstruct the five-person distribution for each artifact.

My metric recommendation is therefore:

| Purpose | Metric |
| --- | --- |
| Optimize/select a distributional judge | CRPS |
| Report interpretable distribution disagreement on fully rated artifacts | \(W_1\) |
| Report score accuracy | Mean absolute error and signed bias |
| Report ranking behavior | Spearman or Pearson correlation, as a secondary metric |

If you ultimately need only a single expected coverage score, squared error against the human mean is a simpler appropriate objective. That supports a narrower claim than matching the full distribution.

## 4. My concrete recommendation for \(T,A,H\)

Using 896 as the task count from your supplied plan, rather than an independently verified count for a particular release:

| Symbol | What it counts | Recommendation | Why |
| --- | --- | --- | --- |
| ( | T | ) | Distinct tasks in the frozen benchmark |
| ( | A | ) | Distinct agent configurations |
| ( | H | ) | Distinct experts in the fixed reference panel |
| \(K\) | Fresh final-audit outputs per task–agent pair | 1 initially | With 896 tasks, this gives approximately a 0.05 confidence margin for each agent’s mean loss. |
| \(m_i\) | Human ratings on one artifact | 2 or 5 during development; 5 on every final-audit artifact | Sparse labels support development; complete panel ratings support direct distribution comparison. |

\(H=5\) means five distinct experts total. “Two ratings per file” means \(m_i=2\), not \(H=2\).

I would keep the previously proposed annotation plan:

| Phase | Reviews |
| --- | --- |
| Development: one output for every task–agent pair, two of the five humans per output | \(896\times4\times2=7{,}168\) |
| Complete the five-person panel on a randomly selected 256-task development subset, across all four agents | \(256\times4\times3=3{,}072\) additional |
| Final audit: fresh outputs for every task–agent pair, all five humans per output | \(896\times4\times5=17{,}920\) |
| Total | 28,160 reviews |

That is substantial work: approximately 5,632 reviews per expert under balanced assignment. Five humans should not be mistaken for a small annotation project.

Partition the development artifacts into training and validation sets. Keep all ratings of an artifact together. Repeated prompt optimization against validation scores makes those scores part of development; retain the untouched final audit after freezing the judge. Optimizing a selection criterion on finite data can overfit that criterion. [jmlr.org](https://www.jmlr.org/papers/v11/cawley10a.html?utm_source=chatgpt.com)

The same tasks and agents can appear in development and audit because your claim concerns that fixed benchmark and those configurations. The final candidate outputs and their labels must remain unavailable during optimization.

## 5. How the bound supports these sizes

For the frozen judge, define each audit artifact’s loss as
\(Z_{tak,H}
=
W_1\!\left(q_{\hat\theta}(\cdot\mid z_{tak}),p_H(\cdot\mid z_{tak})\right)
\in[0,1],\)
where \(p_H\) is the complete recorded panel distribution.

Let \(\widehat{\mathcal E}_{a,H}\) be agent \(a\)’s observed average loss, and \(\mathcal E_{a,H}\) its expected loss on fresh outputs, averaged over the fixed benchmark.

Assuming independent audit cases within each agent, conditional on the frozen generation and rating protocols, Hoeffding plus a union bound gives
\(\boxed{
\Pr\!\left[
\forall a\in A:\quad
\mathcal E_{a,H}
\le
\widehat{\mathcal E}_{a,H}
+
\sqrt{\frac{\ln(|A|/\delta)}{2|T|K}}
\right]
\ge 1-\delta.
}\)
The cases need not be identically distributed. [people.eecs.berkeley.edu](https://people.eecs.berkeley.edu/~bartlett/courses/281b-sp08/13.pdf?utm_source=chatgpt.com)

For \(|T|=896,\ |A|=4,\ K=1,\ \delta=0.05\),
\(\boxed{
\mathcal E_{a,H}
\le
\widehat{\mathcal E}_{a,H}+0.04945
\quad\text{simultaneously for all four agents.}
}\)
Equivalently, achieving a one-sided margin of at most \(0.05\) requires
\(|T|K
\ge
\frac{\ln(4/0.05)}{2(0.05)^2}
\approx876.4,\)
so 877 independent audit cases per agent suffice for that margin; 896 tasks with one fresh output each exceeds that count.

Three qualifications determine what you can conclude:

- The margin is uncertainty around the observed error. If observed mean \(W_1=0.03\), the upper bound is approximately \(0.0795\). The formula does not promise error below \(0.05\).
- This bounds a per-agent average over all tasks. It does not guarantee small error on every individual task or every possible future submission. It also does not bound Pearson correlation.
- \(H=5\) defines the panel target; the formula does not derive five as sufficient to represent all experts. All five ratings give the recorded panel histogram. They do not precisely identify those humans’ repeated-rating probabilities or a broader expert-population distribution.

Finally, keep two kinds of variance separate: spread within the predicted rating distribution should reproduce human disagreement; instability of the judge’s returned distribution across repeated calls should be small. Forcing the first variance toward zero can work against your distribution-matching goal.

### TL;DR

Keep the corrected inputs \((x_{\mathrm{input}},y_{\mathrm{pred}},y^*)\). Optimize CRPS, audit with \(W_1\), and report correlation secondarily.

My concrete design remains all 896 tasks if that is the frozen release, four fixed agent configurations, and five fixed experts, with 28,160 reviews under the sparse-development/full-panel-audit plan. The bound explains why one fresh audit output per task–agent pair gives about a 0.05 margin on each agent’s average distribution error. It does not establish that five humans represent all experts or that the trained judge will achieve a sufficiently small error.

## Message 9 — user

ok one more thought…I think we are making progress…if we did have a "correlation metric”/approach were we just plugged in all the data into the scatter plot of ai judge (judge1) vs human (judge2) and just told us how close the two distributions are (or eg all the moments of the two distributions, mean, variance, skew, kurtosis, etc), then we'd be measuring what I actually truly want. Because pearson for example suffers from the issue that it's only linear (in some feature space). Or kendall and spearson only ordering/rankings…

So I guess we could use kl-divergence? But we have the actual ratings (normalized btw 0-1 though it is a number/ordinal 0, 1, 2, 3, 4, 5, so we could even do "classification" learning lol).

But I guess what I want to know is:

1. how do I justify to myself that the approach we are doing of matching two correlations makes sense (to me now after all this conv makes a lot more sense than I expected)
2. ⁠given some choice (or choices) of 1, how do I justify how much data/ratings to collect (T, A, H) and that it will generalize across all three dimensions (eg I think having an unsee fraction of the 3 in the val, test set would do that)
3. ⁠then present the results to a reviewer or someone that would believe me this works (eg eximers phd thesis committee) (but ideally that it actually works in practice tbh, but I do need to graduate/publish this)

I think that's much more accurate of what I want (or at least I've laid out ALL my actual thoughts now).

## Message 10 — assistant

Yes—your goal is now a coherent statistical learning problem: predict the distribution of ratings that qualified humans would assign to the same submission, then test whether that prediction transfers to new tasks, agents, and people.

That is a stronger and more useful goal than maximizing correlation. It also changes my earlier data recommendation: five fixed humans can define a reference panel, but they do not establish generalization to new experts. For that broader goal, I would recruit more distinct humans and ask each to rate fewer files.

I’ll address your three questions directly, then give one concrete starting design.

## 1. Why is this approach mathematically justified?

### The crucial distinction: match distributions conditional on the submission

Keep your notation:
\(z=(x_{\mathrm{input}},y_{\mathrm{pred}},y^*).\)
Define
\(p^*(r\mid z)
=
\Pr(\text{a qualified expert assigns rating }r\text{ to }z),\)
under a specified rubric and expert population. Your judge predicts
\(q_\theta(r\mid z),\qquad r\in\{0,1,2,3,4,5\}.\)
Your objective is to make these distributions close for the same \(z\), averaged over the submissions you care about.

This qualification matters even if you compare every moment or use KL divergence. Consider:

| Submission group | Human rating | AI rating |
| --- | --- | --- |
| Half the submissions | 0 | 5 |
| Other half | 5 | 0 |

The pooled AI and human distributions are identical. Their means, variances, skewness, kurtosis, and every other moment match. Pooled KL divergence is zero.

Yet every AI judgment is wrong.

Therefore, the target should be
\(\boxed{
\mathcal D(\theta)
=
\mathbb E_z\!\left[
D\!\left(p^*(\cdot\mid z),q_\theta(\cdot\mid z)\right)
\right].
}\)
Compare the distributions within each submission, then average. Do not pool all ratings before comparing.

A scatterplot of AI mean versus human mean remains useful, especially with the identity line \(y=x\), but it discards disagreement around those means. More sophisticated dependence measures do not solve this automatically: a judge can depend strongly on human scores while consistently reversing or distorting them.

### Yes, this really is probabilistic classification

Your “we could even do classification” observation is correct. There are six possible rating categories, so the judge can output six probabilities:
\(q_\theta(z)=(q_0,q_1,q_2,q_3,q_4,q_5),
\qquad
\sum_{k=0}^{5}q_k=1.\)
The categories are ordered, making this probabilistic ordinal prediction.

The intended interpretation is “the probabilities of different human ratings.” Repeated stochastic LLM scores do not automatically have that interpretation; those probabilities themselves must be learned or calibrated against human data.

### KL is justified—but I prefer an ordinal proper loss here

Forward KL is a principled choice because
\(\mathbb E_{R\sim p^*}[-\log q_\theta(R\mid z)]
=
\underbrace{\mathsf H(p^*(\cdot\mid z))}_{\text{independent of }\theta}
+
D_{\mathrm{KL}}(p^*\|q_\theta).\)
Thus, minimizing expected cross-entropy minimizes forward KL. You can train using individual human ratings without first knowing the complete human distribution.

However, ordinary cross-entropy does not use the ordering of the categories, and it becomes infinite if the judge assigns zero probability to an observed rating. Proper scoring rules offer alternatives that target the full distribution. [sites.stat.washington.edu](https://sites.stat.washington.edu/people/raftery/Research/PDF/Gneiting2007jasa.pdf?utm_source=chatgpt.com)

My recommendation is the normalized ranked probability score, or RPS. This is the discrete version of the CRPS we discussed, specialized to your six ordered categories.

Define cumulative probabilities
\(Q_c=\sum_{k=0}^{c}q_k,
\qquad c=0,\ldots,4.\)
Then, for an observed human rating \(r\),
\(\boxed{
S_{\mathrm{RPS}}(q,r)
=
\frac15\sum_{c=0}^{4}
\left(Q_c-\mathbf1\{r\le c\}\right)^2.
}\)
This loss lies in \([0,1]\). It scores the predicted probabilities of all five threshold events: rating at most 0, at most 1, and so on. Using cumulative probabilities is what makes it sensitive to the ordering. [sites.stat.washington.edu](https://sites.stat.washington.edu/people/raftery/Research/PDF/Gneiting2007jasa.pdf?utm_source=chatgpt.com)

### The equation that justifies the objective

Let \(P_c\) be the corresponding cumulative human probabilities. Expanding the squares gives
\(\boxed{
\mathbb E_{R\sim p^*}S_{\mathrm{RPS}}(q,R)
=
\underbrace{\frac15\sum_{c=0}^{4}(Q_c-P_c)^2}
_{\text{distributional prediction error}}
+
\underbrace{\frac15\sum_{c=0}^{4}P_c(1-P_c)}
_{\text{human disagreement}}.
}\)
The second term does not depend on your judge. Therefore, minimizing expected RPS minimizes the first term, whose unrestricted optimum is exactly
\(q(\cdot\mid z)=p^*(\cdot\mid z).\)
That answers your first question: the population optimization objective has precisely the distribution you want as its optimum.

There is also a connection to an interpretable distance. For ratings normalized by dividing by 5,
\(W_1(q,p^*)=\frac15\sum_{c=0}^{4}|Q_c-P_c|.\)
By Cauchy–Schwarz,
\(\boxed{
W_1(q,p^*)^2
\le
\underbrace{
\mathbb E_{p^*}S_{\mathrm{RPS}}(q,R)
-
\mathbb E_{p^*}S_{\mathrm{RPS}}(p^*,R)
}_{\text{excess RPS}}.
}\)
So reducing excess RPS controls a distance between the complete conditional rating distributions.

This establishes that the objective is appropriate. It does not establish that a particular model, prompt optimizer, or dataset will achieve low error. That is what the evaluation must determine.

### What about matching all moments?

With six known possible values, normalization plus the first five raw moments identifies the distribution in principle. But learning six probabilities—or five cumulative probabilities—is more direct.

Mean, variance, skewness, and kurtosis alone generally do not identify a six-category distribution. More importantly, even matching every moment must happen conditionally on the submission. The reversed-grades example defeats pooled moment matching.

### The practical training objective

For artifact \(i\), let \(H_i\) be its assigned raters and \(m_i=|H_i|\). Optimize
\(\hat\theta
=
\arg\min_\theta
\frac1n\sum_{i=1}^{n}
\frac1{m_i}\sum_{h\in H_i}
S_{\mathrm{RPS}}\!\left(q_\theta(\cdot\mid z_i),r_{ih}\right).\)
Average within each artifact first, then across artifacts. This prevents heavily annotated artifacts from automatically dominating.

Randomly assigned individual ratings can estimate this objective. You do not need an accurately reconstructed human histogram for every training artifact before learning, just as probabilistic classification does not require knowing the true class probabilities for every training example.

## 2. How do we justify \(T,A,H\), and generalization across them?

Your idea of holding out fractions of all three dimensions is right, with two conditions:

- Hold out identities, not merely individual tensor cells.
- State which population those held-out identities represent.

For humans, I would define the population as something like:

Qualified Lean/formal-methods reviewers who receive the specified task information, reference, and grading instructions.

That is a much clearer target than “humans” generally.

### What each holdout establishes

| Desired claim | What must be unavailable during development |
| --- | --- |
| New-task performance | Entire task identities; related variants should stay together |
| New-agent performance | The held-out agent’s labeled outputs, including during validation |
| New-human performance | All labels from the held-out people |
| All three simultaneously | Test examples combining held-out tasks, an excluded agent, and held-out humans |

Randomly splitting \(R_{tah}\) cells can leave the same task, agent, human, and even candidate artifact on both sides. That does not test the generalization you described.

Also, repeated optimization against validation scores makes that validation set part of development. Keep a final test set untouched after selecting prompts, models, calibration, and reporting thresholds. Model selection can itself overfit finite validation data. [jmlr.org](https://www.jmlr.org/papers/v11/cawley10a.html?utm_source=chatgpt.com)

### Why there is no universally sufficient \(T,A,H\)

The coworker’s three-letter equation becomes useful once interpreted as uncertainty in an estimated average loss, rather than the judge’s actual error.

For illustration, suppose we have a balanced, fully crossed study and a random-effects model with independent task, agent, human, and interaction effects. Writing \(T,A,H\) for the evaluation-set counts in this equation,
\(\begin{aligned}
\operatorname{Var}(\widehat{\mathcal L})
={}&
\frac{\sigma_T^2}{T}
+
\frac{\sigma_A^2}{A}
+
\frac{\sigma_H^2}{H}\\
&+
\frac{\sigma_{TA}^2}{TA}
+
\frac{\sigma_{TH}^2}{TH}
+
\frac{\sigma_{AH}^2}{AH}
+
\frac{\sigma_{\mathrm{res}}^2}{TAH}.
\end{aligned}\)
Here \(\mathcal L\) is mean judging loss, and the variance components describe how that loss changes across tasks, agents, people, and their combinations.

This explains the allocation decision:

- Large task variability calls for more distinct tasks.
- Large human variability calls for more distinct humans.
- Large agent variability calls for more different systems.
- Large generation variability calls for additional outputs from the same task–agent pairs.

Thousands of reviews by the same five people do not become thousands of independent samples of people.

For a sparse assignment design, use the actual assignment structure rather than mechanically substituting counts into the balanced formula. Uncertainty calculations must respect the crossed dependence; naïvely bootstrapping individual ratings can be misleading. [arxiv.org](https://arxiv.org/abs/0712.1111?utm_source=chatgpt.com)

### How a pilot turns this into a human-count decision

Suppose a pilot estimates that the standard deviation of human-specific average-loss effects is \(\sigma_H=0.10\). The human component of a normal-approximation 95% half-width would be
\(w_H\approx1.96\frac{\sigma_H}{\sqrt{H_{\mathrm{test}}}}.\)
That gives:

| Distinct held-out humans | Approximate human component of the half-width |
| --- | --- |
| 6 | 0.080 |
| 16 | 0.049 |

Equivalently,
\(H_{\mathrm{test}}
\gtrsim
\left(\frac{1.96\sigma_H}{w_H}\right)^2.\)
These are illustrative calculations, not measured variance estimates. They concern only the human component, not the entire interval; small-sample intervals can also be wider.

This is the justification I would use for choosing \(H\): estimate the relevant variance, specify acceptable precision, and calculate the required count. If the human-effect SD doubles, maintaining the same precision requires about four times as many humans under this model.

### What a conservative three-dimension bound says

There is also a useful theoretical check. In an idealized complete-grid experiment, assume:

- A frozen judge;
- Independent iid samples of task, agent, and human identities;
- A bounded loss in \([0,1]\), determined by those identities.

Changing one task, agent, or human changes the grid-average loss by at most \(1/T\), \(1/A\), or \(1/H\). McDiarmid’s inequality then gives
\(\boxed{
\mathcal L
\le
\widehat{\mathcal L}
+
\sqrt{
\frac{\ln(1/\delta)}2
\left(\frac1T+\frac1A+\frac1H\right)
}
}\)
with probability at least \(1-\delta\). Additional random generation and rating steps require accounting for their randomness too. [people.eecs.berkeley.edu](https://people.eecs.berkeley.edu/~bartlett/courses/281b-sp08/13.pdf?utm_source=chatgpt.com)

This bound is deliberately conservative. Its value here is to show why a large product \(TAH\) does not automatically imply strong generalization across all three dimensions.

It also exposes the limitation of \(A=4\): four named systems provide limited evidence about a population of future systems, regardless of how many task outputs you collect. Furthermore, the four systems you deliberately select are not automatically iid samples from such a population.

### My revised concrete starting design

For the broader goal you now describe, I recommend the following initial budget, adjusted after a pilot.

I am still using 896 as the task count from your supplied plan, conditional on that being the size of the chosen benchmark release.

| Quantity | Starting recommendation |
| --- | --- |
| ( | T |
| Development task split | 64 training + 64 validation |
| Tasks untouched during development | 768 |
| ( | A |
| ( | H |
| \(m\): ratings per artifact | 3 randomly assigned distinct humans |
| Dense distribution-diagnostic subset | 128 randomly selected untouched tasks, all four agents, 8 ratings per artifact |
| Final candidate outputs | One fresh output per task–agent pair initially |

Why these choices?

64 training and 64 validation tasks are a starting allocation for prompt/model/calibration selection with an already pretrained judge. They provide 512 development artifacts across four agents while preserving a large unseen-task test set. They are not a demonstrated sample-complexity requirement for training a new model. Expand development data if learning curves warrant it, before inspecting the final test results.

24 humans instead of five reflects your changed target. More independent people help assess transfer across people. Sparse ratings keep their workloads manageable. The eight development raters can support grouped human cross-validation during selection; the sixteen audit raters remain entirely separate.

Three ratings per artifact support estimation of the proper-loss objective. The denser subset provides better diagnostics of disagreement and conditional rating distributions. Neither three nor eight votes should be described as the exact distribution of the entire expert population.

### Annotation budget

| Component | Reviews |
| --- | --- |
| Development | \(128\times4\times3=1{,}536\) |
| Final audit across all tasks and agents | \(896\times4\times3=10{,}752\) |
| Add five ratings on the dense subset, bringing each artifact from three to eight | \(128\times4\times5=2{,}560\) |
| Total | 14,848 reviews |

This is fewer reviews than my earlier 28,160 proposal, while involving more distinct humans. With balanced assignment, each audit expert would perform about 832 reviews. That remains a substantial commitment, so the pilot should measure review time as well as variability.

The change is possible because a proper-loss evaluation uses individual votes directly; it does not require every expert to rate every artifact.

### How to test agent transfer with the four required agents

Evaluate two things separately:

- The main judge, developed using all four agents’ development outputs.
- Four leave-one-agent-out judges, each developed without one agent’s labeled outputs in either training or validation.

Evaluate each excluded-agent judge on:
\(\boxed{
768\text{ untouched tasks}
\times
\text{the excluded agent}
\times
\text{untouched audit humans}.
}\)
Each fold therefore tests all three unseen dimensions simultaneously. The same collected audit labels can be reused, so these additional judge fits need not multiply annotation costs.

The supported claim would be:

The judging procedure transferred to each of the four evaluated agent configurations when developed on the other three.

This evaluates the development procedure. It does not independently validate a final judge trained on all four against arbitrary future agents. A prospective evaluation on a genuinely new system or release would strengthen that claim.

### What happens to the earlier “approximately 0.05” margin?

For independent bounded artifact-level losses conditional on a fixed panel/protocol, the 768-task calculation is
\(\sqrt{\frac{\ln(4/0.05)}{2(768)}}\approx0.0534.\)
That explains why preserving a large unseen-task set is attractive. But this is not the total uncertainty for the new population-level design. Human selection, task-family dependence, and claims about unseen agents require their own treatment.

I would not present the old 0.04945 margin as a guarantee of distribution matching across new tasks, agents, and humans.

## 3. What would make a reviewer or committee believe this?

I would organize the evidence around four explicit questions.

### A. Does the objective measure the stated target?

Present the RPS decomposition above. It establishes that the loss targets the complete conditional human-rating distribution.

Keep individual ratings, including disagreements. Do not replace them all with an adjudicated consensus score and then claim to have modeled disagreement. Research on annotation disagreement supports preserving information that majority-vote labels can discard, although formal-specification grading needs its own validation. [ACL Anthology](https://aclanthology.org/2022.tacl-1.6/?utm_source=chatgpt.com)

Also distinguish:

- Predicted rating spread: should reflect human disagreement.
- Instability across repeated judge calls: should be small enough for dependable use.

A stable probability vector can correctly predict substantial human disagreement.

### B. Does the learned judge improve on independent data?

At minimum, compare:

| Method | Purpose |
| --- | --- |
| Constant rating-distribution baseline | Detects whether the judge uses submission-specific information |
| Fixed rubric/reference-assisted judge | Establishes the untuned baseline |
| Correlation-selected judge | Tests the approach you originally proposed |
| RPS-selected judge | Tests whether the objective change improves the intended target |

Use the same candidate artifacts and ratings for paired comparisons. Report the primary proper-loss result and uncertainty, not just the largest correlation.

For absolute distributional closeness, there is an additional detail: raw RPS includes human disagreement, and distance to a three-vote histogram includes finite-human sampling noise. Neither is automatically pure judge error.

Independent human ratings can help estimate that noise. For example, at one threshold let \(X_h=\mathbf1\{R_h\le c\}\). Under independent human draws from the target population,
\(\mathbb E\left[
(Q_c-\bar X)^2-\frac{s_X^2}{m}
\right]
=
(Q_c-P_c)^2.\)
Thus a noise-corrected squared-CDF discrepancy can be estimated from multiple ratings. Such estimates can be negative on individual items because of sampling noise; aggregate them and report uncertainty. Reusing humans across artifacts still requires dependence-aware inference.

That is a stronger basis for a distributional-error claim than treating a tiny empirical histogram as ground truth.

### C. Does performance transfer in the ways claimed?

Report separate results for:

- Fresh outputs across the entire fixed benchmark.
- The 768 unseen tasks.
- The independent audit raters.
- Each agent individually.
- Each leave-one-agent-out transfer experiment.

Show the four agent-transfer results rather than hiding a weak agent in a pooled average. If the claim is that all four meet a threshold, use uncertainty statements appropriate for that simultaneous claim.

The uncertainty should respect task and human identities. Four agent folds are not thousands of independent agent observations.

This level of specificity is warranted: broader empirical work on LLM judges has found substantial variation across evaluation tasks, models, and human expertise. [arxiv.org](https://arxiv.org/abs/2406.18403?utm_source=chatgpt.com)

### D. Does human agreement correspond to actual formal-specification quality?

This is essential for VeriBench. Humans and the AI could agree because they share the same mistaken reference or grading shortcut.

Add a separately reported set of controlled specification changes:

| Change | Expected response |
| --- | --- |
| Remove a necessary specification obligation | Coverage should decrease |
| Strengthen a precondition to exclude required difficult inputs | Coverage/domain score should decrease |
| Replace a specification with a semantically equivalent formulation | Score should remain similar |
| Add irrelevant or vacuous statements | They should not earn meaningful coverage credit |
| Supply a faulty or incomplete reference | The judge should expose the discrepancy where possible |
| Preserve the specifications while changing proof completion | Coverage should remain distinct from proof completion |

Use mechanically checked implications or counterexamples where available to establish the expected relationship. A correct but unproven specification should not lose coverage credit merely because its proof is absent.

This connects “matches experts” to the capability you actually want to measure.

### How I would frame the contribution

I would frame the study as:

We develop a reference-assisted probabilistic judge of formal-specification coverage, optimize it using a proper ordinal scoring loss, and evaluate transfer to held-out tasks, experts, and agent configurations. Controlled specification perturbations assess whether agreement with experts tracks the intended semantic properties.

The proper scoring rule itself is established methodology. Your contribution would be the effective formal-specification judge, the expert-rated evaluation data, and credible evidence of semantic validity and transfer.

A reviewer does not need a promise about every future agent or every possible expert. They need a clearly defined target, an appropriate objective, an honest independent evaluation, and results strong enough to support the stated scope.

## TL;DR

- Your intuition is right when the distributions are matched conditional on the same submission. Pooled histograms or moments can match perfectly while every judgment is wrong.
- Use probabilistic ordinal learning. Forward KL/cross-entropy is justified; I recommend RPS because it respects the ordered 0–5 scale and is bounded. Its excess expected loss equals a distance between conditional rating distributions.
- Your broader generalization goal changes the human design. My starting recommendation is all 896 tasks, four agent configurations, and 24 experts: eight development plus sixteen held out.
- Start with 64 training tasks, 64 validation tasks, and 768 untouched tasks. Collect three ratings per artifact, with eight ratings on a random 128-task audit subset: 14,848 reviews.
- Those are planning numbers, not proven sufficient counts. Use pilot variance and prespecified precision requirements to revise them. Run leave-one-agent-out experiments for joint transfer, and retain semantic checks so that human agreement supports the actual formal-specification claim.

# Related branch — 10 available messages; overlaps the shared snapshot

Source: <https://chatgpt.com/c/6af21580-7588-83e8-8b09-1913bba9d716>

## Message 1 — user

summarize. Include how your "equation"/bound lead to that conclusion an explicitly what T, A, H (sizes) are.

## Message 2 — assistant

Recommended sizes: \(|H|=5\) experts, \(|A|=4\) agents, and \(|T|=N\), where \(N\) is every task in the fixed VeriBench version.

Important clarification: the bound does not derive “five humans.” Five is a practical choice of reference panel. Four agents and all tasks come from your requested scope. The bound determines how much independent testing supports an accuracy claim.

## What the symbols mean

| Symbol | Meaning | Recommended size |
| --- | --- | --- |
| \(T\) | Set of benchmark tasks | ( |
| \(A\) | Set of fixed solver configurations | ( |
| \(H\) | Fixed expert panel | ( |
| \(m\) | Fresh test outputs per task–agent pair | Initially 1; increase for tighter bounds |

The original two-output proposal was one development output plus one test output, so \(m=1\).

## The bound—and what it actually implies

Let \(\widehat{\mathcal E}_a\) be the judge’s measured average disagreement with the panel for agent \(a\), using a distribution-distance metric normalized to \([0,1]\).

With a fixed judge/reference protocol and independent test generations, simultaneously for every agent, with confidence at least \(1-\delta\):
\(\boxed{
\mathcal E_a
\le
\widehat{\mathcal E}_a
+
\underbrace{\sqrt{\frac{\ln(|A|/\delta)}{2|T|m}}}_{\text{uncertainty margin}}
}\)
This follows from Hoeffding’s inequality plus a union bound over agents. [people.eecs.berkeley.edu](https://people.eecs.berkeley.edu/~bartlett/courses/281b-sp08/13.pdf?utm_source=chatgpt.com)

Why no \(H\) in the denominator? All five ratings together define one submission’s panel distribution. They are not five independent submissions.

### Concrete example: \(N=170\), four agents, 95% confidence

| Test outputs per task–agent pair | Conservative uncertainty margin |
| --- | --- |
| \(m=1\) | 0.114 |
| \(m=6\) | 0.046 |

To require a margin no larger than \(\eta\), choose
\(m\ge
\left\lceil
\frac{\ln(4/0.05)}{2N\eta^2}
\right\rceil.\)
For \(N=170\) and \(\eta=0.05\), this gives six test outputs per pair, plus the development output.

A five-point uncertainty margin is not a five-point error guarantee: the upper error bound is measured error + margin.

## TL;DR

Five experts, four agents, every task. The two-output design is a starting study. For a conservative five-point audit margin on a 170-task example, use one development output plus six test outputs per task–agent pair. The bound determines testing precision; observed errors determine whether the judge is trustworthy.

## Message 3 — user

coworker said:

```
[11/5/26, 1:37:01 PM] Brando Miranda Garay: summarize. Include how your "equation"/bound lead to that conclusion an explicitly what T, A, H (sizes) are.
[11/5/26, 1:37:26 PM] Ultimate Brando9 Scalable Coworker: Summary of the two pasted answers and my pick (my suggestion; I haven't checked their numbers).

My bound, from before:
gap ≈ √(σ_T²/|T| + σ_A²/|A| + σ_H²/|H|)

With a fixed benchmark and named agents:
•⁠  ⁠Tasks and agents are the whole population, so the |T| and |A| terms drop out.
•⁠  ⁠Only the human term is left.
•⁠  ⁠Score error ≈ √(0.25 / (tasks × raters per file)).
•⁠  ⁠For a claim per agent, add the Hoeffding term √(ln(A/δ) / (2·N·R)). N is the number of tasks, R is fresh outputs per task, and A is the number of agents, which is the union-bound factor.

Sizes:

Codex
T (tasks): 896
A (agents): 4
H (humans): 64, 2 ratings per file (7,168 ratings)

ChatGPT Pro
T (tasks): all (example 170)
A (agents): 4
H (humans): 5, all rate every output, 2 rounds

My pick, stage 1
T (tasks): 896
A (agents): 4
H (humans): as many as you can recruit, 2 per file

My pick, stage 2
T (tasks): 256 (Tiny-256) or your 125 files
A (agents): 4
H (humans): 5 to 8, all rate every file

Why that conclusion:
•⁠  ⁠Stage 1: error ≈ √(0.25/(896×2)) ≈ 0.012. It answers whether the judge ranks like experts, for each agent.
•⁠  ⁠Stage 2: error ≈ √(0.25/(256×5)) ≈ 0.014 on the benchmark score. Per agent, with 1 fresh output per task, the Hoeffding margin is √(ln(4/0.05)/512) ≈ 0.09. It answers whether the judge matches the whole rating distribution, scored with W1.
•⁠  ⁠Full distribution on all 896 tasks with 5 raters is about 36,000 reviews over two rounds. That is why it goes on a subset.

TLDR-end: [VeriBench judge] T=896 or 256, A=4, H=2 per file for ranking plus 5-8 for distribution; error ≈ 0.01 to 0.09.
```

It's equation seems simpler to understand. It has the 3 letter explicitly (and independence). Might be wrong though? Does it change your mind of what the recommendation should be?

## Message 4 — assistant

Their equation is a useful model of sampling uncertainty, but they are using it to support stronger claims than it establishes. It does change my recommendation about annotation cost: use fewer ratings during development, while preserving a complete-panel final audit if you want distribution matching assessed on every task.

Taking 896 as the task count in their plan, I would keep:
\(\boxed{|T|=896,\qquad |A|=4,\qquad |H|=5\text{ fixed experts}.}\)
The main correction is to distinguish how accurately we have measured a gap from how small that gap actually is.

## 1. What their simpler equation actually means

Their expression
\(\sqrt{
\frac{\sigma_T^2}{|T|}
+
\frac{\sigma_A^2}{|A|}
+
\frac{\sigma_H^2}{|H|}
}\)
can describe the standard error of an average under a model with independent, additive task, agent, and human effects. More elaborate designs require interaction and residual terms.

A clearer interpretation is:
\(\boxed{
\text{measured judge–human gap}
=
\text{actual gap}
+
\text{sampling noise}.
}\)
Their square-root expression describes the size of the sampling noise.

For example, a judge could consistently overscore humans by 0.30. With enough data, you could estimate that 0.30 gap extremely precisely. A tiny standard error would establish that the judge is reliably wrong.

Shared task and rater effects also matter when deciding which observations are independent; treating every rating as an independent observation can give misleading uncertainty estimates. [arxiv.org](https://arxiv.org/abs/0712.1111?utm_source=chatgpt.com)

### Do the task and agent terms disappear?

For a census of the fixed tasks and agents, their population-selection uncertainty disappears. That part of the coworker’s reasoning is reasonable.

But other uncertainty remains:

- Which humans rate each submission.
- Which submission a stochastic agent generates.
- Which tasks receive full-panel assessment when you examine only 256 of 896.
- Whether the human rating protocol is stable.

In particular, sampling 256 tasks from 896 reintroduces task-sampling uncertainty for the full-benchmark estimate.

## 2. Their numerical calculations need different interpretations

### The 0.012 calculation can be valid

For a fixed set of outputs, two appropriately randomized human ratings per file can estimate the average human benchmark score quite precisely.

Indeed,
\(\sqrt{\frac{0.25}{896\times2}}
\approx0.0118.\)
That can be a valid conservative standard error under the relevant rating-sampling assumptions.

It does not, by itself, establish that:

- The AI judge agrees with humans.
- The judge ranks the four agents correctly.
- Each submission’s human rating distribution is accurately known.

Ranking requires examining the human-supported differences between agents and whether the judge reproduces those differences.

### The 0.014 calculation does not establish distribution-matching precision

For full-panel distribution evaluation, each artifact produces one quantity:
\(W_1(\text{judge distribution},\text{panel distribution}).\)
Five ratings define the panel distribution; they do not create five independent artifacts.

Thus, with 256 evaluated artifacts per agent, a generic worst-case standard error for their average bounded \(W_1\) loss is
\(\frac{0.5}{\sqrt{256}}=0.03125,\)
before a finite-population correction. For a random sample of 256 from 896 fixed artifacts, the corresponding worst-case correction brings this to approximately 0.0264, under simple random sampling.

The claimed 0.014 comes from counting the five human votes as though they supplied five independent units for that distribution-level calculation.

Consequently, their final “error ≈ 0.01 to 0.09” combines different quantities: a standard error for a human mean and a confidence-bound margin for judge error.

### Two votes also give a noisy distribution target

Suppose the full panel’s binary ratings are
\([0,0,1,1,1].\)
A perfect judge predicts 60% probability of rating 1. Its true discrepancy from the panel is zero.

If you compare that prediction against only two randomly selected panelists, the apparent distribution can differ substantially. In this example, the expected apparent \(W_1\) error is 0.24, despite the judge being perfect against the complete panel.

That is why two ratings are useful for estimating aggregate scores, but require care when evaluating per-file distribution matching.

## 3. Separate panel size from ratings per file

These are different quantities:

| Symbol | Meaning |
| --- | --- |
| ( | T |
| ( | A |
| ( | H |
| \(m\) | Number of those people rating each artifact |

The coworker’s first proposal has \(|H|=64\), but \(m=2\).

For fixed artifacts, if each file receives a uniformly random subset of \(m\) members of the same fixed panel, independently across files, a useful per-agent bound is
\(\boxed{
\operatorname{SE}(\text{estimated panel mean})
\le
\sqrt{
\frac{|H|-m}{|H|-1}
\frac{1}{4|T|m}
}.
}\)
This explicitly distinguishes the roster from the reviews per file. For 64 panelists, two ratings per file, and 896 tasks, it gives approximately 0.0117, consistent with their 0.012 calculation.

When all panelists rate every artifact, human-subsampling uncertainty disappears. Human disagreement remains part of the observed target.

Neither five nor 64 humans follows automatically from these equations. Five defines the reference panel I recommend. A larger panel can serve a broader human-population goal, but that requires a different justification.

Also, moving from a 64-person target in stage 1 to a five-person target in stage 2 changes the human standard. I would use the same fixed five experts throughout.

## 4. My revised recommendation

Because you emphasized all tasks, I would economize during development and retain full-panel assessment of every final-audit output.

| Phase | Design | Human reviews |
| --- | --- | --- |
| Development: broad coverage | All \(896\) tasks × 4 agents × 2 randomly assigned members of the fixed five-person panel | 7,168 |
| Development: complete-panel subset | Random 256 tasks × 4 agents × the remaining 3 panelists | 3,072 |
| Final audit | Fresh outputs on all 896 tasks × 4 agents × all 5 panelists | 17,920 |
| Total |  | 28,160 |

This reduces the original 35,840 reviews while preserving a complete five-person distribution for every final-audit submission.

The 256-task subset should be random or use documented stratified sampling. A convenience subset such as Tiny-256 or your existing 125 files supports conclusions about that subset unless its selection supports broader inference.

Freeze the judge before the final audit and use fresh outputs. Keep individual human ratings independent.

A cheaper alternative uses the broad-two-plus-complete-five-on-256 design in both rounds, costing 20,480 reviews. That can estimate benchmark-average distributional agreement with appropriate sampling. It does not observe the complete panel distribution on every final-audit artifact.

## 5. With 896 tasks, the earlier bound supports one audit output per pair

For normalized distribution error, a fixed judge and reference protocol, and independent test generations, the simultaneous one-sided bound across all four agents is
\(\mathcal E_a
\le
\widehat{\mathcal E}_a
+
\sqrt{
\frac{\ln(|A|/\delta)}
{2|T|R}
},\)
where \(R\) is fresh audit outputs per task–agent pair. This follows from Hoeffding’s inequality and a union bound. [people.eecs.berkeley.edu](https://people.eecs.berkeley.edu/~bartlett/courses/281b-sp08/13.pdf?utm_source=chatgpt.com)

Using
\(|T|=896,\quad |A|=4,\quad R=1,\quad \delta=0.05\)
gives an additive margin of
\(\boxed{0.0495}.\)
So the six-test-output example I gave for 170 tasks is unnecessary for that same five-point margin when there are 896 tasks. One fresh audit output per pair suffices for this particular conservative margin.

The actual upper error bound remains observed error + 0.0495. This is an average fresh-output claim for each agent, not a guarantee for every possible submission.

## TL;DR

Their equation is useful for precision, but it does not bound judge accuracy by itself. Their 0.012 calculation can support estimation of an average human score; their 0.014 calculation does not establish full-distribution agreement.

My revised recommendation is 896 tasks, four agents, five fixed experts, with sparse development ratings and complete five-person ratings on every fresh final-audit output: 28,160 reviews total. With 896 tasks, that final audit yields the earlier conservative 0.0495 uncertainty margin per agent, simultaneously across all four.

## Message 5 — user

sorry I think I made a small typo in my notation...it should have been (for either pdf judge, ai or human) p^{judge}_j(rating | y_pred, x_input) so given the question x_input the (ideal) judge should be able to give a score/rating for weather y_pred is "good" (in our case formal spec coverage, ie if y_pred has a complete set of unproven theorems/formal specs). This formulation would/could avoids the "anchoring" bias of a gold reference. But since I don't actually know how to do that I will change the notition to actually use some gold reference (because afaik, it does bias it to that specific answer but at least it also increases the correctness/validity of the rating/score given by the AI judge).
So
p^{judge}_j(rating | y_pred, y*)
weather judge is a human, collection of humans, or AI judge.
y* = gold reference y = y_gold_ref.

Actually including x (x_input) too all 3 is likely the best cuz x_input is the original source code to check/formalize -- so likely has the right intention (which the user might just want to translate or catch a bug if it has one)

p^{judge}_j(rating | x_input, y_pred, y*)

----

Ok given now all the context...is this correlation approach optimization justified?

PS: and the current suggestions you gave me for T, A, H sizes too?

## Message 6 — assistant

Your corrected formulation is appropriate. Optimizing a judge against human ratings is justified; correlation alone is insufficient for the distribution-matching goal you’ve written down. I would change the primary optimization objective and keep correlation as a secondary metric.

For the study sizes, I would retain all benchmark tasks, four fixed agent configurations, and a fixed panel of five experts—with the qualification that five humans is a practical panel choice, not a sample size proved sufficient by the bound.

## 1. Your corrected conditioning makes sense

Write
\(z=(x_{\mathrm{input}},y_{\mathrm{pred}},y^*),
\qquad
q_\theta(r\mid z)=p_j^{\mathrm{AI}}(r\mid z),\)
where \(\theta\) identifies the judge’s model, prompt, and other settings. Both humans and the AI should receive the same inputs and a fixed grading rubric.

Including the reference supplies useful evidence, but whether it increases correctness is an empirical question. It can also encourage both humans and the AI to favor one particular formalization. I would therefore grade coverage of the reference’s semantic obligations, allowing alternative equivalent formulations.

Also, source code establishes existing behavior; if it contains a bug, it does not by itself establish intended behavior. The rubric must specify whether the task is faithful translation, specification of intended behavior, or bug detection. A complete set of unproven specifications can receive full coverage credit; proof completion is a separate criterion.

## 2. Why correlation is insufficient

If your objective were only to rank submissions, correlation would be a reasonable optimization proxy. Your stated objective is stronger:
\(q_\theta(\cdot\mid z)\approx p_H(\cdot\mid z).\)
Two counterexamples show the difference.

Perfect correlation can coexist with incorrect scores.

| Across three submissions | Submission 1 | Submission 2 | Submission 3 |
| --- | --- | --- | --- |
| Human mean score | 0 | 0.5 | 1 |
| AI mean score | 0.5 | 0.75 | 1 |

Pearson correlation is 1, but mean absolute error is 0.25. The AI systematically overgrades weaker submissions.

Correct means can coexist with an incorrect rating distribution.

Suppose humans assign either 0 or 1 with equal probability, while the AI assigns probability 1 to a rating of 0.5. Both distributions have mean 0.5, but:

- Human rating variance is \(0.25\); the AI’s predicted rating variance is \(0\).
- Their Wasserstein distance \(W_1\) is \(0.5\), on a scale whose maximum is 1.

Across submissions, an AI could predict every human mean correctly while making this kind of distributional mistake.

A notation correction in your photograph: maximizing correlation requires \(\arg\max_\theta \operatorname{Corr}\), or minimizing \(1-\operatorname{Corr}\). The optimizer returns the selected configuration \(\hat\theta\), from which you obtain \(q_{\hat\theta}\).

## 3. The objective I recommend—and its mathematical justification

For numerical ratings normalized to \([0,1]\), I recommend CRPS, a proper scoring loss for predicted rating distributions. It compares the predicted probability of falling below each rating threshold with the observed human rating. Proper scoring rules are designed so that the correct distribution minimizes expected loss. [sites.stat.washington.edu](https://sites.stat.washington.edu/people/raftery/Research/PDF/Gneiting2007jasa.pdf?utm_source=chatgpt.com)

Let \(F_q(u\mid z)\) be the predicted cumulative distribution. Then
\(\mathrm{CRPS}(q,r)
=
\int_0^1
\left(F_q(u\mid z)-\mathbf 1\{r\le u\}\right)^2du.\)
Use this training objective:
\(\boxed{
\hat\theta
=
\arg\min_\theta
\frac{1}{n_{\mathrm{train}}}
\sum_{i\in D_{\mathrm{train}}}
\frac{1}{m_i}
\sum_{h\in H_i}
\mathrm{CRPS}\!\left(q_\theta(\cdot\mid z_i),r_{ih}\right)
}\)
Here:

- \(i\) identifies a candidate artifact: a task, agent, and output run.
- \(H_i\subseteq H\) contains the humans assigned to that artifact.
- \(m_i=|H_i|\) is the number of ratings for it.
- Averaging within each artifact first prevents artifacts with more ratings from automatically receiving more weight.

### Why this objective targets what you want

For a human rating distribution \(p_H\), the excess expected CRPS satisfies
\(\underbrace{
\mathbb E_{r\sim p_H}\mathrm{CRPS}(q,r)
-
\mathbb E_{r\sim p_H}\mathrm{CRPS}(p_H,r)
}_{\text{excess loss above the correct human distribution}}
=
\int_0^1(F_q-F_H)^2du.\)
This is zero exactly when the distributions match. The human-disagreement component of the loss cancels. [sites.stat.washington.edu](https://sites.stat.washington.edu/people/raftery/Research/PDF/Gneiting2007jasa.pdf?utm_source=chatgpt.com)

Furthermore, by Cauchy–Schwarz on \([0,1]\),
\(\boxed{
W_1(q,p_H)^2
=
\left(\int_0^1|F_q-F_H|du\right)^2
\le
\int_0^1(F_q-F_H)^2du.
}\)
That is the objective-to-goal connection: reducing excess CRPS controls distributional discrepancy. Correlation does not provide that implication.

This justifies the objective, not a guarantee that a particular prompt optimizer will find a sufficiently good judge. That still requires an independent audit.

For development, two uniformly randomly assigned raters from the same five-person panel provide an unbiased estimate of the panel-average proper loss, for a fixed judge. They do not reliably reconstruct the five-person distribution for each artifact.

My metric recommendation is therefore:

| Purpose | Metric |
| --- | --- |
| Optimize/select a distributional judge | CRPS |
| Report interpretable distribution disagreement on fully rated artifacts | \(W_1\) |
| Report score accuracy | Mean absolute error and signed bias |
| Report ranking behavior | Spearman or Pearson correlation, as a secondary metric |

If you ultimately need only a single expected coverage score, squared error against the human mean is a simpler appropriate objective. That supports a narrower claim than matching the full distribution.

## 4. My concrete recommendation for \(T,A,H\)

Using 896 as the task count from your supplied plan, rather than an independently verified count for a particular release:

| Symbol | What it counts | Recommendation | Why |
| --- | --- | --- | --- |
| ( | T | ) | Distinct tasks in the frozen benchmark |
| ( | A | ) | Distinct agent configurations |
| ( | H | ) | Distinct experts in the fixed reference panel |
| \(K\) | Fresh final-audit outputs per task–agent pair | 1 initially | With 896 tasks, this gives approximately a 0.05 confidence margin for each agent’s mean loss. |
| \(m_i\) | Human ratings on one artifact | 2 or 5 during development; 5 on every final-audit artifact | Sparse labels support development; complete panel ratings support direct distribution comparison. |

\(H=5\) means five distinct experts total. “Two ratings per file” means \(m_i=2\), not \(H=2\).

I would keep the previously proposed annotation plan:

| Phase | Reviews |
| --- | --- |
| Development: one output for every task–agent pair, two of the five humans per output | \(896\times4\times2=7{,}168\) |
| Complete the five-person panel on a randomly selected 256-task development subset, across all four agents | \(256\times4\times3=3{,}072\) additional |
| Final audit: fresh outputs for every task–agent pair, all five humans per output | \(896\times4\times5=17{,}920\) |
| Total | 28,160 reviews |

That is substantial work: approximately 5,632 reviews per expert under balanced assignment. Five humans should not be mistaken for a small annotation project.

Partition the development artifacts into training and validation sets. Keep all ratings of an artifact together. Repeated prompt optimization against validation scores makes those scores part of development; retain the untouched final audit after freezing the judge. Optimizing a selection criterion on finite data can overfit that criterion. [jmlr.org](https://www.jmlr.org/papers/v11/cawley10a.html?utm_source=chatgpt.com)

The same tasks and agents can appear in development and audit because your claim concerns that fixed benchmark and those configurations. The final candidate outputs and their labels must remain unavailable during optimization.

## 5. How the bound supports these sizes

For the frozen judge, define each audit artifact’s loss as
\(Z_{tak,H}
=
W_1\!\left(q_{\hat\theta}(\cdot\mid z_{tak}),p_H(\cdot\mid z_{tak})\right)
\in[0,1],\)
where \(p_H\) is the complete recorded panel distribution.

Let \(\widehat{\mathcal E}_{a,H}\) be agent \(a\)’s observed average loss, and \(\mathcal E_{a,H}\) its expected loss on fresh outputs, averaged over the fixed benchmark.

Assuming independent audit cases within each agent, conditional on the frozen generation and rating protocols, Hoeffding plus a union bound gives
\(\boxed{
\Pr\!\left[
\forall a\in A:\quad
\mathcal E_{a,H}
\le
\widehat{\mathcal E}_{a,H}
+
\sqrt{\frac{\ln(|A|/\delta)}{2|T|K}}
\right]
\ge 1-\delta.
}\)
The cases need not be identically distributed. [people.eecs.berkeley.edu](https://people.eecs.berkeley.edu/~bartlett/courses/281b-sp08/13.pdf?utm_source=chatgpt.com)

For \(|T|=896,\ |A|=4,\ K=1,\ \delta=0.05\),
\(\boxed{
\mathcal E_{a,H}
\le
\widehat{\mathcal E}_{a,H}+0.04945
\quad\text{simultaneously for all four agents.}
}\)
Equivalently, achieving a one-sided margin of at most \(0.05\) requires
\(|T|K
\ge
\frac{\ln(4/0.05)}{2(0.05)^2}
\approx876.4,\)
so 877 independent audit cases per agent suffice for that margin; 896 tasks with one fresh output each exceeds that count.

Three qualifications determine what you can conclude:

- The margin is uncertainty around the observed error. If observed mean \(W_1=0.03\), the upper bound is approximately \(0.0795\). The formula does not promise error below \(0.05\).
- This bounds a per-agent average over all tasks. It does not guarantee small error on every individual task or every possible future submission. It also does not bound Pearson correlation.
- \(H=5\) defines the panel target; the formula does not derive five as sufficient to represent all experts. All five ratings give the recorded panel histogram. They do not precisely identify those humans’ repeated-rating probabilities or a broader expert-population distribution.

Finally, keep two kinds of variance separate: spread within the predicted rating distribution should reproduce human disagreement; instability of the judge’s returned distribution across repeated calls should be small. Forcing the first variance toward zero can work against your distribution-matching goal.

### TL;DR

Keep the corrected inputs \((x_{\mathrm{input}},y_{\mathrm{pred}},y^*)\). Optimize CRPS, audit with \(W_1\), and report correlation secondarily.

My concrete design remains all 896 tasks if that is the frozen release, four fixed agent configurations, and five fixed experts, with 28,160 reviews under the sparse-development/full-panel-audit plan. The bound explains why one fresh audit output per task–agent pair gives about a 0.05 margin on each agent’s average distribution error. It does not establish that five humans represent all experts or that the trained judge will achieve a sufficiently small error.

## Message 7 — user

ok one more thought…I think we are making progress…if we did have a "correlation metric”/approach were we just plugged in all the data into the scatter plot of ai judge (judge1) vs human (judge2) and just told us how close the two distributions are (or eg all the moments of the two distributions, mean, variance, skew, kurtosis, etc), then we'd be measuring what I actually truly want. Because pearson for example suffers from the issue that it's only linear (in some feature space). Or kendall and spearson only ordering/rankings…

So I guess we could use kl-divergence? But we have the actual ratings (normalized btw 0-1 though it is a number/ordinal 0, 1, 2, 3, 4, 5, so we could even do "classification" learning lol).

But I guess what I want to know is:

1. how do I justify to myself that the approach we are doing of matching two correlations makes sense (to me now after all this conv makes a lot more sense than I expected)
2. ⁠given some choice (or choices) of 1, how do I justify how much data/ratings to collect (T, A, H) and that it will generalize across all three dimensions (eg I think having an unsee fraction of the 3 in the val, test set would do that)
3. ⁠then present the results to a reviewer or someone that would believe me this works (eg eximers phd thesis committee) (but ideally that it actually works in practice tbh, but I do need to graduate/publish this)

I think that's much more accurate of what I want (or at least I've laid out ALL my actual thoughts now).

## Message 8 — assistant

Yes—your goal is now a coherent statistical learning problem: predict the distribution of ratings that qualified humans would assign to the same submission, then test whether that prediction transfers to new tasks, agents, and people.

That is a stronger and more useful goal than maximizing correlation. It also changes my earlier data recommendation: five fixed humans can define a reference panel, but they do not establish generalization to new experts. For that broader goal, I would recruit more distinct humans and ask each to rate fewer files.

I’ll address your three questions directly, then give one concrete starting design.

## 1. Why is this approach mathematically justified?

### The crucial distinction: match distributions conditional on the submission

Keep your notation:
\(z=(x_{\mathrm{input}},y_{\mathrm{pred}},y^*).\)
Define
\(p^*(r\mid z)
=
\Pr(\text{a qualified expert assigns rating }r\text{ to }z),\)
under a specified rubric and expert population. Your judge predicts
\(q_\theta(r\mid z),\qquad r\in\{0,1,2,3,4,5\}.\)
Your objective is to make these distributions close for the same \(z\), averaged over the submissions you care about.

This qualification matters even if you compare every moment or use KL divergence. Consider:

| Submission group | Human rating | AI rating |
| --- | --- | --- |
| Half the submissions | 0 | 5 |
| Other half | 5 | 0 |

The pooled AI and human distributions are identical. Their means, variances, skewness, kurtosis, and every other moment match. Pooled KL divergence is zero.

Yet every AI judgment is wrong.

Therefore, the target should be
\(\boxed{
\mathcal D(\theta)
=
\mathbb E_z\!\left[
D\!\left(p^*(\cdot\mid z),q_\theta(\cdot\mid z)\right)
\right].
}\)
Compare the distributions within each submission, then average. Do not pool all ratings before comparing.

A scatterplot of AI mean versus human mean remains useful, especially with the identity line \(y=x\), but it discards disagreement around those means. More sophisticated dependence measures do not solve this automatically: a judge can depend strongly on human scores while consistently reversing or distorting them.

### Yes, this really is probabilistic classification

Your “we could even do classification” observation is correct. There are six possible rating categories, so the judge can output six probabilities:
\(q_\theta(z)=(q_0,q_1,q_2,q_3,q_4,q_5),
\qquad
\sum_{k=0}^{5}q_k=1.\)
The categories are ordered, making this probabilistic ordinal prediction.

The intended interpretation is “the probabilities of different human ratings.” Repeated stochastic LLM scores do not automatically have that interpretation; those probabilities themselves must be learned or calibrated against human data.

### KL is justified—but I prefer an ordinal proper loss here

Forward KL is a principled choice because
\(\mathbb E_{R\sim p^*}[-\log q_\theta(R\mid z)]
=
\underbrace{\mathsf H(p^*(\cdot\mid z))}_{\text{independent of }\theta}
+
D_{\mathrm{KL}}(p^*\|q_\theta).\)
Thus, minimizing expected cross-entropy minimizes forward KL. You can train using individual human ratings without first knowing the complete human distribution.

However, ordinary cross-entropy does not use the ordering of the categories, and it becomes infinite if the judge assigns zero probability to an observed rating. Proper scoring rules offer alternatives that target the full distribution. [sites.stat.washington.edu](https://sites.stat.washington.edu/people/raftery/Research/PDF/Gneiting2007jasa.pdf?utm_source=chatgpt.com)

My recommendation is the normalized ranked probability score, or RPS. This is the discrete version of the CRPS we discussed, specialized to your six ordered categories.

Define cumulative probabilities
\(Q_c=\sum_{k=0}^{c}q_k,
\qquad c=0,\ldots,4.\)
Then, for an observed human rating \(r\),
\(\boxed{
S_{\mathrm{RPS}}(q,r)
=
\frac15\sum_{c=0}^{4}
\left(Q_c-\mathbf1\{r\le c\}\right)^2.
}\)
This loss lies in \([0,1]\). It scores the predicted probabilities of all five threshold events: rating at most 0, at most 1, and so on. Using cumulative probabilities is what makes it sensitive to the ordering. [sites.stat.washington.edu](https://sites.stat.washington.edu/people/raftery/Research/PDF/Gneiting2007jasa.pdf?utm_source=chatgpt.com)

### The equation that justifies the objective

Let \(P_c\) be the corresponding cumulative human probabilities. Expanding the squares gives
\(\boxed{
\mathbb E_{R\sim p^*}S_{\mathrm{RPS}}(q,R)
=
\underbrace{\frac15\sum_{c=0}^{4}(Q_c-P_c)^2}
_{\text{distributional prediction error}}
+
\underbrace{\frac15\sum_{c=0}^{4}P_c(1-P_c)}
_{\text{human disagreement}}.
}\)
The second term does not depend on your judge. Therefore, minimizing expected RPS minimizes the first term, whose unrestricted optimum is exactly
\(q(\cdot\mid z)=p^*(\cdot\mid z).\)
That answers your first question: the population optimization objective has precisely the distribution you want as its optimum.

There is also a connection to an interpretable distance. For ratings normalized by dividing by 5,
\(W_1(q,p^*)=\frac15\sum_{c=0}^{4}|Q_c-P_c|.\)
By Cauchy–Schwarz,
\(\boxed{
W_1(q,p^*)^2
\le
\underbrace{
\mathbb E_{p^*}S_{\mathrm{RPS}}(q,R)
-
\mathbb E_{p^*}S_{\mathrm{RPS}}(p^*,R)
}_{\text{excess RPS}}.
}\)
So reducing excess RPS controls a distance between the complete conditional rating distributions.

This establishes that the objective is appropriate. It does not establish that a particular model, prompt optimizer, or dataset will achieve low error. That is what the evaluation must determine.

### What about matching all moments?

With six known possible values, normalization plus the first five raw moments identifies the distribution in principle. But learning six probabilities—or five cumulative probabilities—is more direct.

Mean, variance, skewness, and kurtosis alone generally do not identify a six-category distribution. More importantly, even matching every moment must happen conditionally on the submission. The reversed-grades example defeats pooled moment matching.

### The practical training objective

For artifact \(i\), let \(H_i\) be its assigned raters and \(m_i=|H_i|\). Optimize
\(\hat\theta
=
\arg\min_\theta
\frac1n\sum_{i=1}^{n}
\frac1{m_i}\sum_{h\in H_i}
S_{\mathrm{RPS}}\!\left(q_\theta(\cdot\mid z_i),r_{ih}\right).\)
Average within each artifact first, then across artifacts. This prevents heavily annotated artifacts from automatically dominating.

Randomly assigned individual ratings can estimate this objective. You do not need an accurately reconstructed human histogram for every training artifact before learning, just as probabilistic classification does not require knowing the true class probabilities for every training example.

## 2. How do we justify \(T,A,H\), and generalization across them?

Your idea of holding out fractions of all three dimensions is right, with two conditions:

- Hold out identities, not merely individual tensor cells.
- State which population those held-out identities represent.

For humans, I would define the population as something like:

Qualified Lean/formal-methods reviewers who receive the specified task information, reference, and grading instructions.

That is a much clearer target than “humans” generally.

### What each holdout establishes

| Desired claim | What must be unavailable during development |
| --- | --- |
| New-task performance | Entire task identities; related variants should stay together |
| New-agent performance | The held-out agent’s labeled outputs, including during validation |
| New-human performance | All labels from the held-out people |
| All three simultaneously | Test examples combining held-out tasks, an excluded agent, and held-out humans |

Randomly splitting \(R_{tah}\) cells can leave the same task, agent, human, and even candidate artifact on both sides. That does not test the generalization you described.

Also, repeated optimization against validation scores makes that validation set part of development. Keep a final test set untouched after selecting prompts, models, calibration, and reporting thresholds. Model selection can itself overfit finite validation data. [jmlr.org](https://www.jmlr.org/papers/v11/cawley10a.html?utm_source=chatgpt.com)

### Why there is no universally sufficient \(T,A,H\)

The coworker’s three-letter equation becomes useful once interpreted as uncertainty in an estimated average loss, rather than the judge’s actual error.

For illustration, suppose we have a balanced, fully crossed study and a random-effects model with independent task, agent, human, and interaction effects. Writing \(T,A,H\) for the evaluation-set counts in this equation,
\(\begin{aligned}
\operatorname{Var}(\widehat{\mathcal L})
={}&
\frac{\sigma_T^2}{T}
+
\frac{\sigma_A^2}{A}
+
\frac{\sigma_H^2}{H}\\
&+
\frac{\sigma_{TA}^2}{TA}
+
\frac{\sigma_{TH}^2}{TH}
+
\frac{\sigma_{AH}^2}{AH}
+
\frac{\sigma_{\mathrm{res}}^2}{TAH}.
\end{aligned}\)
Here \(\mathcal L\) is mean judging loss, and the variance components describe how that loss changes across tasks, agents, people, and their combinations.

This explains the allocation decision:

- Large task variability calls for more distinct tasks.
- Large human variability calls for more distinct humans.
- Large agent variability calls for more different systems.
- Large generation variability calls for additional outputs from the same task–agent pairs.

Thousands of reviews by the same five people do not become thousands of independent samples of people.

For a sparse assignment design, use the actual assignment structure rather than mechanically substituting counts into the balanced formula. Uncertainty calculations must respect the crossed dependence; naïvely bootstrapping individual ratings can be misleading. [arxiv.org](https://arxiv.org/abs/0712.1111?utm_source=chatgpt.com)

### How a pilot turns this into a human-count decision

Suppose a pilot estimates that the standard deviation of human-specific average-loss effects is \(\sigma_H=0.10\). The human component of a normal-approximation 95% half-width would be
\(w_H\approx1.96\frac{\sigma_H}{\sqrt{H_{\mathrm{test}}}}.\)
That gives:

| Distinct held-out humans | Approximate human component of the half-width |
| --- | --- |
| 6 | 0.080 |
| 16 | 0.049 |

Equivalently,
\(H_{\mathrm{test}}
\gtrsim
\left(\frac{1.96\sigma_H}{w_H}\right)^2.\)
These are illustrative calculations, not measured variance estimates. They concern only the human component, not the entire interval; small-sample intervals can also be wider.

This is the justification I would use for choosing \(H\): estimate the relevant variance, specify acceptable precision, and calculate the required count. If the human-effect SD doubles, maintaining the same precision requires about four times as many humans under this model.

### What a conservative three-dimension bound says

There is also a useful theoretical check. In an idealized complete-grid experiment, assume:

- A frozen judge;
- Independent iid samples of task, agent, and human identities;
- A bounded loss in \([0,1]\), determined by those identities.

Changing one task, agent, or human changes the grid-average loss by at most \(1/T\), \(1/A\), or \(1/H\). McDiarmid’s inequality then gives
\(\boxed{
\mathcal L
\le
\widehat{\mathcal L}
+
\sqrt{
\frac{\ln(1/\delta)}2
\left(\frac1T+\frac1A+\frac1H\right)
}
}\)
with probability at least \(1-\delta\). Additional random generation and rating steps require accounting for their randomness too. [people.eecs.berkeley.edu](https://people.eecs.berkeley.edu/~bartlett/courses/281b-sp08/13.pdf?utm_source=chatgpt.com)

This bound is deliberately conservative. Its value here is to show why a large product \(TAH\) does not automatically imply strong generalization across all three dimensions.

It also exposes the limitation of \(A=4\): four named systems provide limited evidence about a population of future systems, regardless of how many task outputs you collect. Furthermore, the four systems you deliberately select are not automatically iid samples from such a population.

### My revised concrete starting design

For the broader goal you now describe, I recommend the following initial budget, adjusted after a pilot.

I am still using 896 as the task count from your supplied plan, conditional on that being the size of the chosen benchmark release.

| Quantity | Starting recommendation |
| --- | --- |
| ( | T |
| Development task split | 64 training + 64 validation |
| Tasks untouched during development | 768 |
| ( | A |
| ( | H |
| \(m\): ratings per artifact | 3 randomly assigned distinct humans |
| Dense distribution-diagnostic subset | 128 randomly selected untouched tasks, all four agents, 8 ratings per artifact |
| Final candidate outputs | One fresh output per task–agent pair initially |

Why these choices?

64 training and 64 validation tasks are a starting allocation for prompt/model/calibration selection with an already pretrained judge. They provide 512 development artifacts across four agents while preserving a large unseen-task test set. They are not a demonstrated sample-complexity requirement for training a new model. Expand development data if learning curves warrant it, before inspecting the final test results.

24 humans instead of five reflects your changed target. More independent people help assess transfer across people. Sparse ratings keep their workloads manageable. The eight development raters can support grouped human cross-validation during selection; the sixteen audit raters remain entirely separate.

Three ratings per artifact support estimation of the proper-loss objective. The denser subset provides better diagnostics of disagreement and conditional rating distributions. Neither three nor eight votes should be described as the exact distribution of the entire expert population.

### Annotation budget

| Component | Reviews |
| --- | --- |
| Development | \(128\times4\times3=1{,}536\) |
| Final audit across all tasks and agents | \(896\times4\times3=10{,}752\) |
| Add five ratings on the dense subset, bringing each artifact from three to eight | \(128\times4\times5=2{,}560\) |
| Total | 14,848 reviews |

This is fewer reviews than my earlier 28,160 proposal, while involving more distinct humans. With balanced assignment, each audit expert would perform about 832 reviews. That remains a substantial commitment, so the pilot should measure review time as well as variability.

The change is possible because a proper-loss evaluation uses individual votes directly; it does not require every expert to rate every artifact.

### How to test agent transfer with the four required agents

Evaluate two things separately:

- The main judge, developed using all four agents’ development outputs.
- Four leave-one-agent-out judges, each developed without one agent’s labeled outputs in either training or validation.

Evaluate each excluded-agent judge on:
\(\boxed{
768\text{ untouched tasks}
\times
\text{the excluded agent}
\times
\text{untouched audit humans}.
}\)
Each fold therefore tests all three unseen dimensions simultaneously. The same collected audit labels can be reused, so these additional judge fits need not multiply annotation costs.

The supported claim would be:

The judging procedure transferred to each of the four evaluated agent configurations when developed on the other three.

This evaluates the development procedure. It does not independently validate a final judge trained on all four against arbitrary future agents. A prospective evaluation on a genuinely new system or release would strengthen that claim.

### What happens to the earlier “approximately 0.05” margin?

For independent bounded artifact-level losses conditional on a fixed panel/protocol, the 768-task calculation is
\(\sqrt{\frac{\ln(4/0.05)}{2(768)}}\approx0.0534.\)
That explains why preserving a large unseen-task set is attractive. But this is not the total uncertainty for the new population-level design. Human selection, task-family dependence, and claims about unseen agents require their own treatment.

I would not present the old 0.04945 margin as a guarantee of distribution matching across new tasks, agents, and humans.

## 3. What would make a reviewer or committee believe this?

I would organize the evidence around four explicit questions.

### A. Does the objective measure the stated target?

Present the RPS decomposition above. It establishes that the loss targets the complete conditional human-rating distribution.

Keep individual ratings, including disagreements. Do not replace them all with an adjudicated consensus score and then claim to have modeled disagreement. Research on annotation disagreement supports preserving information that majority-vote labels can discard, although formal-specification grading needs its own validation. [ACL Anthology](https://aclanthology.org/2022.tacl-1.6/?utm_source=chatgpt.com)

Also distinguish:

- Predicted rating spread: should reflect human disagreement.
- Instability across repeated judge calls: should be small enough for dependable use.

A stable probability vector can correctly predict substantial human disagreement.

### B. Does the learned judge improve on independent data?

At minimum, compare:

| Method | Purpose |
| --- | --- |
| Constant rating-distribution baseline | Detects whether the judge uses submission-specific information |
| Fixed rubric/reference-assisted judge | Establishes the untuned baseline |
| Correlation-selected judge | Tests the approach you originally proposed |
| RPS-selected judge | Tests whether the objective change improves the intended target |

Use the same candidate artifacts and ratings for paired comparisons. Report the primary proper-loss result and uncertainty, not just the largest correlation.

For absolute distributional closeness, there is an additional detail: raw RPS includes human disagreement, and distance to a three-vote histogram includes finite-human sampling noise. Neither is automatically pure judge error.

Independent human ratings can help estimate that noise. For example, at one threshold let \(X_h=\mathbf1\{R_h\le c\}\). Under independent human draws from the target population,
\(\mathbb E\left[
(Q_c-\bar X)^2-\frac{s_X^2}{m}
\right]
=
(Q_c-P_c)^2.\)
Thus a noise-corrected squared-CDF discrepancy can be estimated from multiple ratings. Such estimates can be negative on individual items because of sampling noise; aggregate them and report uncertainty. Reusing humans across artifacts still requires dependence-aware inference.

That is a stronger basis for a distributional-error claim than treating a tiny empirical histogram as ground truth.

### C. Does performance transfer in the ways claimed?

Report separate results for:

- Fresh outputs across the entire fixed benchmark.
- The 768 unseen tasks.
- The independent audit raters.
- Each agent individually.
- Each leave-one-agent-out transfer experiment.

Show the four agent-transfer results rather than hiding a weak agent in a pooled average. If the claim is that all four meet a threshold, use uncertainty statements appropriate for that simultaneous claim.

The uncertainty should respect task and human identities. Four agent folds are not thousands of independent agent observations.

This level of specificity is warranted: broader empirical work on LLM judges has found substantial variation across evaluation tasks, models, and human expertise. [arxiv.org](https://arxiv.org/abs/2406.18403?utm_source=chatgpt.com)

### D. Does human agreement correspond to actual formal-specification quality?

This is essential for VeriBench. Humans and the AI could agree because they share the same mistaken reference or grading shortcut.

Add a separately reported set of controlled specification changes:

| Change | Expected response |
| --- | --- |
| Remove a necessary specification obligation | Coverage should decrease |
| Strengthen a precondition to exclude required difficult inputs | Coverage/domain score should decrease |
| Replace a specification with a semantically equivalent formulation | Score should remain similar |
| Add irrelevant or vacuous statements | They should not earn meaningful coverage credit |
| Supply a faulty or incomplete reference | The judge should expose the discrepancy where possible |
| Preserve the specifications while changing proof completion | Coverage should remain distinct from proof completion |

Use mechanically checked implications or counterexamples where available to establish the expected relationship. A correct but unproven specification should not lose coverage credit merely because its proof is absent.

This connects “matches experts” to the capability you actually want to measure.

### How I would frame the contribution

I would frame the study as:

We develop a reference-assisted probabilistic judge of formal-specification coverage, optimize it using a proper ordinal scoring loss, and evaluate transfer to held-out tasks, experts, and agent configurations. Controlled specification perturbations assess whether agreement with experts tracks the intended semantic properties.

The proper scoring rule itself is established methodology. Your contribution would be the effective formal-specification judge, the expert-rated evaluation data, and credible evidence of semantic validity and transfer.

A reviewer does not need a promise about every future agent or every possible expert. They need a clearly defined target, an appropriate objective, an honest independent evaluation, and results strong enough to support the stated scope.

## TL;DR

- Your intuition is right when the distributions are matched conditional on the same submission. Pooled histograms or moments can match perfectly while every judgment is wrong.
- Use probabilistic ordinal learning. Forward KL/cross-entropy is justified; I recommend RPS because it respects the ordered 0–5 scale and is bounded. Its excess expected loss equals a distance between conditional rating distributions.
- Your broader generalization goal changes the human design. My starting recommendation is all 896 tasks, four agent configurations, and 24 experts: eight development plus sixteen held out.
- Start with 64 training tasks, 64 validation tasks, and 768 untouched tasks. Collect three ratings per artifact, with eight ratings on a random 128-task audit subset: 14,848 reviews.
- Those are planning numbers, not proven sufficient counts. Use pilot variance and prespecified precision requirements to revise them. Run leave-one-agent-out experiments for joint transfer, and retain semantic checks so that human agreement supports the actual formal-specification claim.

## Message 9 — user

Do this first:

- Summarize the conclusions and recommendations of this chat.

Then:

- Transcribe the images and describe them.
- The, from the most up to date sketches of the procedures that can be used to to select a LLM judge in general. 4 uses the standard ML approach (eg using CE loss). 2 uses the current populat (imho hacky) maximize correlations to humans (which limitations eg corrs have constraints eg pearson learns linear, spearman only ranking etc) while CE "matches" the true distribution eventually.

So, I'm trying to understand how 1 relates to 2 & 3.

Go!

## Message 10 — assistant

# VeriBench Formal-Specification Judge: Research Summary and Formulation

## 1. Conclusions and recommendations from our conversation

I think we have converged on a much clearer research problem:

Can we learn or select an AI judge whose predicted distribution of formal-specification quality ratings matches the distribution of ratings given by qualified human experts—and demonstrate that this generalizes to unseen tasks, solver agents, and human raters?

This is a standard statistical learning problem, with an important distinction between learning to reproduce human judgments and establishing that those judgments reflect genuine formal correctness.

### 1.1 Our current mathematical objective

Let

\(z=(x,\hat y,y^*)\)

where:

-

\(x\): original Python source, task description, and relevant requirements.

-

\(\hat y\): candidate Lean formal specifications produced by a solver agent.

-

\(y^*\): gold/reference formal specification.

-

\(r\in\mathcal R=\{0,1,2,3,4,5\}\): human rating of formal-specification coverage.

Our ideal judge approximates

\(\boxed{
q_\theta(r\mid x,\hat y,y^*)
\approx
p_H(r\mid x,\hat y,y^*)
}\)

where \(p_H\) is the rating distribution of the target human population and \(q_\theta\) is the AI judge's predicted distribution.

This is probabilistic ordinal learning: classification over six ordered rating categories, rather than merely predicting one scalar score.

### 1.2 What we concluded about optimization

| Approach | What it encourages | Our conclusion |
| --- | --- | --- |
| Pearson correlation | Agreement in linear association across submissions | Useful diagnostic; insufficient for calibrated ratings |
| Spearman/Kendall | Agreement in rankings | Useful for leaderboard comparisons; insufficient for score accuracy |
| Cross-entropy / KL | Matching the full conditional rating distribution | Mathematically justified training objective |
| Ranked Probability Score (RPS) | Matching the full distribution while respecting ordered categories | My preferred primary objective for your 0–5 scale |
| Human–AI agreement | Matching how humans assess specifications | Necessary empirical validation, but not a substitute for semantic correctness |

The key discovery is that a proper scoring loss targets the actual probability distribution, whereas maximizing correlation alone generally does not.

### 1.3 Current experimental recommendation

Our recommendation changed when you expanded the goal from matching a fixed panel of humans to generalizing to unseen humans.

| Dimension | Current recommendation |
| --- | --- |
| \(T\): benchmark tasks | All 896, assuming that is the frozen benchmark size |
| \(A\): solver configurations | Four: Claude Code, Codex, Gemini, Grok |
| \(H\): distinct human experts | 24 total: 8 for development, 16 held out |
| Ratings per submission | Three, with eight on a diagnostic subset |
| Training/validation tasks | 64 / 64 |
| Tasks untouched during development | 768 |
| Indicative human-review budget | 14,848 ratings |

These counts are a starting experimental design, not theoretically established sufficient sample sizes. The next step is a pilot estimating disagreement and variance across tasks, agents, and humans, followed by a power/precision calculation.

Your earlier five-human design remains appropriate if the target is agreement with those exact five people. The 24-person design is better suited to studying transfer to previously unseen experts.

### 1.4 What a trustworthy result must demonstrate

We have identified two separate claims:

Statistical fidelity: The AI judge predicts how qualified humans would rate the candidate specification. This can be tested using held-out data and proper scoring losses.

Construct validity: High ratings actually mean that the Lean specifications adequately express the intended obligations of the original Python task. This needs expert rubrics, semantic checks, adversarial examples, and ideally checkable proofs or counterexamples.

A judge can match human ratings without being logically sound, particularly when the humans and AI share a misleading gold reference.

## 2. Transcription and description of the new images

The first two uploaded photographs are identical images of the same handwritten page. The third photograph is a whiteboard with a more developed mathematical formulation.

I preserve the intended notation below, with uncertain handwriting marked.

### 2.1 Handwritten page — equations (1) and (2)

Opening text:

I figured out what the correlation formulation is doing...

Boxed equation (1):

\(P_j^{\widehat{AJ}}(\cdot)
=
\underset{\widehat{AJ}\in\Theta}{\arg\max}
\operatorname{Corr}
\left(
\widehat P_j^{AJ}(\cdot),
P_j^H(\cdot)
\right).
\tag{1, handwritten}\)

Annotations underneath appear to say:

-

The candidates are constrained or informed by \(S^{tr},R^{tr}\) (training data).

-

The correlation uses \(S^{val},R^{val}\) (validation data).

Text immediately below:

→ This is what people are doing.

→ TODO: deep research to justify/cite if this is true.

I actually think this is more true!

Boxed equation (2):

\(P_j^{AJ_j}(\cdot)
=
\underset{AJ_j\in\Theta}{\arg\max}
\operatorname{Corr}
\left(
\widehat P_j^{AJ_j}(\cdot),
P_j^H(\cdot)
\right).
\tag{2, handwritten}\)

Under the choice of \(AJ_j\in\Theta\), your annotation says approximately:

optimizing, e.g. with an AI agent, or prompt opt., or sampling.

Final questions:

Q: Is this how people “justify” we can trust an LLM judge?

At least literature — most important are frontier papers by Chinese companies!

Q: deep research.

The last two lines have some uncertain words, but that is their apparent meaning.

Description: Both boxed expressions describe selecting a judge from a set of candidates \(\Theta\) by maximizing its correlation with human judgments. The difference is primarily how you describe the search and its constraints, not a distinct statistical objective.

There is a small mathematical typing error worth correcting: \(\arg\max\) returns the selected judge or its parameters, not the correlation coefficient or probability distribution itself.

The cleaner expression is

\(\hat\theta_{\mathrm{corr}}
=
\arg\max_{\theta\in\Theta}
\operatorname{Corr}_{D_{\mathrm{val}}}
\left(q_\theta,p_H\right),\)

followed by

\(q_{\hat\theta_{\mathrm{corr}}}
=
\text{the selected AI judge}.\)

We still need to specify exactly what is being correlated: the mean scores over submissions, or the probabilities of the individual rating categories. Those are different experiments.

### 2.2 Whiteboard — correlation versus loss minimization

TOP: CORRELATION FORMULATION

The first equation appears to be

\(P_j^{\widehat{AJ_j}}(\cdot\mid\cdot,\cdot)
=
\arg\max_{AJ_j\in\Theta}
\left\{
\operatorname{Corr}
\left(
P_j^{AJ_j}(\cdot\mid\cdot,\cdot),
P_j^H(\cdot\mid\cdot,\cdot)
\right)
\right\}.\)

MIDDLE: LOSS-MINIMIZATION FORMULATION

\(\arg\min_{AJ_j\in\Theta}
\left\{
\operatorname{Loss}
\left(
\widehat P^{AJ_j},P^H
\right)
\right\}.\)

Beside this is a green formula:

\(\ell=E+AN^{-\alpha}+BD^{-\beta}.\)

This resembles a neural scaling-law loss model, relating loss to model size \(N\) and data quantity \(D\). It is not itself a definition of cross-entropy, nor does it establish the sample complexity of your judge. The loss needs to be specified independently.

BOTTOM: PROBABILITY-DISTRIBUTION CONSTRAINTS

The whiteboard defines a valid prediction as a probability distribution over ratings. Cleaned up:

\(p(\cdot\mid\hat y,y^*)\in\Delta^5\)

with

\(\Delta^5=
\left\{
p\in\mathbb R^6:
p_r\ge0,\quad
\sum_{r\in\mathcal R}p_r=1
\right\}.\)

It lists the rating categories:

\(\mathcal R=\{0,1,2,3,4,5\}\)

and indicates normalization into \([0,1]\).

Six rating categories correspond to a five-dimensional probability simplex. If you normalize rating values, the categories become \(\{0,0.2,0.4,0.6,0.8,1\}\), but the judge still predicts six probabilities.

Description: The whiteboard is the more useful sketch because it brings together your judge-selection procedure, a generic loss-minimization alternative, and the mathematical domain of the judge's output.

My interpretation is that you are asking:

Why should I choose an AI judge by maximizing its correlation with humans, rather than treating judge selection as ordinary learning of a conditional probability distribution?

That is exactly the question to resolve.

## 3. How the two judge-selection procedures relate

The important observation is that your two approaches are both empirical optimization procedures. They differ in which property of human–AI agreement they optimize.

I would write them in a common notation.

### 3.1 Approach A: select the judge by maximizing correlation

Suppose we have candidate judges \(\theta\in\Theta\), where \(\theta\) might specify a model, prompt, rubric, sampling strategy, or calibration procedure.

For submission \(z_i\), let

\(\mu_\theta(z_i)=\sum_{r=0}^{5}\frac r5q_\theta(r\mid z_i)\)

be its expected normalized AI score, and let \(\bar r_i\) be its average normalized human score.

The conventional score-correlation formulation is

\(\boxed{
\hat\theta_{\mathrm{corr}}
=
\arg\max_{\theta\in\Theta}
\operatorname{Corr}_{i\in D_{\mathrm{val}}}
\left(
\mu_\theta(z_i),\bar r_i
\right).
}\)

You could choose Pearson, Spearman, or Kendall correlation.

This formulation is justified if the goal is to preserve a particular relationship between scores. For example, Spearman correlation is sensible if you care primarily about ranking submissions.

But it is not sufficient to learn the conditional human-rating distribution.

There is an even stronger counterexample than the scalar-score examples we discussed. Suppose for one submission:

\(p_H=(1,0,0,0,0,0)\)

and

\(q_\theta=(0.5,0.1,0.1,0.1,0.1,0.1).\)

The Pearson correlation between these six-dimensional probability vectors is exactly 1.

Why? Because

\(q_\theta=0.4p_H+0.6(1/6,\ldots,1/6).\)

It is a positive affine transformation, which Pearson correlation cannot distinguish.

Yet the human distribution gives the first rating 100% probability, while the judge gives it only 50%.

Their KL divergence is

\(D_{\mathrm{KL}}(p_H\|q_\theta)=\log 2\approx0.693.\)

So even computing Pearson correlation directly between probability distributions does not solve your problem.

The mathematical problem is not that Pearson forces your model to be linear. Your judge may be highly nonlinear. The limitation is that Pearson measures linear association, not equality of probability distributions.

Drag points

Linear correlation is positive (r = 0.98).

Choose a correlation direction. You can also drag points in the scatter plot; the selected direction, least-squares regression line, and Pearson correlation update together.

### 3.2 Approach B: select the judge using cross-entropy

Now suppose every submission \(z_i\) has human ratings \(r_{ih}\).

Define

\(\boxed{
\hat\theta_{\mathrm{CE}}
=
\arg\min_{\theta\in\Theta}
\left[
-\frac1n
\sum_{i=1}^{n}
\frac1{m_i}
\sum_{h\in H_i}
\log q_\theta(r_{ih}\mid z_i)
\right].
}\)

This is just multiclass probabilistic learning, where the labels are human ratings.

The theoretical reason it is appropriate is the decomposition

\(\boxed{
\mathbb E_{R\sim p_H}[-\log q_\theta(R\mid z)]
=
\mathsf H(p_H(\cdot\mid z))
+
D_{\mathrm{KL}}(p_H(\cdot\mid z)\|q_\theta(\cdot\mid z)).
}\)

The entropy term is independent of the judge. Therefore, the unique optimal predicted distribution, among unrestricted valid distributions, is

\(\boxed{
q^*(r\mid z)=p_H(r\mid z).
}\)

This is a consequence of the logarithmic score being strictly proper. It is a well-established statistical result, not a new property specific to LLM judges.

sites.stat.washington.edu

That is the major difference between your two equations.

The correlation objective can achieve its optimum without matching the human distribution. Cross-entropy has the human distribution as its population optimum.

Of course, finite data, model limitations, optimization failures, and distribution shift can prevent us from reaching that optimum.

One important detail: CE must be computed on the human rating labels or their empirical distribution. If you convert all human ratings into a single majority label first, CE learns to predict that aggregate label—not the original distribution of human opinions.

### 3.3 How I would compare the methods

| Property | Maximize correlation | Minimize CE / RPS |
| --- | --- | --- |
| Is it an empirical optimization objective? | Yes | Yes |
| Can it select among prompts and LLMs? | Yes | Yes |
| Does it require gradient-based training? | No | No |
| Can it also train model parameters with gradients? | Sometimes | Yes, if the judge exposes trainable parameters |
| Does it directly target the full human rating distribution? | No | Yes |
| Does its population optimum identify the true conditional distribution? | Generally no | Yes, with sufficient model expressivity |
| Is it appropriate for ranking? | Yes | Yes, but not specifically optimized for rank |
| Is it sufficient to establish formal correctness? | No | No |

Notice that CE is not limited to fine-tuning a model.

You can run twenty different frozen LLMs or prompts on a human-rated validation set, compute their CE losses, and select the lowest-loss judge.

That is directly analogous to choosing the highest-correlation judge.

The difference is the selection criterion, not necessarily the optimization machinery.

For your ordinal labels, I still prefer RPS as the primary loss, with CE as a key baseline. Both are proper distributional objectives; RPS additionally uses the ordering of the ratings.

### 3.4 The relationship as an experimental pipeline

Same candidate judges \(\Theta\)

Same human-rated development data, prompts, and search budget

Correlation selection

\(\max_\theta\;\operatorname{Corr}\)

Produces \(\hat\theta_{\mathrm{corr}}\)

Distributional selection

\(\min_\theta\;\operatorname{CE/RPS}\)

Produces \(\hat\theta_{\mathrm{dist}}\)

Freeze both selected judges

Same untouched test data

Compare RPS / CE, distributional distance, correlation, generalization, and semantic errors

This would give you a scientifically clean comparison between the two procedures.

There is another important distinction: training, model selection, and evaluation are different operations.

For example, a paper may train a judge with next-token cross-entropy and then evaluate its agreement with humans using Pearson correlation.

That does not mean it trained the judge by maximizing Pearson correlation.

This distinction is crucial when interpreting the literature.

## 4. What the actual LLM-judge literature says

I checked several directly relevant primary sources. Your handwritten TODO is pointing toward a real distinction in the field.

[G-Eval — EMNLP 2023](https://aclanthology.org/2023.emnlp-main.153/?utm_source=chatgpt.com)

Uses correlation with human scores as a major meta-evaluation metric, including Spearman correlation for summarization. This helps establish that score correlation has been a standard way to evaluate LLM judges, but does not show that maximizing it is a universally used training objective.

ACL Anthology

[Prometheus — ICLR 2024](https://proceedings.iclr.cc/paper_files/paper/2024/hash/803485352e61e3ebf41221e4776c9fd4-Abstract-Conference.html?utm_source=chatgpt.com)

Trains an evaluator using a large feedback collection and reports Pearson correlation with human evaluators. Its use of reference materials and scoring rubrics is particularly relevant to your input tuple \((x,\hat y,y^*)\).

ICLR Proceedings

[Distributional LLM-as-a-Judge — NeurIPS 2025](https://proceedings.neurips.cc/paper_files/paper/2025/hash/2b1a5611403691061e6b279d13f3d0c6-Abstract-Conference.html?utm_source=chatgpt.com)

Especially important: this paper, involving Renmin University of China and Huawei Noah's Ark Lab, explicitly minimizes KL divergence between predicted and human rating distributions, adds a CE objective, and addresses noise in empirical distributions. It is remarkably close to the direction in your sketches.

NeurIPS Papers

[Post-hoc Alignment of LLM-judges to Human Judgment Distribution — EMNLP 2026](https://aclanthology.org/2026.emnlp-main.436/?utm_source=chatgpt.com)

Shows why reproducing consensus labels is insufficient for matching individual human judgment distributions. Proposes entropy-aware post-hoc alignment, using specialized calibration models.

ACL Anthology

Another recent example is [Human-Residual Steering](https://arxiv.org/abs/2610.37868?utm_source=chatgpt.com), posted October 27, 2026, which trains distributional judge alignment using proper scoring rules for nominal and ordinal judgments. It is a preprint, but highly relevant to your research direction.

arXiv

These results lead to a more precise conclusion than the one written in your notebook:

Correlation is a popular meta-evaluation measure. Distributional alignment with KL/CE is already an established research direction. Neither is universally the way all LLM judges are selected or trained.

This is encouraging for the correctness of your formulation, but it also affects how you should position its novelty.

## 5. How sections 1, 2, and 3 fit together

The relationship is:

| Part | Its role in your research |
| --- | --- |
| 1. Our conclusions | Defines the desired capability, target human distribution, generalization claims, and data requirements |
| 2. Your handwritten formulations | Proposes selecting an AI judge by maximizing an empirical human-agreement objective |
| 3. The whiteboard and CE/RPS alternative | Makes the objective mathematically aligned with the desired probability distribution |

So the main conceptual progression is:

\(\boxed{
\begin{gathered}
\text{Desired capability}\\
q_\theta(r\mid z)\approx p_H(r\mid z)\\[5pt]
\Downarrow\\
\text{Choose an objective whose optimum is }p_H\\
\Downarrow\\
\text{Use CE or RPS to train/select the judge}\\
\Downarrow\\
\text{Test on independent tasks, agents, and humans}\\
\Downarrow\\
\text{Verify semantic validity separately}
\end{gathered}
}\)

Your choice of objective answers what you are trying to learn. Your choice of \(T,A,H\) and the held-out protocol answers how convincingly you can claim to have learned it.

The sample-size calculations cannot rescue a misaligned objective. Conversely, choosing CE does not eliminate the need for adequate data.

### What I would actually run for VeriBench

I would turn the latest notes into an experiment with three main judge-selection approaches: select by Pearson/Spearman correlation, select by CE, and select by RPS. Use the same candidate pool, development budget, and final test cases. Report both distributional and scalar agreement metrics.

The three-axis generalization study would use the 896-task, four-agent, 24-human starting design summarized in Section 1. Hold out task identities and human identities, and perform leave-one-agent-out tests. Those tests evaluate transfer among the four specified systems—not a guarantee about arbitrary future agents.

Finally, evaluate the formal-specification construct itself. A judge that assigns high ratings to specifications with missing obligations, narrowed preconditions, or vacuous claims is not trustworthy merely because it matches human annotations.

## 6. What I think the publishable research question is

I would avoid making the central claim simply “KL is better than correlation.” Proper scoring theory already explains why KL/CE is appropriate for learning distributions, and prior judge papers have explored that idea.

A more compelling thesis question is:

Can distributionally calibrated AI judges reliably assess formal-specification coverage across frontier solver agents, unseen programming tasks, and independent expert reviewers—and does improved human-distribution alignment correspond to improved detection of genuine semantic specification errors?

That produces three testable contributions: a formal-specification judging task and expert-rated dataset; a controlled comparison of correlation-selected versus proper-loss-selected judges; and an independent semantic-validity evaluation.

It also separates a potentially publishable empirical result from claims that would require a new statistical theorem. If CE/RPS selection does not outperform correlation selection, that is still informative—but the semantic checks and generalization analysis become especially important.

TL;DR: Your handwritten equation (1) and (2) are essentially two versions of correlation-based judge selection. The whiteboard introduces the more general loss-minimization formulation. Our conversation establishes why CE/RPS is better aligned with your stated goal of predicting human rating distributions. The experiment now needs to determine whether that theoretical advantage produces a judge that is demonstrably more trustworthy for VeriBench.

# Original conversation — recent connector supplement (9 messages; earlier history omitted)

## Message 1 — user

Are you in charge of the main task of human ratings from this repo [https://github.com/brando90/trustworthy-theorem-judges](https://github.com/brando90/trustworthy-theorem-judges) (handing it off to ppl)?

## Message 2 — assistant

**Yes—the repository is officially designated as the primary owner of the VeriBench human-rating collection and delegation to human raters.** I checked GitHub, and that ownership was explicitly recorded on November 9, 2026.

However, **the handoff is not yet complete**, and I'm not independently managing it in the background.

### Current status

**Human-rating coordination** (In preparation)

| Item | Status |
|--------|--------|
| Primary repository | `trustworthy-theorem-judges` |
| Current collection | 25 tasks, 125 candidate files |
| Required annotations | 250 ratings from two independent raters per file |
| Assignments delivered | 4 of 50 folder assignments |
| Additional emails | 2 task emails and 6 warm-up emails drafted, not sent |
| Preferred deadline | Friday, November 13 |
| Final deadline | Sunday, November 15 |

The repo already has the grading instructions, packet builder, assignment workflow, private roster, and email drafts. The remaining work is to verify consent and assignments, distribute approved packets, and track completed ratings.

See the [current human-rating preparation and handoff record](https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_human_rating_collection/PREPARATION_11-09-2026.md)\.

### What I recommend

I can take responsibility for coordinating this work with you through the connected GitHub and Gmail tools: reviewing assignments, preparing messages, handling approved dispatches, and tracking replies.

The **immediate priority is getting the existing 125-file collection assigned and completed by November 15**, rather than launching the much larger 896-task study prematurely.

The repository explicitly requires your approval before sending collaborator emails, so that dispatch has not yet been authorized by this conversation.

**TL;DR\:** The repo owns human-rating coordination. The materials are prepared, but most assignments still need dispatch. I can help manage the handoff directly, with your approval for sending invitations.

## Message 3 — user

transcribe images. How do they relate to your main task?

[User attached 3 images; image contents were not included]

## Message 4 — assistant

These notes clarify an important distinction in the VeriBench research: **selecting an existing judge using correlation, selecting one using a proper loss, and actually training a judge using that loss are three different experiments.**

They relate directly to the human-rating task, because those ratings are the supervision and evaluation data needed to compare the approaches.

## 1\. Transcription

I've organized the three images in their logical order: handwritten formulations ①–②, handwritten formulations ③–④, then the whiteboard. I have cleaned up punctuation and marked unclear wording.

### Image 3 — Correlation formulations ① and ②

> I figured out what the correlation formulation is doing…

① Correlation-based judge selection

\[
\hat P_j^{AI_j}(\cdot)
=
\underset{\widehat{AI}_j\in\Theta}{\arg\max}
\operatorname{Corr}
\left(
\hat P_j^{AI_j}(\cdot),P_j^H(\cdot)
\right).
\]

Annotations: constrained / hypothesis set by \(S^{tr},R^{tr}\)\. Correlation on \(S^{val},R^{val}\)\.

> This is what people are doing.
>
> TODO: deep research to justify/cite if this is true.
>
> I actually think this is more true\!

② Correlation optimization

\[
P_j^{AI_j}(\cdot)
=
\underset{\widehat{AI}_j\in\Theta}{\arg\max}
\operatorname{Corr}
\left(
\hat P_j^{AI_j}(\cdot),P_j^H(\cdot)
\right).
\]

Annotation: optimizing, e.g. with an AI agent or prompt optimizer or something.

> Q: Is this how people “justify” we can trust an LLM judge?
>
> At least literature — most important are frontier papers by Chinese companies\!
>
> Q: Deep research.

The two handwritten equations are similar. Their conceptual distinction appears to be **choosing among existing judges** versus **actively optimizing a judge to increase correlation**\. I've preserved their intended form, although mathematically an `argmax` returns a configuration, not the probability distribution itself.

### Image 1 — Loss-based formulations ③ and ④

> But I don't think ② is needed. I conjecture\:
>
> 1. ③ + ④ gives better \[overall\] results (since it uses general ML knowledge, instead of a bunch of human correlations).
> 2. ③ + ④ is more “principled” / or at least it's easier to think about, since it uses the (successful) framework of ML learning (not necessarily “constrained” learning theory).
> 3. \[Blank.\]

③ Loss-based validation selection

\[
\hat P_j^{AI_j}(\cdot)
=
\underset{AI_j\in\Theta}{\arg\min}
\left\{
\mathcal L_{\mathrm{loss}}
\left(
\hat P_j^{AI_j}(\cdot),P_j^H(\cdot)
\right)
\right\}.
\]

Annotations: constrained / hypothesis set by training data \(S^{tr},R^{tr}\)\. Loss evaluated on validation set \(S^{val},R^{val}\)\.

> Or what I think people/we do more in practice (we train, \[unclear\], training set and choose hyperparameters on validation or historical hyperparameters…).

④ Loss-based training

\[
\hat P_j^{AI_j}(\cdot)
=
\underset{AI_j\in\Theta}{\arg\min}
\left\{
\mathcal L_{\mathrm{loss}}
\left(
\hat P_j^{AI_j}(\cdot),P_j^H(\cdot)
\right)
\right\}.
\]

Annotation: training loss, evaluated on \(S^{tr},R^{tr}\)\.

> ④ is more similar to what we do in practice. Do a pretraining run on all the data\!
>
> So comparing to ④ feels especially important, but in our setting with such small datasets, I wonder if “trying” to approximate the test set with a validation set would give better evaluation results.
>
> Q: Do both experiments? Which one is the best?

### Image 2 — Whiteboard: Unified mathematical framework

The whiteboard summarizes correlation maximization and loss minimization.

**Correlation approach**

\[
\underset{AI_j\in\Theta}{\arg\max}
\left\{
\operatorname{Corr}
\left(P_j^{AI_j}(\cdot\mid\cdots),P_j^H(\cdot\mid\cdots)\right)
\right\}
\]

**Loss approach**

\[
\underset{AI_j\in\Theta}{\arg\min}
\left\{
\mathcal L_{\mathrm{loss}}(P^{AI_j},P^H)
\right\}
\]

The word *loss* is underlined, with an arrow pointing to \(\ell\)\.

The board also defines the output as a rating distribution\:

\[
P(\cdot\mid\hat y,y^*)\in\mathcal P(\mathcal R),
\]

where

\[
\mathcal R=\{0,1,2,3,4,5\},
\]

and the probability distribution satisfies

\[
\sum_{r\in\mathcal R}p(r\mid\hat y,y^*)=1,
\qquad p(r\mid\hat y,y^*)\ge0.
\]

You also wrote a separate scaling-law-like expression\:

\[
\ell=E+AN^{-\alpha}+BD^{-\beta}.
\]

That appears to be a note about how loss could scale with model size or data, not part of the formal judge objective itself.

The complete judge input, from our previous discussion, is

\[
z=(x_{\mathrm{input}},y_{\mathrm{pred}},y^*).
\]

---

## 2\. What I think the notes establish

Your formulations can be expressed more precisely as three experimental interventions.

| Approach | What changes? | What you are testing |
|--------|--------|--------|
| ① Correlation-based selection | Select from existing candidate judges using validation correlation | Whether correlation selects a good judge |
| ③ Proper-loss-based selection | Select from the **same candidate judges** using validation CE/RPS/Brier | Whether a better selection criterion improves evaluation results |
| ④ Proper-loss-based training | Optimize judge parameters or prompts on training labels using a proper loss | Whether learning directly against the desired target improves generalization |

Approach ② is an additional optimization variant of the correlation approach, rather than a prerequisite for the first comparison.

**My recommendation is to test ① versus ③ first, then investigate ④.**

Why? The first comparison is exceptionally clean. If the candidate judges, rating data, model costs, and evaluation set are identical, the selection metric is the main changed variable.

For ④, many other factors become relevant: optimizer effectiveness, training budget, model capacity, and overfitting.

Your conjecture that ③/④ should outperform correlation-based selection is plausible for distributional accuracy, but it is not guaranteed for every correlation metric. That is exactly what the experiment should measure.

## 3\. How does this relate to my main human-rating task?

It answers **what we need the human annotations for**, and why preserving individual ratings is important.

The repository [trustworthy-theorem-judges](https://github.com/brando90/trustworthy-theorem-judges) is the primary owner of human-rating preparation and collection. Its existing collection and future study serve different purposes.

| Collection | Immediate scientific use |
|--------|--------|
| **Current 125 candidate files**, two independent ratings per file | Pilot ① versus ③, test rubric consistency, investigate annotation noise, estimate feasibility |
| **Larger planned 896-task study**, 24 distinct experts, sparse ratings | Train and evaluate ④, estimate distributional performance, test generalization across task, agent, and human identities |

The current handoff record shows four of 50 folder assignments delivered, with additional collaborator messages awaiting approval. That collection should continue rather than be redesigned midstream.

### What I would preserve in the current collection

The humans should each provide an **independent 0–5 score per candidate file** under the existing FSC rubric. We should preserve the individual responses, rater identifiers, task identities, candidate identities, gold-reference version, and annotation provenance.

**Do not ask humans to generate six-category probability distributions.** The learning algorithm predicts that distribution; independent individual ratings supply observations from it.

Two ratings per file can support an initial comparison using proper scoring losses, but the resulting two-vote histogram is too sparse to treat as the true conditional human distribution for that file.

One more important point: FSC is about the **coverage of formal specifications (unproved theorem statements)**, not whether agents successfully prove them. The rubric and data collection must retain that distinction.

## 4\. What I would change in the research execution plan

The data-collection task and judge-optimization task should be coordinated, but not conflated.

**First: complete the human-rating handoff.**

Distribute the approved frozen packets, track independent ratings, resolve qualifications and assignments, and preserve all labels privately.

**Second: compare ① and ③.**

Use the same fixed collection of candidate judges. Select with correlation versus CE/RPS/Brier on development validation data; evaluate on untouched examples using proper scores, correlations, and calibration. Do not report repeatedly reused historical data as fresh validation.

**Third: evaluate ④.**

Train a judge or calibration head using proper loss on training data. Select hyperparameters on validation data and evaluate once on a sealed test set. Match budgets to the selection baselines where possible.

The repository already separates collection ownership from the broader objective-comparison research. The human collection belongs to `trustworthy-theorem-judges`; the general CE-versus-correlation argument is also developed in `judges-dont-need-psychometrics-or-corr`\.

I would keep that separation.

## 5\. The key answer to the question at the bottom of your notes

You wrote\:

> Do both experiments? Which one is the best?

**Yes, do both. But make ① versus ③ the controlled first experiment, and treat ④ as the follow-up learning experiment.**

There is an important mathematical subtlety: if candidate judge predictions are fixed, the loss-minimizing judge on validation is not necessarily the one that minimizes true test loss. Selection still has finite-sample estimation noise.

Likewise, ④ can overfit small training sets. A proper loss has the correct *population optimum*, but does not guarantee that a finite-data optimizer discovers it.

That is why your human-rating collection, untouched test set, and uncertainty intervals matter so much.

### TL;DR

Your images formalize an increasingly clear experimental thesis\:

**Does selecting or training formal-specification judges using a proper probabilistic loss give better held-out judgments than selecting them using correlation?**

The equations motivate a controlled study comparing ①, ③, and ④. The **main human-rating task provides the labels that make this comparison scientifically meaningful**\. Finish the current independent-rating collection without changing its frozen protocol, run the clean selection comparison first, and expand to training and broader generalization once sufficient labels are available.

## Message 5 — user

do you belong to project [https://github.com/brando90/trustworthy-theorem-judges](https://github.com/brando90/trustworthy-theorem-judges) or [https://github.com/brando90/judges-dont-need-psychometrics-or-corr](https://github.com/brando90/judges-dont-need-psychometrics-or-corr)?

## Message 6 — assistant

**For this conversation, I primarily belong to the workstream of [trustworthy-theorem-judges](https://github.com/brando90/trustworthy-theorem-judges)\.**

I checked both repositories through GitHub. Their documented responsibilities are\:

| Repository | Responsibility |
|--------|--------|
| **[trustworthy-theorem-judges](https://github.com/brando90/trustworthy-theorem-judges)** | Develop the best practical formal-specification judge, compare correlation training (②) against proper-loss training (④), and coordinate human-rating collection |
| **[judges-dont-need-psychometrics-or-corr](https://github.com/brando90/judges-dont-need-psychometrics-or-corr)** | Investigate the general scientific hypothesis that correlation-based optimization is insufficient or inferior to proper probabilistic objectives; develop the position paper |

I don't have permanent membership or an autonomous assignment to either GitHub project. But **my role in this conversation is most closely aligned with the first repository**, especially its human-rating collection and judge development.

The second repository should use the scientific findings and authorized data from the first without duplicating its collection workflow.

**TL;DR\:** Primary project: `trustworthy-theorem-judges`\. Sister research project: `judges-dont-need-psychometrics-or-corr`\.

## Message 7 — user

Ok then move yourself to that codex or chatgpt project please. Anything else you need to do?

## Message 8 — user

ps: therefore change the title of your chat too, and jsutify why you belon to that project.

## Message 9 — assistant

This conversation belongs in the **Trustworthy Theorem Judges** project.

### Recommended chat title

**Trustworthy Theorem Judges — Human Ratings &amp; Judge Training**

[Copy]

### Why this project?

The majority of our work directly supports [trustworthy-theorem-judges](https://github.com/brando90/trustworthy-theorem-judges)\:

- **Human-rating collection\:** recruiting reviewers, distributing assignments, preserving ratings.
- **Judge development\:** comparing correlation training (②) against proper-loss training (④).
- **Formal specification coverage\:** determining whether candidate unproved specifications adequately cover the gold reference.
- **Evaluation\:** choosing \(T,A,H\), designing holdouts, and establishing statistical reliability.

The sister repository, `judges-dont-need-psychometrics-or-corr`, owns the broader theoretical argument and position paper. It should reuse findings from this applied project.

### Moving and renaming this chat

I can't directly change this conversation's project membership or title through my available tools, so **neither change has been made yet**\.

In ChatGPT\:

1. Find this conversation in the sidebar and open its **•••** menu.
2. Select **Rename** and use the title above.
3. Select **Move to project** → **Trustworthy Theorem Judges**\. Create that ChatGPT Project first if necessary. citeturn883703search0

Moving it into a ChatGPT Project preserves the conversation and makes it part of that project's context. It does not move the GitHub repository or create a Codex coding session.

**One remaining operational priority\:** The human-rating handoff still needs its approved collaborator dispatch and completion tracking. That work belongs to this same project.

**TL;DR\:** The correct project is **Trustworthy Theorem Judges**, and the title above reflects our actual research focus. The remaining UI move and rename require your action.
