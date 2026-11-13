# Judge formulations 2 and 4: context for human-rating dispatch

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026/support/JUDGE_FORMULATIONS_11-09-2026.md>

**TLDR:** Formulation 2 develops a judge by maximizing training correlation; formulation 4 develops a judge by minimizing a proper probabilistic training loss. Collect independent, unchanged human ratings that support both, preserve development/test separation, and do not tell raters which objective is expected to win.

User decision, **11-09-2026:** every agent preparing, dispatching, importing, or handing off human-rating packets must read this note. This records methodology and coordination context; it does not revise the locked rater email, rubric, assignments, existing experiment freezes, or dispatch authorization.

**Single coordination owner:** [Prepare human grading task](codex://threads/01a1a8f9-dcb7-7381-9368-91d6e51faffd) owns collection and practical judge development. Follow the [ownership and handoff record](COORDINATION_11-09-2026.md) before starting overlapping work; the former Best human-rating judge chat has handed its work to that owner.

**Goal:** fairly compare correlation-based and probabilistic judge development for formal specification coverage (FSC).
**Confidence:** high in the distinction between objectives; empirical superiority is unresolved.
**Importance:** high for preserving interpretable collection and evaluation.
**Key uncertainty:** which procedure generalizes best with the available task families, solver outputs, and independently collected human ratings.

## Source and transcription

The source is Brando Miranda's three photographs supplied in this coordination chat on 11-09-2026. Originals are preserved byte-for-byte with [hashes and original paths](assets/formulations_11-09-2026_provenance.json). Transcriptions distinguish visible text from interpretation and mark uncertain words:

- [Whiteboard: objectives and rating distributions](assets/whiteboard_objective_overview_11-09-2026.md).
- [Handwritten page: formulations 1 and 2](assets/notes_correlation_formulations_1_2_11-09-2026.md).
- [Handwritten page: formulations 3 and 4](assets/notes_loss_formulations_3_4_11-09-2026.md).

Earlier context: [shared discussion](https://chatgpt.com/share/6af21760-343c-83e8-a92f-b66b5a429e74), [prospective human-target plan](../../02_design_a_judge_that_predicts_human_ratings_0_to_5_start_06Nov2026/README.md), and [current inherited collection](COORDINATOR_README.md). Recommendations in the shared discussion are not new experimental results or authorization to replace this collection.

## Precise formulation

For artifact \(i\), let \(z_i=(x_i,\hat y_i,y_i^*)\) contain the original Python source, candidate Lean artifact, and gold-reference artifact. Formal specifications are unproved theorem statements. Record exactly which proof bodies are visible; the inherited packet retains its existing visibility.

Let \(r_{ih}\in\{0,1,2,3,4,5\}\) be an independently supplied rating by human \(h\). A judge predicts \(q_\theta(r\mid z_i)\), a probability mass function with six nonnegative entries summing to one. Its expected score is \(\mu_\theta(z_i)=\sum_{r=0}^{5}r q_\theta(r\mid z_i)\). Let \(\bar r_i\) be the human mean among the \(m_i\) observed raters of that artifact. Missing ratings are absent observations, not zeros.

The population target is the conditional distribution of ratings from the specified qualified rater population or fixed panel under the specified rubric. The empirical histogram is an estimate, not that distribution known exactly. A fixed panel and an unseen-rater population are different claims.

For a split \(D\), define:

\[
C_D(\theta)=\operatorname{Corr}_{i\in D}\left(\mu_\theta(z_i),\bar r_i\right),
\qquad
\widehat L_D(\theta)=\frac{1}{|D|}\sum_{i\in D}\frac{1}{m_i}\sum_{h\in H_i}\ell(q_\theta(\cdot\mid z_i),r_{ih}).
\]

Corr must name Pearson, Spearman, or Kendall and define ties and zero-variance failures. The loss averages within artifact, then equally over artifacts; extra raters do not silently increase an artifact's weight. This risk is defined for artifacts with observed ratings; the frozen missingness policy must account for any artifacts with none, rather than silently dropping them from the scheduled population.

| User's number | What varies | Objective and data |
| --- | --- | --- |
| **1** | Select among judges already developed using training data | Maximize **validation correlation** over the same candidate set. |
| **2** | Train, optimize a prompt, or search for a judge | \(\hat\theta_2\in\arg\max_{\theta\in\Theta} C_{\mathrm{train}}(\theta)\). |
| **3** | Select among judges already developed using training data | Minimize **validation proper loss** over the same candidate set. |
| **4** | Train, optimize a prompt, or search for a judge | \(\hat\theta_4\in\arg\min_{\theta\in\Theta}\widehat L_{\mathrm{train}}(\theta)\). |

An argmax/argmin returns a parameter or judge; the resulting distribution is \(q_{\hat\theta}(\cdot\mid z)\). It does not directly return a probability distribution unless the search space is explicitly defined as distributions. Correlation here compares expected scores across artifacts, not two unspecified distributions directly. Neither correlation of expected scores nor matching a pooled histogram identifies the per-artifact rating distribution.

Both training procedures still need a declared validation rule for hyperparameters, stopping, prompt candidates, and probability mappings. Formulations 1 and 3 are selection stages that can follow either 2 or 4, not mutually exclusive alternatives to training. “All the data” in the handwritten note means the allowed training data for an optimization run; it does not open sealed evaluation ratings.

## Recommended experiment

**Main comparison: 2 versus 4.** Use the same inputs, model/parameter family, training artifacts and raters, initialization seeds where applicable, output representation, and declared compute/search budgets. Use one common prespecified validation-selection rule to isolate the training-objective change. Name whether the experiment trains a language model, fits a small prediction head, or searches prompts; those are different interventions. Retain convergence failures and actual resource usage.

For ordinal human ratings, preserve the prospective plan's primary **normalized ranked probability score (RPS)**:

\[
\ell_{\mathrm{RPS}}(q,r)=\frac15\sum_{k=0}^{4}\left(\sum_{s=0}^{k}q_s-\mathbf1\{r\leq k\}\right)^2.
\]

Cross-entropy (CE), \(\ell_{\mathrm{CE}}(q,r)=-\log q_r\), is another proper-loss candidate for the comparison owned by the sister project. Brier loss, log loss, score error, signed bias, and Pearson/Spearman/Kendall can be reported on the same held-out support under the frozen analysis plan. Forward Kullback–Leibler divergence \(D_{\mathrm{KL}}(p\Vert q)=\mathrm{CE}(p,q)-H(p)\) differs from CE by target entropy; for fixed targets these are equivalent objectives, not independent methods. Specify smoothing or probability floors before testing.

**Secondary comparison: 1 versus 3.** Reuse an identical fixed candidate pool and change only the validation criterion. If both training and validation criteria change, call the comparison a whole-pipeline comparison. A two-by-two design (training objective × validation criterion) can separate the effects when feasible, but is a proposed future condition, not a modification of a completed experiment. Scalar-only judges need the same declared train-fitted probability-mapping procedure; normalized scalar ratings are not probabilities, and correlation-selected competitors must receive comparable mapping opportunities.

With little development data, grouped cross-validation inside the permitted development pool can help choose hyperparameters or compare selection procedures. Every data-dependent step must be fit inside each training fold. Keep related task families together and preserve the separate sealed test. Repeatedly optimizing against validation makes it development data; it does not create an additional independent test.

Do not discard formulation 2 before the comparison: it is a legitimate comparator for the hypothesis. Proper losses target the desired conditional distribution in population, but finite data, constrained models, regularization, and optimization can change which method wins. Lower CE does not guarantee higher correlation. Pearson is insensitive to positive affine changes of expected score; a correlation-only objective also leaves many different probability distributions with the same means indistinguishable. A fair comparison must disclose how it resolves that freedom.

The whiteboard's \(E+A N^{-\alpha}+B D^{-\beta}\) is a scaling-law conjecture, not a justified sizing formula for task, solver, and human counts. Choose future collection sizes using precision goals, pilot variability, learning curves, and the actual dependence structure; do not infer sufficiency from the number of tensor cells.

## What the literature supports

These primary-source examples distinguish learning objectives from reported metrics; they are not an exhaustive survey of current company practice.

- **G-Eval** (Liu et al., 2023, methods §2 and experiments §3) describes a prompted evaluator and reports correlations with human judgments. Reporting those correlations does not establish that its parameters were trained by maximizing correlation. [Paper](https://aclanthology.org/2023.emnlp-main.153.pdf).
- **InstructGPT** (Ouyang et al., 2022, §3.5, equation 1) trains a reward model with pairwise logistic cross-entropy. This is probabilistic preference learning, not six-category rating-distribution learning and not direct correlation maximization. [Paper](https://arxiv.org/pdf/2203.02155).
- **Qwen2.5-Math** (Alibaba, 2024, §3.2.2, equation 1) trains its reward model with a logistic ranking loss over valid positive/negative response comparisons, described as listwise implementation. It provides another counterexample to treating direct correlation optimization as universal. [Report](https://arxiv.org/html/2409.12122v1#S3.SS2.SSS2).
- **DeepSeek-GRM** (2025, §4) trains its separate meta reward model using binary cross-entropy to assess generated principles and critiques; the main model has a different training procedure. Do not describe that component loss as the objective of the entire system. [Report](https://arxiv.org/html/2504.02495v1#S4).

The defensible claim is a controlled comparison of specified judge-development procedures in our setting, not that proper-loss judge training is novel or that all frontier companies use formulation 2.

## Required context for packet-dispatch agents

1. **Understand both targets of development:** 2 maximizes training correlation; 4 minimizes proper training loss. The same independent ordinal human observations can support both analyses. Do not collect a different rating type for each objective or coach raters to favor either method.
2. **Preserve the existing collection:** 25 tasks × five candidate files = 125 artifacts; the inherited design requests two qualified independent ratings per artifact, with the coordinator's ratings separate. These counts are not the prospective 896-task design. Five files do not by themselves prove there are five distinct solver systems.
3. **Keep the raw observations and provenance:** ordinal rating, opaque rater identity, task/family identity, candidate and reference hashes, rubric/round version, solver identity when supported, missingness, qualification, and exposure history. Preserve exact source/candidate/reference bytes and independent responses. Do not replace individual ratings with consensus or an average-only sheet.
4. **Protect the study split:** follow the existing sealed-data and assignment rules. Dispatching or importing ratings does not authorize using them for judge selection. A new split cannot erase prior exposure. Sparse per-artifact ratings can score probabilistic forecasts, but do not precisely identify each artifact's full human distribution or establish generalization to all raters.
5. **Keep the prover target distinct:** a forecast of acceptance by a pinned bounded proving procedure uses a binary outcome and Brier loss. Failure to find a proof is not a semantic negative. Human rating 4/5 is not a probability of prover success of 0.8.
6. **Follow the actual dispatch contract:** [preparation record](PREPARATION_11-09-2026.md), current private queue, locked text and explicit send authorization. Do not insert this research discussion in participant emails or silently rewrite delivered packets. The preferred date is 11-13-2026 and final date is 11-15-2026.
7. **Respect ownership:** this repository owns collection and the FSC application. The general CE-versus-correlation comparison belongs to [judges-dont-need-psychometrics-or-corr](https://github.com/brando90/judges-dont-need-psychometrics-or-corr). Its [matched comparison checkpoint](https://github.com/brando90/judges-dont-need-psychometrics-or-corr/blob/main/experiments/02_exp06_ce_vs_pearson_matched_budget_start_09Nov2026/ckpt.md) records completed work; this note does not restart or overwrite it.

## Availability and continuation

This note is linked from the repository's mirrored agent entry points, the collection README, the sending protocol, and the active private preparation checkpoint. An already-running agent must read the new note at its next task boundary; a file change is not proof that every other process has reloaded it. The desktop inventory on 11-09-2026 showed this chat as the active human-rating dispatch owner, not a second independently verified dispatcher.

Google companion: the existing [methodology document](https://docs.google.com/document/d/1zB-gYk-zU1wToS_E_carGSRGtUcF1NgZ-jWF5t1SJws/edit), section **11-09-2026 — Dispatch context: formulations 2 and 4**. Updated through the signed-in owner browser after the connector returned a permission error; a fresh export verified the new section exactly once and preserved all prior document content. The companion's earlier discussion of comparing 3 versus 4 remains historical context; this clarification records the user's present emphasis on 2 versus 4 and warns against tuning on test outcomes.
