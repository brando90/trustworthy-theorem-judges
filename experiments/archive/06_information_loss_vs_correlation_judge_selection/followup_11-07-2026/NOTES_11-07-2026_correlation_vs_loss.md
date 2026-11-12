# Correlation vs. proper losses for LLM judges: notes and research synthesis (11-07-2026)

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/06_information_loss_vs_correlation_judge_selection/followup_11-07-2026/NOTES_11-07-2026_correlation_vs_loss.md>

**TLDR:** Matching human judgments is the standard way LLM judges are justified, and correlation is one common metric for it. If the target is the distribution of human judgments, proper scoring rules (log loss, Brier, RPS) are the principled objective and primary metric; correlation is a secondary diagnostic.

Source: three handwritten pages from Brando Miranda (11-07-2026), transcribed and answered in a Grok Bot research session. Google Doc copy: [Trustworthy LLM Judges: Research Notes and Experimental Framing](https://docs.google.com/document/d/1WI-raRtTBnQETjkyMzg23PdhgDLgn33A9kQY1EU0zyE/edit).

## 1. Transcription (literal, lightly expanded)

Brackets mark uncertain readings. Hat placement on some symbols is unclear; the structure is preserved rather than silently corrected.

### Page 1

"I figured out what the correlation formulation is doing..."

**(1)**

$$\hat{p}_j^{AI_j}(\cdot) = \arg\max_{AI_j \in \Theta} \mathrm{Corr}\left(\hat{p}_j^{AI_j}(\cdot), p_j^{H}(\cdot)\right)$$

Annotations: "Constrained/helped by $S^{tr}, R^{tr}$" under the optimization; $S^{val}, R^{val}$ under the correlation.

"This is what people are doing. TODO: deep research to justify/cite if this is true. I actually think this is even true!"

**(2)** Same objective, correlation annotated with $S^{tr}, R^{tr}$, optimization variable hatted:

$$\hat{p}_j^{AI_j}(\cdot) = \arg\max_{\widehat{AI}_j \in \Theta} \mathrm{Corr}\left(\hat{p}_j^{AI_j}(\cdot), p_j^{H}(\cdot)\right)$$

Annotation: "optimizing, say, with an AI system or prompt opt. or search."

"Q: Is this how people 'justify' we can trust an LLM judge? At least literature; most important are frontier papers by diverse companies! Q: deep research."

### Page 2

"But I don't think (2) is needed. I conjecture!

1. (3)+(4) gives better eval results, since it uses general ML knowledge, instead of a hack to max corr.
2. (3)+(4) is more 'principled', or at least it's easier to think about, since it uses the (successful) framework of ML learning (not necessarily 'constrained' learning theory).
3."

**(3)**

$$\hat{p}_j^{AI_j}(\cdot) = \arg\min_{AI_j \in \Theta} \left\lbrace \mathrm{Loss}\left(\hat{p}_j^{AI_j}(\cdot), p_j^{H}(\cdot)\right) \right\rbrace$$

Annotations: "Constrained/helped by train data $S^{tr}, R^{tr}$"; loss evaluated "on val set: $S^{val}, R^{val}$".

"Or what I think people do more in practice (we train, eval on the train set, and choose hps on val [as habitual hps]...)"

**(4)** Same loss objective, evaluated on $S^{tr}, R^{tr}$.

"(4) is more similar to what we do in practice. Do a pre-training run on 'all the data'. So comparing to (1) feels especially important, but in our setting with such small data, I wonder if 'trying to approx the test set with val set' would give better eval results. Q: Do both experiments? Which one is the best?"

### Page 3

"Q: What does best mean in this setting? People/researchers report correlations with humans as 'the answer/eval'. But I conjecture correlations is not the right thing to be doing; it has strong limitations, e.g. Pearson: only linear; Kendall/Spearman: only ranking, etc. While something like a loss (e.g. KL div, although harder to interpret) matches more 'learning the true target distribution of human judgments/preferences'. So we can compute 'all the metrics' at eval to see if (3), (4), with a 'normal' distributional distance setting like CE with Adam if changing weights, or prompt opt., or whatever... is best."

- Corr: Pearson, Spearman, Kendall, ICC, others? "To show/persuade reviewers, since I'm proposing to change the way we judge correctness/evals for LLM judges."
- Loss: CE, KL, W, TVD, WD, others?
- "[Utilities?] People love accuracy..."

## 2. Is correlation how people justify trusting LLM judges?

Yes, in the sense that judges are commonly developed or selected to match human judgments and then justified by measured agreement. Correlation is one major metric; others use preference agreement, accuracy, or macro-F1. It is common, not universal, and agreement does not by itself establish trust outside the tested setting.

| Source | How the judge is developed | Evidence used |
|---|---|---|
| [AutoCalibrate](https://aclanthology.org/2024.lrec-main.237/) (Microsoft/PKU) | Optimizes scoring criteria in the prompt to maximize correlation with expert labels (Eq. 2). Closest literal match to (1). | Correlation with humans |
| [G-Eval](https://aclanthology.org/2023.emnlp-main.153/) (Microsoft) | Prompted, probability-weighted scores; no correlation training | Spearman/Kendall vs human ratings |
| [MT-Bench / Chatbot Arena](https://arxiv.org/html/2306.05685) (LMSYS) | Prompted GPT-4 judge; separately trained Vicuna judge | Agreement vs human-human agreement |
| [JudgeLM](https://arxiv.org/html/2310.17631) | SFT on GPT-4 judgments | Mostly teacher agreement; separate human sets |
| [Prometheus 2](https://aclanthology.org/2024.emnlp-main.248/) | SFT + weight merging | Pearson/Spearman/Kendall and pairwise accuracy |
| [HealthBench](https://arxiv.org/html/2505.08775) (OpenAI) | Grader prompt search | Macro-F1 vs physicians ("Trustworthiness of model grading") |
| [Bloom](https://alignment.anthropic.com/2025/bloom-auto-evals/) (Anthropic) | Scaffold refined by manual review | Spearman vs hand labels, score buckets |
| [FACTS Grounding](https://arxiv.org/html/2501.03200) (Google) | Prompt selection on human-annotated set | Macro-F1, multi-judge ensemble |
| [Self-Taught Evaluators](https://arxiv.org/html/2408.02666) (Meta) | Synthetic pairs, no new human labels in the loop | Benchmarks afterward; counterexample to universal human-corr training |

Limits documented elsewhere: position bias ([FairEval](https://aclanthology.org/2024.acl-long.511/)), adversarial phrases ([Raina et al.](https://aclanthology.org/2024.emnlp-main.427/)), system-level ranking failures ([JuStRank](https://aclanthology.org/2025.acl-long.34/), [Progress Illusion](https://aclanthology.org/2025.findings-emnlp.1036/)), human-label uncertainty ([Beyond Correlation](https://proceedings.iclr.cc/paper_files/paper/2025/hash/8798321486948322be2b4d658744ba72-Abstract-Conference.html)), and task specificity ([TASTE](https://alignment.anthropic.com/2026/taste/)).

## 3. Clean formulation

Let $q_{\theta,\lambda}(y \mid x)$ be the judge's predicted distribution over human judgments, with weights $\theta$ and configuration $\lambda$ (prompt, rubric, examples, decoding). The argmax/argmin returns parameters or a configuration; the fitted judge is defined afterward.

Correlation-based selection (notes' (1)):

$$\hat{\lambda}_{corr} \in \arg\max_{\lambda \in \Lambda} \widehat{\mathrm{Corr}}_{D_{dev}}\left( s_{\theta_0,\lambda}(x_i), \bar{h}_i \right)$$

Loss-based selection (notes' (3)) and fitting (notes' (4)):

$$\hat{\lambda}_{loss} \in \arg\min_{\lambda \in \Lambda} \frac{1}{|D_{dev}|} \sum_{i \in D_{dev}} \ell\left(q_{\hat{\theta},\lambda}(\cdot \mid x_i), y_i\right), \qquad \hat{\theta} \in \arg\min_{\theta} \frac{1}{|D_{tr}|} \sum_{i \in D_{tr}} \ell\left(q_{\theta,\lambda}(\cdot \mid x_i), y_i\right)$$

Target: $p_{\Pi}(y \mid x) = \Pr_{H \sim \Pi}\left[H \text{ gives } y \mid x\right]$ for a specified annotator population $\Pi$ and protocol.

Why log loss is principled for this target:

$$\mathbb{E}_{Y \sim p_{\Pi}}\left[-\log q(Y \mid x)\right] = H\left(p_{\Pi}(\cdot \mid x)\right) + D_{KL}\left(p_{\Pi}(\cdot \mid x) \Vert q(\cdot \mid x)\right)$$

so the population minimizer is $p_{\Pi}$ ([Gneiting and Raftery 2007](https://sites.stat.washington.edu/raftery/Research/PDF/Gneiting2007jasa.pdf)). Correlation has no such guarantee: $q = 0.1 + 0.2\,p_{\Pi}$ has Pearson and rank correlation 1 with $p_{\Pi}$ but never exceeds 0.3.

## 4. Answers to the notes' questions

1. **Why do people use correlation?** It checks whether scores move with human scores without requiring a shared scale, which is fine for ranking. The questionable step is treating association as accurate prediction of human judgments.
2. **Are (3)/(4) more principled?** Yes for distribution prediction, via strictly proper losses. Not guaranteed better in finite samples or for system ranking; that needs the experiment.
3. **Which losses?** Primary: log loss / CE. Also Brier, and ranked probability score for ordinal ratings. Forward KL ranks models identically to CE on fixed targets, so it is not independent evidence. TV and Wasserstein against single votes are not proper (they favor modal or median point masses); use them only as diagnostics against well-estimated distributions.
4. **What does "best" mean?** Declare it before comparing: proper score for distribution prediction, ranking quality for model selection, serious-error rates for safety screening.
5. **Do both experiments?** Yes, matched. First compare (1) vs (3) on one fixed candidate pool, same data and budget. Treat loss-based fitting (4) as a separate intervention. With small data use grouped nested cross-validation; refitting on train+val is fine, but those items stop being independent evidence.
6. **Novelty.** Prior art exists: [Judging with Confidence](https://arxiv.org/html/2510.00263) (Google, 2025) targets preference distributions with Brier/log rewards, mainly on synthetic persona labels. Sharper question: under matched budgets, does proper-loss selection or fitting improve prediction of real human judgments and downstream decisions compared with correlation-based selection?

Note: one human vote per item does not reveal that item's distribution. Repeated independent ratings on a subset are needed to test whether the judge captures genuine disagreement.

## 5. Relation to existing work in this repo pair

- `trustworthy-theorem-judges/experiments/06_information_loss_vs_correlation_judge_selection` already runs the matched selection and fitting comparison on cached data. Its README reports the primary comparison did not resolve a CE-selection advantage, and the Pearson head comparison has a nonconvergence limitation.
- `judges-dont-need-psychometrics-or-corr` is the general position-paper repo (correlation objective vs standard ML loss). See the 11-07/08-2026 weekly update for the plan.
