# How representative judge papers use correlation and losses

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/06_information_loss_vs_correlation_judge_selection/followup_11-07-2026/LITERATURE.md>

**TLDR:** Correlation is common in judge evaluation, but the checked papers use different training and selection procedures. Directly optimizing correlation is a useful proposed comparison, not an established description of all judge research.

This is a focused check of four primary judge/reward papers, plus a probability-scoring reference; it is not a systematic review or a novelty claim.

| Primary source | What the paper does | What it supports |
| --- | --- | --- |
| [G-Eval, EMNLP 2023](https://aclanthology.org/2023.emnlp-main.153.pdf), sections 2–4 | Prompted evaluation, generated evaluation steps and probability-weighted scalar ratings; compares designs using human correlations. | Correlation is an evaluation/design-comparison criterion. The paper does not specify a formal held-out correlation argmax or direct correlation training. |
| [Prometheus 2, EMNLP 2024](https://arxiv.org/html/2405.01535v1), sections 3.4 and 4.1, appendix B | Supervised fine-tuning on direct-assessment and pairwise feedback, plus weight merging; reports Pearson, Spearman and Kendall for direct assessment, accuracy for pairwise evaluation. | Training by feedback imitation differs from reporting correlation. |
| [JudgeLM, ICLR 2025](https://proceedings.iclr.cc/paper_files/paper/2025/file/7f8f73134e253845a8f82983219a8452-Paper-Conference.pdf), sections 3.2 and 6.3 | Instruction fine-tuning to reproduce teacher scores/reasons; agreement, precision, recall, F1, swap consistency and position-bias checks. | Not all judge evaluation is correlation-based. An exact token-loss equation was not verified, so we do not invent one. |
| [Skywork-Reward, 2024](https://arxiv.org/html/2410.18451v1), section 3.3 equation 1 and section 4.2 table 3 | Bradley–Terry negative-log preference likelihood, with alternative-loss comparisons under preference evaluation. | Objective comparisons already exist in reward modeling. Its pairwise target, and its separate per-response binary cross-entropy variant, differ from a six-category human-rating target. |
| [Gneiting and Raftery, 2007](https://sites.stat.washington.edu/raftery/Research/PDF/Gneiting2007jasa.pdf) | Proper and strictly proper probability scoring rules, including logarithmic and quadratic scores. | Population identification of the true distribution under the assumptions; no universal finite-sample or optimization guarantee. |

The empirical question should be stated narrowly: holding inputs, candidates or model capacity, data access and search budget fixed, does selecting or fitting with a human-rating probability loss improve the same held-out metric panel relative to correlation objectives? Selecting a configuration, fitting model parameters, and choosing an evaluation metric are three different decisions.

For type-consistent notation, select a judge j* = argmin_j L_validation(q_j,p_hat), or fit parameters theta* = argmin_theta L_train(q_theta,p_hat). Evaluate the resulting forecast on separate test data. The handwritten left-hand-side distribution and right-hand-side argmin over judges are an informal shorthand, not a complete typed definition. Refitting on training plus validation after locking choices is possible; evaluating on those same ratings does not give an independent test.
