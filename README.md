# Trustworthy theorem judges

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/README.md>

**TLDR:** This project learns and evaluates artificial-intelligence (AI) judges, including large language models (LLMs), of human ratings of formal specification coverage (FSC). Track three efforts: the original VeriBench ratings, the new rating packet and collection, and estimates of how many tasks, solver configurations and raters are needed. The [standalone judge paper](paper_latex/AAAI_2027_Evaluation_AI_Scientists/README.md) connects them and keeps fresh results pending.

## Three efforts to track

| Effort | Where to start | Status checked 11-11-2026 |
| --- | --- | --- |
| Original 25 × 3 × 5 rating study | [Historical judge evidence](experiments/archive/01_legacy_veribench_judge/README.md), [count reconciliation](experiments/07_exp1_metrics/results.md#1-which-count-is-right-343-or-195) | 25 tasks × three candidate generation samples × five rater columns. **75 artifacts; 345 of 375 possible ratings observed; 195 ratings in the three-expert subset.** These are historical data, not three solver systems. |
| New packet and human-rating collection | [Experiment 09](experiments/09_human_rating_collection/README.md), [editable task](experiments/09_human_rating_collection/rating_task_packet/START_HERE.md) | Replacement emphasizing native Claude Code, Codex and Pi, with fewer Terminus2 artifacts: **85 artifacts and 170 independent ratings planned**. In preparation; completed manifest and collection remain pending. |
| Estimate T, A and H | [Experiment 15](experiments/15_rating_tensor_size_estimation/README.md), [source conversations](experiments/15_rating_tensor_size_estimation/SOURCE_INDEX.md) | T = tasks, A = solver configurations, H = distinct human raters. Final size remains open. The 544-rating suggestion was optional Codex planning, not a user-required count. |

The [paper evidence ledger](paper_latex/AAAI_2027_Evaluation_AI_Scientists/README.md#historical-evidence-ledger) tracks the original audits and later analyses of the same ratings. Reusing that evidence does not create another collection. [Experiment 02](experiments/02_probabilistic_ordinal_judge/README.md) holds the shared judge methodology; it is not a fourth rating collection. The [experiment index](experiments/README.md) keeps paused and supporting studies visible separately.

Given original Python source, a candidate Lean formalization, and a gold reference, can a judge predict how qualified humans rate the candidate's coverage of the required specifications? A gold statement may follow from several candidate statements together. Proof correctness and statement coverage are different properties.

**Current priority (11-09-2026):** find the best practical human-rating judge by pursuing method 2 (correlation training) and method 4 (proper-loss training) fairly. The [priority and execution plan](experiments/02_probabilistic_ordinal_judge/PRIORITY_2_VS_4_11-09-2026.md) separates training objectives from the common held-out metrics, records the pending task/agent/rater split amendment, and preserves existing funding limits. Native-probability implementation is in progress; this priority update reports no completed training or inference.

## Sister repo

[judges-dont-need-psychometrics-or-corr](https://github.com/brando90/judges-dont-need-psychometrics-or-corr) is the general position paper behind this project: correlation alone does not identify the desired conditional human-rating distribution. Proper probability losses evaluate that target, while correlations remain useful diagnostics. This limitation does not establish that every psychometric method is unnecessary. This repo is its concrete application to theorem/formalization judges.

Origin: this study motivated the position paper's question about fitting judges to human ratings. Pearson measures linear association of output ratings and Spearman their ordering; neither identifies the full human-rating distribution or requires a linear input-to-rating mapping. Which training objective yields the best practical judge remains an empirical question.

## Project boundary

This repository owns the probabilistic human-rating judge and, separately, an optional forecaster of success under a specified bounded proving procedure. VeriBench owns the actual Lean/FSC engine and differential-testing benchmark reference acceptance; the cert-judge proxy project remains separate. VeriBench's intended evaluation direction is a **prover judge**: AI may guide proof search, while the prover checks whether the required implication has been established. A search timeout is unresolved, not evidence of non-entailment. This documentation records that project boundary; it does not change VeriBench's scorer or relabel its historical LLM-based results.

## Human-rating task ownership

**Primary owner: `trustworthy-theorem-judges`** (Brando's decision, 11-09-2026). Preparing the human grading task first serves VeriBench and the development and evaluation of a formal specification coverage judge. The active task lives in [`experiments/09_human_rating_collection/`](experiments/09_human_rating_collection/README.md), which coordinates instructions, packets, the approved email template, assignments and collection status. Authorized named ratings, the response index and collection status live in experiment 09. Private correspondence, consent and sealed test data remain restricted.

[cert-judge](https://github.com/brando90/cert-judge) and [judges-dont-need-psychometrics-or-corr](https://github.com/brando90/judges-dont-need-psychometrics-or-corr) can use suitable authorized ratings for their own studies while preserving consent, provenance and split/exposure history. They reference this collection rather than own separate copies of its coordination process. The comparison of cross-entropy against correlation objectives belongs in `judges-dont-need-psychometrics-or-corr`.

A larger, appropriately sampled collection can strengthen evidence about agreement with humans; more ratings alone do not establish that a judge is reliable. Studies targeting a specified prover's outcomes instead of human ratings have a different data requirement, as described below.

## Judge paper and supporting work

The canonical [paper and evidence ledger](paper_latex/AAAI_2027_Evaluation_AI_Scientists/README.md) reuse the existing AAAI-style draft. The title, abstract, introduction, methods and discussion now concern **learning and evaluating judges of formal specification coverage**. VeriBench is related work and task provenance; its solver leaderboard and prover results are separate. The draft reports labeled historical evidence and a prospective comparison, not completed results from the new collection.

Compare correlation training with proper-loss training using matched capacity, data and search budgets, selecting both by validation ranked probability score (RPS). Normalized RPS is also the primary held-out metric; cross-entropy and total variation distance are secondary. See the [current methods 2 versus 4 plan](experiments/02_probabilistic_ordinal_judge/PRIORITY_2_VS_4_11-09-2026.md). Strict task-family, solver and rater separation requires a prospective amendment; existing exposure cannot be removed by relabeling splits.

The old 896-task, four-configuration, 24-rater design totals 14,848 planned ratings. It remains a historical budget scenario, not the current packet or an adopted requirement. The preserved older main packet has 125 Terminus2 artifacts and a 250-rating target; the replacement instead plans 85 artifacts and 170 independent ratings, pending execution and collection. Experiment 15 records the open sizing decision and its assumptions.

[Archived studies](experiments/archive/README.md) preserve completed or superseded evidence. Separate prover-target and constructed entailment studies remain linked from the [full index](experiments/README.md); they do not count as human-rating validation.

## Verify and build

```sh
python3 experiments/02_probabilistic_ordinal_judge/scripts/validate_design.py
python3 scripts/check_project.py
python3 scripts/build_paper.py
git diff --check
```

The paper build requires a TeX installation with `latexmk` and the packages required by the official AAAI-27 style. It builds in a temporary directory and writes the current PDF beside its source.

## Prepare or complete ratings

Use experiment 09's [current task instructions](experiments/09_human_rating_collection/rating_task_packet/START_HERE.md), [field guide](experiments/09_human_rating_collection/rating_task_packet/RATING_FORM_GUIDE.md) and [collection status](experiments/09_human_rating_collection/README.md#ratings-and-completion). That folder is the sole editable home for the participant task, forms, scripts, assignments and responses. Follow its versioned packet and delivery procedure; this paper rewrite does not change assignments or send authorization.

## Reference anchoring study

[Replication plan for VeriBench formal specification coverage](docs/reference-anchoring-plan.md). The plan measures whether a gold reference helps a judge distinguish full from partial coverage and whether equally valid formalizations get different scores.
