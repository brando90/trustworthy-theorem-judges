# Trustworthy theorem judges

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/README.md>

**TLDR:** This project studies artificial-intelligence (AI), agent, and large language model (LLM) judges for formal specification coverage (FSC). It contains a prospective human-rating methodology, a prover-outcome forecasting study, historical VeriBench judge evidence, and an AAAI-27 workshop paper draft. A fresh local feasibility test is complete; broad judge validation remains pending.

Given original Python source, a candidate Lean formalization, and a gold reference, can a judge predict how qualified humans rate the candidate's coverage of the required specifications? A gold statement may follow from several candidate statements together. Proof correctness and statement coverage are different properties.

**Current priority (11-09-2026):** find the best practical human-rating judge by pursuing method 2 (correlation training) and method 4 (proper-loss training) fairly. The [priority and execution plan](experiments/02_probabilistic_ordinal_judge/PRIORITY_2_VS_4_11-09-2026.md) separates training objectives from the common held-out metrics, records the pending task/agent/rater split amendment, and preserves existing funding limits. Native-probability implementation is in progress; this priority update reports no completed training or inference.

## Sister repo

[judges-dont-need-psychometrics-or-corr](https://github.com/brando90/judges-dont-need-psychometrics-or-corr) is the general position paper behind this project: correlation alone does not identify the desired conditional human-rating distribution. Proper probability losses evaluate that target, while correlations remain useful diagnostics. This limitation does not establish that every psychometric method is unnecessary. This repo is its concrete application to theorem/formalization judges.

Origin: this study motivated the position paper's question about fitting judges to human ratings. Pearson measures linear association of output ratings and Spearman their ordering; neither identifies the full human-rating distribution or requires a linear input-to-rating mapping. Which training objective yields the best practical judge remains an empirical question.

## Project boundary

This repository owns the probabilistic human-rating judge and, separately, an optional forecaster of success under a specified bounded proving procedure. VeriBench owns the actual Lean/FSC engine and differential-testing benchmark reference acceptance; the cert-judge proxy project remains separate. VeriBench's intended evaluation direction is a **prover judge**: AI may guide proof search, while the prover checks whether the required implication has been established. A search timeout is unresolved, not evidence of non-entailment. This documentation records that project boundary; it does not change VeriBench's scorer or relabel its historical LLM-based results.

## Human-rating task ownership

**Primary owner: `trustworthy-theorem-judges`** (Brando's decision, 11-09-2026). Preparing the human grading task first serves VeriBench and the development and evaluation of a formal specification coverage judge. The active task lives in [`experiments/09_human_rating_collection/`](experiments/09_human_rating_collection/README.md), which coordinates instructions, packets, the approved email template, assignments and collection status. Participant records and individual ratings stay in the approved private store.

[cert-judge](https://github.com/brando90/cert-judge) and [judges-dont-need-psychometrics-or-corr](https://github.com/brando90/judges-dont-need-psychometrics-or-corr) can use suitable authorized ratings for their own studies while preserving consent, provenance and split/exposure history. They reference this collection rather than own separate copies of its coordination process. The comparison of cross-entropy against correlation objectives belongs in `judges-dont-need-psychometrics-or-corr`.

A larger, appropriately sampled collection can strengthen evidence about agreement with humans; more ratings alone do not establish that a judge is reliable. Studies targeting a specified prover's outcomes instead of human ratings have a different data requirement, as described below.

## Methodology and paper

- [Human-rating task preparation and collection](experiments/09_human_rating_collection/README.md): the operational home migrated from VeriBench, with private records preserved and the remaining team-delivery blockers stated explicitly.
- [T, A, H estimates and original conversations](experiments/15_rating_tensor_size_estimation/README.md): source passages and methods for choosing tasks, solver configurations and raters; final size remains open.
- [Study methodology and collection design](experiments/02_probabilistic_ordinal_judge/README.md): predict the six-category conditional human-rating distribution with ranked probability score as the primary held-out metric and common validation criterion; cross-entropy and total variation distance are secondary evaluation metrics, and correlations are diagnostics.
- [Historical results and provenance](experiments/archive/01_legacy_veribench_judge/README.md): preserved aggregate receipts, limitations, and a clear separation from new validation.
- [Prover-outcome forecasting study](experiments/archive/03_prover_target_fsc_judge/README.md): predict acceptance by a specified proof-search procedure with Brier loss. A retrospective analysis using saved results is complete; fresh statement-only validation remains pending.
- [Fresh local prover-target pilot](experiments/archive/05_fresh_local_prover_target_judges/README.md): completed eight statement-generation attempts and explicit probability forecasts under a frozen local target. Five artifacts were malformed and all three available outcomes were unsuccessful; no judge was validated.
- [Master-specification entailment pilot](experiments/08_master_specification_entailment/README.md): a separate statement-only condition with kernel-checked constructed labels, explicit ineligible cases, and task-family-held-out probability forecasts. It targets semantic implication conditional on satisfiability; it does not substitute bounded search failure for non-entailment.
- [AAAI-27 workshop paper](paper_latex/AAAI_2027_Evaluation_AI_Scientists/README.md): anonymous LaTeX source and compiled PDF using the official author kit.
- [Experiment index](experiments/README.md): status, scope, and next evidence needed.

The starting collection design has **896 tasks, four solver configurations, and 24 distinct raters** (eight for training/validation and 16 for the final audit). Collect three ratings per artifact and eight total on a 128-task audit subset. Separate training/validation artifacts from fresh final-audit outputs: **14,848 individual ratings** in total. These are planning counts, not a precision guarantee or a completed collection. The pilot must establish feasibility, thresholds, and uncertainty before the test is opened.

The prover-target study requires no human ratings for its operational target. This changes the question: predicting proof-search success under a specified procedure and budget does not establish agreement with experts. A valid checked proof establishes the formal implication checked; an unsuccessful search does not establish that the implication is false. Historical prover acceptance also includes proof and adapter checks that differ from statement coverage, as documented in the study's source audit.

## Verify and build

```sh
python3 experiments/02_probabilistic_ordinal_judge/scripts/validate_design.py
python3 scripts/check_project.py
python3 scripts/build_paper.py
git diff --check
```

The paper build requires a TeX installation with `latexmk` and the packages required by the official AAAI-27 style. It builds in a temporary directory and writes the current PDF beside its source.

## Rate a file

Open the extracted packet’s `START_HERE.md` and `Rating_Instructions.md`. Read the Python source and gold theorem statements, then open the first candidate in its folder. A gold statement counts as covered if the candidate statements imply it, possibly by combining several lemmas. Apply the packet’s 0–5 rubric and record one final score per candidate file. A score summarizes the whole file.

The coordinator uses the personal sheet supplied with the original packet. Team members use a separate answer sheet each. Keep completed ratings private until collection closes.

## Prepare identical examples for independent ratings

The coordinator needs the original, extracted VeriBench human-rating packet. The public checkout contains the builder. On the coordinator’s machine, the packet, individual answers and shareable archives live under the ignored `private/` directory.

From the repository root, build an archive for the folders assigned to a rater. For example, for folder 1:

```sh
python3 experiments/09_human_rating_collection/support/scripts/make_team_packet.py private/original private/team-folder-01-new.zip --folders 1
```

Follow the [collection task's current delivery status](experiments/09_human_rating_collection/README.md#edit-or-prepare-the-task) before sending. Pass multiple folder numbers to package an assignment. Omit `--folders` to package all 25 folders. Use a new output filename for each build. The builder checks the frozen delivery manifest, preserves the original example bytes and filenames, and includes the rubric, instructions, a blank answer sheet and file checksums. Send the same archive to raters rating the same assignment. Each returns their own completed sheet privately.

## Reference anchoring study

[Replication plan for VeriBench formal specification coverage](docs/reference-anchoring-plan.md). The plan measures whether a gold reference helps a judge distinguish full from partial coverage and whether equally valid formalizations get different scores.
