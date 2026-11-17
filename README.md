# Trustworthy theorem judges

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/README.md>

**TLDR:** This project learns and evaluates artificial-intelligence (AI) judges, including large language models (LLMs), that predict how humans rate formal specification coverage (FSC). Three efforts are tracked below: the original VeriBench rating study, the current rating packet and collection, and the estimate of how many tasks, solver configurations and raters a study needs.

## Three efforts to track

| Effort | Start here | Status checked 11-14-2026 |
| --- | --- | --- |
| 1. Original 25 × 3 × 5 rating study | [archive/01_veribench_25_tasks_3_samples_5_raters_judge_evaluation_start_03May2026_end_29Sep2026](experiments/archive/01_veribench_25_tasks_3_samples_5_raters_judge_evaluation_start_03May2026_end_29Sep2026/README.md), [count reconciliation](experiments/archive/07_compare_5_judges_on_75_outputs_and_estimate_rating_needs_start_09Nov2026_end_09Nov2026/results.md#1-which-count-is-right-343-or-195) | **Complete, historical.** 25 tasks × three candidate generation samples × five rater columns: 75 artifacts, 345 of 375 possible ratings observed, 195 in the three-expert subset. The three samples are not three solver systems. |
| 2. Current rating packet and collection | [09_prepare_packets_and_collect_human_ratings_start_28Sep2026](experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026/README.md), [the task to rate](experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026/rating_task_packet/START_HERE.md) | **All-native 100-file packet (25 tasks × 4 frontier agents, each in its vendor's own harness) in 32 personal 100-row Google Sheets; no main rating completed yet; Brando's own packet emailed to him on 11-17-2026; 31 team emails saved as unsent Gmail drafts, on hold until he has done his own ratings.** Target: two independent ratings per file, **200 in total** (plus Brando's author ratings). That README's "Who is grading" table holds live per-rater progress. |
| 3. How many tasks, solver configurations and raters | [15_estimate_required_tasks_solver_configurations_and_human_raters_start_04Nov2026](experiments/15_estimate_required_tasks_solver_configurations_and_human_raters_start_04Nov2026/README.md) | **Decision open.** Finish the 200 ratings first. Comparing two training objectives to ±0.01 needs about 37 held-out task families, with a range of 3 to 155 until one quantity is measured. Three choices await Brando there. |

The current 100-file main rating packet covers all 25 tasks with four frontier agents, each run in its vendor's own harness (five solver conditions): 25 Codex with GPT-6 Astra (`xhigh`, prompt v5; historical), 25 Claude Code with Claude Fable 5.1 (`max`, prompt v8; 19 from 11-11-2026 and 6 rerun on 11-16 to 11-17-2026 with a larger single-response cap), 25 Grok CLI with Grok 4.7 (`xhigh`, prompt v8) and 25 Antigravity CLI with Gemini 4 Argon (`high`, prompt v8). Pi with Gemini 3.8 Flash returned zero outputs. Earlier snapshots (the 54- and 75-file packets, the 11-16-2026 packet whose Grok and Gemini files came from Terminus 2, and an older 125-file Terminus 2 packet) are preserved as history and are not the current task.

## Everything else

- **Judge methodology:** [02_design_a_judge_that_predicts_human_ratings_0_to_5_start_06Nov2026](experiments/02_design_a_judge_that_predicts_human_ratings_0_to_5_start_06Nov2026/README.md) defines the six-probability judge and the [current priority](experiments/02_design_a_judge_that_predicts_human_ratings_0_to_5_start_06Nov2026/PRIORITY_2_VS_4_11-09-2026.md): train one judge by Pearson correlation (method 2) and one by a proper probability loss (method 4) under matched budgets, select both by validation ranked probability score, and evaluate both on the same held-out ratings. It is methodology, not a fourth rating collection; no training or inference has been completed.
- **Paper:** [paper_latex/AAAI_2027_Evaluation_AI_Scientists](paper_latex/AAAI_2027_Evaluation_AI_Scientists/README.md) holds the standalone judge paper and the ledger of historical evidence. New results remain pending.
- **TMLR paper:** [paper_latex/TMLR_2026_Formal_Specification_Coverage_Judge_Audit](paper_latex/TMLR_2026_Formal_Specification_Coverage_Judge_Audit/README.md) is built only from the VeriBench launch page's language-model judge section. It audits that page's Pearson r ≈ 0.61 claim from archived scores: the number reproduces, but the judge rates 0.825 points below the pooled human mean and read mismatched references for 8 of 25 tasks.
- **Archive:** [experiments/archive](experiments/archive/README.md) lists completed, paused and proposed studies with what remains open for each. Later analyses of the original ratings reuse the same observations; they are not additional collections.
- **Sister repository:** [judges-dont-need-psychometrics-or-corr](https://github.com/brando90/judges-dont-need-psychometrics-or-corr) is the general position paper: correlation alone does not identify the human rating distribution. General objective-comparison studies 06 and 11–14 live there. This repository is its concrete application to theorem and formalization judges.
- **Rules for agents:** [AGENTS.md](AGENTS.md), mirrored in `CLAUDE.md`, records ownership, privacy and file-placement decisions.

## What the project asks

Given the original Python source, a candidate Lean formalization and a gold reference, can a judge predict how qualified humans rate the candidate's coverage of the required specifications? A gold statement may follow from several candidate statements together. Proof correctness and statement coverage are different properties.

This repository owns the probabilistic human-rating judge and the collection of the human ratings it needs. VeriBench owns the Lean prover and the benchmark's reference acceptance; a prover establishes an implication only with a checked proof, and a search timeout is unresolved. More ratings can strengthen evidence about agreement with humans, but sample size alone does not establish that a judge is reliable.

## Verify and build

```sh
python3 scripts/check_project.py
python3 scripts/build_paper.py
git diff --check
```

The project check runs the design validator, the collection tests and the experiment 15 consistency checks. The paper build requires a TeX installation with `latexmk` and the packages of the official AAAI-27 and TMLR styles; it builds every paper in a temporary directory and writes each current PDF beside its source. Pass `--paper <directory name>` to build one paper.
