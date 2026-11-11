# Formulation ② versus ④ on cached judge scores: pick by correlation or by cross-entropy, 80/20 task splits

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/12_formulation2_vs_4_corr_vs_ce_80_20_splits/README.md>

**TLDR:** The judge was chosen on training tasks only, once with correlation to the human ratings as the objective (②) and once with cross-entropy as the objective (④), then scored on held-out tasks with RPS (main), CE, TVD, Spearman and Pearson. 1,000 task-grouped 20/5 splits plus one fixed split, cached judges, $0, CPU only. On RPS the two tie (interval includes 0); ④ wins CE, ② wins the correlations.

Results and numbers: [results.md](results.md), [results/results.json](results/results.json). Run log: [results/run_transcript.txt](results/run_transcript.txt) and [agent_log.md](agent_log.md).

## What was run

- Data: the experiment 11 dataset (75 artifacts, 25 tasks; three Claude 3.7 Sonnet samples per task; 195 expert ratings, 2 to 3 per artifact; five cached judges, three cached scalar ratings each, VeriBench commit `be287d9`, experiment 100), rebuilt by [scripts/build_dataset.py](scripts/build_dataset.py). The dataset stays private (individual ratings).
- Splits: [scripts/common.py](scripts/common.py), 20 train and 5 test tasks, grouped by task. Repeated splits use seeds 20261210 to 20262209; the fixed split is seed 1210, declared before any fitting.
- Selection, repeated splits ([scripts/run_exp12.py](scripts/run_exp12.py)): the searched family is one cached judge or a weighted mixture of the five. ② maximizes train Pearson (exact solver of experiments 10/03), or train Spearman (4,000-point simplex search); ④ minimizes train CE (SLSQP with a checked certificate). Single-judge versions pick the argmax or argmin. No validation split (③ and ① are not run). No LLM in this loop.
- Selection, fixed split: two Claude Code subagents saw only the 60 training artifacts ([scripts/prep_agent_inputs.py](scripts/prep_agent_inputs.py)) and one objective each, and wrote their judge to [agent_fixed_split/](agent_fixed_split/); [scripts/score_agents.py](scripts/score_agents.py) scored them on the 5 held-out tasks.
- Statistics: per-artifact test metric averaged over the splits where it was held out, 10,000-draw task bootstrap of the paired difference; correlations are task-attributed split-level values. [scripts/make_report.py](scripts/make_report.py) writes results.md.

## Limits

Five test tasks per split is small. The cached judges' prompts were developed on the original train split's ratings (see results.md), so held-out tasks may have been seen at design time. No new prompts or models were searched, no paid API, no frontier-model arm. Not a test of ③ versus ④.
