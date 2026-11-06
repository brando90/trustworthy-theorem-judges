<!-- TLDR: Experiment 03's unchanged probability map transfers to 339 unseen Core-614 tasks: pooled Brier loss 0.107 versus 0.144 for the constant; retrospective, historical target, unbound judge. -->
# Experiment 04 Phase 0 results: frozen-map transfer to unseen tasks

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/04_fresh_prover_target_judge_validation/RESULTS_phase0_transfer.md>

**TLDR:** On 1,352 artifacts from 339 VeriBench Core-614 tasks that experiment 03 never used, its unchanged probability map lowers Brier loss from 0.144 (constant) to 0.107, a paired difference of -0.037 [-0.049, -0.026] (p-val=n/a), and it beats every simple baseline. Within a single solver, though, candidate file length ranks outcomes as well as or better than the rating for three of four solvers, so the rating's advantage is largely calibration across solvers. This is a zero-call retrospective check on the historical target, not fresh judge validation.

Protocol frozen at commit `9d9a29b` before any metric was computed ([protocol](PROTOCOL_phase0.md), [configuration](config_phase0.json), [script](scripts/phase0_transfer.py)). Aggregates: [`results/phase0_transfer.json`](results/phase0_transfer.json); source hashes: [`results/phase0_sources.json`](results/phase0_sources.json). New model calls: 0. Cost: $0.

## Scope

- **Artifacts:** 1,352 Core-614 solver runs (one solver run on one task) from 339 tasks, from VeriBench experiments `144_core614_dt_first_batch_claude_code_11-01-2026` and `147`–`153` (summary `154_core614_dt_overview_358_tasks_11-01-2026`), VeriBench revision `ec1f9b2a44`. There are 452 artifacts on 114 tasks in the first batch and 900 on 225 tasks in the security set. No task is shared with Tiny-256, checked case-insensitively.
- **Outcome:** first-pass Lean-checked entailment under the experiment 145 five-condition rule; 1,117 of 1,352 accepted (0.826). Three retry-round conversions are scored 0 here; the final-outcome sensitivity row uses 1,120.
- **Input:** the saved judge-ensemble formal specification coverage (FSC) rating `FSC_cov` from VeriBench experiment `137_public_vbv1_896_harsh_failure_reasons_and_smooth_components_10-30-2026`; the join is complete and unique. No exact judge model is bound to a rating.
- **Checks:** the split manifest reproduces experiment 03's hash split; refitting the map on experiment 03's training split reproduces the frozen coefficients exactly (gap 0.0); oracle, 0.5 and complement controls give Brier 0, 0.25 and 1; 902 Core-614 candidate files checked against solver manifests, 0 mismatches.

## Pooled result (1,352 artifacts, 339 tasks)

| Forecast | Brier loss ↓ | Bias (forecast − outcome) | Mean forecast | Area under ROC curve | Spearman | Pearson | Kendall |
|---|---:|---:|---:|---:|---:|---:|---:|
| Frozen map | **0.107** [0.092, 0.123] | -0.002 [-0.026, 0.022] | 0.824 | 0.749 [0.705, 0.790] | 0.525 [0.440, 0.600] | 0.504 [0.425, 0.573] | 0.510 [0.429, 0.582] |
| Constant 0.800781 | 0.144 [0.126, 0.163] | -0.025 [-0.056, 0.006] | 0.801 | 0.500 | n/a | n/a | n/a |
| Raw rating (diagnostic) | 0.132 [0.110, 0.155] | 0.135 [0.109, 0.161] | 0.961 | 0.749 [0.705, 0.790] | 0.525 [0.440, 0.600] | 0.496 [0.424, 0.559] | 0.510 [0.429, 0.582] |
| Theorem-count ratio map | 0.144 [0.126, 0.163] | -0.027 [-0.058, 0.004] | 0.799 | 0.514 [0.495, 0.533] | 0.039 [-0.014, 0.095] | 0.056 [-0.005, 0.114] | 0.039 [-0.014, 0.094] |
| File-length map | 0.138 [0.121, 0.155] | -0.028 [-0.056, 0.001] | 0.798 | 0.618 [0.568, 0.665] | 0.155 [0.087, 0.220] | 0.230 [0.152, 0.302] | 0.126 [0.071, 0.180] |
| Per-solver prevalence | 0.139 [0.122, 0.157] | -0.025 [-0.056, 0.006] | 0.801 | 0.632 [0.604, 0.662] | 0.179 [0.141, 0.217] | 0.186 [0.147, 0.225] | 0.163 [0.129, 0.198] |

Outcome mean 0.826 [0.795, 0.857]. ROC means receiver operating characteristic. Correlations are undefined for a constant forecast.

| Paired Brier difference (negative favors the first) | Pooled | First batch (452 / 114 tasks) | Security set (900 / 225 tasks) |
|---|---:|---:|---:|
| Map − constant (**primary**) | **-0.037** [-0.049, -0.026] | -0.061 [-0.094, -0.029] | -0.025 [-0.032, -0.019] |
| Map − theorem-count ratio map | -0.037 [-0.048, -0.026] | -0.059 [-0.090, -0.029] | -0.026 [-0.032, -0.019] |
| Map − file-length map | -0.030 [-0.041, -0.020] | -0.045 [-0.074, -0.017] | -0.023 [-0.030, -0.016] |
| Map − per-solver prevalence | -0.032 [-0.044, -0.020] | -0.056 [-0.089, -0.024] | -0.020 [-0.028, -0.013] |
| Final-outcome sensitivity, map − constant | -0.037 [-0.049, -0.026] | — | — |

## Per solver (one artifact per task, so tasks = artifacts)

| Solver | Artifacts | Accepted | Map Brier | Constant Brier | Map − constant | Map − length | Map ROC area | Length-map ROC area |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| GPT-6 Astra / Terminus 2 | 338 | 296 | 0.081 | 0.114 | -0.033 [-0.046, -0.021] | -0.020 [-0.032, -0.008] | 0.768 [0.691, 0.844] | 0.862 [0.798, 0.918] |
| Claude Code | 339 | 256 | 0.168 | 0.187 | -0.019 [-0.035, -0.003] | -0.006 [-0.021, 0.008] | 0.639 [0.586, 0.693] | 0.760 [0.699, 0.820] |
| Codex CLI | 337 | 255 | 0.122 | 0.186 | -0.064 [-0.090, -0.038] | -0.061 [-0.090, -0.034] | 0.820 [0.765, 0.871] | 0.795 [0.744, 0.843] |
| Fable 5.1 / Terminus 2 | 338 | 310 | 0.057 | 0.090 | -0.033 [-0.044, -0.023] | -0.034 [-0.044, -0.023] | 0.804 [0.708, 0.894] | 0.935 [0.899, 0.965] |

The map beats the constant for every solver. For Claude Code its advantage over the file-length map has an interval that includes zero. Within each solver, the file-length map's ranking (area under the ROC curve) is higher than the rating's for three of four solvers. Its pooled Brier loss is worse because one map fitted on pooled Tiny-256 data is miscalibrated across solvers. These ROC comparisons are descriptive: no paired ROC test was declared.

## Calibration by saved rating (pooled)

| Saved rating | Artifacts | Tasks | Accepted | Mean forecast | Observed rate |
|---|---:|---:|---:|---:|---:|
| 1.0 | 1,147 | 315 | 1,042 | 0.887 | 0.908 |
| 0.9 | 76 | 56 | 42 | 0.753 | 0.553 |
| 0.8 | 43 | 31 | 12 | 0.542 | 0.279 |
| 0.7 | 40 | 27 | 13 | 0.315 | 0.325 |
| 0.6 | 19 | 16 | 4 | 0.151 | 0.211 |
| at most 0.5 | 27 | 25 | 4 | 0.034 | 0.148 |

The map overpredicts at ratings 0.9 and 0.8 and underpredicts at 0.5 or below. 85% of artifacts carry the top rating, which limits how much any rating-based forecast can separate them.

## Predictions versus observations

| Prediction (plan commit `8be94a8`) | Observed |
|---|---|
| Map beats constant, pooled paired difference in [-0.07, -0.03] | -0.037, inside the range |
| Smaller gain on the security set than on the first batch | -0.025 versus -0.061 |
| Map overpredicts at rating 0.9 | 0.753 forecast versus 0.553 observed |
| Theorem-count ratio may match the map (unknown) | It does not: ratio map ≈ constant (difference -0.000 [-0.002, 0.001]) |
| Not predicted | File length ranks outcomes within solver as well as or better than the rating for three of four solvers |

## Deviations and data notes

1. **Missing gold counts (post-freeze, outcome-blind).** 14 Core-614 rows had no gold theorem count because a gold or solver file did not compile; each took its task's largest count recorded for another solver. This affects only the theorem-count baseline.
2. **Tiny-256 candidate bytes.** For 24 of 1,024 Tiny-256 runs, the experiment 138 `solver.lean` differs from the hash in its receipt; only baseline training features use these files.
3. The theorem-count and length baselines selected ridge 0 on validation; the theorem-count map barely varies (validation Brier 0.2205 at every ridge).

## What this establishes and what it does not

- **Supported:** under the same historical target, experiment 03's frozen map transfers to 339 tasks it never saw, and it beats a constant, a theorem-count ratio, file length and solver identity on Brier loss.
- **Not established:** fresh validation (the outcomes were already tabulated in aggregate); validity of the target (agent-written bridges, name-based statement correspondence, no trusted kernel replay); a named judge (the rating is an unbound historical ensemble); family independence (the security set has Tiny-256 sibling families, and the intervals omit family dependence).
- **Implication for the fresh study:** a named judge must beat both the constant and a within-solver file-length baseline. The fresh test should report within-solver ranking, not only pooled Brier loss.

**TLDR-end:** [ttj: experiment 04 Phase 0] Experiment 03's unchanged map transfers to 339 unseen tasks (Brier 0.107 versus 0.144, paired -0.037 [-0.049, -0.026]) and beats every simple baseline pooled. Within a solver, file length ranks about as well as the rating, so the fresh study needs that baseline.
