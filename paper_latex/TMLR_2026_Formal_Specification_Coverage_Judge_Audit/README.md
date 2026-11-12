# TMLR paper: auditing one language-model judge of formal specification coverage

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/paper_latex/TMLR_2026_Formal_Specification_Coverage_Judge_Audit/README.md>

**TLDR:** An anonymous Transactions on Machine Learning Research (TMLR) draft built only from the language-model (LLM) judge section of the [VeriBench launch page](https://cs.stanford.edu/people/brando9/veribench/blog/veribench-launch/). It audits the page's claim that a GPT-5.3-Codex rubric judge reaches Pearson r ≈ 0.61 against human ratings, using archived scores only: the number reproduces exactly, but it hides wide task-level uncertainty, weaker rank agreement, a judge that rates 0.825 points low, a strong dependence on which raters define the target, and mismatched reference inputs for 8 of 25 tasks.

- [Compiled PDF](00_main.pdf) (12 pages: main text on pages 1–9, references on pages 9–10, appendices on pages 10–12) and [main LaTeX source](00_main.tex); numbered files hold one section each, one sentence per line.
- [Official TMLR style provenance](vendor/README.md); the style files are byte-for-byte copies.
- Evidence: [archive experiment 19](../../experiments/archive/19_audit_gpt_5_3_codex_rubric_judge_on_75_rated_outputs_start_12Nov2026_end_12Nov2026/README.md) holds the [results](../../experiments/archive/19_audit_gpt_5_3_codex_rubric_judge_on_75_rated_outputs_start_12Nov2026_end_12Nov2026/results.md), [every number as JSON](../../experiments/archive/19_audit_gpt_5_3_codex_rubric_judge_on_75_rated_outputs_start_12Nov2026_end_12Nov2026/POSTHOC_CLI_RUBRIC_JUDGE_AGREEMENT_11-12-2026.json), [the analysis script](../../experiments/archive/19_audit_gpt_5_3_codex_rubric_judge_on_75_rated_outputs_start_12Nov2026_end_12Nov2026/scripts/recompute_cli_rubric_judge_agreement.py) and the hash-pinned receipts in its [source manifest](../../experiments/archive/19_audit_gpt_5_3_codex_rubric_judge_on_75_rated_outputs_start_12Nov2026_end_12Nov2026/SOURCE_MANIFEST.json).

## Scope: the launch page's judge section only

User request, 11-12-2026: "create a TMLR version, based on the [launch page] LLM judge section only." That section has two parts: step 3 of "How We Score a Solution" ("Do the theorems cover the gold reference?") and "Human Calibration". Its claims, and where the paper handles each:

| Launch-page claim | Paper |
| --- | --- |
| Raters receive the same guidelines as the LLM judge and score candidate Lean files against gold reference files | Section 2 and Appendix A: the audited judge's system prompt restates the raters' rubric; the deployed scorer used a different, equivalence-style rubric |
| Human and judge scores are compared to measure how well the judge tracks human judgment | Sections 2.4 and 3 |
| Theorem coverage (TC1) is estimated by the paper's deployed LLM coverage judge | Section 2.3 and Section 4: the deployed judge (Claude Sonnet 4.6) is not the audited judge, and its own agreement was not reported |
| A GPT-5.3-Codex CLI rubric check reaches raw Pearson about 0.61, with weaker rank correlations | Reproduced exactly (r = 0.6137, ρ = 0.3755, τ = 0.2996) and audited in Section 3 |
| This is an alignment audit, not a claim that the deployed scorer was fitted to human labels | Introduction and Section 4 |

Deliberately left out:

- **The page's illustrative figure** ("Human vs. LLM judge calibration", Pearson r = 0.86, "n = 75" with about 40 dots). It matches no archived receipt: task means of the audited run give r = 0.685, and the report's own task-aggregated diagnostics (about 0.85) come from a run we could not match. The [AAAI paper README](../AAAI_2027_Evaluation_AI_Scientists/README.md) already warns against copying it.
- **Everything outside the judge section**: benchmark construction, solver results and the scoring formula.
- **Later judge work on the same ratings** (VeriBench experiments 100 and 104, the selected two-model ensemble) and this project's prospective method 2 versus method 4 study. They are not in the launch section; the [AAAI paper](../AAAI_2027_Evaluation_AI_Scientists/README.md) remains their home.

**Paper template** (Neel Guha's archetypes): *discovery*, as a measurement audit. It answers what one reported judge–human correlation establishes; the reporting checklist is supporting material, not a separate claim.

## What the audit found

All statistics use the 75 artifacts from 25 tasks and the pooled human target (mean of all available ratings in seven rating files), on the 0–5 scale. Brackets are 95% percentile intervals from 10,000 bootstrap draws over tasks, seed 20261112, p-val=n/a; only the receipt's point correlations and their p-values pre-existed.

| Question | Measured |
| --- | --- |
| Does the reported number reproduce? | Yes, to 1e-12: r = 0.614 [0.213, 0.821], ρ = 0.375 [0.013, 0.668], τ_b = 0.300 [0.021, 0.545]. Receipt p-values (independent-item tests) 4.78e-9, 9.03e-4, 4.49e-4 overstate precision. |
| Rank versus linear | r − ρ = 0.238 [0.061, 0.408] |
| Level (mean bias = judge − human; negative = stricter judge) | Judge mean 2.382 vs human 3.207: bias −0.825 [−1.082, −0.594]; ICC(A,1) 0.429 [0.110, 0.662] vs ICC(C,1) 0.613 [0.206, 0.819]; mean absolute error 0.889 [0.695, 1.122], 0.184 [−0.098, 0.440] above an out-of-fold constant prediction |
| Between versus within tasks | Task means r = 0.685 [0.150, 0.911]; centered within-task r = 0.358 [0.055, 0.635]; Spearman computed inside each task averages 0.255 [−0.073, 0.579] over the 20 tasks where neither score is constant |
| Which raters (receipt, no intervals; every row reproduced from the rating files to 1e-12) | Lenient group r = 0.702, bias −1.191; expert group r = 0.372, bias −0.249; five raters r = 0.500; single raters r 0.275–0.742, bias from −1.484 (participant 4) to +0.303 (participant 3) |
| Did the judge read the raters' files? | Artifacts: 75/75 byte-identical. References: the rated theorem statements for 51 artifacts (17 tasks); on those, r = 0.775 [0.371, 0.915], ρ = 0.565 [0.197, 0.800], ICC(A,1) 0.617, bias −0.587 [−0.760, −0.393]. For the other 24 artifacts (8 tasks) the statements differ (21 even differ in theorem count); they include all five placeholder-reference tasks (the whole security family): bias −1.330 [−1.838, −0.866]. |
| Isotonic remapping (two-fold task split, out of fold) | r = 0.211 [−0.123, 0.505], ρ = 0.046 [−0.320, 0.415]; bias −0.018; mean absolute error 0.628, 0.077 [−0.178, 0.020] below an out-of-fold constant (interval includes zero). Each fold keeps its order (ρ 0.596, 0.238) but is shifted toward the other fold's human mean, which scrambles the pooled order. |

The audited configuration was the best of three tried on these same ratings (Pearson 0.333, 0.406, 0.614), so it has no untouched test set.

## Light QA: one Gemini Argon round, 11-12-2026

Reviewer: Antigravity `agy` with `gemini-4-argon-high`, effort high, read-only brief, run once (11:41–11:57 PST). Verdict: **PASS WITH FIXES** (1 major, 6 minor, 3 nits). It independently recomputed the headline statistics, intervals, input-audit counts and leave-one-expert-out comparator from the receipts and found them correct.

| Finding | Disposition |
| --- | --- |
| F1 minor: Figure 1 caption said 0.78; the largest plotted value is 0.775 | Fixed to 0.77 |
| F2 major: no explanation of why a monotone remapping collapses Spearman ρ | Fixed: verified per-fold numbers (within-fold ρ 0.596 and 0.238; fold human means 2.966 and 3.468; predictions shifted to 3.376 and 2.989); Section 3.6 explains the opposite level shifts; new `isotonic_fold_diagnostics` in the JSON |
| F3 minor: "an interval for every derived statistic" overclaimed | Fixed: contribution limited to pooled-target statistics; constant-baseline comparisons now have paired task-bootstrap intervals; Table 2 caption says how the last column is computed |
| F4 minor: centered Spearman still ranks residuals across tasks | Fixed: clarified, and added the average within-task Spearman, 0.255 [−0.073, 0.579] over 20 tasks |
| F5 minor: the third-version reference does differ (7 theorems vs 5 rated) | Fixed: all 8 mismatched tasks now described as differing; theorem counts added to the JSON |
| F6 minor: participant 1 and 3 judge means are computable; counts have a known cause | Fixed: rebuilt every rater-group row from the seven rating files (exact to 1e-12); Table 2 now shows −0.329 and +0.303; causes stated (an older reference file name in three rows, one malformed row; 44 ratings in participant 3's file at run time) |
| F7 minor: the cited sources call the quantity TC1/TE1, and the FSC acronym was unused | Fixed: naming sentence added, acronym dropped |
| F8 nit: Table 3 printed −0.00 | Fixed: Tables 3 and 4 use three-decimal intervals (−0.002) |
| F9 nit: bold caption sentence shares a line with the next sentence | Not changed: the shared one-sentence-per-line checker treats a bold run-in heading as sharing its line with the first sentence and fails the split form |
| F10 nit: VeriBench reference truncated to three authors | Fixed: all 28 authors listed |

Self-review fixes in the same pass: the remapping's error is described as close to, not "no better than", a constant prediction (it is 0.077 [−0.178, 0.020] lower); the target-maximizes-correlation statement is limited to the four group targets; the matched-input result is stated descriptively; the benchmark-totals sentence is cited and softened. Per the light-QA rule, there is no second review round.

## Open items before submission

- `TODO(internal-review)` in [05_validity.tex](05_validity.tex): a later private VeriBench appendix reports the retired equivalence-rubric judge at Spearman 0.270 against the all-rater mean, with references from a later snapshot. Citing it needs Brando's approval to import that aggregate with its caveat.
- The submission is anonymous (`\usepackage{tmlr}`); it cites the public VeriBench report in the third person. Its bibliography URL is a personal web page; replace it with an arXiv or OpenReview link if one exists before submitting. Use `[preprint]` only for a de-anonymized preprint.
- Recheck the [TMLR author guide](https://jmlr.org/tmlr/author-guide.html) and add any required AI-writing disclosure at submission time.

## Build and reproduce

From the repository root:

```bash
python3 scripts/build_paper.py --paper TMLR_2026_Formal_Specification_Coverage_Judge_Audit
```

```bash
python3 paper_latex/TMLR_2026_Formal_Specification_Coverage_Judge_Audit/figures/make_agreement_figure.py
```

```bash
python3 experiments/archive/19_audit_gpt_5_3_codex_rubric_judge_on_75_rated_outputs_start_12Nov2026_end_12Nov2026/scripts/recompute_cli_rubric_judge_agreement.py --source-repo /path/to/veribench
```

The build compiles in a temporary directory and refreshes `00_main.pdf` only when there are no overfull boxes or unresolved references. The figure script reads only the aggregate JSON. The analysis script needs the private VeriBench repository at the pinned commits, verifies every input hash, makes no model calls, and writes aggregates only.

**Terms used throughout:** *artifact* (a rated candidate Lean file), *reference* (the human-written gold Lean file), *rating*/*rater*/*judge* (data/people/model), *pooled target*, *lenient group*, *expert group*, *five-rater target*, *mean bias* (judge minus human), *isotonic remapping* (never "calibration", per the project checker and the terminology skill).
