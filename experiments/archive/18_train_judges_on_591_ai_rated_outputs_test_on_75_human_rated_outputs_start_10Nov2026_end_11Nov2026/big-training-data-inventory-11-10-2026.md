# Is there a training set bigger than the 75 human-rated artifacts? Inventory and plan

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/archive/18_train_judges_on_591_ai_rated_outputs_test_on_75_human_rated_outputs/big-training-data-inventory-11-10-2026.md>

**TLDR:** Brando's memory is right: the large collection run is VeriBench experiment 106 (leave-one-agent-out, seven AI rater families, 725 artifacts on 75 tasks), not experiment 104. It is a bigger training set, but its labels are AI-rater scores, not human ratings; no human-labelled set larger than the 75 artifacts (25 tasks, 195 expert ratings) exists in the places searched. The plan is to train on experiment 106's 650 fresh artifacts (50 tasks, zero task overlap with the 25) and test on all 75 human-rated artifacts, comparing correlation-selected against loss-selected judges. Experiment 106 already ran a close cousin of this and found a judge fitted to the AI raters falls from about 0.91 against them to 0.621 against the real experts.

Source: Brando Miranda's WhatsApp voice notes of 11-10-2026 17:39 and 17:49. Read-only inventory by ub9sc on 11-10-2026; no model or paid API was run, nothing in the source repos was changed, and no per-item human ratings, rater identifiers or private task names are listed (counts only). Label for each count: (V) recounted from files this session, (S) counted by a read-only sub-inventory, (R) quoted from a repo report, not recounted.

## Answer in five lines

1. **Human-labelled, larger than 75 artifacts:** I did not find one in the repos, the machine's records or the files searched (list below). All human ratings are the same 75 artifacts: 25 tasks x 3 samples from `claude-3-7-sonnet-20250219`, with 195 expert ratings (75 + 75 + 45) and 345 across all five rater columns (V in `veribench` experiment 100 inputs; the repo's own earlier inventory says the same). The new 125-file, 8-rater human round has only blank packets so far; I did not find returned sheets.
2. **Larger with AI-rater labels, saved per item:** yes. `veribench` experiment 106: 725 items (75 human-rated + 650 fresh), 666 not blank (V, `results/targets.csv`). 14 agent groups G00 to G13 (G00 is the 75), 50 fresh tasks (V: zero overlap with the 25 human tasks). Labels: a panel of simulated expert raters.
3. **Larger with Lean prover labels:** yes, binary pass/fail, no human ratings: Tiny-256 (1,024 runs), the VBV1-896 and Core-614 sets, the private set (214 tasks).
4. **Larger with LLM-judge scores:** yes, same family of data: 3,584 to 10,438 rows per set, all judge-scored, none human-rated.
5. **Not reachable and not searched:** Brando's Mac, the Vals repo and Vals billing or run store, Sherlock files that need Duo, Delta (login unverified), Google Drive and Docs.

## Experiment 106 in detail (the run Brando remembers)

Path: `veribench/experiments/106_simulated_expert_raters_icl_from_human_labels_leave_one_agent_out_fsc_judge/` (private repo). Report: `KFOLD_SIMULATED_RATERS_RESULTS_10-15-2026.md`. Harness: Vals Valkyrie custom agents (`vb106_rater_v2` for raters, `vb103_judge` for judges), no direct keys.

| Item | Value |
|---|---|
| Rater families | Gemini 4 Argon, GPT-6 Astra, Claude Fable 5.1, Grok 4.7, MiMo-V2.6-Pro, Kimi K3, Qwen3.8 Max; each plays the three expert personas and an instructions-only world (R) |
| Judges | `gpt-6-sol-high` and `claude-opus-5-5-no-fallback` at max effort; arms F (frozen H2 judge), Z (bare instructions, H0), L (recipe rebuilt per fold) (R, run names V) |
| Artifacts | 725 in `targets.csv`: G00 = 75 (the human-rated ones), G01 to G13 = 50 each = 650 fresh (V); 666 non-blank, 59 blank (V) |
| Tasks | 75 in total: the 25 human tasks and 50 fresh; the fresh 50 share no task with the 25 (V) |
| Solver groups | 14 agent groups, plus late groups G16 and G17 (R) |
| Raw rater cells in this checkout | 28,613 `vb106_rater_v2` rows of which 23,730 carry `score_0_5` (V); the Argon cells are not in this checkout, only a summary (V) |
| Raw judge cells | 15,992 `vb103_judge` rows; F and Z arms have 1,998 cells each = 666 artifacts x 3 repeats (V) |
| Declared cells | 47,908 main + 6,320 late cells (R); it was the most expensive judge-collection run on the Vals side (amounts are in the report and not repeated here) |
| Per-item targets saved | `expt_v5/results/targets.csv`: panel agreement targets per item (V); per-cell scores in `expt_v5/runs/*/cells.jsonl` (V) |
| Candidate Lean files saved | 641 (S) |
| Overlap with the 75 | G00 is exactly the 75; G01 to G13 are disjoint in tasks and artifacts (V) |

What the labels are worth, in the report's own numbers (R): the seven-family panel agrees with the real experts at Spearman 0.770 [0.527, 0.898] on the 75, and the frozen judge agrees with those experts at 0.772, a dead heat. A judge built against the stand-ins scores about 0.91 against them and 0.621 [0.278, 0.832] against the real experts; the frozen judge scores 0.772 [0.570, 0.901]. Rebuilding the judge k-fold style was worse than bare instructions (delta Spearman -0.040, interval below zero). These are single-metric Spearman results; they used no RPS.

Experiment 104 (the 5-fold on the 75 only): two judge models, 440 cells per model per repetition in the spend lines (V from the README and sub-inventory; the README text says about 375 calls). It stays on the same 75 artifacts. Its raw per-call outputs are not in the current `veribench` checkout (only `per_item_oof.csv`, 75 rows, and `CV_RESULTS.json`); the repo's earlier inventory says receipts exist at commit `f1bfbe3`, which I did not open.

## Every dataset found, by label type

All counts are over artifacts or runs, not tasks, unless stated. "Overlap" is against the 75 artifacts / 25 tasks. Name-based overlap figures are a heuristic and were not checked item by item.

### A. Human ratings

| Dataset | Where | Artifacts | Labels | Saved per item? | Overlap |
|---|---|---|---|---|---|
| Expert pool (25 tasks x 3 samples) | `veribench` experiment 100 `inputs/items.jsonl`, `veribench_dataset/human_labels/` (private) | 75 | 195 expert ratings (3 columns), 345 over 5 columns; raw TSVs give 193 non-empty expert ratings, 2 fewer than `items.jsonl`, not investigated (S) | yes, private | is the 75 |
| Same pool, other labels | `no-gold-ref-judge`: 78 single-rater labels (S) | 75-ish | same artifacts | not checked | same 75 |
| Set N (125 files, 8 raters) | blank packets in the machine's mail only | 125 | none returned yet | no | n/a |

### B. AI-rater labels (simulated experts)

| Dataset | Where | Artifacts | Raters | Saved per item? | Overlap |
|---|---|---|---|---|---|
| Experiment 106 | `veribench` experiments 106 (above) | 650 fresh + the 75 | 7 families x personas | yes: `targets.csv` + `cells.jsonl` | G01 to G13 disjoint |
| Experiment 47 | `cert-judge` experiments 47 | 750 candidates (691 non-blank), 50 fresh tasks, 15 solver systems | simulated 7-family panel | aggregates only; per-rater scores and Lean files not in that repo (S) | probably the same population as 106 (not checked) |
| Set-N panel (condition v6) | `veribench` experiment 106 v6 | the 125 set-N candidates | GLM 5.3 and DeepSeek V4 Pro runs by name (not read in detail) | not checked | not the 75 |

### C. LLM-judge scores on the 75 (more judges, not more artifacts)

| Dataset | Where | Judge configs | Rows | Saved per item? |
|---|---|---|---|---|
| Experiment 39 | `cert-judge` | 56 | 12,600 criterion cells (12,362 measured) over 75 x 3 repeats (S) | yes, harnesses `vb103_judge` and `terminus2` |
| Experiment 60 (open weights) | `cert-judge` | 62 units | 13,950 cells (S) | yes |
| Experiments 58, 59 | `cert-judge` | 117 / 65 units | aggregates only (S) | no |
| Experiment 100 | `veribench` | 10 configs; 5 complete scalar caches | 3,342 receipt files; 1,125 repeated draws documented (R) | receipts yes, histograms in `paper_support/public_judge_retrospective_11-10-2026` |
| Experiment 104 | `veribench` | 2 models, 5-fold | per-item out-of-fold means only (V) | partial |
| 4 LLM judges | `no-gold-ref-judge` | Claude Code Opus 4.6, Codex CLI, Opus 4.6 API, an OpenAI API judge (labelled GPT-5.4 in files, GPT-4.1 in the summary; unresolved) | 288 scores on 72 of the 75 (S) | yes |
| Experiment 42 | `cert-judge` | 56 configs on 194 probes | 32,592 cells; labels are expected directions by construction, not ratings (S) | yes |

### D. Lean prover or test labels (binary), no human ratings

| Dataset | Where | Size | Label | Harness / models | Overlap |
|---|---|---|---|---|---|
| Tiny-256 | `veribench` experiments 138, 142, 158; `brandos-stanford-thesis` experiment 27 `per_run_dt.csv` | 1,024 runs = 256 tasks x 4 solvers; 801 counted passes in the machine's notes | compile, Lean entailment, differential-testing agreement | Claude Code Opus 5, Codex CLI GPT-5.6 Sol, Fable 5.1 Terminus 2, GPT-6 Astra Terminus 2 (S) | about 5 to 7 of the 25 tasks by name |
| Core-614 | `veribench` | 1,352 artifacts (S); 17 systems x 614 = 10,438 judge rows (S) | Lean-checked, judge coverage | various | not checked |
| VBV1-896 | `veribench` experiments 102, 137 | 896 tasks x 4 systems = 3,584 rows (S); experiment 103 single-call baselines 6,316 rows (S) | judge FSC coverage scores | Vals harnesses | 22 of the 25 task names appear in the 896 (heuristic) |
| Experiment 109 | `veribench` | 9 models x 896 tasks | aggregates only, per-cell scores not saved (S) | | |
| Private set | `vb-priv-bmg` experiments 34, 35 | 214 official tasks, one Claude Code Opus 5.5 artifact each (212 saved); 50 strict entailment passes, 164 fails; 3,421 theorem-level proved/not-proved labels (S) | Lean-checked | Claude Code, Opus 5.5 | disjoint, private |
| Private judge scores | `vb-priv-bmg` | Fable 5.1 (3 raters per cell) 169 cells = 507 ratings; H2 judge about 132 more; about 301 cells over 239 task IDs (S) | FSC rubric, not the paper's rubric | | disjoint |
| RL rollouts | `rl-4-code-verification` experiments 01, 05, 08, 25 | exp 05: 21,504 kernel-scored cells (896 tasks x 8 samples x 3 base models); exp 08: 10,656 test cells with 4,302 judge ratings; exp 01: 9 models x 896 outputs; exp 25 smoke: 1,024 rollouts (50 with strict reward above 0); exp 25 full: about 24,576 rollouts as per-update aggregates only (S) | binary Lean strict reward, smooth proxy (geometric mean of 3 per-declaration factors) | | V1 domains, overlap not checked |
| Verina + VeriBench candidates | `pass-tests-fail-proofs-` | 684 Lean candidate rows (Claude Opus 4.6 and GPT-5.1 on 189 Verina + 153 VeriBench tasks) | test and proof outcomes | | about 19 of the 25 tasks by name (heuristic); leakage risk |
| Toy controls | `trustworthy-theorem-judges` experiment 08 | 48 constructed Lean controls (18 positive, 18 negative, 12 ineligible) | prover | | toy only |

### E. Other domains (transfer only, not formal-verification judging)

`judge-free-eval` (44,217 score rows, 16,712 with a frontier-judge score; about 242 hand labels on traces) and `judge-reference-anchoring` (177,752 open-judge rows; about 2.3M automatic candidate labels) are math and QA data. `tvdmi-judge-asymptotics` is entirely synthetic. `judges-dont-need-psychometrics-or-corr` is synthetic plus copies of aggregates. `mirage-effect-llms`, `rl-env-scaling`, `alignment-scaling-laws`, `self-opt-data-gen`, `agentic-nl-fl-maths`, `veri-veri-bench`, `veri-safe-cyber-bench`, `harbor-datasets`: I did not find judge-training data for formal-verification artifacts in them (`harbor-datasets` holds task bundles only).

### F. Blocked or empty

Experiment 169 (Daytona sandbox): no per-item verdicts, hosted credits ran out (14 of 100 pairs checkable per the machine's notes). Experiment 117 stopped at its gate. Experiment 41 rating sheets are blank templates. `veribench-inf` experiment 10 tables are empty; experiment 12 is a mechanical replay with no judge or human labels. The VCVio pilot (11 of 120 Gemini passes, 51 of 55 for ub9sc on 19 of 40 tasks) is too small.

## Is there a bigger training set with usable labels?

- **With human labels: no** (from what I searched). 75 artifacts, 25 tasks, one solver (`claude-3-7-sonnet-20250219`).
- **With AI-rater labels: yes, 650 fresh artifacts on 50 tasks (experiment 106), per-item labels saved**, plus 59 blank. The artifacts come from 13 different agent groups, which is more diversity than the 75 have.
- **With prover labels: yes, thousands**, but the label is binary pass/fail on a different question (does the Lean spec entail the gold spec), not the 0 to 5 coverage rating.

## Plan: train on the big set, test on all 75

Goal: compare formulation 2 (select the judge by correlation with the labels) against formulation 4 (fit or select by a proper loss: RPS primary, CE and TVD secondary) when the training data is experiment 106 and the held-out test is the 75 human-rated artifacts.

1. **Training data.** The 650 fresh artifacts of G01 to G13 (minus blanks, 591 non-blank per the earlier sub-inventory). Label per artifact: the empirical distribution over ratings 0 to 5 from the AI raters' saved `score_0_5` cells (six families in the checkout; the Argon cells are missing, so I did not count on seven). Report also the mean target from `targets.csv`.
2. **Test data.** All 75 artifacts of G00 with the individual human ratings (195 expert ratings), never used for selection, fitting or early stopping. 25 tasks, grouped intervals.
3. **Candidate judges, no new inference (first version).** The four judge configs that exist both on the 666 and on the 75: H0 Sol, H0 Opus, H2 Sol, H2 Opus (three repeats each, V from run names and cell counts). Fit mixture weights and a probability head on the 591 and evaluate on the 75. Free, hours of CPU.
4. **Candidate judges, with new inference (second version).** An agent searches prompts and models on the 650, with correlation as its goal in one arm and CE or RPS in the other. This needs judge calls on 650 artifacts; allowed only on free hardware (open-weight models on Sherlock or Delta) per Brando's standing rule, not Vals credits or a paid API. Prior open-weight results on the 75 are weak (Qwen3.6-27B Spearman 0.18 to 0.21 per the private repo's aggregates), so expect a weak ceiling.
5. **Controls.** (a) Train on the 75 only with the experiment 12 protocol, as the baseline. (b) Train on the big set and test on the AI-panel targets for G00 and for held-out groups, to separate label shift from judge quality. (c) A calibration variant that uses a small human subset to fix the level is excluded from the headline because the test must stay held out; it can run on a split of the 75 as a separate named condition.
6. **Metrics.** RPS first, then CE, TVD and Spearman, intervals by task-grouped resampling. Name harness and model for every judge config.
7. **Known risk, stated plainly.** The training labels are AI-rater scores; the report shows they agree with experts no better than the judge does (0.770 vs 0.772) and that a judge fitted to them inflates (0.91 vs 0.621). So the likely result is that the big set helps correlation against the AI panel and does not help against humans. My guess, about 70%: the loss-trained judge on the big set beats the correlation-trained one on RPS against humans, but both fall short of the frozen H2 judge's agreement with humans. That is a guess from the report's numbers, not a result.
8. **Honest scope.** A different, much cheaper way to get more human-labelled data is the human round (125 files, 8 raters); it has not been collected.

## What was searched and what was not

Searched: 20 `brando90` repos shallow-cloned at depth 1 (`veribench`, `veribench-inf`, `veri-veri-bench`, `vb-priv-bmg`, `cert-judge`, `trustworthy-theorem-judges`, `judges-dont-need-psychometrics-or-corr`, `judge-free-eval`, `judge-reference-anchoring`, `no-gold-ref-judge`, `tvdmi-judge-asymptotics`, `rl-4-code-verification`, `rl-env-scaling`, `brandos-stanford-thesis`, `alignment-scaling-laws`, `pass-tests-fail-proofs-`, `agentic-nl-fl-maths`, `self-opt-data-gen`, `mirage-effect-llms`, `veri-safe-cyber-bench`); file trees of `the-difficulty-confound`, `harbor-datasets`, `unified-training`, `spec`, `brandomiranda` through the GitHub API; the machine's scratch (name-based, not an exhaustive content search of all folders), notes, mail, downloads and day logs; checkouts of `veribench` at the Nov 3 commit for the scratch copy and the current `main` for the fresh clones.

Not searched or not reachable: Brando's Mac, the Vals repo, Vals billing and the Valkyrie run store, Sherlock and Delta files, Google Drive and Docs, `brandos-stanford-thesis` experiments 00 to 26 beyond file-type scans, several `rl-4-code-verification` experiments (08 v13 to v28, 10, 11, 15 to 18, 21, 22), the raw receipts of experiments 104 and 83 (pruned in the clone), and experiment 106's Argon `cells.jsonl`.

Not verified: the cost figures (quoted from reports); the task-overlap counts against the 25 (names only); the judge model behind the fourth `no-gold-ref-judge` arm; the 2-rating gap in the raw human TSVs; whether experiment 47's candidates are the same population as experiment 106's.
