<!-- TLDR: Light QA of experiments/03_prover_target_fsc_judge/ at commit 6b288c7: data join, scoring, split, bootstrap and every source-audit number reproduce exactly; no critical defect; two major fixes (a world-editable Google Doc link published in a public repo, and an under-reported integrity caveat on the exact target label) plus nine minor items. -->
# Review verdict: experiments/03_prover_target_fsc_judge/ (light QA, one round)

Reviewed: commit `6b288c71e09a2233e6465b6910ccfc7547e6ad8d` against base `03e4416`, scope `experiments/03_prover_target_fsc_judge/` only. Date: 11-06-2026. Reviewer: Claude Fable 5.1, effort max, on the claude.ai Max subscription; evidence in `private/prover_target/review/launch.json` (`"model": "claude-fable-5-1", "effort": "max", "permission_mode": "bypassPermissions"`), `active_cli_evidence.json` (pid 17912, `--model claude-fable-5-1 --effort max --dangerously-skip-permissions`) and the session id `d5ba886e-4fc6-445b-9aac-0d1c6cdc659f` in `stream.jsonl`. No measured judge or prover call was made; zero model-inference spend by this review. No reviewed file was modified (`git status --short` empty; all review artifacts live under ignored `private/prover_target/review/`).

Terms: FS = formal specification (an unproved theorem statement). FSC = formal specification coverage, the VeriBench judge score saved as `tc`. Brier loss = mean squared error of a probability forecast against a 0/1 outcome. LOAO = leave-one-agent-out.

## 1. What was verified (all passed unless noted)

| Check | Evidence | Result |
|---|---|---|
| Source pinning | 17 of 17 blobs under `private/prover_target/source/` match `sources/provenance.json` (sha256 and byte count) and `git show be287d9…:<path>` in the private `brando90/veribench` repository | PASS |
| Join and counts | `per_run.csv`: 1,024 rows, 256 tasks x 4 solvers, 0 missing joins; `lean_entails_raw` 840, `lean_entails` 801, `counted_all5` 789; 39 rows carry `drop_reason = "axiom/native_decide-dependent agent theorem"`; 12 rows have `all_gold_names_proved = 0`; per solver 212/212/209, 213/184/181, 199/189/186, 216/216/213 | PASS, matches RESULTS.md and the 145 README tables |
| One label, one feature | Code uses `counted_all5` as the only outcome and `tc` only as a scalar feature; `tc` has 10 distinct levels 0.1–1.0, 819 of 1,024 artifacts at 1.0 | PASS |
| `tc` origin | Source 140 README line 43: "`manifest_tiny256.json`: run, task, solver agent, FSC (`tc`)"; line 3 "judging theorem coverage (FSC)". It is a judge score, not a human rating | PASS (see minor 7 on wording) |
| Split | 64/64/128 tasks, pairwise disjoint, 4 artifacts per task kept together; `split_manifest.json` sha256 `e3a7ca9d…` equals the hash in provenance; manifest itself not committed | PASS |
| Protocol freeze | `git diff 24c9152 6b288c7 -- PROTOCOL.md config.json` is empty | PASS |
| Brier identity | E[(q−Y)²] = (q−p)² + p(1−p) is correct; `verify.py` checks it on a grid; oracle 0, constant 0.25, complement 1 | PASS |
| Metric code | AUROC = Mann–Whitney with average ranks (ties count 0.5); Spearman = Pearson of average ranks; Kendall tau-b via scipy; bias = mean(forecast − outcome); task-clustered paired bootstrap, 10,000 draws, seed 11062026, fitted map held fixed (disclosed) | PASS (see minor 3) |
| Selection boundary | Ridge chosen on validation Brier only; test evaluated once; LOAO excludes the solver from train and validation and scores only its 128 test artifacts | PASS (see minor 4) |
| Reproduction | `uv run --python 3.12 --with numpy==2.4.2 --with scipy==1.17.0 python scripts/analyze.py --source-repo ~/veribench` in an isolated copy: `results/retrospective.json` and `sources/provenance.json` byte-identical to the commit; 20 s wall | PASS |
| Renderer | `render_report.py` from the committed JSON reproduces `RESULTS.md` byte-identical | PASS |
| RUNBOOK checks | `verify.py` prints `PASS: proper-loss identities, parsing, selection and task-disjoint denominators`; `git diff --check 03e4416 6b288c7` clean | PASS |
| Source audit, 117 | `PROTOCOL_phaseA_t2.md` pins Goedel-Prover-V2-8B `dfd02e6…`, DeepSeek-Prover-V2-7B `a8d9e14…`, n=32, seed 1, T=1.0, top-p 0.95, 16,384 new tokens, context 32,768, vLLM 0.21.0, ≤6 GPU-hours; `g2v2_t2check_goals.csv`: 30 agent-dependent statable goals, 3 proved + 7 refuted = 10, gate 0.333 < 0.50; harness has `decideGoal`, `kernelAccept`, `axiomsOk`, countermodel search | PASS |
| Source audit, 140/142 | 140 PROTOCOL asks for entailment of all public gold theorems from an arbitrary f_A through a natural adapter, proof status excluded; 142: ub9sc helper agents, one prover per two runs, at most two fix rounds | PASS |
| Source audit, 145 Lean | `AxLib.lean` runs `collectAxioms` over every `Agent.*` theorem (proof-dependent); `WitLib.lean` discharges hypotheses with agent definitions and `stdOnly` agent theorems; `GoldChkLib.lean` lines 49–63 check only existence, `thmInfo` and axioms of `Bridge.G_*`, never the statement type | PASS: proof dependence and the missing type comparison are real |
| Source audit, 168 | `attacks/summary.json`: repaired fixed-goal checker 8/72 (C08 4 + P01 4, all forged-audit), patched 0/72, positives 28/28; `attacks_check_candidate_patched.py` line 23 draws the nonce after the candidate is fixed; `prover_pi_runner.py` provider `koyejolab-openai-bm`; README "no other experiment" | PASS (see major 2) |
| Claims hygiene | No fresh-validation or semantic-oracle claim in README, PROTOCOL, RESULTS, RUNBOOK, CKPT; `fresh_validation: false`; "oracle q=Y" is an outcome control; "no human count" claim is valid for the operational target and hedged against replacing the human study | PASS |
| Privacy | Committed files contain no per-artifact rows, task identities, human ratings or secrets (regex scan of the diff); only aggregates, hashes and solver-configuration labels | PASS (see major 1) |
| Spelling and dates | Dictionary scan of all seven documents: no misspellings; dates `MM-DD-YYYY`; "11:32 PST" correct for 11-06 | PASS |

Extra checks run by the reviewer (not in the commit): a per-solver training-prevalence constant scores test Brier 0.1653 versus the pooled constant 0.1654, and a two-feature logistic map (tc plus solver one-hot) scores 0.1079 versus the mapped 0.1072, so solver identity does not explain the gain; 104 of 128 test tasks have the same outcome for all four solvers, consistent with the 145 README's task ICC(1) of 0.605, which the task-clustered bootstrap handles.

## 2. Critical issues (0)

None. No unsupported conclusion and no incorrect data or scoring was found.

## 3. Major issues (2)

**M1. A world-editable Google Doc link is published in a public repository.** `SOURCE_AUDIT.md` line 39 and `sources/human_plan_provenance.json` line 2 publish `https://docs.google.com/document/d/1335CIhz8Y2AKexBg1NdsRWteIrr5J-pXz6uKLKBgPiQ/…` as "the authoritative human-study Google Doc". The Drive permissions on 11-06-2026 are `{"role": "writer", "type": "anyone"}` plus four named writers/owner. The link is absent from base `03e4416`, so this commit creates the exposure. Anyone reading the public repository can edit the document the audit calls authoritative; the recorded `returned_text_sha256` detects but does not prevent tampering. The private snapshot (`private/prover_target/human_plan_drive.json`, 22,786 characters) contains no email addresses, so this is an integrity and access-control problem rather than a rater-identity leak. Fix (builder): drop the URL from both public files and keep it in `private/prover_target/human_plan_drive.json` (already there), or keep the URL only after the sharing is changed to Viewer or restricted (Brando's decision; Rule 68 allows Editor only when readers fill a file in). Keep the hash and `modified_time` in the public provenance.

**M2. The audit quotes the wrong integrity statistic for the exact target label.** `SOURCE_AUDIT.md` lines 111 and RESULTS.md's "Source experiment 168 found adversarial failures in related checkers" cite 8 of 72 forged-audit acceptances for veribench-inf experiment 12's fixed-goal checker, which is not the pipeline that produced `counted_all5`. The source documents stronger, directly relevant facts that the audit omits:
- 168 `attacks/summary.json`, `names_axioms_accepts`: the names-and-axioms gate (the closest analogue to conditions 2 and 5 of the label) accepted 155 of 212 constructed invalid bridge submissions (0.731, Wilson 95% [0.668, 0.786]); by class, gold-proof reuse 10/11, "adapter hypothesis assumes the gold statement" 11/11, tautology restatement 11/11, shadowed gold names 11/11, goal restated as a disjunction with True 7/7.
- 145 README, Cons: "Conditions 1 to 5 do not block a bridge that reuses the gold's own proof (veribench-inf experiment 12: the raw rule accepts 6 of 7 invalid controls, the name and axiom gates alone 3 of 7)".
- 145 README: "Ungrounded passes … 51 of 789 counted runs have at least one gold theorem proved without any agent hypothesis (2 have all)" (candidate condition 6, not applied), and "732 of 789 are trivial or identical" (a reading).
- 168 README log 11-04-2026 16:20: the parsed-audit weakness "exists in any pipeline that parses printed audit lines, including experiment 145's"; a text scan of 1,023 experiment-142 bridge files found no audit-line strings or printing commands, but "the solver agents' own files … were not scanned".
The conclusions in RESULTS.md stay hedged ("bridge faithfulness remains unverified"), so no number is wrong, but a reader of the public audit gets a rosier picture of the label than the source gives. Fix: add these four facts with their denominators to `SOURCE_AUDIT.md` (experiments 145 and 168 sections) and one sentence to RESULTS.md "Uncertainty and limits".

## 4. Minor issues (9)

1. **Constant-forecast Pearson is inconsistent in the JSON.** `corr()` returns `nan` for the pooled constant (205/256) but `0.0` with `valid_resamples: 10000` for `exclude_codex` (157/192) and `exclude_fable51` (149/192), because `np.full(n, 157/192)` does not center to exactly zero. RESULTS.md renders only the pooled table ("unavailable"), so the public table is right; the per-condition JSON would render "0.000 [0.000, 0.000]". Fix: in `corr`, return NaN when `np.ptp(x, axis=-1) == 0` (or when `den` is below a relative tolerance).
2. **Ridge selection is degenerate.** The penalty `ridge * beta[1]**2 / 2` is added to the *mean* log loss, so ridge 0.01 already shrinks the pooled slope from 9.46 to 1.98 and loses 0.036–0.054 validation Brier in every condition; ridge 0.0 wins 5 of 5 times. The text "select the nonnegative ridge coefficient … by validation Brier loss" is literally true, but validation did no effective work. Disclose this in RESULTS.md; rescale the grid (for example 1e-4 to 1e-2) only in a future, separately versioned condition.
3. **Calibration by score level is not reported, and it is uneven.** Pooled map versus test acceptance: tc=1.0 predicts 0.887, observed 379/417 (0.909); tc=0.9 predicts 0.753, observed 11/28 (0.393); tc=0.8 predicts 0.542, observed 7/15 (0.467); tc=0.7 predicts 0.315, observed 7/25 (0.280); tc≤0.5 predicts 0.002–0.065, observed 0/17. The overall bias +0.007 [−0.036, 0.054] is carried by the 81% of test artifacts at tc=1.0. Add a band table (the judge recipe's "check level, not only order").
4. **Mean absolute error is listed with a ↓ arrow as if it ranked forecasts.** MAE is not a proper score for probabilities: the raw scalar wins MAE (0.171 vs 0.220) while losing Brier (0.141 vs 0.107). State that MAE is descriptive only, or drop the arrow.
5. **Task-family overlap can be quantified from the private manifest.** By a name heuristic (same security vulnerability number and stem across `security_6858__safe__N_*_safe` and `security_6858__vulnerabilities__N_*`; `heapsort*`; `humaneval_32_*`), 28 families straddle splits and 26 of 128 test tasks have a train or validation sibling, for example `security_6858__safe__108_unsafeanyrootcascope_safe` (train) versus `security_6858__vulnerabilities__108_unsafeanyrootcascope` (test), and `cs_set__heapsort_problems` (validation) versus four `cs_set__heapsort*` tasks (test). PROTOCOL.md already says family separation is unverified; replace "unverified" with this count and the heuristic.
6. **Historical-exposure disclosure is less specific than the source.** Source 140 README already tabulates "FSC = 1" against the entailment readings per group (the feature against a precursor of the label), and 142/145 tabulate outcomes by reader verdict. PROTOCOL.md says only "aggregate counts were already inspected". Also, source 142 does not record whether bridge authors saw `tc`; the 140 reading protocol withheld scores from readers, but the 142 bridge protocol is silent. Say both.
7. **Terminology (Rule 85).** README, PROTOCOL and RESULTS call `tc` "scalar coverage ratings" / "historical coverage ratings"; in this repository "ratings" means human ratings. Use one term throughout, such as "judge-produced FSC score", and define "artifact" once as one solver run on one task (the source's `run`/`cell`).
8. **Funding-gate evidence has no path.** PROTOCOL.md line 73 and SOURCE_AUDIT.md line 115 say the current `PAUSE` and `ALLOW` files were read and that "live local Valkyrie pause files" allow only named experiments, without a path or hash. I found no `PAUSE`/`ALLOW` files under `~/vals-valkyrie`, `~/veribench` (the pinned revision contains neither word), `~/veribench-inf`, `~/vb-priv`, `~/vb_worktrees`, `~/agent-dispatches` or `~/agents-config` (depth ≤ 6). Name the exact paths and their sha256 (Hard Rule 11 research precision), or mark the claim as resting on the parent's records.
9. **Wording.** RESULTS.md line 128: "improves Brier loss … by -0.058" reads as a negative improvement; write "lowers Brier loss by 0.058 (difference −0.058 [−0.087, −0.031])". SOURCE_AUDIT.md line 111 "do not prove that all historical natural bridges were attacked" should quote the source's actual exposure check (see M2, last bullet).

Structural notes (no change requested): folder is self-contained with README, PROTOCOL, RESULTS, RUNBOOK, SOURCE_AUDIT, checkpoint, config, prompt template, results JSON, scripts and provenance; every document opens with a TLDR comment; private inputs stay under the ignored `private/` tree with public hashes; private `brando90/veribench` folder names and blob hashes are exposed as metadata by design and are documented as such.

## 5. Tests run (reviewer, 11-06-2026, this Mac)

```
uv run --python 3.12 --with numpy==2.4.2 --with scipy==1.17.0 python experiments/03_prover_target_fsc_judge/scripts/verify.py
  -> PASS: proper-loss identities, parsing, selection and task-disjoint denominators
uv run ... python experiments/03_prover_target_fsc_judge/scripts/analyze.py --source-repo ~/veribench   (isolated copy under private/prover_target/review/repro_analyze/)
  -> {"rows": 1024, ..., "primary_difference": {"value": -0.058226422165788806, "ci95": [-0.08741558671751744, -0.03103262789462241], "valid_resamples": 10000}}
  -> diff results/retrospective.json: identical; diff sources/provenance.json: identical; split_manifest sha256 e3a7ca9d0228b27a3bd1ad4bcde467f3a905a87b28e29ed98fd1e44dc0b5736c
python3 scripts/render_report.py (copy)  -> RESULTS.md identical to the commit
git diff --check 03e4416 6b288c7         -> clean
git diff 24c9152 6b288c7 -- PROTOCOL.md config.json -> empty
sha256 of 17 source blobs vs provenance and vs git show at be287d9 -> 17/17 match
Google Drive get_file_permissions(1335CIhz…) -> anyone: writer (see M1)
```

VERDICT: PASS
CRITICAL_ISSUES: 0
MAJOR_ISSUES: 2
STRUCTURAL: PASS
SUMMARY: The zero-call retrospective result (pooled paired Brier difference −0.058 [−0.087, −0.031], 512 test artifacts from 128 tasks) reproduces byte-for-byte from the pinned private sources, and every source-audit number checks against the raw evidence. Before publication the builder should remove or re-permission the world-editable Google Doc link and add the source's own integrity statistics for the exact target label; the nine minor items are disclosure and robustness improvements.
