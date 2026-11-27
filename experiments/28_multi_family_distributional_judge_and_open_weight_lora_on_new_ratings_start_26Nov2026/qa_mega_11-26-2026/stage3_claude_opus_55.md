TASK [ttj: Exp 28 Stage 3 Mega QA]: read-only adjudication of the Stage 1 and Stage 2 findings, plus a final sweep for anything they missed. No repository files were changed. My recomputations ran from `/tmp/s3audit/` with `PYTHONDONTWRITEBYTECODE=1`, so no bytecode was written into the repo. I did not write the agent-sync `log.md` line because you asked for read-only. `qa_mega_11-26-2026/stage3_claude_opus_55.md` is still empty; whoever orchestrates should save this output there.

**Status:** Exp 28's main positive result holds after cleaning: the strict nested global judge (H3-free) gets RPS 0.0704 against 0.1186 for the set-aware constant, a paired gap of −0.0483 [−0.0724, −0.0258]. Three claims do not hold. "Strongly confirmed CE ≫ Pearson" for the head falls apart once hyperparameter selection is matched. The 50-task "Works" verdict against Exp 27 F8 relies only on rows with leakage. And C7 never beats Exp 27's own set-aware model.

## Verdict: **FAIL** (as committed at `df7f6af`); **CONDITIONAL PASS** once the amended checklist below is done

The failure rests on Stage 1 #1 (unresolved CRITICAL), plus four MAJOR issues: #3, #4/A2, Stage 2's own expected outcome for its fix, and the governance finding N1.

## Adjudication of Stage 1 findings

| # | Ruling | Stage 3 evidence and notes |
|---|---|---|
| 1 | **CONFIRMED, CRITICAL** for the rows that carry the "strict nested" label | `build_h3_requests.py:49-90`: demonstrations and the base rate come from Exp 27 train tasks, which fall into Exp 28's cv5 test folds. Folds 1 and 4 select `C12`. I recomputed the run without C12: selections are C7, C9b, C7, C10, C7, giving **RPS 0.0719, CE 0.9292, TVD 0.3446**. Against the constant: −0.0467 [−0.0707, −0.0248]. Against F8: −0.0028 [−0.0082, +0.0031], p=0.318. This matches Stage 2. Both stages under-weighted one point: **every cv5 "vs F8" comparison uses a contaminated F8**, because F8 consumes H3. |
| 2 | **CONFIRMED, MAJOR** | Cannot be fixed on CPU, because the inner-OOF LoRA predictions were never saved. Quarantine the `pearson_postcal` and `ce_vs_pearson_postcal` rows for LoRA. |
| 3 | **CONFIRMED, MAJOR** | Overlap with the 105 selection items is 18/25/24/18/20 per fold. This also covers `head_ce`, `head_rps` and `head_pearson`, which reuse the C7 winner's hyperparameters, and the headline "0.0689 … 5-fold nested OOF" in `.tex:5`. |
| 4 | **CONFIRMED, MAJOR, and understated by both stages** | See N2. Under matched selection the head result reverses on the primary metric. |
| 5 | **CONFIRMED, MAJOR** | Add the LoRA epoch-count deviation (A5.1). |
| 6 | **CONFIRMED, MAJOR**, with Stage 2's nuance | I recomputed Qwen's shuffled-control mean as 0.6064, so it passes. The label-in-prompt gate fails for 3/5 models (Argon 0.622, Grok 0.096, Qwen 0.940). PREREG §2 says this gate runs "before scaling", yet Argon was scaled anyway and is part of both frozen judges. |
| 7 | **CONFIRMED, MAJOR** | The `df7f6af` diff shows F8 moving from `alpha=1,m=0.10` to `alpha=0,m=0`. Line 19 pairs CE 0.914 (nested global) with RPS 0.0689 (C7 fixed). |
| 8 | **CONFIRMED as fact; downgraded to MINOR** | The claim is false, but AGENTS.md explicitly allows participant names and IDs in this repo. The `.tex` has none, and the rows are aggregate counts, not one row per rater. **I reject Stage 2's fix of editing the frozen data CSV**: that rewrites a hashed, frozen receipt. Correct the claim instead. |
| 9 | **CONFIRMED, MINOR** | The F8 change was a correctness fix toward Exp 27's `FREEZE_11-24-2026.md:10` (alpha 0, mix 0). It made the comparator stronger, so it is not p-hacking, but it is an undisclosed post-test rerun. The Pearson-initialization change after the freeze only affects the head Pearson rows. |
| 10 | **CONFIRMED, MINOR** | 7 cv5 rows have p = 0.0. |
| 11 | **CONFIRMED, MINOR** | `run_qwen_gpu_mercury2.py:561-567` emits only `step0_full_vs_leftpad_max_diff`. Three keys in `qwen_sanity.json` have no committed code that produces them. |
| 12 | **CONFIRMED, MINOR** | `mega_results.tex` (+6 lines) and `mega_meta.tex` are dirty. The committed PDF cannot be rebuilt from the committed sources. |

## Adjudication of Stage 2 findings

| ID | Ruling | Stage 3 evidence and notes |
|---|---|---|
| **A1** | **CONFIRMED numerically, CORRECTED on configuration; MAJOR only as a consequence of #5** | F9 at `alpha=0,m=0` gives **0.0659**, CE 0.8736, TVD 0.3302. C7 − F9 = +0.0069 [−0.0021, +0.0170], p=0.134, which reproduces Stage 2. But Exp 27's own search selected **F9 at `alpha=0, mix=0.25`** (val 0.0519). That configuration gives **0.0706**, and C7 − F9 = +0.0022 [−0.0090, +0.0137], p=0.70. Either way C7 does not beat Exp 27's set-aware model. The registered comparison, global vs global, is a tie: **G9 − F8 = −0.0008 [−0.0086, +0.0064], p=0.85**. From JSON, clean nested global vs F8 is −0.0044 [−0.0098, +0.0012], with F8 itself contaminated by H3. |
| **A2** | **CONFIRMED mechanism; Stage 2's conclusion is WRONG** | At α=0.3 I reproduce the collapse exactly: RPS 0.2325, mean E 2.382, fold-1 sd(E) 0.0017. At α=1e-4: 0.0806, which matches Stage 2. This is not a code bug. Pearson is invariant to location and scale, so an L2 penalty that was never searched sets the scale. See N2 for the matched result. A z-scored 1D post-calibration does **not** fix it: my implementation gave RPS 0.0944, worse than the matched raw head at 0.0734. |
| **A3** | **CONFIRMED; downgraded to MINOR (disclosure)** | max \|std4−std3\| = 1.2118. The fitted `w(judge_std4)` is −0.0000, and swapping in std3 gives 0.0726 vs 0.0728. There is no material numerical effect. The governance side is raised as N1. |
| **A4** | **CONFIRMED fact; downgraded to MINOR (wording)** | 70/70 test predictions were present in `b7a1b10`, and that file is unchanged up to HEAD. Neither `run_train_lora_4b` nor `export_track4_results.py` scores test labels; the export only asserts counts. All H4 and Qwen test-item inference also necessarily ran before the freeze. Fix the wording to "before any test-label scoring". |
| **A5** | **CONFIRMED; downgraded to MINOR**, folded into #5 | 24×32 = 768 sample draws: 10.97 epochs at n=70 and 7.31 at n=105. The final cv5 refits at n=140 run 5.49 epochs. The SDPA backend mismatch is real but low-risk: `CHUNK_SIZE=1` means no padding mask, and differences are at bf16 kernel level. New detail: **CE LoRA picked steps=24, the largest value in the grid, on all 6 splits**. That is a boundary choice, so CE may be under-trained; this does not weaken the direction of CE > Pearson. |
| **A6** | **CONFIRMED, MINOR** | README, PREREG and results.md line 3 point to `brandomiranda`; FREEZE and RESULTS correctly use `brando90`. |
| **A7** | **AGREED** (verification note, not a defect) | Independently confirmed: no duplicate or `#r` rows in the H4 lanes, and `lane` records 165 `agy_opus` + 10 `claude_opus_cli` (items 091–100). |

## Additional findings missed by both stages

- **[MAJOR] N1: rule violation, "Models: always frontier" (AGENTS.md:17, 11-14-2026).** The rule says "never use … small models for … judge runs." Qwen3-4B and Qwen3-8B are used as judges. Qwen3-8B also feeds the frozen **global primary judge G9**, plus C9b, C10 and G11, and reaches C7 through `judge_std4`. PREREG, the amendment and the README record no exemption. Fix: either record your explicit authorization for the open-weight lane (the folder name suggests it may have been requested), or label the Qwen lanes exploratory and report an all-frontier global judge (G6 with std3, or G6b).
- **[MAJOR] N2: matched selection overturns head Prediction 3 on RPS.** I ran strict-nested selection inside each outer fold with the same grid for all three objectives (α ∈ {1e-4, 1e-2, 0.3, 1, 3, 10} × η × quad), ranked by inner-CV RPS:
  - Results: head CE **0.0683**, head RPS **0.0703**, head Pearson **0.0734** (CE 1.006, ICC 0.875).
  - CE − Pearson: dRPS **−0.0051 [−0.0111, +0.0006], p=0.079**; dCE −0.094 [−0.169, −0.029]; dTVD −0.032 [−0.059, −0.006].
  - RPS − Pearson: a tie on all three metrics (dRPS p=0.27).
  - Conclusion: CE beats Pearson on CE and TVD but not on the primary RPS. Stage 2's expectation that "CE still beats Pearson cleanly" is wrong.
  - These are post-hoc audit numbers, not confirmatory ones.
- **[MAJOR] N3: the 50-task "Works" verdict is not defensible on clean rows.** PREREG:58 requires paired RPS vs F8 "< 0" and calls the cv5 CI < 0 "the cleanest" test. Only the leaky fixed C7 row has a CI below zero (−0.0058 [−0.0124, −0.0004]). The clean rows cross zero: nested global −0.0044 [−0.0098, +0.0012]; H3-free nested set-aware −0.0028 [−0.0082, +0.0031]. The cv5 F8 baseline is itself contaminated by H3 and by selection. Stage 2's checklist does not touch the verdict label. Resolve the "< 0" ambiguity explicitly: it reads as Works if it means the point estimate, Promising if it means the CI. Also add an H3-free Exp 27 comparator on cv5, such as F3 (H2 Astra + Opus).
- **[MINOR] N4: stray `~/` directory at the repo root.** It holds `.claude-vals/.claude.json` and `.claude-su/.claude.json`, which contain `userID` and `machineID` but no token keys at top level. It was created at 15:52 on 11-26, probably by a `CLAUDE_CONFIG_DIR='~/…'` that was never expanded; no Exp 28 script produces it. It is not ignored, so a commit-everything workflow would publish account identifiers to a public repo. It falls outside the Exp 28 audit range: never stage it, and delete it.
- **[MINOR] N5: no Rule 92 Google Doc.** No dated Doc is linked from `results.md` or `RESULTS_11-26-2026.md`.
- **[MINOR] N6: control receipts are incomplete.** `karpathy_controls_11-26-2026.json` records only maxima for the blank, vacuous and shuffled controls, while the PREREG bars are on means.
- **[MINOR] N7: all fixes from here on are post-test.** Every remediation number is computed after test exposure. Label them "post-hoc sensitivity (Amendment 2)", never confirmatory.
- **Checked clean:** split, task and fold consistency (0 mismatches; 5 old + 5 new tasks per fold); rating counts (195 + 250, sorted, consistent with `n_ratings`); H4 completeness; F8 matches the Exp 27 freeze; unit tests pass (5/5).

## Sign-off: Go/No-Go on Stage 2's remediation checklist

**No-Go** on the checklist as written; it does not cover everything. **Go** once these amendments are added. All of them are CPU-only.

1. **Item 1:** exclude C12 only inside the cv5 nested selection, and record it in Amendment 2. Do not re-run or overwrite the frozen `inner_cv_search` receipt. Keep the leaky rows as labeled history.
2. **Item 2:** report F9 at **both** settings: 0.0659 (F8's hyperparameters) and **0.0706** (Exp 27's selected `mix=0.25`). Present G9 vs F8 (a tie) as the registered primary comparison.
3. **Item 3:** replace it with N2. Run nested matched selection for CE, RPS and Pearson heads over a shared grid that includes small α. Report the raw matched Pearson head and drop post-calibration from the head headline. Rewrite Prediction 3 as: not confirmed on RPS for the head; confirmed on CE and TVD; LoRA CE > Pearson confirmed; LoRA RPS vs Pearson mixed. Quarantine LoRA post-calibration (#2).
4. **Item 4:** add A5's epoch counts, the CE grid-boundary choice, the post-test F8 and Pearson-initialization reruns, and **N1**: either your recorded authorization or an all-frontier primary judge.
5. **Item 5:** replace "remove IDs from the CSV" with "correct the 'zero rater identities' claim". Add N3 (verdict wording plus an H3-free cv5 Exp 27 comparator), N5 (the Doc), N6 (control means) and N4 (keep `~/` out of Git).
6. **After the patch:** rerun `final_eval_exp28.py`, run a deterministic table-to-JSON transcription check, `python3 scripts/check_project.py`, and `git diff --check`; then commit `mega_results.tex`, `mega_meta.tex` and the PDF together. A further model-reviewer round is optional, at your request.

With these amendments, every remaining quantitative claim can be defended, with no open critical or major flaw. Without amendments 3 and N3, the head Prediction 3 and the 50-task "Works" verdict would still be overstated.

**Next steps (graded):**
- **A (do first):** amendments 3 and N3, which change the headline claims.
- **A:** item 1 and N1, for leakage and governance.
- **B:** items 2, 4 and 5 text fixes, plus N4 hygiene.
- **C:** a GPU rerun of LoRA with saved inner-OOF predictions and a wider step grid. Only if you want a valid LoRA post-calibration row.

**TLDR-end:** [ttj: Exp 28 Stage 3 QA] FAIL as committed; the strict nested global judge's clean gain over the constant (−0.0483 [−0.0724, −0.0258]) holds. Once hyperparameter selection is matched, the head's CE vs Pearson gap on RPS crosses zero (−0.0051 [−0.0111, +0.0006]). The 50-task "Works" vs F8 claim relies only on leaky rows, and Qwen3-8B inside the primary judge conflicts with the frontier-only rule, so Stage 2's CPU checklist passes only with those three additions.

**Snapshot:** none produced; this was a read-only audit with no new artifacts in the repo. The scratch scripts are in `/tmp/s3audit/`.
