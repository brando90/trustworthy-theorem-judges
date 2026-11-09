# Judge selection with the new human ratings: proposal

**TLDR:** Brando asked whether the new human ratings could be used to improve ("train") the FSC judge and check whether its known problems go away. The current rating round's protocol spends every new rating on evaluation. This memo lays out three options. The recommendation is to keep rating set N evaluation-only and run judge selection on a separate pool of ratings from tasks disjoint from set N; experiment 106's 50 tasks already have outputs from 15 agent groups. Only option B has a deadline: it must be decided before the first team rating sheet arrives. Status: **DECIDED 10-07-2026 by Brando: option A now, option C later.** Set N stays evaluation-only, as experiment 102's protocol C already says, so no amendment is needed. A separate, task-disjoint rating pool for judge selection is designed after set N is rated. No work launched yet.

- **Asked by:** Brando, weekly notes (newest section, 10-07-2026): "As we get more human data I wonder if we can start doing 'judge training'/optimizing (need to find a good term for this) … to see if the previous issues we identified are 'removed'/improved."
- **Owner of any decision:** experiment 102's human round (`experiments/102_rescore_vbv1_paper_fsc_with_validated_judge_rewrite_tmlr_icml/`), which records the choice as a protocol amendment.

## The issues a new judge would have to fix

All of these concern the frozen judge (experiment 100's two-member H2: GPT-6 Sol high + Claude Opus 5.5 max):

- **Lenient on partial coverage.** Experts' 0.44 becomes about 0.78 (experiment 102 `human_round/README.md`). The mean bias is +0.10 on the test split, judge minus human. Experiment 106's known-answer battery agrees: with 1/4, 1/2 and 3/4 of the reference deleted, the judge's medians are 0.80, 0.80 and 0.40, against expected 0.71, 0.45 and 0.18.
- **Little test evidence.** Its ordinary-item test agreement rests on 8 tasks: Spearman 0.652 [−0.17, 0.92].
- **One agent only.** It was validated only on Claude 3.7 Sonnet outputs.
- **The rebuilt recipe is lenient on OpenAI agents** (experiment 106, simulated raters). It fails per-group bias gates on G10 (+0.103 [0.069, 0.139]), G06 (+0.111 [0.080, 0.143]) and G09 (+0.141 [0.111, 0.172]).
- **Its learned parts can hurt** (experiment 106). The learned conventions and examples lowered agreement against the bare instructions: L − Z Spearman −0.040 [−0.077, −0.006] in the persona world.

## Constraint

Experiment 102's protocol C says: "The old ratings are used up" and "new ratings go entirely to evaluation". Reusing any set-N rating for selection therefore needs an amendment fixed **before any team sheet is read**, or the test is contaminated. Brando's own A1 sheet is a sensitivity analysis only and does not count.

## Options

| | Option | What it buys | What it costs |
|---|---|---|---|
| A | Keep set N evaluation-only (current pre-registration) | The paper's central claim, that the deployed judge agrees with experts on frontier agents, is tested on all 25 tasks | No judge improvement from this round |
| B | Split set N by task, as experiment 75 did: about 10 train / 5 validation / 10 test. Select on train and validation; score the frozen and the selected judge once on the 10 test tasks | A same-test comparison of "did selection fix it?" in this paper cycle | The test shrinks from 25 tasks to 10 (about 50 files), so intervals on the main claim widen. **Must be decided before the first team sheet.** |
| C | Keep set N evaluation-only, and build a separate training/validation pool from tasks disjoint from set N | A clean test plus selection data. Experiment 106's 50 fresh tasks already have outputs from 15 agent groups, so no new runs are needed | More rater hours, later; a second, smaller recruitment |

**Recommendation: A now, plus C after set N is rated.** For an ML venue the deployed judge's held-out validation on frontier agents is the claim that matters most, and A keeps it at full strength. C then gives selection its own data without touching that test. Choose B only if judge improvement has to land in this paper cycle.

## Terminology for the paper

- **"Judge selection"** is the term this project already uses for searching candidate judges on the training split, choosing on the validation split and reporting once on the test split.
- **"Prompt optimization"** is the ML-literature name for the search itself, as in DSPy or OPRO-style search over judge prompts.
- If a score mapping is fitted, say "fit a score mapping". Never write "calibrate" or "calibration" (repo `CLAUDE.md`, Judge terminology).

## Decision (10-07-2026)

Brando, chat: "go with option A now, C later for judge selection." Consequences:
- No set-N rating may be used to build, select or tune any judge.
- Option C's pool must use tasks disjoint from set N's 25 tasks; experiment 106's 50 fresh tasks are the default candidate.
- C's selected judge and the frozen judge are each scored once on set N, as the shared final test. Disclose that the frozen judge's set-N results were known when C was designed.

## Revisit condition

Revisit when Brando picks an option. B must be picked before the first team rating sheet is read (replies due 10-09-2026, folders after). A and C can be decided any time.
