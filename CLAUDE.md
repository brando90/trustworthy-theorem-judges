# Project instructions

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/AGENTS.md>

**TLDR:** Keep judge methodology, historical evidence, and fresh results distinct. This public project studies AI/agent/LLM judges for formal specification coverage; VeriBench's prover judge is a separate evaluation route.

## Current priority — user clarification, 11-09-2026

The first task is the best practical judge of human ratings: pursue method 2 (correlation training, starting with Pearson) and method 4 (proper-loss training, with normalized ranked probability score primary and cross-entropy/Brier as separate conditions). Match capacity, data, harness and search budgets; select hyperparameters with the same validation ranked probability score, then evaluate the fixed judges on the same held-out metric panel without selecting on test results. Ranked probability score (RPS) remains the primary held-out metric; cross-entropy (CE) and total variation distance (TVD) are secondary evaluation metrics. TVD compares each forecast with its artifact's empirical human rating distribution and is averaged equally across artifacts; it is distinct from TVD mutual information (TVD-MI). This prospective panel does not rewrite completed protocols or results. Pearson measures linear association between output ratings; it does not require a linear neural judge or input-to-rating mapping, and high correlation can coexist with bias. This repository owns the probabilistic human-rating judge and an optional bounded-prover-success forecaster; VeriBench owns the actual Lean/formal specification coverage engine and differential-testing reference acceptance. The cert-judge proxy project is separate. The sister repository tests the general objective-comparison hypothesis without assuming correlation is inferior. Follow the [methods 2 and 4 priority plan](experiments/02_probabilistic_ordinal_judge/PRIORITY_2_VS_4_11-09-2026.md): strict task/agent/rater split separation needs a prospective amendment; preserve existing evidence, pins, funding pauses and active owners.

## Shared rules

At each non-trivial task, refresh `~/agents-config` with `git pull --ff-only` (preserve concurrent work), read `INDEX_RULES.md`, then its Hard Rule details and matching triggers. If absent, clone <https://github.com/brando90/agents-config>. Follow explicit user decisions and existing funding, privacy, and model pins. Model-reviewer quality assurance is opt-in; deterministic verification always applies. Keep this file and `CLAUDE.md` byte-identical.

## Research workflow: no branches

This is a research project. Each experiment lives in its own numbered experiment folder (`experiments/NN_<setup_name>/`). Commit and push straight to `main`. Do not create branches or pull requests. If a leftover branch turns up, merge it into `main` (no force-push) and delete it. If two experiments pick the same number, keep the one already on `main` and renumber the new folder to the next free number, updating its internal references.

## Scientific contract

- Read the relevant experiment's README, configuration, and source receipts before writing a definition or number. Preserve provenance and denominator, split, uncertainty, bias, and missingness. Historical results do not validate a new judge.
- Judge inputs are the original Python source, candidate Lean artifact, and gold reference. State exactly which proof bodies are visible. Formal specification coverage evaluates statements, not success at proving them.
- The human-target judge predicts six probabilities over ratings 0–5, scored with normalized ranked probability score, averaged within artifact and then equally over artifacts. The separate prover-target judge forecasts acceptance under a specified protocol, scored with Brier loss. Preserve these different targets; correlations alone do not establish distributional or absolute agreement.
- Split by task family, solver identity, and rater identity as specified in the plan. Keep sealed test ratings sealed during selection. Record prior exposure, model/version, harness, effort, prompt, aggregation, failures, and artifact hashes.
- A prover establishes an implication only with a checked proof; a timeout remains unresolved. This repository does not silently replace VeriBench's scorer.
- Treat sample sizes and thresholds as planned until verified. New human data and paid inference are separate execution work with their own frozen manifest and budgets.

## Human-rating task ownership

User decision, 11-09-2026: this repository is the primary owner of preparing and collecting VeriBench human ratings to develop and evaluate a formal specification coverage judge. The active task is `experiments/09_human_rating_collection/`; keep rater instructions, packet preparation, the approved email template, assignment tracking and collection status there. The prospective collection design remains in `experiments/02_probabilistic_ordinal_judge/`. Participant records and individual ratings remain private.

Before preparing, dispatching, importing, or handing off ratings, read [judge formulations 2 and 4](experiments/09_human_rating_collection/JUDGE_FORMULATIONS_11-09-2026.md): 2 optimizes training correlation; 4 optimizes a proper probabilistic training loss. Preserve independent raw ratings and sealed splits so both can be compared fairly. Validation selection (1 versus 3) is a separate comparison. This methodology context does not change the locked packet, rubric, assignments, or send authorization.

`cert-judge` and `judges-dont-need-psychometrics-or-corr` may use suitable authorized ratings for their own studies, with consent, provenance and split/exposure history preserved. Cross-link the collection rather than create competing collection workflows. The cross-entropy-versus-correlation objective comparison belongs in `judges-dont-need-psychometrics-or-corr`; it does not take ownership of human-rating preparation. More ratings can support stronger human-agreement evidence, but sample size alone does not establish judge validity, and the separate prover-outcome target does not require human ratings.

## How we choose (learn) a judge: the formulations (Brando, 11-09-2026)

**Current clarification, 11-09-2026:** The section below preserves an earlier interpretation. The [current priority plan](experiments/02_probabilistic_ordinal_judge/PRIORITY_2_VS_4_11-09-2026.md) supersedes the tentative 3-versus-4 priority and cross-entropy-primary recommendation below: pursue 2 versus 4 with common validation ranked probability score, keeping cross-entropy as a separate training condition and shared evaluation metric. This historical context does not authorize changing locked packets, assignments or evaluation-only data use.

**Any agent that prepares or dispatches the human-rating task packet reads this first and keeps the packet (instructions, rating scale, splits, what the ratings are used for) consistent with it.** Full notes and sources: judge paper Q&A Doc, Part 3 (<https://docs.google.com/document/d/1zB-gYk-zU1wToS_E_carGSRGtUcF1NgZ-jWF5t1SJws/edit>).

Brando's four formulations, from his handwritten pages (Θ = the judge search space; S^tr, R^tr = train tasks and ratings; S^val, R^val = validation tasks and ratings; p^H = the human rating distribution; p^AJ = the judge's):

- ① argmax over judge in Θ of Corr(p^AJ, p^H), train data helps, Corr evaluated on S^val, R^val. "This is what people are doing" (his TODO: check by deep research).
- ② argmax over judge in Θ of Corr(p^AJ, p^H), using S^tr, R^tr only (e.g. optimizing the system with an agent or prompt optimization).
- ③ argmin over judge in Θ of Loss(p^AJ, p^H) on the validation set S^val, R^val, train data helps.
- ④ argmin over judge in Θ of Loss(p^AJ, p^H) on S^tr, R^tr only. "What we do in practice": train (or tune) on the train set only, choose hyperparameters on validation or historical hyperparameters.

His conjectures (not tested): (a) ③ gives better evaluation results than ④ (it uses general machine learning knowledge instead of a hack on human correlations); (b) ③ is more principled, or at least easier to think about, since it uses the successful machine learning framework. He does not think ② is needed. His question: do both experiments, and which is best? He also wrote that "the two main formulations" are "② & ④"; whether he meant ③ and ④ or ② and ④ is being clarified. Until he answers, drop neither reading: his words, ② and ④ (develop a judge by training correlation vs by training loss; the collection note `experiments/09_human_rating_collection/JUDGE_FORMULATIONS_11-09-2026.md` in trustworthy-theorem-judges reads it this way), and our reading, ③ and ④ (select on validation vs train only), need the same independent raw ratings and sealed splits, so keep all four formulations evaluable.

Our recommendation (an idea, not a result): run ③ and ④ in one repeated 5-fold cross-validation loop over tasks with an untouched test fold; test cross-entropy is the primary metric; ③ wins only if the paired 95% interval of the difference excludes 0 and the gain exceeds a margin fixed beforehand; ties go to ④. No such experiment has been run.

What the literature check found (about 90 papers read by abstract and key passages, none end to end; 6 re-checked by the author; 11-09-2026): the usual justification of an LLM judge is agreement with humans on a test set (accuracy, kappa, Pearson/Spearman/Kendall). I did not find a paper that states formulation ① or ② as its principle. In the 21 Chinese-company papers opened (Seed1.5-Thinking, MiniMax-M1, LongCat-Flash-Thinking, DeepSeek-GRM, Kimi k1.5 and others) I did not find one choosing a judge by maximum correlation; they report accuracy on a human-labeled test set. Baidu ERNIE 4.5 could not be opened. The ③/④ direction (a loss against the human rating distribution) appears in 2025-26 papers, each also reporting correlation or accuracy; two papers report that correlation alone selects poorly (arXiv 2510.09738; arXiv 2503.05965, "as much as 31%" worse judges). I did not find a source comparing ③ against ④ at about 25 tasks, so conjecture (a) is neither supported nor refuted.

For packets: keep the validation and test splits by task family, solver and rater; keep test ratings out of judge selection; record which ratings were available to the judge search (train, validation, test) so ③ and ④ can be run later without re-collecting; use "rating" for the data and "judge" for the model (one term per concept).

## Human-rating file placement — user decision, 11-11-2026

Keep the human-facing collection directly in `experiments/09_human_rating_collection/`: `RATINGS_INDEX.md` identifies each person and links their actual files, `COMPLETION_STATUS.md` states who is done and what remains with a checked date, and `ratings/` contains the actual collected rating files. Link these local paths prominently from the experiment README. A link to an index hidden only under `private/` is not sufficient. Do not relocate these deliverables away from the user's requested experiment folder.

Preserve original imports and receipts; if the experiment files are convenience copies, verify their bytes, refresh them together with the index/status after collection, and never count copies as new observations. Keep names available locally for coordination. User clarification, 11-11-2026: track the collected rating files, named index and completion status in Git in this experiment folder. Do not add ignore rules for these deliverables. This explicitly supersedes the earlier exclusion rule for these collection artifacts; credentials, unrelated private records and sealed test data remain excluded. Verify the files exist at the requested absolute path. If an editor hides ignored files, open those exact files in the user's requested editor; distinguish editor visibility, missing files and Git synchronization using evidence.

## Files and privacy

- Put experiment-specific configuration, scripts, aggregate evidence, and reports together under `experiments/NN_descriptive_setup/`; update `experiments/README.md`.
- This repository is public. Keep participant identities, individual rating sheets, consent, private packets, credentials, and sealed ratings in ignored `private/`, or the approved restricted store, except for the explicitly authorized tracked collection artifacts above. Import only authorized aggregate historical evidence.
- Preserve the existing packet builder's byte-exact delivery contract and source snapshots. Do not rewrite a delivered packet in place.
- Use “rating” for data, “rater” for people, and “judge” for the model. Prefer “judge selection” and “judge–human agreement”; do not introduce certification claims from human agreement.

## Paper and verification

Use `paper_latex/AAAI_2027_Evaluation_AI_Scientists/`, one file per section and one sentence per source line. Preserve the official vendor style bytes. Keep the submission PDF anonymous and new outcomes explicitly pending. Source comments should link numerical claims to receipts.

Run `python3 scripts/check_project.py`, the experiment's design validator, `python3 scripts/build_paper.py`, and `git diff --check`. Inspect the PDF after substantive edits; commit its current version with the source. Inspect the exact staged diff for private data and secrets, preserve concurrent work, and follow the shared landing rule after requested review and checks pass.

## Sister repo

Sister repo: https://github.com/brando90/judges-dont-need-psychometrics-or-corr (general position paper: distribution matching, not correlation, for LLM judges). This repo is its concrete application. Keep claims and terminology consistent across both; cross-link rather than duplicate.

Origin: this study motivated the position paper's question about fitting judges to human ratings. Pearson measures linear association of output ratings and Spearman their ordering; neither identifies the full human-rating distribution or requires a linear input-to-rating mapping. Which training objective yields the best practical judge remains an empirical question.
