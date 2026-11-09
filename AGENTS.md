# Project instructions

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/AGENTS.md>

**TLDR:** Keep judge methodology, historical evidence, and fresh results distinct. This public project studies AI/agent/LLM judges for formal specification coverage; VeriBench's prover judge is a separate evaluation route.

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

`cert-judge` and `judges-dont-need-psychometrics-or-corr` may use suitable authorized ratings for their own studies, with consent, provenance and split/exposure history preserved. Cross-link the collection rather than create competing collection workflows. The cross-entropy-versus-correlation objective comparison belongs in `judges-dont-need-psychometrics-or-corr`; it does not take ownership of human-rating preparation. More ratings can support stronger human-agreement evidence, but sample size alone does not establish judge validity, and the separate prover-outcome target does not require human ratings.

## Files and privacy

- Put experiment-specific configuration, scripts, aggregate evidence, and reports together under `experiments/NN_descriptive_setup/`; update `experiments/README.md`.
- This repository is public. Keep participant identities, individual rating sheets, consent, private packets, credentials, and sealed ratings in ignored `private/` or the approved restricted store. Import only authorized aggregate historical evidence.
- Preserve the existing packet builder's byte-exact delivery contract and source snapshots. Do not rewrite a delivered packet in place.
- Use “rating” for data, “rater” for people, and “judge” for the model. Prefer “judge selection” and “judge–human agreement”; do not introduce certification claims from human agreement.

## Paper and verification

Use `paper_latex/AAAI_2027_Evaluation_AI_Scientists/`, one file per section and one sentence per source line. Preserve the official vendor style bytes. Keep the submission PDF anonymous and new outcomes explicitly pending. Source comments should link numerical claims to receipts.

Run `python3 scripts/check_project.py`, the experiment's design validator, `python3 scripts/build_paper.py`, and `git diff --check`. Inspect the PDF after substantive edits; commit its current version with the source. Inspect the exact staged diff for private data and secrets, preserve concurrent work, and follow the shared landing rule after requested review and checks pass.

## Sister repo

Sister repo: https://github.com/brando90/judges-dont-need-psychometrics-or-corr (general position paper: distribution matching, not correlation, for LLM judges). This repo is its concrete application. Keep claims and terminology consistent across both; cross-link rather than duplicate.

Origin: working on this study is what led to the position paper. We realized we were doing something odd: fitting judges to maximize correlation with humans, even though correlation has severe drawbacks as a metric (Pearson captures only linearity, Spearman only rank order, neither the full human-rating distribution).
