<!-- TLDR: Pre-registered list of 15 deterministic criteria and in-distribution tests used to measure how close frontier-model (FM) Lean outputs are to the 75-item human-rated pool the H2 FSC judge was validated on; written 10-09-2026 before any FM or pool criterion value was computed. -->

# Experiment 110 pre-registration: is the FSC judge's validation pool similar to frontier-model outputs?

**Written:** 10-09-2026, before any criterion value was computed on either the pool or the FM files.
**Freeze rule:** this file and the extractor script's SHA-256 are recorded in the first results commit; any later change to a criterion, threshold or aggregation is a dated amendment reported beside (never instead of) the pre-registered result.
**No new model calls.** Every quantity below is computed from existing files and existing judge records.

## 1. What is being compared

- **Judge under study:** the H2 ensemble from experiment 100 (`experiments/100_karpathy_recipe_tc_judge_search_human_train_val_test/`): GPT-6 Sol (high effort) and Claude Opus 5.5 (max effort), median of 3 repeats per member, mean of the two members, divided by 5.
- **Pool (P, the judge-validation pool):** the 75 human-rated items in `inputs/items.jsonl` = 25 VBV1 tasks × 3 Claude 3.7 Sonnet (May-2026) outputs, all three splits (train / validation / test) together, with the reference the judge saw for each item (`ref_snap_path`, checked against `ref_ann_path`; the Gather stage records which one the judge prompt actually contained and uses the same kind for FM files).
- **Frontier-model set (F):** every FM candidate file on VBV1 tasks that has an H2 judge record (expected sources: experiment 107 frontier-agent outputs and experiment 103 single-call baselines; the Gather stage writes the exact manifest with file SHA-256, solver model ID, harness and task before any criterion is computed). Each FM model is also analyzed separately.
- **Two comparisons, both reported:**
  - **Primary, deployed set:** all F files (task mix and model both differ from P).
  - **Secondary, matched tasks:** F restricted to the 25 pool tasks (isolates the model shift from the task-mix shift).
- VBV2 FM outputs are out of scope for the primary claim (task distribution differs and references are private); if analyzed, they are a separately labeled condition.

## 2. Deterministic extraction (shared by all file-side criteria)

One script, `extract_criteria.py` (stdlib only, run with `python3 -I`), applied identically to P and F:

1. **Comment stripping:** remove `--` line comments and nested `/- … -/` block comments (docstrings `/-- … -/` and `/-! … -/` included). Structural counts use the stripped text.
2. **Declarations:** a declaration starts at a line beginning (after optional `@[…]`, `private`, `protected`, `noncomputable`, `partial`, `unsafe`) with one of `def abbrev instance structure inductive class theorem lemma example`. A declaration ends where the next one (or `namespace`/`section`/`end`/`#eval`/`#guard`/`open` at column 0) starts.
3. **Formal specification statement:** a `theorem` or `lemma` declaration; its *statement text* runs from the keyword to the first `:=` at bracket depth 0 (or to `where`/a leading `|` if no `:=`), its *proof text* is the rest.
4. **Tokens:** regex `[A-Za-z_][A-Za-z0-9_'.!?]*|[^\sA-Za-z0-9_]` on statement text; identifiers are tokens matching the first alternative minus Lean keywords and a fixed stoplist (`Nat Int List Bool Prop Type True False fun Option some none Array String Char Float` plus `theorem lemma def by`), lowercased, namespace prefix removed (last dotted component).
5. **Main function:** the first top-level non-underscore `def` in the task's Python source (`veribench_dataset/py_src/…`), excluding `main` and `test_*`. A Lean `def` matches if its normalized name (lowercase, `_` removed, last dotted component) equals or contains the normalized Python name. The Gather stage reports how many P and F files have no match (a parser-coverage figure, not hidden).
6. **Extractor validation before any pool/FM run:** hand-check counts on `veribench_dataset/gold_examples/lean_src/my_add.lean` and on 3 pool files chosen by `random.Random(20261009)`; record the hand counts and the script output side by side; freeze the script hash.

## 3. The 15 criteria

Each criterion is one number per file (file-side, C1–C13) or per judged file (judge-side, J1–J2).

| ID | Criterion | Definition (per file) | Why the judge may care |
|---|---|---|---|
| C1 | File length | Non-blank lines after comment stripping | Long files carry more material to read; possible length bias |
| C2 | Definitions | Count of `def`/`abbrev`/`instance`/`structure`/`inductive`/`class` declarations | Helper-heavy specifications look different from the pool |
| C3 | Statement count | Number of theorem/lemma statements | Directly drives perceived coverage |
| C4 | Statement length | Median token count of statement texts (0 if none) | Rich versus trivial statements |
| C5 | Quantified statements | Fraction of statements containing `∀`/`forall` or an explicit binder group `(x : T)`/`{x : T}` before the top-level `:` | General properties versus single instances |
| C6 | Conditional/relational statements | Fraction of statements containing `→`, `->` or `↔`/`<->` outside binder types | Pre/post and equivalence style |
| C7 | Ground-instance statements | Fraction of statements with no binder, no quantifier and no `→`/`↔` (e.g. `f 3 = 5`) | Test-like theorems that can inflate apparent coverage |
| C8 | Pre/post scaffold | Ordinal 0–3: +1 a def named `*Pre`/`*_pre`/`*Precondition`, +1 a def named `*Post`/`*_post`/`*Postcondition`, +1 a statement mentioning both names and containing `→` | VeriBench file format; the judge rubric reads pre/post |
| C9 | Executable tests | Count of `example` declarations + `#eval` + `#guard` commands | Tests are visible to the judge though not scored by FSC |
| C10 | Hole rate | Fraction of statements whose proof text contains `sorry` or `admit` (0 if no statements) | FSC judges statements, but holes may sway the judge |
| C11 | Main-function focus | Fraction of statements that mention a matched main-function name (step 5) | Off-target statements versus specifications of the task function |
| C12 | Lexical overlap with reference | For each reference statement, max Jaccard of its identifier set against every candidate statement's identifier set (both main names replaced by the token `MAIN`); mean over reference statements | Closeness to the gold obligations the judge compares against |
| C13 | Statement-count ratio | `log2((C3 + 1) / (n_ref_statements + 1))`, with reference statements extracted by the same script | More or fewer properties than the reference obligations |
| J1 | Judge repeat spread | Mean over the two members of (max − min) of that member's 3 raw 1–5 repeat scores | Instability signals items unlike those the judge was selected on |
| J2 | Judge member disagreement | Absolute difference between the Sol median and the Opus median (raw 1–5 scale) | Cross-family disagreement signals ambiguity or shift |

**J1/J2 availability rule.** They are computed only from judge records whose identity (models, effort, prompt/rubric hash, repeats, aggregation) matches the experiment-100 H2 configuration, verified against the relevant `JUDGE_IDENTITY*.json`. If FM records do not match, J1/J2 are reported as unavailable and the count becomes k/13 with that denominator stated; no substitute judge is used and no call is made.

**Diagnostics (reported, not counted):** comment density (comment characters / all characters), identifier style (fraction of def names in snake_case), use of `Decidable`/typeclass/`structure`, `native_decide` count, Mathlib import, Lean compile status where an existing receipt has it, and the judge score level itself (the score level is the outcome, not a covariate of shift).

## 4. In-distribution test per criterion

Let X be the pool values (n = 75) and Y the FM values for one comparison set.

**Primary rule (pre-declared):** criterion c is *in-distribution (ID)* iff both
- **(a) location:** median(Y) lies in the pool interval [P5(X), P95(X)] (quantile type 7), and
- **(b) coverage:** at least **0.70** of the FM files lie in [P5(X), P95(X)].

*Degenerate pools:* if P5(X) = P95(X) (for example C10 or C8 concentrated on one value), replace the interval by [min(X), max(X)] in both (a) and (b).

*Threshold source:* the pool interval is the pool's own 90% central range; the 0.70 coverage threshold is a convention fixed in this document (the pool itself has about 0.90 by construction, so 0.70 tolerates a moderate shift without allowing a majority of FM files outside). There is no external standard; sensitivity results at 0.60 and 0.80 are reported beside the primary result.

**Strict rule (secondary):** ID under the primary rule **and** the two-sample Kolmogorov–Smirnov statistic D(X, Y) is at most the 95th percentile of a pool-internal null: 2,000 random splits of the 25 pool tasks into 12 and 13 tasks (all 3 items of a task stay together), D computed between the two halves (seed 20261009). This asks whether FM files differ from the pool more than two halves of the pool differ from each other. Energy distance with the same null is reported as a descriptive companion.

Per criterion the results table shows: pool median and [P5, P95], FM median and IQR, coverage, KS D with null 95th percentile, energy distance, the ID verdict under both rules, and n (files and tasks) for each side.

## 5. Aggregation and uncertainty

- **Headline:** k = number of criteria ID under the primary rule, reported as **k/15** (or k/13 under the availability rule) for the deployed set, the matched-task set and each FM model.
- **Uncertainty:** task-cluster bootstrap, 2,000 draws, seed 20261009: resample pool tasks (25, with replacement, keeping each task's 3 items) and FM tasks independently, recompute every interval, verdict and k; report the 95% percentile interval for k and, per criterion, the fraction of draws in which it is ID (stability).
- **Pre-declared verbal labels:** k ≥ 12/15 "mostly in-distribution"; 8–11 "partially in-distribution"; ≤ 7 "substantially shifted". The label never replaces the number.

## 6. Does the shift matter? (descriptive error relevance)

For each criterion, compute on the pool the Spearman correlation (task-cluster bootstrap 95% interval) between the criterion and the judge error (H2 ensemble score minus human rating, both on [0,1]) over all 75 items. A criterion is flagged *error-relevant* if |rho| ≥ 0.30 and its interval excludes 0. Any out-of-distribution, error-relevant criterion must be named in the transfer claim. With 25 tasks these correlations are weak evidence and are reported as such.

**Test-split disclosure.** Section 6 reads human ratings of all 75 items, including the 10 test tasks. It selects no judge and changes no judge, so it adds no selection inflation; the write-up still states that it read the test split and quotes, from `results/TEST_RECEIPT.json` and the 10-02-2026 split-reuse rule, how many judge versions have read the test split so far. Sections 2–5 read no human ratings.

## 7. Reporting template (filled only from computed results)

"On the deployed FM set (n files, T tasks, models …), k/15 [95% CI lo–hi] pre-declared criteria fall inside the judge-validation pool (75 items, 25 VBV1 tasks, Claude 3.7 Sonnet May-2026 outputs); out of distribution: …; of those, … were associated with judge error on the pool. The judge's agreement with human ratings is Spearman … on the test split (… on train, … on validation; one-shot test receipt), mean bias … (judge mean … minus human mean …) on the … split."

All agreement numbers, mean bias with sign and both means, and split names are copied from the experiment-100 receipts, never re-derived or rounded differently.

## 8. What this does not establish

ID on these criteria is evidence that FM files resemble the pool in the features measured, not that the judge's judge--human agreement transfers; only human ratings of FM outputs can validate the judge on them. Unmeasured features (semantic correctness of statements, proof style, task difficulty) can still shift. Any missing file, parser failure or unavailable judge record stays in the denominator and is reported.
