The review is complete. The verdict is FIXES_REQUIRED: the science and the historical numbers check out, but two process and venue items block landing as documented, and seven minor items need small edits.

# Light QA report: ordinal FSC judge methodology and AAAI-27 workshop paper

**Reviewer runtime:** Claude Fable 5.1 (`claude-fable-5-1`), effort `max`, per `../qa/dispatch.json`; read-only review, no project files edited, no model or data-collection runs. The staged state I reviewed matches all 39 hashes in `../qa/reviewed_files.json`.

## Coverage and verification results

I read every file in the manifest, the accepted GPT Pro plan, the shared rules routed by the index (Hard Rules 3, 4, 5, 10, 11; Trigger Rules 13, 77, 85), and the review-paper and terminology skills. Deterministic and source checks:

| Check | Result |
|---|---|
| `scripts/check_project.py` (includes `validate_design.py`) | pass |
| `git diff --cached --check` on the staged tree | fails on 2 vendor lines (finding 1) |
| One-sentence-per-line on all 10 `.tex` files | pass |
| Clean `latexmk` rebuild in a scratch dir | 0 overfull boxes, 0 unresolved refs, PDF byte-identical to the staged `00_main.pdf` |
| 13 source hashes at VeriBench commit `be287d9b` (read-only `git show`) | all match `SOURCE_MANIFEST.json` |
| exp104 excerpt vs `CV_RESULTS.json`; addendum vs `results.md` suffix | all selected fields match; addendum byte-exact |
| Post hoc interval script rerun with the uv NumPy env in a scratch copy | output JSON byte-identical |
| Expert-rating availability 18/12, 9/6, 18/12 | matches `items.jsonl` |
| Generation provenance (Claude 3.7 Sonnet, T=0.7, 74 of 75 receipts, zero-shot, sorry allowed) | matches the provenance memo |
| Routes, 3-call medians, six calls per score, repeat-SD unit | match explainer, `ensemble.py`, and `freeze_and_receipt.py` line 43 (`stability_per_pass_mean`) |
| `AuthorKit27.zip`, `aaai2027.sty`, `aaai2027.bst` hashes | match the official download; preamble matches the kit template; no disallowed package used |
| Workshop call (6–8 pages, references excluded, deadline, date, double-blind, non-archival) | matches `vendor/README.md` and paper README |
| `harbor-datasets@c9dfd8e` | 896 task directories |
| RPS decomposition, strict propriety, W1 bound, noise-corrected CDF error (iid and finite panel), 0.080/0.049, √(3/8) | derived correct |
| 896/64/64/768, 512/3584/4096, 1536/10752/2560/14848, 192/832, fresh generations for seen tasks, four leave-one-agent-out fits framed as a procedure test | correct and consistent across README, config, paper |
| PDF anonymity | "Anonymous submission" header, anonymized notice, no names, handles, or URLs printed |
| Dictionary spell check of all prose | no misspellings |

## Findings, severity first

**MAJOR**

1. `[p 9/10]` **The documented landing check fails on the official style bytes.** `git diff --cached --check` reports trailing whitespace at `paper_latex/AAAI_2027_Evaluation_AI_Scientists/vendor/aaai2027.bst:11` and `vendor/aaai2027.sty:96`. Both are byte-exact kit files that `AGENTS.md:29` forbids changing, while `AGENTS.md:31` requires `git diff --check` to pass; no `.gitattributes` exists. Remedy: add a root `.gitattributes` containing `paper_latex/AAAI_2027_Evaluation_AI_Scientists/vendor/* -whitespace`, stage it, and confirm `git diff --cached --check` exits 0. Optionally assert that attribute in `scripts/check_project.py`.

2. `[p 8/10]` **Body length is below the venue's full-paper range.** The PDF is 6 pages and References begin on page 6 at line 13 of 59, so the body is about 5.2 pages. The call states full papers are 6–8 pages with references excluded, and `paper_latex/.../README.md:18` says the draft targets a full paper. Remedy: add roughly one page of substantive content before submission (candidates: a table of the four comparison conditions and what each isolates; a holdout-structure table mirroring the plan's "what each holdout establishes"; the historical human comparator and extra test caveats from finding 3; the controlled-edit table from README 02), then rebuild and recount. If a shorter category is intended instead, record that decision in the paper README.

**MINOR**

3. `[p 7/10]` **Historical comparators and limitations are incompletely carried over.** (a) The imported excerpt holds the raters' leave-one-expert-out Spearman 0.764 over all 75 artifacts and 0.747 on the 45 held-out artifacts (`exp104_original_aggregate_excerpt.json`, `human_loo_spearman`); neither `experiments/01_legacy_veribench_judge/README.md` nor `07_legacy_evidence.tex` reports it beside 0.826, which the judge checklist asks for when raters exist. (b) The source appendix at the manifest commit (`98_4a_appendix_validated_coverage_judge.tex`, line 13) discloses five tasks whose references changed during the rating window, so the version each rater saw is unknown (six test artifacts from two test tasks are flagged ambiguous in `items.jsonl`), and three test items whose rating sheet linked a different candidate file; excluding either raises test agreement. `README.md:75-85` and `07_legacy_evidence.tex:59` mention only the nine changed references and placeholders. Remedy: add one sentence for each caveat in both places and a human-comparator row with its denominator.

4. `[p 6/10]` **Bias sign convention is not stated in the paper.** `01_abstract.tex:12` and `07_legacy_evidence.tex:38,46` give +0.181 and +0.206 with both means but never say "judge minus expert mean, positive is lenient"; `README.md:64` and the post hoc JSON do. Remedy: define it once at `07_legacy_evidence.tex:38` and add "judge minus expert" in the abstract.

5. `[p 6/10]` **Proof visibility for the main study is not stated.** `AGENTS.md:14` requires stating exactly which proof bodies are visible; `03_target.tex:11` only says it is "recorded separately", and README 02 line 93 says byte-identical contents. Remedy: one sentence in `03_target.tex` and README 02 item 5 stating that raters and the judge both see the complete candidate and reference files, including any proof bodies or `sorry` placeholders, with proof completion recorded as a separate variable.

6. `[p 5/10]` **Terminology drift against Rule 85 and `AGENTS.md:25`.** People: the paper uses expert(s) 25 times, people 9, participant(s) 5, rater(s) 9, person 2 (for example `05_design.tex:15-17,29,73`, `06_inference.tex:7,12,18,19,48`, `09_discussion.tex:7`); README 02 uses "people" 21 times. Solvers: the paper uses solver configuration(s), configuration(s), solver, and agent(s); README 02 mostly "agent", also "systems"; `config.json` keys say agents. Ratings versus reviews: `05_design.tex:29`, `06_inference.tex:18`, README 02 lines 76-85, `config.json` stage keys. Dictionary words from the terminology skill: "cell" (`05_design.tex:22-23`, README 02 line 72), "frozen/freeze" (`05_design.tex:8,69,72`, `07_legacy_evidence.tex:40,64`, `09_discussion.tex:14`), "protocol" (abstract line 15, `02_introduction.tex:29`, `03_target.tex:22`, `08_controls_reporting.tex:37`), "files" for artifacts at `05_design.tex:40`. Remedy: choose rater, solver configuration, rating, artifact; apply across the paper, both READMEs and the root README; keep `config.json` keys or rename them together with `validate_design.py`.

7. `[p 5/10]` **Judge-recipe gaps (Rule 77).** The planned baselines at `06_inference.tex:61` and README 02 line 112 include no non-LLM baseline and no label-reproduction test, although the historical record shows a one-line theorem-count ratio beat every earlier LLM judge. Remedy: add a theorem-count-ratio baseline expressed in the six-category format and a label-in-prompt reproduction test to the pilot list in README 02 and `05_design.tex` "Pilot and frozen execution".

8. `[p 4/10]` **Anonymity check and bibliography hygiene.** `scripts/check_project.py:38` asserts the literal "Anonymous Submission" in `00_main.tex`, but the rendered header comes only from `\usepackage[submission]{aaai2027}` (`vendor/aaai2027.sty:35-37,135`); the assertion would pass even if the option were dropped. `references.bib:34` embeds a GitHub handle in the url field; the official `.bst` does not print url for `@misc`, so the PDF is clean, but any source upload would leak it. Remedy: assert the `[submission]` option in `check_project.py`; drop the url field and keep the commit hash in the note.

9. `[p 3/10]` **Document-header and public-prose hygiene.** `experiments/01_legacy_veribench_judge/README.md:1` and `vendor/README.md:1` put an HTML comment before the H1 unlike the other READMEs (Rule 16 wants the title first). `README.md:13-14` ("The remembered correlations around '0.6, 0.8, 0.8'...") is a private note inside a public file. Remedy: move or delete the comments; rewrite lines 13-14 as a neutral disambiguation of the three experiment-100 statistics, or delete them.

## Remaining limitations and notes, not counted

- `07_legacy_evidence.tex` quotes six-decimal values in prose while its table uses three; three decimals in prose would suffice, receipts keep full precision.
- Three underfull boxes exist (the paragraph at `07_legacy_evidence.tex:55-61`, badness 4441, and two in the bibliography); the build rule allows them.
- The paper does not say how the six probabilities are elicited (verbalized, log-probability, or sampling-based) or the fitted-mapping family. Consistent with the pending status, but reviewers will ask.
- The continued private paper's own caption describes the repeat SD as per-model SDs averaged, which contradicts the archived code; the new README is right. A one-line note of that discrepancy in README 01 would pre-empt confusion.
- README 02 cites Owen 2007 while the paper cites Owen and Eckles 2012; both are valid, align if desired.
- I did not visually re-inspect rendered pages; I verified text, page count, and byte identity with a clean rebuild. Pending human data and unset thresholds are treated as intended limitations, not defects.

## Ranked next steps

- `[p 9/10]` Add the `.gitattributes` exemption and re-run `git diff --cached --check`, since the documented landing check currently fails.
- `[p 8/10]` Decide the page-length route (add content or declare the category) before the 11-20-2026 06:00 UTC deadline.
- `[p 7/10]` Carry the human comparator and the two extra test caveats into README 01 and section 7, then rebuild and recommit the PDF.
- `[p 5/10]` Do the terminology pass and the small statement fixes (bias sign, proof visibility) in one edit, then rerun `check_project.py`.

VERDICT: FIXES_REQUIRED
CRITICAL_ISSUES: 0
MAJOR_ISSUES: 2
MINOR_ISSUES: 7

**TLDR-end:** [ttj: light QA of the ordinal FSC judge methodology, historical import, and AAAI-27 workshop paper] The math, counts, hashes, recompute, kit, and anonymity all verify, but landing is blocked until the vendor whitespace exemption is added and the 5.2-page body versus the 6–8-page full-paper rule is resolved, plus seven minor edits.

**Snapshot:**
```
$ git diff --cached --check
paper_latex/AAAI_2027_Evaluation_AI_Scientists/vendor/aaai2027.bst:11: trailing whitespace.
paper_latex/AAAI_2027_Evaluation_AI_Scientists/vendor/aaai2027.sty:96: trailing whitespace.
$ pdfinfo 00_main.pdf | grep Pages        -> Pages: 6   (References start page 6, line 13 of 59)
$ latexmk rebuild (scratch) sha256        -> c07d2f9f...98bbb == staged 00_main.pdf (byte-identical, 0 Overfull)
$ manifest hash check (13 sources @ be287d9b)  -> 13 OK
$ recompute_error_intervals.py (uv NumPy, scratch) -> POSTHOC JSON BYTE-IDENTICAL
$ shasum AuthorKit27.zip -> 9406a545...80c960 (matches vendor/README.md); sty/bst hashes match
$ harbor-datasets@c9dfd8e datasets/veribench_v1_3 -> entries: 896 dirs: 896
$ items.jsonl expert_n by split -> test {3:18, 2:12}, train {3:18, 2:12}, val {3:9, 2:6}
```
