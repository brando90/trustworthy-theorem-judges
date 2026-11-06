# Trustworthy theorem judges

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/README.md>

**TLDR:** This project studies artificial-intelligence (AI), agent, and large language model (LLM) judges for formal specification coverage (FSC). It contains a prospective human-rating methodology, historical VeriBench judge evidence, and an AAAI-27 workshop paper draft; fresh validation results are pending human data.

Given original Python source, a candidate Lean formalization, and a gold reference, can a judge predict how qualified humans rate the candidate's coverage of the required specifications? A gold statement may follow from several candidate statements together. Proof correctness and statement coverage are different properties.

## Project boundary

This repository owns the AI/agent/LLM judge study. VeriBench's intended evaluation direction is a **prover judge**: AI may guide proof search, while the prover checks whether the required implication has been established. A search timeout is unresolved, not evidence of non-entailment. This documentation records that project boundary; it does not change VeriBench's scorer or relabel its historical LLM-based results.

## Methodology and paper

- [Study methodology and collection design](experiments/02_probabilistic_ordinal_judge/README.md): predict the six-category conditional human-rating distribution with the ranked probability score as the primary loss; correlations are secondary diagnostics.
- [Historical results and provenance](experiments/01_legacy_veribench_judge/README.md): preserved aggregate receipts, limitations, and a clear separation from new validation.
- [AAAI-27 workshop paper](paper_latex/AAAI_2027_Evaluation_AI_Scientists/README.md): anonymous LaTeX source and compiled PDF using the official author kit.
- [Experiment index](experiments/README.md): status, scope, and next evidence needed.

The starting collection design has **896 tasks, four solver configurations, and 24 distinct raters** (eight for training/validation and 16 for the final audit). Collect three ratings per artifact and eight total on a 128-task audit subset. Separate training/validation artifacts from fresh final-audit outputs: **14,848 individual ratings** in total. These are planning counts, not a precision guarantee or a completed collection. The pilot must establish feasibility, thresholds, and uncertainty before the test is opened.

## Verify and build

```sh
python3 experiments/02_probabilistic_ordinal_judge/scripts/validate_design.py
python3 scripts/check_project.py
python3 scripts/build_paper.py
git diff --check
```

The paper build requires a TeX installation with `latexmk` and the packages required by the official AAAI-27 style. It builds in a temporary directory and writes the current PDF beside its source.

## Rate a file

Open the extracted packet’s `START_HERE.md` and `Rating_Instructions.md`. Read the Python source and gold theorem statements, then open the first candidate in its folder. A gold statement counts as covered if the candidate statements imply it, possibly by combining several lemmas. Apply the packet’s 0–5 rubric and record one final score per candidate file. A score summarizes the whole file.

The coordinator uses the personal sheet supplied with the original packet. Team members use a separate answer sheet each. Keep completed ratings private until collection closes.

## Prepare identical examples for independent ratings

The coordinator needs the original, extracted VeriBench human-rating packet. The public checkout contains the builder. On the coordinator’s machine, the packet, individual answers and shareable archives live under the ignored `private/` directory.

From the repository root, build an archive for the folders assigned to a rater. For example, for folder 1:

```sh
python3 scripts/make_team_packet.py private/original private/team-folder-01.zip --folders 1
```

Pass multiple folder numbers to package an assignment. Omit `--folders` to package all 25 folders. Use a new output filename for each build. The builder checks the frozen delivery manifest, preserves the original example bytes and filenames, and includes the rubric, instructions, a blank answer sheet and file checksums. Send the same archive to raters rating the same assignment. Each returns their own completed sheet privately.

## Reference anchoring study

[Replication plan for VeriBench formal specification coverage](docs/reference-anchoring-plan.md). The plan measures whether a gold reference helps a judge distinguish full from partial coverage and whether equally valid formalizations get different scores.
