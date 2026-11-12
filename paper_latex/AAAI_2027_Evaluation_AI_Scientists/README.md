# AAAI-27 workshop paper

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/paper_latex/AAAI_2027_Evaluation_AI_Scientists/README.md>

**TLDR:** Anonymous methodology paper for the Effective and Efficient Evaluation for AI Scientists workshop. Historical scalar-judge evidence is included with its limitations; new probabilistic-judge results await human data.

## Draft and build

- [Compiled paper](00_main.pdf)
- [Main LaTeX source](00_main.tex), with numbered files for each section
- [Methodology](../../experiments/02_probabilistic_ordinal_judge/README.md)
- [Historical evidence](../../experiments/archive/01_legacy_veribench_judge/README.md)
- [Separate prover-target fallback study](../../experiments/archive/03_prover_target_fsc_judge/README.md): retrospective operational forecasting results and a prospective protocol; these are not fresh human-study results in this draft.

Run `python3 scripts/build_paper.py` from the repository root. The build uses temporary storage and refreshes `00_main.pdf` only after a successful compile without overfull boxes or unresolved references. Do not edit the official [vendor sources](vendor/README.md). The current seven-page draft uses the official anonymous submission mode, with references beginning on page seven after more than six pages of body content. It is a working draft, not a submitted paper or a completed empirical study. Submit the anonymous PDF, not an identifying repository archive.

## Venue requirements checked 11-06-2026

The [workshop call](https://eval-ai-scientists.github.io/aaai27/) specifies anonymous, double-blind review, the official AAAI-27 two-column style, and a full-paper length of 6–8 pages excluding references. It also accepts 2–4-page position papers. The draft targets a full methodological paper and includes no invented fresh results.

The submission deadline is **11-20-2026 at 06:00 UTC**, or **11-19-2026 at 10:00 p.m. Pacific Standard Time**. The workshop is non-archival and takes place on **02-22-2027**. Recheck the call before submitting; this task does not submit a paper.

## Evidence status before submission

The historical import is available now. The prospective allocation, input contract, objective, and transfer design are documented. Exact solver configurations, pilot feasibility, practical thresholds, repeated-judge count, and the sparse-assignment inference procedure still need to be frozen before the test is inspected. New human ratings and all new outcome tables remain pending.

The mathematical identities are derived in the text; the proper-scoring and selection principles are cited to primary research. Historical claims have source-receipt comments in the LaTeX. Do not replace limitations with a positive validation claim until the corresponding prespecified criteria have been evaluated.

The user's supplied GPT Pro plan is preserved byte-for-byte under the experiment's `sources/` directory with a hash and source links. It is planning provenance, not an empirical result or a research citation. This draft was prepared with AI assistance and received the requested separate model review; any venue-required disclosure must describe that assistance accurately.

[Light review and resolution record](QA_11-06-2026.md) documents the single Claude Fable/max review and the subsequent deterministic fixes.
