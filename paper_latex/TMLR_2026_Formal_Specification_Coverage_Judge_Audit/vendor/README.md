# Official TMLR style files

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/paper_latex/TMLR_2026_Formal_Specification_Coverage_Judge_Audit/vendor/README.md>

**TLDR:** `tmlr.sty` and `tmlr.bst` are byte-for-byte copies of the official Transactions on Machine Learning Research (TMLR) style kit; do not edit them.

Source accessed on **11-12-2026**: [JmlrOrg/tmlr-style-file](https://github.com/JmlrOrg/tmlr-style-file), branch `main` at commit `7bf90efe3a0debbba703c05c43f3ff7e4d4a2992` (06-30-2023, "Removed duplicated line in tmlr.sty"), downloaded as the GitHub archive of that branch.

| Artifact | SHA-256 |
|---|---|
| Downloaded archive `tmlr-style-file-main.zip` | `48f9f972cc812d2cfc8032a78578c2f5d8939b92fbd4f61095e8cbeb3394f92d` |
| `tmlr.sty` | `816214ff5919aa457b6b443bee52b15d9561421417b7f8a50cc84651519f0002` |
| `tmlr.bst` | `306fd454cf40771bee01293eeb98d2c1cd5f4e11ed0cd7296b335f354fc45206` |

The kit's `fancyhdr.sty` and `math_commands.tex` are not copied: TeX Live supplies `fancyhdr`, and the paper defines no notation from `math_commands.tex`.

## Use

- `\usepackage{tmlr}` with no option produces the anonymous double-blind submission ("Anonymous authors / Paper under double-blind review").
- `\usepackage[preprint]{tmlr}` de-anonymizes the paper for a preprint server; `\usepackage[accepted]{tmlr}` is for the camera-ready version after acceptance and needs `\month`, `\year` and `\openreview`.
- `\bibliographystyle{tmlr}` gives TMLR's author-year references through `natbib`, which the style loads.

The [author guide](https://jmlr.org/tmlr/author-guide.html), read on **11-12-2026**, requires double-blind, anonymized PDF submissions on OpenReview made with this template. Submissions may be any length justified by their content; unusually long main texts (appendices excluded) can delay reviewing. A broader impact statement is required only for work with a significant risk of harm. Supplementary material may be up to 100 MB of PDF or ZIP files. Recheck the guide before submission.
