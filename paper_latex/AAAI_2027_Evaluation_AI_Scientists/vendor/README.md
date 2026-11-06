# Official AAAI-27 style files

Source accessed on **11-06-2026**: [official author-kit landing page](https://aaai.org/authorkit27/), redirecting to [AuthorKit27.zip](https://aaai.org/wp-content/uploads/2026/10/AuthorKit27.zip).
Both files below are copied byte-for-byte from that archive; neither is renamed from an earlier year or modified.

| Artifact | SHA-256 |
|---|---|
| Official `AuthorKit27.zip` | `9406a545d5d213757245eb37118fe652b2fccf64f555aff28b49ebe2a780c960` |
| `aaai2027.sty` | `01990f8d3716f8e39c5b28a7478f3ac6e28630d1161de6105a7217f5e7f60e43` |
| `aaai2027.bst` | `5db7765ba99de5c1e4686f9b3940a0add9c5e702f2164514462bec130ccb6e3c` |

## Workshop requirements

The [Effective and Efficient Evaluation for AI Scientists call for papers](https://eval-ai-scientists.github.io/aaai27/), accessed on **11-06-2026**, requires an anonymized PDF in the official AAAI-27 two-column format and double-blind review.
Full papers are **6–8 pages**, with references excluded.
Position, resource/artifact, and reproduction/negative-result papers are **2–4 pages**; the reference exclusion is not separately stated for these short categories.
Proceedings are non-archival, and authors retain full rights.
System comparisons must use matched compute and token budgets or explain why matching is infeasible.

The submission deadline is **11-20-2026 at 06:00 Coordinated Universal Time (UTC)**, equivalent to **11-19-2026 at 10:00 PM Pacific Standard Time (PST)**.
The workshop is on **02-22-2027** in Montréal.

## Use

Use `\documentclass[letterpaper]{article}` and the style's `submission` option for anonymous review.
The style loads its required fonts and sets the bibliography style itself; do not add `times`, `helvet`, `courier`, or a separate `\bibliographystyle` command.
The official template uses `url` with the `hyphens` option, `graphicx`, `natbib` and `caption` without options, and `\frenchspacing`.
Do not modify these style files or use `hyperref`, forced page breaks, or negative spacing to compress the layout.
