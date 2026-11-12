# Collected human ratings, by person

**TLDR:** The current collection contains 15 numeric warm-up ratings from Rylan, Yegor and Sri. The live-sheet check on 11-11-2026 found no additional or revised ratings; main-task submissions remain blank.

## Open the actual rating data

These links open the canonical imported comma-separated value (CSV) files, not a duplicate export. Each row preserves the participant's rating and available notes.

| Person who supplied the ratings | Actual data | Numeric ratings | Other entries |
| --- | --- | ---: | --- |
| Rylan Schaeffer | [Rylan's ratings — warmup_T01.csv](legacy_veribench/human_round/private_ratings_setN/warmup_T01.csv) | 6 | None |
| Yegor Denisov-Blanch | [Yegor's ratings — warmup_T02.csv](legacy_veribench/human_round/private_ratings_setN/warmup_T02.csv) | 3 | Three N/A reference-issue entries remain in the [source snapshot](preparation_11-09-2026/collected/all_raters_11-11-2026/warmup_T02/ratings.csv); they are not numeric ratings |
| Srivatsava Daruru (Sri) | [Sri's ratings — warmup_T05.csv](legacy_veribench/human_round/private_ratings_setN/warmup_T05.csv) | 6 | None |

Open the [canonical data folder](legacy_veribench/human_round/private_ratings_setN/) for the original import receipts and immutable historical snapshots.

## Current completion status

- [Who is done and what is missing — checked 11-11-2026](preparation_11-09-2026/collected/all_raters_11-11-2026/STATUS.md).
- [Machine-readable completion and duplicate check](preparation_11-09-2026/collected/all_raters_11-11-2026/SUMMARY.json).
- [Latest live-sheet snapshots, CSV exports and source receipts](preparation_11-09-2026/collected/all_raters_11-11-2026/).

Rylan and Sri finished their warm-ups; each main assignment still has ten blank rating rows. Yegor remains extra-only under the existing qualification decision. Dilara, Allen, Don, Simon and Nikil each have six blank warm-up rows. No returned CSV was found for Slava in the scoped mail searches. Brando's 125 main-task rows were also blank when checked.

The primary collection still requires 250 ratings: 20 assigned but blank and 230 not yet assigned. Brando's ratings are additional. Warm-up ratings are not main-task ratings, and the latest snapshots must not be appended as new independent observations.

## Finding these files locally

From the repository root, open `private/09_human_rating_collection/RATINGS_INDEX.md`. The public [experiment README](../../experiments/09_human_rating_collection/README.md) links here.

The repository is public, so participant names, scores and personal source links remain under ignored `private/`. These files exist in this Mac's canonical checkout, but `git pull` cannot restore them in another checkout or machine. Open `/Users/brandomiranda/trustworthy-theorem-judges`; if an editor hides ignored files, use its Open File dialog with this index's full path. Do not force-add the private data to Git.
