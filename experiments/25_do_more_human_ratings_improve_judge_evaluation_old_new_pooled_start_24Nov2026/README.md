# Experiment 25: does pooling old and new human ratings give a better evaluation of the trustworthy judge?

**Dated:** 11-24-2026. Status: first run done (ratings frozen at about 10:38 PST on 11-24-2026; 247 of 3,300 new rating rows returned). See [PREREG.md](PREREG.md) (commit 3f5a460, before any judge call on the new artifacts) and [RESULTS.md](RESULTS.md).

**TLDR:** Pooling old (75 artifacts, 25 tasks) and new (100 artifacts, 25 tasks) human ratings narrows the RPS interval to 0.60x (GPT-6 Astra) and 0.64x (Claude Opus 5.5) of old alone and steadies the estimate, so the evaluation is better; the judge is not shown better (against a set-aware constant neither is clearly ahead, and both overscore the old set by about half a point). Re-run when the Wed 11-25 and Thu 12-03 rating waves arrive.

Individual ratings and rater names stay private (this repository is public); only aggregates are committed. Scripts: [analyze.py](scripts/analyze.py), [evalcore.py](scripts/evalcore.py), [setaware.py](scripts/setaware.py), [plot_curve.py](scripts/plot_curve.py), [qa_recompute_claude.py](scripts/qa_recompute_claude.py). Results: [results/](results/). Companion retrospective analysis: [experiment 26](../26_how_new_and_old_human_ratings_fix_06_08_08_and_expand_5metric_eval_start_24Nov2026/README.md).
