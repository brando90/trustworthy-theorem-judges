# Working transcript (aggregate-only)

Worker: ultimate_brando9, Headless Work run on task AT-2749, 2026-11-09 01:40 to 02:45 PST. Harness: Claude Code agent (Claude Sonnet 5.5) writing and running Python on CPU; the numbers in results.md come from the scripts, not from a model.

1. Cloned brando90/trustworthy-theorem-judges (main ea5d842); read experiments/06 README, DATA_INVENTORY.md, RESULTS.md and scripts/import_cached.py. Experiments 01-06 exist, so 07 is next free.
2. Partial clone of brando90/veribench at be287d9 (sparse: experiments/100_karpathy_recipe_tc_judge_search_human_train_val_test); ran experiment 06's import_cached.py into a private directory: 75 artifacts, 25 tasks, 19 families, 195 expert ratings, 1,125 judge calls all COMPLETE (results/import_audit.json).
3. Counted ratings per column in inputs/items.jsonl: p1 75, p2 75, p3 45, p4 75, p5 75 (345 in total; 45 artifacts with 5, 30 with 4). The string 343 was not found in the ratings files searched.
4. Ran scripts/exp1_metrics.py (seed 20261109, 10,000 task-level resamples, three panels). Cross-check: H2 Opus Pearson 0.777, Spearman 0.769, Kendall 0.652 equal experiment 06's reported values for the same judge.
5. Ran scripts/exp1_scaling.py (20,000 draws, 500 Monte-Carlo refits, 5 leave-5-tasks-out refits).
6. Rendered results.md with scripts/write_results.py.
