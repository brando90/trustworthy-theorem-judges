# Run log, experiment 12 (Claude Code worker, Sonnet 5.5, 11-10-2026)

1. Read experiments 10 and 11 (dataset builder, metrics, Pearson and CE mixture solvers); reused them unchanged (vendored copies in scripts/).
2. Wrote common.py (split rule, metrics) and prep_agent_inputs.py; fixed split = seed 1210 (20 train / 5 test tasks); wrote the train-only file for the agents.
3. Started two Claude Code subagents in parallel (one per objective), each told to read only the train-only file, with no access intended to test data. Replies:
   - ② agent: grid over the 6-component simplex (step 0.05, 53,130 candidates), max train Pearson 0.7923 at H0_sol 0.25, H2_opus 0.45, train_marginal 0.30 (many near-equal ties; the marginal weight does not change Pearson).
   - ④ agent: same grid plus an EM optimizer, min train CE 1.5243 at H0_sol 0.17, H2_sol 0.02, H2_opus 0.21, train_marginal 0.59.
4. Smoke run of run_exp12.py (20 splits), then the full run (1,000 splits, 10,000 bootstrap draws, 160 s); output in results/run_transcript.txt.
5. score_agents.py scored both agent specs on the 5 held-out tasks; make_report.py wrote results.md.
No model or API call, no GPU, no paid service. The run stopped when done; no background process left.
