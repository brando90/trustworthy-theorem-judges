# Add 3 frontier judges to the pool and repeat ② (pick by correlation) versus ④ (pick by cross-entropy)

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/21_add_3_frontier_judges_to_pool_pearson_vs_ce_80_20_start_16Nov2026/README.md>

**TLDR:** Three new frontier judges (gpt-6-astra, gpt-6.1-sol, gemini-4-argon) scored the 75 human-rated artifacts 3 times each (675 calls, about $20.2 at list prices; about $20.5 with the two optimizing agents, against the $300 cap). Repeating the experiment 12 comparison with the 8-judge pool over 1,000 task-grouped 20/5 splits: ② and ④ still tie on the main metric RPS (② minus ④ = +0.0051, 95% interval [-0.0034, +0.0136]); ④ is better on CE and TVD, ② is better on Spearman and Pearson. With gpt-6-astra as the optimizing agent on one fixed split the picture is the same on RPS and CE. No Opus judge was added (no working Anthropic route).

Results: [results.md](results.md) and [results/](results/) (`results_old5.json`, `results_new3.json`, `results_all8.json`, `extras21.json`, `fixed_split_agents_all8.json`, run transcripts, [judge_scores.csv](results/judge_scores.csv) with every call's score, tokens and cost).

Harness and models:
- Judges: the frozen H2 prompt (human-mirror instructions, 4 rater conventions, 4 leave-task-out rated demos) sent through the OpenAI Responses API (gpt-6-astra reasoning high; gpt-6.1-sol) and the Gemini generateContent API (gemini-4-argon), 3 calls per artifact. [scripts/run_judges.py](scripts/run_judges.py) holds the settings, ledger and hard cap; [scripts/render.py](scripts/render.py) renders the prompts.
- Optimizing agent: gpt-6-astra (reasoning high) in a minimal custom tool loop with one python tool ([agent/agent_loop.py](agent/agent_loop.py)); this is not Codex (Codex could not start its sandbox on the host). Prompts, final specs, call logs and the full transcripts are in [agent/](agent/). One transcript line quoting a human rating was redacted, because the repository is public.
- Pool analysis: the experiment 12 scripts, copied unchanged except pool building ([scripts/build_pool.py](scripts/build_pool.py)), [scripts/extras21.py](scripts/extras21.py) and [scripts/make_report21.py](scripts/make_report21.py).

Data: the human ratings and dataset JSON stay private (individual ratings); the run needs the VeriBench private checkout. Reproduce: `build_dataset.py`, `build_pool.py`, then `run_exp12.py --data <pool>.json --out results/<pool> --splits 1000 --boot 10000`, then `extras21.py` and `make_report21.py`. Python 3.12 venv with numpy 2.5 and scipy 1.18.

Run date: 16 Nov 2026 (after the weekly reset). No process was left running.

Limits: see the end of [results.md](results.md): no Opus API judge, spend computed from list prices rather than provider billing, a data-leakage caveat from the cached judges' demos, 5 test tasks per split, and one fixed split for the agents.
