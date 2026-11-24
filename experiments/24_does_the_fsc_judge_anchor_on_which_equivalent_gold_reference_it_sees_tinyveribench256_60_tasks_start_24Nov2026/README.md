# Experiment 24: does the FSC judge anchor on which equivalent gold reference it sees? (started 11-24-2026)

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/tree/main/experiments/24_does_the_fsc_judge_anchor_on_which_equivalent_gold_reference_it_sees_tinyveribench256_60_tasks_start_24Nov2026>

**TLDR:** Tests the reference-anchoring hypothesis of Sri's paper ("One Answer Key, Many Correct Answers", `papers/AAAI27/main.pdf` in `brando90/judge-reference-anchoring`) on the part of VeriBench formal specification coverage (FSC) that uses an LLM judge: does the judge's 0 to 5 coverage score change when it is shown a matching gold reference, an equivalent but differently written one, a perturbed one, or none? Frontier judges (`claude-opus-5-5` via Claude Code CLI, `gpt-6-astra` via Codex CLI), one prompt for all, 60 TinyVeriBench-256 tasks, pipeline label **no DT**. Status: see `RESULTS.md` (absent until the run ends).

- `PREREG.md`: hypothesis, materials, cells, estimands and decision rules, written and committed before any judge call.
- `inputs/`: the 60 tasks (gold, Python source, historical natural agent) and experiment 09's rubric (`rubric_exp09.md`).
- `materials/`: files built per task: `G`, `N`, `Gother` (deterministic), `Gprime_codex` / `Gprime_claude` (alternative references, gated), `H` (half-coverage), and the audits.
- `scripts/`: `select_tasks.py` (task choice), `build_refs.py`, `gen_alt.py` (G', H with compile gate), `audit_equiv.py` (cross-family equivalence audit), `run_judges.py` (15 cells per task and judge), `analyze.py` (as pre-registered), `llm.py` (router wrapper; Stanford and Vals lanes first, no agy, no paid API), `lean_utils.py`.
- `results/<judge>/`: raw replies, receipts (lane, model, prompt and reply hashes), `cells.csv`; `results/summary.json` and `summary.md`.

Run order (on skampere1): `build_refs.py`, `gen_alt.py --kind alt --family codex`, `gen_alt.py --kind alt --family claude`, `gen_alt.py --kind half`, `audit_equiv.py --gen codex`, `audit_equiv.py --gen claude`, `run_judges.py --judge claude`, `run_judges.py --judge codex`, `analyze.py`.
