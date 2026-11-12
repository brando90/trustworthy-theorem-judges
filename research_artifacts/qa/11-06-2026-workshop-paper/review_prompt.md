# Light QA: ordinal FSC judge methodology and workshop paper

**TLDR:** Perform one independent light review of the new project methodology, historical-evidence import, LaTeX paper, instructions, and deterministic checks in the working directory. Report concrete scientific or implementation defects with file and line references and a final verdict; root will apply fixes and verify them. Review only; do not edit project files or publish anything, and use read-only access to historical sources.

User requested Claude Fable at max effort. This is the one requested cross-company review, not an experiment or measured judge call. Scope: the uncommitted change relative to base origin/main 03e4416, including untracked new files. The immutable review file-hash manifest is ../qa/reviewed_files.json.

User's accepted source plan: experiments/02_probabilistic_ordinal_judge/sources/gpt_pro_plan_11-06-2026.txt. User chose this repository for AI/agent/LLM FSC judges, while VeriBench's intended evaluation direction is a prover judge guided by AI. Do not claim the scoring migration occurred here.

Read README.md, AGENTS.md; both experiment READMEs/configs/receipts; the paper .tex sources and official style provenance; scripts/check_project.py and build_paper.py. Existing make_team_packet.py and docs/reference-anchoring-plan.md are retained unrelated functionality, not redesigned. Source immutable historical commit is in SOURCE_MANIFEST; ../.. paths to old repo are not needed unless a historical discrepancy requires checking /Users/brandomiranda/veribench with git show. Individual/private ratings must remain private and no model/data-collection runs are authorized by this review.

Review math and evidence: normalized ordinal RPS strict propriety and decomposition, W1 bound, noise-corrected CDF error under iid vs fixed panel, weighting of dense subset, dependence and independent identities, task-agent-human holdouts, 896/4/24/14848 counts, no claims of empirical sufficiency, historical test exposure/missingness/reference limitations/repeat-SD unit, honest prospective status, kit authenticity/anonymity and publication/privacy. Ensure counts include fresh generations for seen tasks and that four leave-one-agent-out fits test a procedure, not universal unseen-agent generalization.

Run useful deterministic checks (python3 scripts/check_project.py; git diff --check; optional paper build). The driver already built and visually inspected the 6-page anonymous PDF, checked one-sentence-per-line, and verified source hashes. The build must have no overfull boxes or unresolved references. If using NumPy for historical verification, /Users/brandomiranda/uv_envs/no-gold-ref-judge/bin/python3 works; system NumPy is architecture mismatched.

Deliver a compact report to stdout with actual model/effort if runtime exposes them, review coverage, severity-ordered findings (including exact remedies), remaining limitations, and final block:
VERDICT: PASS or FIXES_REQUIRED
CRITICAL_ISSUES: <count>
MAJOR_ISSUES: <count>
MINOR_ISSUES: <count>
No new review rounds. Do not treat pending new human data or explicit unresolved pre-launch margins as fabricated completed results. They are intended limitations of this prospective paper.
