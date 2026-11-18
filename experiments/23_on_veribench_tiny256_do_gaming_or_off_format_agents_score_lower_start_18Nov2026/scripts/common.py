import pathlib, subprocess, json
HERE = pathlib.Path(__file__).resolve().parents[1]
PACKET = HERE.parents[0] / "09_prepare_packets_and_collect_human_ratings_start_28Sep2026/rating_task_packet/main_rating_task"
MODEL = "claude-opus-5-5"  # Claude Code CLI (subscription), frontier per AGENTS.md
RUBRIC_PATH = PACKET.parent / "human_judgements_prompt.md"
def task_set(name):
    """Return (output_root, [dict(task, gold, python)]) for a task set; inputs are read only."""
    if name == "pilot_exp09":
        return HERE / "pilot_exp09_25_tasks", [dict(task=t.name, gold=t / "gold_lean/reference.lean", python=t / "python_source/source.py")
                                               for t in sorted(PACKET.glob("task_*"))]
    man = json.load(open(HERE / "inputs/tiny256_manifest.json"))
    ids = [r["task"] for r in man["rows"]] if name == "tiny256" else man["llm_sample"]
    out = []
    for t in ids:
        d = HERE / "inputs/tiny256" / t
        out.append(dict(task=t, gold=d / "gold.lean", python=d / "source.py" if (d / "source.py").exists() else None,
                        historical_agent=d / "historical_agent.lean"))
    return HERE / "tiny256", out
def claude(prompt, timeout=2400):
    r = subprocess.run(["claude", "-p", "--model", MODEL, "--tools", ""], input=prompt, text=True,
                       capture_output=True, timeout=timeout, cwd="/tmp")
    return r.stdout
def strip_fence(s):
    s = s.strip()
    if "```" in s:
        parts = s.split("```")
        if len(parts) >= 3:
            body = parts[1]
            return body.split("\n", 1)[1] if body.startswith(("lean", "Lean")) else body
    return s
