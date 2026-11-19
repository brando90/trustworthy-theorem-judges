"""Shared paths and helpers for experiment 23.

Task sets (inputs are read only):
- `pilot_exp09`: experiment 09's 25 packet tasks (pilot, 11-18-2026).
- `tiny256`, `tiny256_sample30`, `tiny256_perm_sorted_pairwise`: the TinyVeriBench-256 run of 11-18-2026 in
  `expt_v1_tinyveribench256/` ("tiny256" is kept only as that run's identifier; the set is TinyVeriBench-256).
- `vb256`, `vb256_sample30`, `vb256_perm_sorted_pairwise`: the VB256 run of 11-19-2026 in `expt_v2_vb256/`.
"""
import pathlib, subprocess, json, re
HERE = pathlib.Path(__file__).resolve().parents[1]
PACKET = HERE.parents[0] / "09_prepare_packets_and_collect_human_ratings_start_28Sep2026/rating_task_packet/main_rating_task"
V1 = HERE / "expt_v1_tinyveribench256"
V2 = HERE / "expt_v2_vb256"
MODEL = "claude-opus-5-5"  # Claude Code CLI (subscription), frontier per AGENTS.md
RUBRIC_PATH = PACKET.parent / "human_judgements_prompt.md"
SHADOW_TARGET_NAMES = re.compile(r"\b(Perm|Sorted|Pairwise)\b")  # names the targeted shadowing attack replaces


def task_set(name):
    """Return (output_root, [dict(task, gold, python, ...)]) for a task set."""
    if name == "pilot_exp09":
        return HERE / "pilot_exp09_25_tasks", [dict(task=t.name, gold=t / "gold_lean/reference.lean", python=t / "python_source/source.py")
                                               for t in sorted(PACKET.glob("task_*"))]
    if name.startswith("tiny256"):
        man = json.load(open(V1 / "inputs/tiny256_manifest.json"))
        ids = [r["task"] for r in man["rows"]] if name in ("tiny256", "tiny256_perm_sorted_pairwise") else man["llm_sample"]
        if name == "tiny256_perm_sorted_pairwise":  # tasks whose gold uses a name the shadowing attack targets
            ids = [t for t in ids if SHADOW_TARGET_NAMES.search((V1 / "inputs/tiny256" / t / "gold.lean").read_text())]
        out = []
        for t in ids:
            d = V1 / "inputs/tiny256" / t
            out.append(dict(task=t, gold=d / "gold.lean", python=d / "source.py" if (d / "source.py").exists() else None,
                            historical_agent=d / "historical_agent.lean"))
        return V1, out
    if name.startswith("vb256"):
        man = json.load(open(V2 / "inputs/vb256_manifest.json"))
        rows = {r["task"]: r for r in man["rows"]}
        if name == "vb256":
            ids = list(rows)
        elif name == "vb256_sample30":
            ids = man["llm_sample"]
        elif name == "vb256_perm_sorted_pairwise":
            ids = man["shadow_target_tasks"]
        elif name == "vb256_industry_ext":  # exploratory IndustrySet extension (native_decide references)
            ids = man["industry_extension"]
        else:
            raise ValueError(name)
        out = []
        for t in ids:
            d = V2 / "inputs/vb256" / t
            out.append(dict(task=t, gold=d / "gold.lean", python=d / "source.py", split=rows[t]["split"], gold_key=rows[t]["gold_key"]))
        return V2, out
    raise ValueError(name)


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
