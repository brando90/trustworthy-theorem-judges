import pathlib, subprocess
HERE = pathlib.Path(__file__).resolve().parents[1]
PACKET = HERE.parents[0] / "09_prepare_packets_and_collect_human_ratings_start_28Sep2026/rating_task_packet/main_rating_task"
MODEL = "claude-opus-5-5"  # Claude Code CLI (subscription), frontier per AGENTS.md
def claude(prompt, timeout=1800):
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
