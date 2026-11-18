"""Blind LLM formal-specification-coverage judge: Claude Opus 5.5 (Claude Code CLI) with experiment 09's human rubric
verbatim. The candidate is shown under a neutral name; condition labels are never in the prompt. One sample per file.
Writes results/judge_raw/<task>__<condition>.json and results/judge.csv."""
import re, csv, sys, json, concurrent.futures as cf
from common import task_set, PACKET, RUBRIC_PATH, claude
RUBRIC = RUBRIC_PATH.read_text().split("## Output format")[0]
TAIL = ('\nReturn only JSON: {"A":"Y|N","B":"Y|N","C":"Y|N","D":"none|handful|dominates","final_score_0_5":<integer 0-5>,'
        '"rationale":"<one sentence>"}')
def job(root, t, path):
    raw = root / "results/judge_raw" / f"{path.parent.name}__{path.stem}.json"
    if not raw.exists():
        p = (RUBRIC + "\n## Python source\n```python\n" + t["python"].read_text() + "\n```\n## Gold Lean file\n```lean\n"
             + t["gold"].read_text() + "\n```\n## Agent Lean file (candidate.lean)\n```lean\n" + path.read_text() + "\n```\n" + TAIL)
        raw.write_text(claude(p))
    m = re.search(r"\{.*\}", raw.read_text(), re.S)
    try: d = json.loads(m.group(0))
    except Exception: d = {}
    print(path.parent.name, path.stem, d.get("final_score_0_5"), flush=True)
    return dict(task=path.parent.name, condition=path.stem, judge_score=d.get("final_score_0_5", ""), A=d.get("A", ""), B=d.get("B", ""),
                C=d.get("C", ""), D=d.get("D", ""), rationale=d.get("rationale", ""))
if __name__ == "__main__":
    root, tasks = task_set(sys.argv[1]); (root / "results/judge_raw").mkdir(parents=True, exist_ok=True)
    jobs = [(t, f) for t in tasks for f in sorted((root / "candidates" / t["task"]).glob("*.lean"))]
    with cf.ThreadPoolExecutor(int(sys.argv[2]) if len(sys.argv) > 2 else 6) as ex: rows = list(ex.map(lambda tf: job(root, *tf), jobs))
    with open(root / f"results/judge_{sys.argv[1]}.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)
