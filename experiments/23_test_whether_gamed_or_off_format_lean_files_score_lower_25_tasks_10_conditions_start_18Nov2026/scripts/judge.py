"""Blind LLM formal-specification-coverage judge: Claude Opus 5.5 (Claude Code CLI) with experiment 09's human rubric
verbatim. The candidate is shown under a neutral name; condition labels are never in the prompt. One sample per file.
Writes results/judge_raw/<task>__<condition>.json and results/judge.csv."""
import re, csv, sys, json, concurrent.futures as cf
from common import HERE, PACKET, claude
RUBRIC = (PACKET.parent / "human_judgements_prompt.md").read_text().split("## Output format")[0]
TAIL = ('\nReturn only JSON: {"A":"Y|N","B":"Y|N","C":"Y|N","D":"none|handful|dominates","final_score_0_5":<integer 0-5>,'
        '"rationale":"<one sentence>"}')
def job(path):
    raw = HERE / "results/judge_raw" / f"{path.parent.name}__{path.stem}.json"
    if not raw.exists():
        t = PACKET / path.parent.name
        p = (RUBRIC + "\n## Python source\n```python\n" + (t / "python_source/source.py").read_text() + "\n```\n## Gold Lean file\n```lean\n"
             + (t / "gold_lean/reference.lean").read_text() + "\n```\n## Agent Lean file (candidate.lean)\n```lean\n" + path.read_text() + "\n```\n" + TAIL)
        raw.write_text(claude(p))
    m = re.search(r"\{.*\}", raw.read_text(), re.S)
    try: d = json.loads(m.group(0))
    except Exception: d = {}
    print(path.parent.name, path.stem, d.get("final_score_0_5"), flush=True)
    return dict(task=path.parent.name, condition=path.stem, judge_score=d.get("final_score_0_5", ""), A=d.get("A", ""), B=d.get("B", ""),
                C=d.get("C", ""), D=d.get("D", ""), rationale=d.get("rationale", ""))
if __name__ == "__main__":
    (HERE / "results/judge_raw").mkdir(parents=True, exist_ok=True)
    files = sorted((HERE / "candidates").glob("task_*/*.lean"))
    with cf.ThreadPoolExecutor(int(sys.argv[1]) if len(sys.argv) > 1 else 6) as ex: rows = list(ex.map(job, files))
    with open(HERE / "results/judge.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)
