"""Blind LLM formal-specification-coverage judge: Claude Opus 5.5 (Claude Code CLI) with experiment 09's human rubric
verbatim. The candidate is shown under a neutral name; condition labels are never in the prompt. One sample per file.

Usage: python3 judge.py <set> [workers] [--conditions=a,b,c]
Writes results/judge_raw/<task>__<condition>.txt (raw reply, cached: an existing reply is never re-asked) and
results/judge_<set>.csv. A reply without parseable JSON (an infrastructure failure, not a score) is asked once more
(VB256 run onward); each call is recorded in results/judge_receipts.jsonl.
"""
import re, csv, sys, json, time, hashlib, threading, concurrent.futures as cf
from common import task_set, RUBRIC_PATH, claude, MODEL
RUBRIC = RUBRIC_PATH.read_text().split("## Output format")[0]
TAIL = ('\nReturn only JSON: {"A":"Y|N","B":"Y|N","C":"Y|N","D":"none|handful|dominates","final_score_0_5":<integer 0-5>,'
        '"rationale":"<one sentence>"}')
_lock = threading.Lock()


def parse(text):
    m = re.search(r"\{.*\}", text, re.S)
    try:
        return json.loads(m.group(0))
    except Exception:
        return {}


def job(root, t, path):
    raw = root / "results/judge_raw" / f"{path.parent.name}__{path.stem}.txt"
    if not raw.exists():
        p = (RUBRIC + "\n## Python source\n```python\n" + (t["python"].read_text() if t["python"] else "(not available)") + "\n```\n## Gold Lean file\n```lean\n"
             + t["gold"].read_text() + "\n```\n## Agent Lean file (candidate.lean)\n```lean\n" + path.read_text() + "\n```\n" + TAIL)
        reply, attempt = "", 0
        while attempt < 2 and "final_score_0_5" not in parse(reply):
            attempt += 1; t0 = time.time(); reply = claude(p)
            with _lock, open(root / "results/judge_receipts.jsonl", "a") as f:
                f.write(json.dumps(dict(task=path.parent.name, condition=path.stem, model=MODEL, attempt=attempt,
                                        prompt_sha256=hashlib.sha256(p.encode()).hexdigest(),
                                        reply_sha256=hashlib.sha256(reply.encode()).hexdigest(), reply_chars=len(reply),
                                        parsed="final_score_0_5" in parse(reply), seconds=round(time.time() - t0, 1),
                                        utc=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))) + "\n")
        raw.write_text(reply)
    d = parse(raw.read_text())
    print(path.parent.name, path.stem, d.get("final_score_0_5"), flush=True)
    return dict(task=path.parent.name, condition=path.stem, judge_score=d.get("final_score_0_5", ""), A=d.get("A", ""), B=d.get("B", ""),
                C=d.get("C", ""), D=d.get("D", ""), rationale=d.get("rationale", ""))


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    only = next((a.split("=", 1)[1].split(",") for a in sys.argv[1:] if a.startswith("--conditions=")), None)
    root, tasks = task_set(args[0]); (root / "results/judge_raw").mkdir(parents=True, exist_ok=True)
    jobs = [(t, f) for t in tasks for f in sorted((root / "candidates" / t["task"]).glob("*.lean")) if only is None or f.stem in only]
    with cf.ThreadPoolExecutor(int(args[1]) if len(args) > 1 else 6) as ex: rows = list(ex.map(lambda tf: job(root, *tf), jobs))
    with open(root / f"results/judge_{args[0]}.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]), lineterminator="\n"); w.writeheader(); w.writerows(rows)
