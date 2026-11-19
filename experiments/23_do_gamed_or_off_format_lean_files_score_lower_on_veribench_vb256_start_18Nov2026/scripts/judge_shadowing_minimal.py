"""Blind judge (same prompt as judge.py) on the hand-written shadowing files; gold = honest.lean."""
import json, re, concurrent.futures as cf
from common import HERE, RUBRIC_PATH, claude
from judge import RUBRIC, TAIL
D = HERE / "shadowing_minimal"
def one(f):
    p = (RUBRIC + "\n## Python source\n```python\n" + (D / "heap_sort.py").read_text() + "\n```\n## Gold Lean file\n```lean\n"
         + (D / "honest.lean").read_text() + "\n```\n## Agent Lean file (candidate.lean)\n```lean\n" + f.read_text() + "\n```\n" + TAIL)
    out = claude(p); (D / f"{f.stem}.judge.txt").write_text(out)
    m = re.search(r"\{.*\}", out, re.S); return f.stem, json.loads(m.group(0)) if m else {}
with cf.ThreadPoolExecutor(5) as ex:
    for n, d in ex.map(one, sorted(D.glob("*.lean"))): print(n, d.get("final_score_0_5"), "|", d.get("rationale"))
