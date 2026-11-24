"""Pick the 60 tasks of experiment 24 (deterministic) and copy their inputs into inputs/.

Population: TinyVeriBench-256 tasks of experiment 23 (expt_v1) whose faithful gold copy passes the experiment 23 gate
(compiles, no sorry, no axiom, no native_decide) and whose saved historical natural agent file compiles and is non-empty.
Sample: the 30 tasks of experiment 23's llm_sample that are in the population, then random.Random(24) fills to 60.
Reads only experiment 23's committed inputs and gate csv. No judge output is read.
Usage: python3 select_tasks.py   (from anywhere; writes inputs/<task>/{gold.lean,source.py,historical_agent.lean} and inputs/tasks.json)
"""
import csv, json, random, shutil, pathlib
HERE = pathlib.Path(__file__).resolve().parents[1]
V1 = next(HERE.parent.glob("23_*")) / "expt_v1_tinyveribench256"
man = json.load(open(V1 / "inputs/tiny256_manifest.json"))
gate = {}
for r in csv.DictReader(open(V1 / "results/gate_tiny256.csv")):
    gate[(r["task"], r["condition"])] = r
def ok(t):
    g, a = gate.get((t, "faithful_gold_copy")), gate.get((t, "historical_natural_agent"))
    d = V1 / "inputs/tiny256" / t
    return (g and g["passes_gate"] == "1" and a and a["compiles"] == "1" and (d / "source.py").exists()
            and (d / "historical_agent.lean").exists() and (d / "historical_agent.lean").stat().st_size > 200)
elig = [r["task"] for r in man["rows"] if ok(r["task"])]
first = [t for t in man["llm_sample"] if t in elig]
rest = sorted(t for t in elig if t not in first)
random.Random(24).shuffle(rest)
tasks = first + rest[: 60 - len(first)]
out = HERE / "inputs"
for t in tasks:
    (out / t).mkdir(parents=True, exist_ok=True)
    for f in ("gold.lean", "source.py", "historical_agent.lean"):
        shutil.copy(V1 / "inputs/tiny256" / t / f, out / t / f)
json.dump(dict(n_population=len(elig), from_exp23_llm_sample=len(first), tasks=tasks), open(out / "tasks.json", "w"), indent=1)
print(len(elig), len(first), len(tasks))
