"""One-time import of the frozen Tiny256 representatives (veribench-inf experiment 11 manifest, 256 rows) from
skampere2:/lfs/skampere2/0/brando9/at2314/src/<id>/{gold,agent}.lean (fetched to a local folder given as argv[1]).
Verifies every gold sha256 against the manifest, maps each to a VeriBench Python source (argv[2] pymap.json, heuristic
name match; ambiguous maps flagged), and draws the seeded 30-task LLM sample."""
import sys, json, glob, hashlib, pathlib, shutil, random, re
HERE = pathlib.Path(__file__).resolve().parents[1] / "expt_v1_tinyveribench256"  # TinyVeriBench-256 run home
src, pymap = pathlib.Path(sys.argv[1]), json.load(open(sys.argv[2]))
amb = set(json.load(open(sys.argv[3]))) if len(sys.argv) > 3 else set()
man = json.load(open(glob.glob(str(pathlib.Path.home() / "veribench-inf/experiments/11_*/evidence/v1/manifest.json"))[0]))["rows"]
rows = []
for r in man:
    t = r["representative"]; g = (src / t / "gold.lean").read_bytes()
    assert hashlib.sha256(g).hexdigest() == r["gold_sha256"], t
    d = HERE / "inputs/tiny256" / t; d.mkdir(parents=True, exist_ok=True)
    (d / "gold.lean").write_bytes(g); shutil.copy(src / t / "agent.lean", d / "historical_agent.lean")
    py = pymap.get(t)
    if py: shutil.copy(py, d / "source.py")
    rows.append(dict(task=t, gold_sha256=r["gold_sha256"], aliases=r["aliases"], gold_lines=g.count(b"\n"),
                     python_source=py.replace(str(pathlib.Path.home()) + "/veribench/", "veribench/") if py else None,
                     python_map_ambiguous=t in amb))
elig = sorted(r["task"] for r in rows if r["python_source"] and not r["python_map_ambiguous"] and r["gold_lines"] <= 400)
sample = sorted(random.Random(0).sample(elig, 30))
json.dump(dict(source="veribench-inf experiments/11 evidence/v1/manifest.json; files from skampere2 at2314/src",
               sample_rule="30 tasks, random.Random(0).sample over tasks with an unambiguous Python map and gold <= 400 lines",
               n_eligible=len(elig), llm_sample=sample, rows=rows), open(HERE / "inputs/tiny256_manifest.json", "w"), indent=1)
print(len(rows), "imported;", len(elig), "eligible;", sample)
