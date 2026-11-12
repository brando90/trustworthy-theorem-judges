# TLDR: Read-only extraction on skampere1 of experiment 103's H2 judge harvest cells (per repeat) and the VBV1 solution.lean files they judged; writes a compact JSON and a tarball under /tmp; makes no model calls.
import glob, hashlib, json, os, sys, tarfile

root = glob.glob("/lfs/skampere1/0/brando9/veribench_vb103/experiments/103_*/private")[0]
out_dir = sys.argv[1]
os.makedirs(out_dir, exist_ok=True)
H = os.path.join(root, "judge/harvests")
cells = []
for f in sorted(os.listdir(H)):
    if not f.startswith("cells_vbv"):
        continue
    d = json.load(open(os.path.join(H, f)))
    stem = f[len("cells_"):-len(".json")]
    parts = stem.split("__")
    member = parts[-1]
    suite = parts[0]
    model = parts[1] if len(parts) == 3 else None
    for c in d["cells"]:
        if c.get("kind") != "main":
            continue
        cells.append({"suite": suite, "model": model, "member": member, "item": c["item"], "repeat": c.get("repeat"),
                      "status": c.get("status"), "score_raw": c.get("score_raw"), "final_score_0_5": c.get("final_score_0_5"),
                      "prompt_match": c.get("prompt_sha256_delivered") == c.get("prompt_sha256_expected"),
                      "harvest_file": f, "run_id": d.get("run_id"), "selector": d.get("selector")})
json.dump(cells, open(os.path.join(out_dir, "cells103.json"), "w"))

# Lean files: suite vbv1 -> jobs, vbv1_recovery_1 -> jobs_recovery_1, vbv1_agent95 -> jobs_agent95
jobdir = {"vbv1": "jobs", "vbv1_recovery_1": "jobs_recovery_1", "vbv1_agent95": "jobs_agent95"}
want = sorted({(c["suite"], c["model"], c["item"]) for c in cells if c["suite"] in jobdir})
files = []
with tarfile.open(os.path.join(out_dir, "lean103.tgz"), "w:gz") as tf:
    for suite, model, item in want:
        p = os.path.join(root, jobdir[suite], model, item, "verifier", "solution.lean")
        rec = {"suite": suite, "model": model, "item": item, "remote_path": "skampere1:" + p}
        if os.path.exists(p):
            b = open(p, "rb").read()
            rec.update(sha256=hashlib.sha256(b).hexdigest(), bytes=len(b))
            arc = f"103/{suite}/{model}/{item}.lean"
            tf.add(p, arcname=arc)
            rec["archive_path"] = arc
        else:
            rec["missing"] = True
        files.append(rec)
json.dump(files, open(os.path.join(out_dir, "files103.json"), "w"))
print(len(cells), "cells;", len(files), "files;", sum(1 for f in files if f.get("missing")), "missing")
