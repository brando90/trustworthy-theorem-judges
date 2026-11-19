"""Import VB256 (VeriBench's 256-task subset of all 896 tasks, frozen 11-18-2026) for experiment 23's VB256 run.

- Reads the official manifest from brando90/veribench at REVISION and checks its sha256 against MANIFEST_SHA256
  (the hash in its freeze record, FREEZE_vb256.md); a mismatch stops the import.
- For every task copies the gold reference and the Python source at REVISION into
  expt_v2_vb256/inputs/vb256/<task_id>/{gold.lean,source.py}. Paths come from experiment 116's task catalog
  (CATALOG: `reference_path`, `python_path` per task ID; IndustrySet Python files are snake_case, e.g.
  `aerospace_set_real/my_fprime_sequence_nonempty.py` for gold key `aerospace_set_real/MyFprimeSequenceNonempty`);
  the reference path must equal `lean_src/veribench/<gold_key>.lean` and every path must be used once.
- Records each file's sha256 at REVISION and at the manifest's own `source_revision`, so any reference change made
  after the manifest's source revision is visible. Missing files are reported, never substituted.
Writes expt_v2_vb256/inputs/{vb256_all_splits.json, vb256_manifest.json}. The 30-task sample and the targeted
shadowing set are added later by draw_vb256_sample.py under the pre-registered rule.
"""
import hashlib, json, subprocess, sys
from common import V2
VERIBENCH = "/Users/brandomiranda/veribench"
REVISION = "8b4a11010cebab0aa40191a4ba4a92565d621080"  # brando90/veribench origin/main on 11-19-2026 (git ls-remote)
MANIFEST = ("experiments/116_tiny_vbv1_subset_selection_and_frontier_validation/"
            "expt_v10_audit_and_heldout_validation_11-18-2026/manifests/vb256_all_splits.json")
MANIFEST_SHA256 = "b2e32dddc306088610152a186fee88c88828f85f2a4ad97215ee64dce80eda21"
CATALOG = "experiments/116_tiny_vbv1_subset_selection_and_frontier_validation/expt_v1/manifests/catalog.json"


def show(rev, path):
    r = subprocess.run(["git", "-C", VERIBENCH, "show", f"{rev}:{path}"], capture_output=True)
    return r.stdout if r.returncode == 0 else None


def sha(b):
    return hashlib.sha256(b).hexdigest() if b is not None else None


raw = show(REVISION, MANIFEST)
if sha(raw) != MANIFEST_SHA256:
    sys.exit(f"manifest sha256 {sha(raw)} != frozen {MANIFEST_SHA256}")
man = json.loads(raw)
(V2 / "inputs").mkdir(parents=True, exist_ok=True)
(V2 / "inputs/vb256_all_splits.json").write_bytes(raw)
src_rev = man["source_revision"]
cat_raw = show(REVISION, CATALOG); cat = {r["task_id"]: r for r in json.loads(cat_raw)["tasks"]}
paths = [(cat[t["task_id"]]["reference_path"], cat[t["task_id"]]["python_path"]) for t in man["tasks"]]
assert len({g for g, _ in paths}) == len({p for _, p in paths}) == len(man["tasks"]), "mapping is not one-to-one"
rows, missing = [], []
for t in man["tasks"]:
    c = cat[t["task_id"]]
    gpath, ppath = c["reference_path"], c["python_path"]
    assert gpath == f"veribench_dataset/lean_src/veribench/{t['gold_key']}.lean", (t["task_id"], gpath)
    g, p = show(REVISION, gpath), show(REVISION, ppath)
    g0, p0 = show(src_rev, gpath), show(src_rev, ppath)
    if g is None or p is None:
        missing.append(dict(task=t["task_id"], gold_missing=g is None, python_missing=p is None)); continue
    d = V2 / "inputs/vb256" / t["task_id"]; d.mkdir(parents=True, exist_ok=True)
    (d / "gold.lean").write_bytes(g); (d / "source.py").write_bytes(p)
    rows.append(dict(task=t["task_id"], split=t["split"], domain=t["domain"], stratum=t["stratum"], gold_key=t["gold_key"],
                     gold_path=gpath, python_path=ppath, gold_sha256=sha(g), python_sha256=sha(p), gold_lines=g.count(b"\n"),
                     gold_sha256_at_manifest_source_revision=sha(g0), python_sha256_at_manifest_source_revision=sha(p0),
                     gold_changed_since_manifest_source_revision=sha(g) != sha(g0),
                     catalog_reference_sha256=c["reference_sha256"], catalog_python_sha256=c["python_sha256"]))
out = dict(source=f"brando90/veribench {MANIFEST} @ {REVISION}", manifest_sha256=MANIFEST_SHA256,
           catalog=f"{CATALOG} @ {REVISION}", catalog_sha256=sha(cat_raw),
           manifest_source_revision=src_rev, files_revision=REVISION, n_tasks=len(man["tasks"]), n_imported=len(rows),
           missing=missing, rows=rows)
json.dump(out, open(V2 / "inputs/vb256_manifest.json", "w"), indent=1)
print(len(rows), "imported;", len(missing), "missing;", sum(r["gold_changed_since_manifest_source_revision"] for r in rows),
      "gold files changed since the manifest's source revision")
