#!/usr/bin/env python3
# TLDR: Read-only gather on skampere1 for experiment 110's VBV2 condition: the exact candidate/reference/Python text the H2 judge saw for every VBV2 cell, the frozen extractor's 13 file-side criteria, and the judge-side spreads J1/J2; writes per-candidate criteria and hashes only (no texts, no score levels). Zero model calls.
"""Usage (on skampere1):  python3 -I gather_vbv2_on_snap.py OUT_DIR EXTRACTOR_DIR

Primary sources (CRITERIA_VBV2.md section 1): experiment 103 suites vbv2, vbv2_recovery_1, vbv2_agent96, whose rendered
judge prompts are on disk. Secondary source (amendment V-A1, reported separately): experiment 100 phase 7 VBV2 cells,
whose exact judge inputs (source.py, gold.lean, solution.lean) are on disk but whose rendered prompt bytes are not.
"""
import glob
import hashlib
import json
import os
import re
import statistics
import sys

OUT, EXTRACTOR_DIR = sys.argv[1], sys.argv[2]
FROZEN_EXTRACTOR_SHA = "d72481b87f0f7714574f2450cf08b42d502234e49c8ca1998c4657fabbf1daa1"
sys.path.insert(0, EXTRACTOR_DIR)
import extract_criteria as ec  # noqa: E402

sha_b = lambda b: hashlib.sha256(b).hexdigest()
sha_t = lambda t: sha_b(t.encode("utf-8"))
assert sha_b(open(ec.__file__, "rb").read()) == FROZEN_EXTRACTOR_SHA, "extractor is not the frozen experiment-110 version"

R103 = glob.glob("/lfs/skampere1/0/brando9/veribench_vb103/experiments/103_*/private")[0]
R100 = glob.glob("/lfs/skampere1/0/brando9/vb100/experiments/100_*/private")[0]
SUITES = {"vbv2": "judge_vbv2", "vbv2_recovery_1": "judge_vbv2_recovery_1", "vbv2_agent96": "judge_vbv2_agent96"}
NOT_FM = {"qwen3.6-27b-thinking", "qwen"}
HEAD = re.compile(r"^## ([123])\. (Python source|Gold Lean file|Agent Lean file): .*$")


def sections(prompt):
    """{1: python, 2: reference, 3: candidate}: the single fenced block under each numbered user-prompt header."""
    body = prompt.split("=== VB103_JUDGE_USER_BEGIN ===", 1)[1].split("=== VB103_JUDGE_USER_END ===", 1)[0]
    lines = body.split("\n")
    heads = [(i, int(HEAD.match(l).group(1))) for i, l in enumerate(lines) if HEAD.match(l)]
    out = {}
    for j, (i, n) in enumerate(heads):
        end = heads[j + 1][0] if j + 1 < len(heads) else len(lines)
        block = lines[i + 1:end]
        opens = [k for k, l in enumerate(block) if l.startswith("```")]
        assert len(opens) >= 2, ("no fenced block under section", n)
        out[n] = "\n".join(block[opens[0] + 1:opens[-1]]) + "\n"
    assert sorted(out) == [1, 2, 3], sorted(out)
    return out


def j12(sol, opus):
    """Experiment 110's J1/J2 on raw 0-5 repeats (both members need 3)."""
    if not sol or not opus or len(sol) != 3 or len(opus) != 3:
        return None, None
    return ((max(sol) - min(sol) + max(opus) - min(opus)) / 2.0,
            abs(float(statistics.median(sol)) - float(statistics.median(opus))))


rows, problems = [], []

# ---------------- primary: experiment 103 VBV2 suites ----------------
reps = {}
for f in sorted(glob.glob(os.path.join(R103, "judge/harvests/cells_vbv2*__H2_*.json"))):
    stem = os.path.basename(f)[len("cells_"):-len(".json")]
    suite, member = stem.rsplit("__", 1)
    for c in json.load(open(f))["cells"]:
        if c.get("kind") != "main":
            continue
        ok = (c.get("status") == "measured" and c.get("score_raw") not in (None, "", "None")
              and c.get("prompt_sha256_delivered") == c.get("prompt_sha256_expected"))
        if ok:
            reps.setdefault((suite, c["item"], member), {})[c.get("repeat")] = int(c["score_raw"])
for suite, packdir in SUITES.items():
    cells = {}
    for d in sorted(glob.glob(os.path.join(R103, "packs", packdir, "judge__*"))):
        text = open(os.path.join(d, "instruction.md"), encoding="utf-8", errors="replace").read()
        hdr = json.loads(re.search(r"<!-- vb103-judge-cell: (\{.*\}) -->", text).group(1))
        cells.setdefault(hdr["item"], []).append((hdr.get("repeat"), sections(text), hdr.get("prompt_sha256")))
    for item, packs in sorted(cells.items()):
        texts = {n: {sha_t(p[1][n]) for p in packs} for n in (1, 2, 3)}
        if any(len(v) != 1 for v in texts.values()):
            problems.append({"source": "exp103_" + suite, "item": item, "problem": "repeat packs carry different texts"})
            continue
        sec = packs[0][1]
        model = "gpt-6-luna-high" if suite == "vbv2_agent96" else item.split("__")[0]
        task = item.split("__")[-1]
        f = ec.features(sec[3], sec[2], sec[1])
        sol = [v for k, v in sorted(reps.get((suite, item, "H2_sol_high"), {}).items())]
        opu = [v for k, v in sorted(reps.get((suite, item, "H2_opus55_max"), {}).items())]
        f["J1"], f["J2"] = j12(sol, opu)
        rows.append({"cond": "VBV2", "source": "exp103_" + suite, "model": model, "task": task, "cluster": task,
                     "id": "exp103_%s|%s" % (suite, item), "is_fm": model not in NOT_FM,
                     "n_repeat_packs": len(packs), "judge_repeats_complete": f["J1"] is not None,
                     "sha256": {"candidate": sha_t(sec[3]), "reference": sha_t(sec[2]), "python": sha_t(sec[1])},
                     "f": f})

# ---------------- secondary (amendment V-A1): experiment 100 phase 7 VBV2 judge inputs ----------------
for pk, cond in (("phase7_inputs", "phase7_original"), ("phase7_inputs_rs", "phase7_rs")):
    for d in sorted(glob.glob(os.path.join(R100, pk, "vbv2_*"))):
        name = os.path.basename(d)
        paths = {n: os.path.join(d, fn) for n, fn in ((1, "source.py"), (2, "gold.lean"), (3, "solution.lean"))}
        if not all(os.path.isfile(p) for p in paths.values()):
            problems.append({"source": "exp100_" + cond, "item": name, "problem": "missing judge input file"})
            continue
        sec = {n: open(p, encoding="utf-8", errors="replace").read() for n, p in paths.items()}
        parts = name.split("__")
        model, task = parts[1], parts[-1]
        f = ec.features(sec[3], sec[2], sec[1])
        f["J1"] = f["J2"] = None  # filled from experiment 100's committed phase-7 repeats in the analysis step, if complete
        rows.append({"cond": "VBV2_secondary", "source": "exp100_" + cond, "model": model, "task": task, "cluster": task,
                     "id": "exp100_%s|%s" % (cond, name), "cell_id": name, "is_fm": model not in NOT_FM,
                     "sha256": {"candidate": sha_t(sec[3]), "reference": sha_t(sec[2]), "python": sha_t(sec[1])}, "f": f})

os.makedirs(OUT, exist_ok=True)
with open(os.path.join(OUT, "vbv2_features.jsonl"), "w") as fh:
    for r in rows:
        fh.write(json.dumps(r, sort_keys=True) + "\n")
summary = {"n_rows": len(rows), "problems": problems,
           "by_source": {s: sum(1 for r in rows if r["source"] == s) for s in sorted({r["source"] for r in rows})},
           "tasks": sorted({r["task"] for r in rows}),
           "j12_complete_primary": sum(1 for r in rows if r["cond"] == "VBV2" and r["judge_repeats_complete"]),
           "main_function_unmatched": {"prereg": sum(1 for r in rows if not r["f"]["diag"]["lean_main_matched"]),
                                       "A1": sum(1 for r in rows if not r["f"]["diag"]["lean_main_matched_A1"])},
           "python_main_found": sum(1 for r in rows if r["f"]["diag"].get("py_main")),
           "extractor_sha256": FROZEN_EXTRACTOR_SHA,
           "gather_script_sha256": sha_b(open(os.path.abspath(__file__), "rb").read())}
json.dump(summary, open(os.path.join(OUT, "gather_summary.json"), "w"), indent=1)
print(json.dumps({k: v for k, v in summary.items() if k != "problems"}, indent=1), "\nproblems:", len(problems))
