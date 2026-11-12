# TLDR: Builds x110/fm_manifest.json: frontier-model (FM) Lean outputs scored by experiment 100's frozen H2 judge (per-repeat ratings), their file paths, and the human ratings that exist (none for FM outputs); sealed experiment-107 values are referenced, never read.
import csv, glob, hashlib, json, os, statistics, sys
from collections import defaultdict

REPO = "/Users/brandomiranda/veribench"
X = sys.argv[1]
E100 = glob.glob(f"{REPO}/experiments/100_*")[0]
E102 = glob.glob(f"{REPO}/experiments/102_*")[0]
E103 = glob.glob(f"{REPO}/experiments/103_*")[0]
E107 = glob.glob(f"{REPO}/experiments/107_*")[0]
rel = lambda p: os.path.relpath(p, REPO)
sha = lambda p: hashlib.sha256(open(p, "rb").read()).hexdigest()


def h2(sol, opus):
    """H2 aggregate: per-member median of repeats (0-5 ints), mean of members, /5."""
    if not sol or not opus:
        return None
    return (statistics.median(sol) + statistics.median(opus)) / 2 / 5


# ---------- rating-task (25) and validation-pool (25) task sets ----------
gold_index = defaultdict(list)
for p in glob.glob(f"{REPO}/veribench_dataset/lean_src/**/*.lean", recursive=True):
    gold_index[os.path.basename(p)].append(os.path.relpath(p, f"{REPO}/veribench_dataset/lean_src"))
rating25 = {}
pk = f"{E102}/human_round/sample_setN/packet"
for folder in sorted(os.listdir(pk)):
    g = glob.glob(f"{pk}/{folder}/gold_lean/*.lean")
    if g:
        cands = gold_index.get(os.path.basename(g[0]), [])
        c0 = cands[0][:-5] if len(cands) == 1 else None
        rating25[folder] = c0[len("veribench/"):] if c0 and c0.startswith("veribench/") else (c0 or cands or [os.path.basename(g[0])])
pool_items = [json.loads(l) for l in open(f"{E100}/inputs/items.jsonl")]
pool_tasks = sorted({f"{r['domain']}/{r['task']}" for r in pool_items})
rating_task_ids = {v for v in rating25.values() if isinstance(v, str)}
norm = lambda t: (t.split("/")[0] + "|" + t.split("/")[-1]).lower()
norm_item = lambda it: None
RATING_KEYS = {norm(t) for t in rating_task_ids}
POOL_KEYS = {norm(t) for t in pool_tasks}
def item_key(item, keys):
    # 103 items are '<domain>__<...>__<basename>' lowercased
    dom = item.split("__")[0]
    return any(k.startswith(dom + "|") and item.endswith("__" + k.split("|")[1]) or item == dom + "__" + k.split("|")[1] for k in keys)

items = []

# ---------- A. experiment 102 Table-2 rescoring (H2, host-side tc_gateway route, now retired) ----------
SLUG = {"Claude Code (Opus 5, spec v2)": "claude_code", "Codex (GPT-5.6 Sol, spec v2)": "codex",
        "Leanstral (labs-leanstral-1-5-1, spec v2)": "leanstral", "Single-call baseline (Opus 5, spec v2)": "baseline"}
SYSDESC = {"claude_code": ("Claude Code + claude-opus-5 (max), spec v2", True),
           "codex": ("Codex + gpt-5.6-sol, spec v2", True),
           "baseline": ("single call claude-opus-5, spec v2", True),
           "leanstral": ("Leanstral labs-leanstral-1-5-1 (Mistral Lean specialist), spec v2", False)}
rec = defaultdict(lambda: {"H2_sol_high": {}, "H2_opus55_max": {}})
for run in ["t1_H2_sol_high", "t1_H2_opus55_max", "t2_H2_sol_high", "t2_H2_opus55_max"]:
    member = run.split("_", 1)[1]
    for f in glob.glob(f"{E102}/runs/{run}/receipts/*.json"):
        d = json.load(open(f))
        if d.get("kind") != "main":
            continue
        cur = rec[d["item"].split("__")[0] + "::" + d["task"]][member].get(d["repeat"])
        if cur is None or d.get("status") == "COMPLETE":
            rec[d["item"].split("__")[0] + "::" + d["task"]][member][d["repeat"]] = {"status": d.get("status"), "score_raw": d.get("score_raw"), "receipt": rel(f)}
vpc = {(r["system"], r["task_id"]): r for r in csv.DictReader(open(f"{E102}/results/tables/validated_per_candidate.csv"))}
n_mismatch_102 = 0
for r in csv.DictReader(open(f"{REPO}/paper_support/iclr2027/results/01_arm_convergence/per_task_factors_rerun.csv")):
    s = SLUG[r["system"]]
    item = f"{s}::{r['task_id']}"
    v = vpc.get((s, r["task_id"]), {})
    path = r["artifact_path"].replace("experiments/71_vals_ai_eval_code", "experiments/71_E2_valkyrie_harbor_vals_ai_eval_code") if r["artifact_path"] else None
    reps = {m: [int(x["score_raw"]) for k, x in sorted(rec[item][m].items()) if x["status"] == "COMPLETE" and x["score_raw"] not in (None, "", "None")]
            for m in rec[item]} if item in rec else {}
    recomputed = h2(reps.get("H2_sol_high"), reps.get("H2_opus55_max")) if reps else None
    if recomputed is not None and v.get("validated_tc") not in (None, "") and abs(recomputed - float(v["validated_tc"])) > 1e-9:
        n_mismatch_102 += 1
    items.append({
        "source": "exp102_table2_rescore", "benchmark": "VBV1", "system": s, "system_desc": SYSDESC[s][0], "is_frontier_model": SYSDESC[s][1],
        "task": r["task_id"], "split_domain": r["split"], "tier": v.get("tier"),
        "in_rating_task_set_25": norm(r["task_id"]) in RATING_KEYS, "in_validation_pool_tasks": norm(r["task_id"]) in POOL_KEYS,
        "file": {"local_path": path, "exists": bool(path and os.path.exists(f"{REPO}/{path}")),
                 "sha256": sha(f"{REPO}/{path}") if path and os.path.exists(f"{REPO}/{path}") else None},
        "judge": {"config": "H2 (exp 100 frozen; GPT-6 Sol high + Claude Opus 5.5 max, median of 3 per member, mean of members, /5)",
                  "route": "Vals gateway /query via exp95 tc_gateway (retired route, results kept with route disclosed)",
                  "status": v.get("status"), "repeats_0_5": reps,
                  "member_medians_0_5": {"H2_sol_high": v.get("sol_median") and float(v["sol_median"]) * 5, "H2_opus55_max": v.get("opus_median") and float(v["opus_median"]) * 5} if v.get("sol_median") else None,
                  "FSC_H2": float(v["validated_tc"]) if v.get("validated_tc") not in (None, "") else None,
                  "FSC_H2_recomputed_from_repeats": recomputed,
                  "FSC_deployed_old_judge": float(v["deployed_tc"]) if v.get("deployed_tc") not in (None, "") else None},
        "ic": {"IC_tests": float(r["ic_ap"]), "IC_proofs": float(r["ic_pp"])},
        "frozen_status": r["status"], "missing_cause": r["missing_cause"] or None,
        "human_rating": None, "human_rating_note": "unrated; in experiment 102 set A pool only if drawn (set A key sealed); no set-A sheet returned"})

# ---------- B. experiment 103 single-call + imported agent95 (H2 via vb103_judge, Valkyrie) ----------
cells = json.load(open(f"{X}/raw/cells103.json"))
files = {(f["suite"], f["model"], f["item"]): f for f in json.load(open(f"{X}/raw/files103.json"))}
by = defaultdict(lambda: defaultdict(dict))
for c in cells:
    key = (c["suite"], c["model"], c["item"])
    if c["status"] == "measured" or c["repeat"] not in by[key][c["member"]]:
        by[key][c["member"]][c["repeat"]] = c
fsc_files = {}
for f in glob.glob(f"{E103}/results/fsc_vbv*.json"):
    d = json.load(open(f))
    fsc_files[os.path.basename(f)] = d
def published(suite, model, item):
    if suite.startswith("vbv1"):
        cond = suite[len("vbv1"):]
        name = f"fsc_vbv1_{model}{('_' + cond) if cond else ''}.json".replace("__", "__")
        name = f"fsc_vbv1_{model}" + (f"_{cond}" if cond else "") + ".json"
    else:
        cond = suite[len("vbv2"):]
        name = "fsc_vbv2" + (cond if cond else "") + ".json"
    d = fsc_files.get(name)
    return (d or {}).get("per_task", {}).get(item), name
n_mismatch_103, n_unpub = 0, 0
for key, members in sorted(by.items()):
    suite, model, item = key
    reps = {m: [int(c["score_raw"]) for r, c in sorted(members[m].items()) if c["status"] == "measured" and c["score_raw"] not in (None, "", "None")] for m in members}
    recomputed = h2(reps.get("H2_sol_high"), reps.get("H2_opus55_max"))
    pub, pubfile = published(suite, model, item)
    if pub is None:
        n_unpub += 1
    elif recomputed is not None and abs(recomputed - pub["FSC"]) > 1e-9:
        n_mismatch_103 += 1
    fr = files.get(key)
    lp = f"{X}/files/{fr['archive_path']}" if fr and fr.get("archive_path") else None
    is_agent = suite.endswith("agent95") or suite.endswith("agent96") or suite.endswith("agent91cv4")
    mdl = model or {"vbv2_agent96": "gpt-6-luna-high", "vbv2_agent91cv4": "gemini-3.1-pro-high"}.get(suite) or (item.split("__")[0] if suite.startswith("vbv2") and "__" in item else None)
    items.append({
        "source": "exp103_" + suite, "benchmark": "VBV1" if suite.startswith("vbv1") else "VBV2",
        "system": (("agent:" if is_agent else "single_call:") + (mdl or "multiple (see item)")),
        "system_desc": ("Terminus2 agent + gpt-6-luna-high, frozen exp95 bytes" if suite.endswith("agent95") else
                        "Terminus2 agent + gpt-6-luna-high, frozen exp96 captures" if suite.endswith("agent96") else
                        "agent (exp91c v4) + gemini-3.1-pro-high" if suite.endswith("agent91cv4") else
                        f"one tool-free Valkyrie request to {mdl}" + (" (recovery_1 re-send)" if "recovery_1" in suite else "")),
        "is_frontier_model": (mdl or "") not in ("qwen3.6-27b-thinking",), "task": item,
        "in_rating_task_set_25": suite.startswith("vbv1") and item_key(item, RATING_KEYS),
        "in_validation_pool_tasks": suite.startswith("vbv1") and item_key(item, POOL_KEYS),
        "file": {"local_path": lp, "remote_path": fr["remote_path"] if fr else "VBV2: skampere1 .../103_*/private/vbv2_captures or raw_runs_vbv2 (not copied)",
                 "sha256": fr.get("sha256") if fr else None, "bytes": fr.get("bytes") if fr else None},
        "judge": {"config": "H2 (exp 100 frozen), identity-checked", "route": "Valkyrie (vb103_judge)", "repeats_0_5": reps,
                  "FSC_H2_recomputed_from_repeats": recomputed, "FSC_H2_published": pub and pub.get("FSC"),
                  "published_file": f"{rel(E103)}/results/{pubfile}", "complete": bool(pub and pub.get("complete"))},
        "human_rating": None})

# ---------- C. experiment 100 phase 7: VBV2 cells re-judged with H2 ----------
a = json.load(open(f"{E100}/results/phase7/phase7_analysis.json"))
inv = {c["cell_id"]: c for c in json.load(open(f"{E100}/results/phase7/INVENTORY.json"))["cells"]}
for cond in ("rs", "original"):
    for c in a["conditions"][cond]["cells"]:
        ic = inv.get(c["cell_id"], {})
        cand = ic.get("candidate") or {}
        items.append({
            "source": f"exp100_phase7_{cond}", "benchmark": c.get("benchmark"), "system": c.get("configuration"),
            "is_frontier_model": True, "task": c.get("task"), "cell_id": c["cell_id"],
            "file": {"remote_root": cand.get("root"), "files": cand.get("files"), "note": "multi-file VBV2 capture; not copied (host path from INVENTORY.json)"},
            "judge": {"config": "H2 (exp 100 frozen); packaging " + str(c.get("packaging")), "route": "Vals gateway (exp 100 phase 7)",
                      "repeats_0_1": c.get("repeats"), "member_medians_0_1": c.get("member_medians"),
                      "FSC_H2": c.get("validated_TC_fspecs"), "spam_free_FSC_H2": c.get("spam_free_TC_fspecs"),
                      "policy_rejected": c.get("policy_rejected"), "prompt_confound": c.get("prompt_confound")},
            "ic": {"IC_tests": c.get("IC_tests"), "IC_proofs": c.get("IC_proofs")}, "human_rating": None})

# ---------- D. experiment 107 / 102 rating sets B and N: files public (blinded), judge values SEALED ----------
for setname, d in (("N", f"{E102}/human_round/sample_setN/packet"), ("B", f"{E102}/human_round/sample_setB/packet")):
    for folder in sorted(os.listdir(d)):
        for p in sorted(glob.glob(f"{d}/{folder}/agent_lean/*.lean")):
            items.append({
                "source": f"exp107_set{setname}_packet", "benchmark": "VBV1", "system": "SEALED (blinded; one of: " +
                ("t2_fable51, t2_astra, t2_grok47, t2_gemini_frontier [internal Google pre-release], t2_kimik3" if setname == "N" else "t2_fable51, t2_astra, terminus2_qwen") + ")",
                "is_frontier_model": None if setname == "B" else "4 of 5 systems frontier; Kimi K3 open-weights",
                "task": rating25.get(folder), "packet_item": os.path.basename(p)[:-5], "in_rating_task_set_25": True,
                "file": {"local_path": rel(p), "sha256": sha(p), "bytes": os.path.getsize(p)},
                "judge": {"status": "SEALED", "where": "skampere2:/lfs/skampere2/0/brando9/veribench_vb107/experiments/107_*/private/sealed/{setN,setN_final,setB,t2v2,t2v3,turncap,fsc_per_item.json}",
                          "commitments": [rel(x) for x in sorted(glob.glob(f"{E107}/results/*COMMITMENT*.json"))],
                          "why_not_read": "PROTOCOL amendments 4/10/11: per-item FSC sealed until every set-B/set-N rating sheet is in; Brando is rater A1 and has not rated"},
                "human_rating": None, "human_rating_note": "set-N round open (closes 11-06-2026); 0 sheets returned as of 10-09-2026"})

manifest = {
    "tldr": "Frontier-model (FM) VeriBench Lean outputs scored by experiment 100's frozen H2 judge, with per-repeat judge ratings and file paths; human ratings of FM outputs: none exist yet (10-09-2026).",
    "written": "10-09-2026", "model_calls": 0,
    "judge_definition": "H2 ensemble (exp 100): GPT-6 Sol high + Claude Opus 5.5 max, prompt family H2_human_mirror_conventions_demos, per-member median of 3 integer 0-5 ratings, mean of members, /5",
    "validation_pool_reference": {"items": rel(f"{E100}/inputs/items.jsonl"), "n_items": len(pool_items), "tasks": pool_tasks,
                                  "note": "75 human-rated items = 25 VBV1 tasks x 3 Claude 3.7 Sonnet (May-2026) outputs; candidates in inputs/candidates/"},
    "rating_task_set_25": rating25,
    "human_ratings_of_FM_outputs": {
        "exp108_pilot": "sheet private/packet/pilot_rating_sheet.csv has 2 rows, 0 filled (A1 has not rated); pilot is practice-only and never enters analysis; no H2 judge run on pilot files",
        "exp102_setN": "0 returned sheets (warm-up sent 10-08; A1 sheet human_round/private_A1/setN_final_A1_rating_sheet.csv does not exist yet; ROSTER has no ratings)",
        "exp102_setA_setB": "packets exist; 0 sheets returned; set B superseded by set N (C14)",
        "verdict": "NO human ratings of FM outputs exist as of 10-09-2026"},
    "checks": {"exp102_items_where_recomputed_H2_differs_from_published": n_mismatch_102,
               "exp103_items_where_recomputed_H2_differs_from_published": n_mismatch_103,
               "exp103_items_without_published_per_task_row": n_unpub},
    "items": items}
json.dump(manifest, open(f"{X}/fm_manifest.json", "w"), indent=1)
from collections import Counter
cnt = Counter((i["source"], i["system"]) for i in items)
for k, v in sorted(cnt.items()):
    print(v, *k)
print("checks", manifest["checks"], "n_items", len(items))
