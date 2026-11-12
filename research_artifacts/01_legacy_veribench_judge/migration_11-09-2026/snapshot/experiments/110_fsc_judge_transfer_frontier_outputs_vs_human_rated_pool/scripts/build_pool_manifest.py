# TLDR: build the 75-item judge-validation pool manifest (zero model calls) from experiment 100 inputs and H2 run outputs.
import csv, json, hashlib, os, sys, statistics
R = "/Users/brandomiranda/veribench"
E = R + "/experiments/100_karpathy_recipe_tc_judge_search_human_train_val_test"
OUT = sys.argv[1]
items = [json.loads(l) for l in open(E + "/inputs/items.jsonl")]
runs = {"train": ("p3_i2_H2_sol_high", "p3_i3_H2_opus55_max"),
        "val": ("p4_val_H2_sol_high", "p4_val_H2_opus55_max"),
        "test": ("p5_test_H2_sol_high", "p5_test_H2_opus55_max")}
def load(run):
    return {r["item"]: r for r in csv.DictReader(open(f"{E}/runs/{run}/per_item.csv"))}
per = {}
for sp, (s, o) in runs.items():
    per[sp] = (load(s), load(o))
def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()
rows = []; mism = 0
for it in items:
    sp = it["split"]; s, o = per[sp]
    rs, ro = s[it["item"]], o[it["item"]]
    cand = f"{E}/{it['candidate_path']}"
    ok = sha(cand) == it["candidate_sha256"]; mism += (not ok)
    sm, om = float(rs["judge_median"]), float(ro["judge_median"])
    rows.append({
        "item": it["item"], "task": it["task"], "domain": it["domain"], "split": sp,
        "agent_sample": it["agent_sample"],
        "candidate_path": cand, "candidate_sha256": it["candidate_sha256"], "candidate_sha_verified": ok,
        "reference_rater_era_path": f"{E}/{it['ref_ann_path']}",
        "reference_snapshot_db1b16e87_path": f"{E}/{it['ref_snap_path']}",
        "python_rater_era_path": f"{E}/{it['py_ann_path']}",
        "ref_status": it["ref_status"], "ref_placeholder_at_rating": it["ref_placeholder_at_annotation"],
        "ref_ambiguous_in_window": it["ref_ambiguous_in_window"],
        "n_ref_theorems_rater_era": it["n_ref_theorems_ann"], "n_cand_theorems": it["n_cand_theorems"],
        "cand_sorry_count": it["cand_sorry_count"], "cand_lines": it["cand_lines"],
        "ratings_0_5": {f"participant{i}": it[f"p{i}"] for i in range(1, 6)},
        "expert_raters_used_in_target": "participant1-3 (available ones)", "expert_n": it["expert_n"],
        "human_target_0_1": it["target_expert"], "all5_mean_0_1": it["target_all5"],
        "h2_sol_high": {"run": runs[sp][0], "median_0_1": sm, "raw_repeats": rs["raw_repeats"].split()},
        "h2_opus55_max": {"run": runs[sp][1], "median_0_1": om, "raw_repeats": ro["raw_repeats"].split()},
        "h2_ensemble_0_1": round((sm + om) / 2, 9),
    })
def summ(sp):
    rr = [r for r in rows if sp in (None, r["split"])]
    j = [r["h2_ensemble_0_1"] for r in rr]; h = [r["human_target_0_1"] for r in rr]
    return {"n_items": len(rr), "n_tasks": len({r["task"] for r in rr}),
            "mean_judge": statistics.mean(j), "mean_human": statistics.mean(h),
            "mean_bias_judge_minus_human": statistics.mean(j) - statistics.mean(h)}
man = {
  "tldr": "75-item FSC judge-validation pool (25 VBV1 tasks x 3 claude-3-7-sonnet-20250219 samples at T=0.7; 74/75 recorded in manifest, binary_search__agent0 attributed only by README) with per-rater ratings, split, and experiment 100 H2 ensemble scores. Zero model calls.",
  "created_by": "build_manifest.py (scratchpad x110), 10-09-2026",
  "sources": {
    "items_jsonl": E + "/inputs/items.jsonl",
    "inputs_manifest": E + "/inputs/MANIFEST.json",
    "provenance": E + "/inputs/provenance.json",
    "candidates_dir": E + "/inputs/candidates",
    "references_rater_era_dir": E + "/inputs/references/annotation",
    "references_snapshot_dir": E + "/inputs/references/snapshot",
    "python_dir": E + "/inputs/python",
    "splits_json": R + "/experiments/75_J1_validating_formal_spec_judge_train_val_test/results/splits.json",
    "ratings_items_csv": R + "/experiments/75_J1_validating_formal_spec_judge_train_val_test/data_description/items.csv",
    "rating_data_doc": R + "/experiments/75_J1_validating_formal_spec_judge_train_val_test/HUMAN_JUDGMENT_DATA.md",
    "raw_rater_tsvs": R + "/veribench_dataset/human_labels/participant{1..5}_*.tsv",
    "candidate_pool_readme": R + "/veribench_dataset/human_labels/calibration/README.md",
    "generation_manifest": R + "/veribench_dataset/human_labels/calibration/generated_agents/generation_manifest.json",
    "h2_configs": [E + "/configs/H2_sol_high.json", E + "/configs/H2_opus55_max.json"],
    "h2_runs": {k: [E + "/runs/" + x for x in v] for k, v in runs.items()},
    "h2_ensembles": [E + f"/results/ensembles/{s}_H2_sol_plus_H2_opus.json" for s in ("train", "val", "test")],
    "test_receipt": E + "/results/TEST_RECEIPT.json",
    "validation_selection": E + "/results/VALIDATION_SELECTION.json",
    "train_test_gap_audit": E + "/results/sanity/TRAIN_TEST_GAP.md",
    "tie_fix_note": R + "/experiments/102_rescore_vbv1_paper_fsc_with_validated_judge_rewrite_tmlr_icml/REPORT.md (finding 1)",
  },
  "notes": [
    "Judge scores are 0-1 (0-5 / 5). Ensemble = mean of the two member medians (median of k=3 each); rounded to 1e-9 here, which is the experiment 102 tie fix (validation Spearman 0.880 vs 0.870 reported in exp 100 files).",
    "Human target = mean of available participant 1-3 ratings / 5; participant 3 missing all easy_set and security_set tasks (30 items -> expert_n=2). Participants 4,5 are secondary only.",
    "Placeholder references at rating time (Pre/Post := True) on five security_set tasks; five cs_set sorting/search tasks had references change during the rating window (ref_ambiguous_in_window).",
  ],
  "summary": {"train": summ("train"), "val": summ("val"), "test": summ("test"), "all": summ(None)},
  "candidate_sha_mismatches": mism,
  "items": rows,
}
json.dump(man, open(OUT, "w"), indent=1)
print(json.dumps(man["summary"], indent=1), "mismatches", mism, "rows", len(rows))
print(sorted({r["split"] for r in rows}), {sp: len({r['task'] for r in rows if r['split']==sp}) for sp in runs})
