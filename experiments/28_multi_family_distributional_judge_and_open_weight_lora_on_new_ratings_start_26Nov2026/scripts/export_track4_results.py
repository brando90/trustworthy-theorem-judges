#!/usr/bin/env python3
"""Experiment 28: Export Track 4A compact JSONLs, compute k=3 repeat stability ICC(1,1),
merge Track 4B LoRA shards, and verify 175/175 completeness across all 5 lanes.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import numpy as np

EXP28 = Path(__file__).resolve().parents[1]
RES_DIR = EXP28 / "results"
CACHE_DIR = Path("/tmp/exp28_cache")


def icc_one_way(mat: np.ndarray) -> float:
    """One-way random-effects single-measure ICC(1,1) for matrix [n_items, k_repeats]."""
    n, k = mat.shape
    row_means = mat.mean(axis=1)
    grand = mat.mean()
    ssb = k * float(np.sum((row_means - grand) ** 2))
    ssw = float(np.sum((mat - row_means[:, None]) ** 2))
    msb = ssb / max(n - 1, 1)
    msw = ssw / max(n * (k - 1), 1)
    denom = msb + (k - 1) * msw
    return float((msb - msw) / denom) if denom > 0 else float("nan")


def export_track4a() -> dict[str, dict[str, dict]]:
    lane_maps: dict[str, dict[str, dict]] = {}
    for lane in ("codex_astra", "agy_argon", "agy_opus"):
        src = CACHE_DIR / f"h4_{lane}.jsonl"
        raw_sha = hashlib.sha256(src.read_bytes()).hexdigest()
        by_id: dict[str, dict] = {}
        for line in src.read_text().splitlines():
            if not line.strip():
                continue
            o = json.loads(line)
            if o.get("status") != "ok":
                continue
            by_id[o["id"]] = {
                "id": o["id"],
                "lane": o["lane"],
                "status": "ok",
                "parsed": o["parsed"],
                "elapsed_seconds": o.get("elapsed_seconds"),
                "requests_sha256": o.get("requests_sha256"),
                "raw_log_sha256": raw_sha,
            }
        assert len(by_id) == 175, f"Expected 175 ok rows for {lane}, got {len(by_id)}"
        dst = RES_DIR / f"h4_{lane}_11-26-2026.jsonl"
        with dst.open("w", encoding="utf-8") as f:
            for iid in sorted(by_id):
                f.write(json.dumps(by_id[iid], ensure_ascii=False) + "\n")
        lane_maps[lane] = by_id
        print(f"[export] {dst.name}: 175/175 ok ({dst.stat().st_size / 1024:.1f} KB)")
    return lane_maps


def compute_repeat_stability(lane_maps: dict[str, dict[str, dict]]) -> None:
    rep_ids = [l.strip() for l in (CACHE_DIR / "repeat15_ids.txt").read_text().splitlines() if l.strip()]
    assert len(rep_ids) == 15
    summary = {"n_items": len(rep_ids), "k_repeats": 3, "items": rep_ids, "lanes": {}}

    for lane, rep_file, base_key in (
        ("codex_astra", "rep_codex_astra.jsonl", "codex_astra"),
        ("agy_argon", "rep_agy_argon.jsonl", "agy_argon"),
        ("claude_opus_cli", "rep_claude_opus_cli.jsonl", "agy_opus"),
    ):
        rp = CACHE_DIR / rep_file
        if not rp.exists():
            continue
        reps: dict[tuple[str, str], dict] = {}
        for line in rp.read_text().splitlines():
            if not line.strip():
                continue
            o = json.loads(line)
            if o.get("status") == "ok" and "#r" in o["id"]:
                base, rtag = o["id"].split("#", 1)
                reps[(base, rtag)] = o["parsed"]

        mat_e = np.zeros((len(rep_ids), 3), dtype=np.float64)
        mat_s = np.zeros((len(rep_ids), 3), dtype=np.float64)
        for i, iid in enumerate(rep_ids):
            r0 = lane_maps[base_key][iid]["parsed"]
            r1 = reps[(iid, "r1")]
            r2 = reps[(iid, "r2")]
            mat_e[i] = [r0["expected_score"], r1["expected_score"], r2["expected_score"]]
            mat_s[i] = [r0["final_score_0_5"], r1["final_score_0_5"], r2["final_score_0_5"]]

        sd_e = mat_e.std(axis=1, ddof=1)
        rng_e = mat_e.max(axis=1) - mat_e.min(axis=1)
        sd_s = mat_s.std(axis=1, ddof=1)
        summary["lanes"][lane] = {
            "icc_1_1_expected_score": round(icc_one_way(mat_e), 6),
            "icc_1_1_final_score": round(icc_one_way(mat_s), 6),
            "mean_within_item_sd_E": round(float(sd_e.mean()), 4),
            "max_within_item_sd_E": round(float(sd_e.max()), 4),
            "mean_within_item_range_E": round(float(rng_e.mean()), 4),
            "mean_within_item_sd_final": round(float(sd_s.mean()), 4),
            "exact_integer_agreement_rate": round(float(np.mean(np.ptp(mat_s, axis=1) == 0)), 4),
        }

    # 3-item harness parity check (agy vs claude_opus_cli)
    ov_path = CACHE_DIR / "h4_opus_harness_overlap.jsonl"
    if ov_path.exists():
        ov_rows = []
        for line in ov_path.read_text().splitlines():
            if not line.strip():
                continue
            o = json.loads(line)
            if o.get("status") == "ok":
                iid = o["id"]
                a = lane_maps["agy_opus"][iid]["parsed"]
                c = o["parsed"]
                ov_rows.append({
                    "item": iid,
                    "agy_score": a["final_score_0_5"],
                    "agy_E": round(a["expected_score"], 4),
                    "claude_cli_score": c["final_score_0_5"],
                    "claude_cli_E": round(c["expected_score"], 4),
                    "abs_diff_E": round(abs(a["expected_score"] - c["expected_score"]), 4),
                })
        summary["opus_harness_overlap_agy_vs_claude_cli"] = ov_rows

    out_p = RES_DIR / "repeat_stability_11-26-2026.json"
    out_p.write_text(json.dumps(summary, indent=2))
    print(f"[repeat] Saved {out_p}")


def merge_lora_shards() -> None:
    merged = {}
    for obj in ("ce", "rps", "pearson"):
        pa = json.loads((RES_DIR / f"qwen3_4b_lora_{obj}_a.json").read_text())[obj]
        pb = json.loads((RES_DIR / f"qwen3_4b_lora_{obj}_b.json").read_text())[obj]
        comb = {
            "exp27_selected_hp": pa["exp27_selected_hp"],
            "exp27_test_preds": pa["exp27_test_preds"],
            "cv5_fold_hps": sorted(pa["cv5_fold_hps"] + pb["cv5_fold_hps"], key=lambda x: x["fold"]),
            "cv5_oof_preds": {**pa["cv5_oof_preds"], **pb["cv5_oof_preds"]},
        }
        assert len(comb["exp27_test_preds"]) == 70, f"{obj} test len={len(comb['exp27_test_preds'])}"
        assert len(comb["cv5_oof_preds"]) == 175, f"{obj} oof len={len(comb['cv5_oof_preds'])}"
        merged[obj] = comb
    out_p = RES_DIR / "qwen3_4b_lora_ce_rps_pearson.json"
    out_p.write_text(json.dumps(merged, indent=2))
    print(f"[lora] Merged 3 objectives -> {out_p} ({out_p.stat().st_size / 1024:.1f} KB)")


def main() -> None:
    lane_maps = export_track4a()
    compute_repeat_stability(lane_maps)
    merge_lora_shards()
    import sys
    sys.path.insert(0, str(EXP28 / "scripts"))
    import data_exp28 as de
    D = de.load_bundle(include_test=True, require_complete=True)
    print(f"[verify] Bundle complete: n={D['n']} lanes={D['has_lanes']} qwen={D['has_qwen']}")


if __name__ == "__main__":
    main()
