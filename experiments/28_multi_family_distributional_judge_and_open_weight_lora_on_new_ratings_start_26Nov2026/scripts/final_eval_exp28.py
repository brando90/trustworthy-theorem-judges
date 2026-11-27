"""Experiment 28: Held-out & Nested 5-Fold OOF Evaluation (run ONLY after FREEZE_11-26-2026.md).

Evaluates:
  - Set-Aware Constant, Global Constant, Exp 27 F8_both_h3 baseline
  - Frozen Exp 28 Multi-Family + Qwen3-8B Calibrated Judge (Set-Aware & Global) on:
      (1) exp27_split (30 train+val tasks -> 20 held-out test tasks)
      (2) cv5_fold nested OOF across all 50 tasks (175 artifacts)
  - Priority 2 vs 4 comparison on both (a) (M+K) calibrator head (CE vs RPS vs Pearson)
    and (b) End-to-End Qwen3-4B Top-4-Block LoRA (CE vs RPS vs Pearson)
  - Single-pass Qwen3 logit readout vs M=1 argmax one-hot ablation.
"""
from __future__ import annotations

import json
import sys
import time
from pathlib import Path
import numpy as np

EXP27_SCRIPTS = Path(__file__).resolve().parents[2] / "27_build_a_judge_that_beats_the_constant_forecast_on_held_out_tasks_old_new_ratings_start_24Nov2026" / "scripts"
sys.path.insert(0, str(EXP27_SCRIPTS))
import judgelib as jl27  # noqa: E402

import data_exp28 as de  # noqa: E402
import distlib as dl  # noqa: E402
from search_inner_cv import CANDIDATE_SPECS, build_lp_and_x, make_4fold_inner_tasks  # noqa: E402


def slice_bundle(D: dict, mask: np.ndarray) -> dict:
    idx = np.where(mask)[0]
    return {
        "rows": [D["rows"][i] for i in idx],
        "n": int(len(idx)),
        "item": D["item"][idx],
        "task": D["task"][idx],
        "set": D["set"][idx],
        "exp27_split": D["exp27_split"][idx],
        "cv5_fold": D["cv5_fold"][idx],
        "is_new": D["is_new"][idx],
        "P": D["P"][idx],
        "C": D["C"][idx],
        "feats": {k: v[idx] for k, v in D["feats"].items()},
        "dists": {k: v[idx] for k, v in D["dists"].items()},
    }


def select_best_on_subset(D_sub: dict, set_aware_filter: bool) -> dict:
    """Strictly select candidate + HPs inside a training subset using 4 stratified inner folds."""
    inner_f = make_4fold_inner_tasks(D_sub)
    best = None
    for cname, dkeys, fkeys, sa in CANDIDATE_SPECS:
        if sa != set_aware_filter:
            continue
        lp, x = build_lp_and_x(D_sub, dkeys, fkeys)
        for obj in ("ce", "rps"):
            for alpha in (0.3, 1.0, 3.0, 10.0):
                for eta in (0.0, 0.05, 0.12):
                    for uq in (True, False):
                        q_oof = np.zeros((D_sub["n"], 6), dtype=np.float64)
                        for f in range(4):
                            itr = inner_f != f
                            iva = inner_f == f
                            cal = dl.MKCalibrator(
                                objective=obj, alpha=alpha, alpha_a=0.05,
                                dirichlet_eta=eta, use_quad=uq, set_aware_prior=sa,
                            ).fit(lp[itr], x[itr], D_sub["is_new"][itr], D_sub["P"][itr])
                            q_oof[iva] = cal.predict(lp[iva], x[iva], D_sub["is_new"][iva])
                        sc = float(dl.rps_items(D_sub["P"], q_oof).mean())
                        if best is None or sc < best["inner_rps"]:
                            best = {
                                "inner_rps": sc, "candidate": cname, "dist_keys": dkeys,
                                "feat_keys": fkeys, "objective": obj, "alpha": alpha,
                                "dirichlet_eta": eta, "use_quad": uq, "set_aware": sa,
                            }
    assert best is not None
    return best


def calibration_bins(p_emp: np.ndarray, q: np.ndarray) -> list[dict]:
    eq = q @ dl.GRID
    ep = p_emp @ dl.GRID
    bins = [(0.0, 1.0), (1.0, 2.0), (2.0, 3.0), (3.0, 4.0), (4.0, 5.0001)]
    out = []
    for lo, hi in bins:
        m = (eq >= lo) & (eq < hi)
        if not m.any():
            out.append({"bin": f"[{lo:.0f},{min(hi, 5.0):.0f}]", "n": 0})
        else:
            out.append({
                "bin": f"[{lo:.0f},{min(hi, 5.0):.0f}]",
                "n": int(m.sum()),
                "mean_pred": round(float(eq[m].mean()), 4),
                "mean_human": round(float(ep[m].mean()), 4),
                "diff": round(float(eq[m].mean() - ep[m].mean()), 4),
            })
    return out


def eval_constant_preds(D: dict, tr_mask: np.ndarray, te_mask: np.ndarray, set_aware: bool) -> np.ndarray:
    c_tr = D["C"][tr_mask]
    pg = dl.smooth(c_tr.sum(0) / c_tr.sum())
    if not set_aware:
        return np.broadcast_to(pg[None, :], (int(te_mask.sum()), 6)).copy()
    out = []
    for f in D["is_new"][te_mask]:
        m = tr_mask & (D["is_new"] == f)
        cm = D["C"][m].sum(0)
        out.append(dl.smooth(cm / cm.sum()) if cm.sum() > 0 else pg)
    return np.stack(out)


def eval_exp27_f8(D: dict, tr_mask: np.ndarray, te_mask: np.ndarray) -> np.ndarray:
    """Reproduce Exp 27 frozen F8_both_h3 Ordinal (alpha=1.0, m=0.10) cleanly using updated ratings."""
    D27 = {
        "P": D["P"],
        "C": D["C"],
        "astra": D["feats"]["h2_astra"],
        "opus": D["feats"]["h2_opus"],
        "h3s": D["feats"]["h3_s"],
        "h3e": D["feats"]["h3_e"],
    }
    tr_idx = np.where(tr_mask)[0]
    te_idx = np.where(te_mask)[0]
    model = jl27.Ordinal(["astra", "opus", "h3s", "h3e"], alpha=1.0, m=0.10).fit(D27, tr_idx)
    return model.predict(D27, te_idx)


def eval_mk_model(D: dict, spec: dict, tr_mask: np.ndarray, te_mask: np.ndarray, obj_override: str | None = None) -> np.ndarray:
    lp, x = build_lp_and_x(D, spec["dist_keys"], spec["feat_keys"])
    obj = obj_override or spec["objective"]
    cal = dl.MKCalibrator(
        objective=obj,
        alpha=spec["alpha"],
        alpha_a=0.05,
        dirichlet_eta=spec["dirichlet_eta"],
        use_quad=spec["use_quad"],
        set_aware_prior=spec["set_aware"],
    ).fit(lp[tr_mask], x[tr_mask], D["is_new"][tr_mask], D["P"][tr_mask])
    return cal.predict(lp[te_mask], x[te_mask], D["is_new"][te_mask])


def posthoc_affine_to_probs_inner_oof(D: dict, spec: dict, tr_mask: np.ndarray, te_mask: np.ndarray, q_te_raw: np.ndarray) -> np.ndarray:
    """Fit post-hoc 1D calibrator on inner-OOF Pearson predictions inside `tr` (zero in-sample leakage)."""
    D_tr = slice_bundle(D, tr_mask)
    inner_f = make_4fold_inner_tasks(D_tr)
    lp_tr, x_tr_raw = build_lp_and_x(D_tr, spec["dist_keys"], spec["feat_keys"])
    q_tr_oof = np.zeros((D_tr["n"], 6), dtype=np.float64)
    for inf in range(4):
        itr = inner_f != inf
        iva = inner_f == inf
        c_p = dl.MKCalibrator(
            objective="pearson", alpha=spec["alpha"], alpha_a=0.05,
            dirichlet_eta=spec["dirichlet_eta"], use_quad=spec["use_quad"], set_aware_prior=spec["set_aware"],
        ).fit(lp_tr[itr], x_tr_raw[itr], D_tr["is_new"][itr], D_tr["P"][itr])
        q_tr_oof[iva] = c_p.predict(lp_tr[iva], x_tr_raw[iva], D_tr["is_new"][iva])

    lp_empty_tr = np.zeros((D_tr["n"], 0, 6))
    lp_empty_te = np.zeros((len(q_te_raw), 0, 6))
    x_tr = np.column_stack([q_tr_oof @ dl.GRID, D_tr["is_new"]])
    x_te = np.column_stack([q_te_raw @ dl.GRID, D["is_new"][te_mask]])
    cal = dl.MKCalibrator(objective="ce", alpha=0.3, alpha_a=0.05, dirichlet_eta=0.05, use_quad=True, set_aware_prior=True)
    cal.fit(lp_empty_tr, x_tr, D_tr["is_new"], D_tr["P"])
    return cal.predict(lp_empty_te, x_te, D["is_new"][te_mask])


def summarize_block(name: str, tasks: np.ndarray, p_emp: np.ndarray, q: np.ndarray, q_const: np.ndarray, q_f8: np.ndarray, seed: int = 20261126) -> dict:
    b_const = dl.task_cluster_bootstrap(tasks, p_emp, q, q_ref=q_const, draws=10000, seed=seed)
    b_f8 = dl.task_cluster_bootstrap(tasks, p_emp, q, q_ref=q_f8, draws=10000, seed=seed)
    return {
        "name": name,
        "point": b_const["point"],
        "ci95": b_const["ci95"],
        "vs_const_set": b_const["paired_vs_ref"],
        "vs_exp27_f8": b_f8["paired_vs_ref"],
    }


def main() -> None:
    t0 = time.time()
    D = de.load_bundle(include_test=True)
    search_json = json.loads((de.RES_DIR / "inner_cv_search_11-26-2026.json").read_text())
    winner_set = search_json["winner_set_aware"]
    winner_global = search_json["winner_global"]

    lines: list[str] = []
    def log(msg: str) -> None:
        print(msg, flush=True)
        lines.append(msg)

    log(f"Experiment 28 Final Evaluation (n={D['n']} items, {len(set(D['task']))} tasks)")
    log(f"Frozen Set-Aware Winner: {winner_set['candidate']} ({winner_set['objective']}, alpha={winner_set['alpha']}, eta={winner_set['dirichlet_eta']}, quad={winner_set['use_quad']})")
    log(f"Frozen Global Winner:    {winner_global['candidate']} ({winner_global['objective']}, alpha={winner_global['alpha']}, eta={winner_global['dirichlet_eta']}, quad={winner_global['use_quad']})")

    # 1) exp27_split (train+val 30 tasks -> test 20 tasks)
    tr27 = D["exp27_split"] != "test"
    te27 = D["exp27_split"] == "test"
    tasks_te = D["task"][te27]
    P_te = D["P"][te27]

    q_const_s_te = eval_constant_preds(D, tr27, te27, True)
    q_const_g_te = eval_constant_preds(D, tr27, te27, False)
    q_f8_te = eval_exp27_f8(D, tr27, te27)
    q_win_s_te = eval_mk_model(D, winner_set, tr27, te27)
    q_win_g_te = eval_mk_model(D, winner_global, tr27, te27)
    best_h4_only = min(
        (search_json["best_by_family"][k] for k in ("C7_h4_3fam_uncert__ce", "C7_h4_3fam_uncert__rps") if k in search_json["best_by_family"]),
        key=lambda r: r["inner_cv"]["RPS"],
    )
    best_c9b = min(
        (search_json["best_by_family"][k] for k in ("C9b_h4_astra_argon_q8b__ce", "C9b_h4_astra_argon_q8b__rps") if k in search_json["best_by_family"]),
        key=lambda r: r["inner_cv"]["RPS"],
    )
    q_h4_only_te = eval_mk_model(D, best_h4_only, tr27, te27)
    q_c9b_te = eval_mk_model(D, best_c9b, tr27, te27)

    exp27_summary = {
        "n_test_items": int(te27.sum()),
        "n_test_tasks": int(len(set(tasks_te))),
        "constant_global": summarize_block("constant_global", tasks_te, P_te, q_const_g_te, q_const_s_te, q_f8_te),
        "constant_set_aware": summarize_block("constant_set_aware", tasks_te, P_te, q_const_s_te, q_const_s_te, q_f8_te),
        "exp27_f8_refit250": summarize_block("exp27_f8_refit250", tasks_te, P_te, q_f8_te, q_const_s_te, q_f8_te),
        "h4_3fam_only": summarize_block("h4_3fam_only", tasks_te, P_te, q_h4_only_te, q_const_s_te, q_f8_te),
        "c9b_zero_opus_fallback": summarize_block("c9b_zero_opus_fallback", tasks_te, P_te, q_c9b_te, q_const_s_te, q_f8_te),
        "winner_global": summarize_block("winner_global", tasks_te, P_te, q_win_g_te, q_const_s_te, q_f8_te),
        "winner_set_aware": summarize_block("winner_set_aware", tasks_te, P_te, q_win_s_te, q_const_s_te, q_f8_te),
        "winner_set_aware_seed20261124": summarize_block("winner_set_aware_seed20261124", tasks_te, P_te, q_win_s_te, q_const_s_te, q_f8_te, seed=20261124),
    }

    log("\n=== PART 1: exp27_split Held-Out Test (20 tasks) ===")
    for k, blk in exp27_summary.items():
        if not isinstance(blk, dict):
            continue
        p = blk["point"]
        vc = blk["vs_const_set"]["dRPS"]
        vf = blk["vs_exp27_f8"]["dRPS"]
        log(f"  {k:20s}: RPS={p['RPS']:.4f} CE={p['CE']:.4f} TVD={p['TVD']:.4f} Brier={p['Brier']:.4f} r={p['Pearson']:.3f} rho={p['Spearman']:.3f} ICC_A={p['ICC_A1']:.3f} Bias={p['Bias']:+.3f} (J={p['Mean_Judge']:.2f}, H={p['Mean_Human']:.2f}) | dRPS_const={vc['point']:+.4f} {vc['ci95']} p={vc['p_val_two_sided']:.4g} | dRPS_f8={vf['point']:+.4f} {vf['ci95']}")

    # 2) cv5_fold Pooled Nested 5-Fold OOF across all 50 tasks (175 artifacts)
    q_const_s_cv = np.zeros((D["n"], 6))
    q_const_g_cv = np.zeros((D["n"], 6))
    q_f8_cv = np.zeros((D["n"], 6))
    q_win_s_cv = np.zeros((D["n"], 6))
    q_win_g_cv = np.zeros((D["n"], 6))
    q_nested_s_cv = np.zeros((D["n"], 6))
    q_nested_g_cv = np.zeros((D["n"], 6))
    q_c9b_cv = np.zeros((D["n"], 6))
    q_mk_ce_cv = np.zeros((D["n"], 6))
    q_mk_rps_cv = np.zeros((D["n"], 6))
    q_mk_pear_raw_cv = np.zeros((D["n"], 6))
    q_mk_pear_cal_cv = np.zeros((D["n"], 6))
    nested_selections = []

    # True nested candidate+HP re-selection inside each 4-fold training set of cv5_fold
    for f in range(5):
        tr = D["cv5_fold"] != f
        te = D["cv5_fold"] == f
        D_tr = slice_bundle(D, tr)
        n_best_s = select_best_on_subset(D_tr, set_aware_filter=True)
        n_best_g = select_best_on_subset(D_tr, set_aware_filter=False)
        nested_selections.append({"fold": f, "set_aware": n_best_s, "global": n_best_g})

        q_const_s_cv[te] = eval_constant_preds(D, tr, te, True)
        q_const_g_cv[te] = eval_constant_preds(D, tr, te, False)
        q_f8_cv[te] = eval_exp27_f8(D, tr, te)
        q_win_s_cv[te] = eval_mk_model(D, winner_set, tr, te)
        q_win_g_cv[te] = eval_mk_model(D, winner_global, tr, te)
        q_nested_s_cv[te] = eval_mk_model(D, n_best_s, tr, te)
        q_nested_g_cv[te] = eval_mk_model(D, n_best_g, tr, te)
        q_c9b_cv[te] = eval_mk_model(D, best_c9b, tr, te)
        q_mk_ce_cv[te] = eval_mk_model(D, winner_set, tr, te, obj_override="ce")
        q_mk_rps_cv[te] = eval_mk_model(D, winner_set, tr, te, obj_override="rps")
        q_mk_pear_raw_cv[te] = eval_mk_model(D, winner_set, tr, te, obj_override="pearson")
        q_mk_pear_cal_cv[te] = posthoc_affine_to_probs_inner_oof(D, winner_set, tr, te, q_mk_pear_raw_cv[te])

    cv5_summary = {
        "n_items": int(D["n"]),
        "n_tasks": int(len(set(D["task"]))),
        "constant_global": summarize_block("constant_global", D["task"], D["P"], q_const_g_cv, q_const_s_cv, q_f8_cv),
        "constant_set_aware": summarize_block("constant_set_aware", D["task"], D["P"], q_const_s_cv, q_const_s_cv, q_f8_cv),
        "exp27_f8": summarize_block("exp27_f8", D["task"], D["P"], q_f8_cv, q_const_s_cv, q_f8_cv),
        "c9b_zero_opus_fallback": summarize_block("c9b_zero_opus_fallback", D["task"], D["P"], q_c9b_cv, q_const_s_cv, q_f8_cv),
        "winner_global_fixed": summarize_block("winner_global_fixed", D["task"], D["P"], q_win_g_cv, q_const_s_cv, q_f8_cv),
        "winner_set_aware_fixed": summarize_block("winner_set_aware_fixed", D["task"], D["P"], q_win_s_cv, q_const_s_cv, q_f8_cv),
        "nested_winner_global": summarize_block("nested_winner_global", D["task"], D["P"], q_nested_g_cv, q_const_s_cv, q_f8_cv),
        "nested_winner_set_aware": summarize_block("nested_winner_set_aware", D["task"], D["P"], q_nested_s_cv, q_const_s_cv, q_f8_cv),
        "head_ce": summarize_block("head_ce", D["task"], D["P"], q_mk_ce_cv, q_const_s_cv, q_f8_cv),
        "head_rps": summarize_block("head_rps", D["task"], D["P"], q_mk_rps_cv, q_const_s_cv, q_f8_cv),
        "head_pearson_raw": summarize_block("head_pearson_raw", D["task"], D["P"], q_mk_pear_raw_cv, q_const_s_cv, q_f8_cv),
        "head_pearson_postcal": summarize_block("head_pearson_postcal", D["task"], D["P"], q_mk_pear_cal_cv, q_const_s_cv, q_f8_cv),
    }

    log("\n=== PART 2: All-50-Task Nested 5-Fold OOF (175 items) ===")
    for k, blk in cv5_summary.items():
        if not isinstance(blk, dict):
            continue
        p = blk["point"]
        vc = blk["vs_const_set"]["dRPS"]
        vf = blk["vs_exp27_f8"]["dRPS"]
        log(f"  {k:22s}: RPS={p['RPS']:.4f} CE={p['CE']:.4f} TVD={p['TVD']:.4f} Brier={p['Brier']:.4f} r={p['Pearson']:.3f} rho={p['Spearman']:.3f} ICC_A={p['ICC_A1']:.3f} Bias={p['Bias']:+.3f} (J={p['Mean_Judge']:.2f}, H={p['Mean_Human']:.2f}) | dRPS_const={vc['point']:+.4f} {vc['ci95']} p={vc['p_val_two_sided']:.4g} | dRPS_f8={vf['point']:+.4f} {vf['ci95']}")

    # 3) Set breakdown (old vs new) for winner_set_aware vs constant_set_aware on cv5 OOF
    set_breakdown = {}
    for st in ("old", "new"):
        m = D["set"] == st
        set_breakdown[st] = {
            "winner_set_aware": dl.evaluate_panel(D["P"][m], q_win_s_cv[m]),
            "constant_set_aware": dl.evaluate_panel(D["P"][m], q_const_s_cv[m]),
            "exp27_f8": dl.evaluate_panel(D["P"][m], q_f8_cv[m]),
        }

    # 4) Raw Frontier + Single-Pass Logit vs M=1 Argmax Ablation on all 175 items
    raw_175 = {}
    for k, q in D["dists"].items():
        raw_175[k] = summarize_block(f"raw_{k}", D["task"], D["P"], q, q_const_s_cv, q_f8_cv)
    log("\n=== PART 3: Uncalibrated Zero-Demo Frontier & Qwen3 Single-Pass vs M=1 Argmax (175 items) ===")
    for k, blk in raw_175.items():
        p = blk["point"]
        log(f"  {k:15s}: RPS={p['RPS']:.4f} CE={p['CE']:.4f} TVD={p['TVD']:.4f} Brier={p['Brier']:.4f} r={p['Pearson']:.3f} rho={p['Spearman']:.3f} tau={p['Kendall']:.3f} ICC_A={p['ICC_A1']:.3f} ICC_C={p['ICC_C1']:.3f} Bias={p['Bias']:+.3f}")

    # 5) Qwen3-4B Top-4-Block LoRA (CE vs RPS vs Pearson) on exp27_split & cv5_fold OOF
    lora_summary = {}
    lora_path = de.RES_DIR / "qwen3_4b_lora_ce_rps_pearson.json"
    if lora_path.exists():
        lora_obj = json.loads(lora_path.read_text())
        log("\n=== PART 4: End-to-End Qwen3-4B Top-4-Block LoRA (CE vs RPS vs Pearson) ===")
        for split_kind, mask, key_map in (
            ("exp27_test", te27, "exp27_test_preds"),
            ("cv5_oof", np.ones(D["n"], dtype=bool), "cv5_oof_preds"),
        ):
            lora_summary[split_kind] = {}
            q_ref_c = q_const_s_te if split_kind == "exp27_test" else q_const_s_cv
            q_ref_f = q_f8_te if split_kind == "exp27_test" else q_f8_cv
            items_m = D["item"][mask]
            tasks_m = D["task"][mask]
            p_m = D["P"][mask]
            q_by_obj = {}
            for obj in ("ce", "rps", "pearson"):
                mp = lora_obj[obj][key_map]
                q_by_obj[obj] = np.stack([np.asarray(mp[it]["probs"], dtype=np.float64) for it in items_m])
                blk = summarize_block(f"lora_{obj}_{split_kind}", tasks_m, p_m, q_by_obj[obj], q_ref_c, q_ref_f)
                lora_summary[split_kind][obj] = blk
                pt = blk["point"]
                log(f"  [{split_kind}] lora_{obj:7s}: RPS={pt['RPS']:.4f} CE={pt['CE']:.4f} TVD={pt['TVD']:.4f} Brier={pt['Brier']:.4f} r={pt['Pearson']:.3f} ICC_A={pt['ICC_A1']:.3f} Bias={pt['Bias']:+.3f}")
            # Post-hoc 1D CE calibration of lora_pearson strictly OOF on cv5_oof
            if split_kind == "cv5_oof":
                q_pear_post = np.zeros_like(q_by_obj["pearson"])
                for ff in range(5):
                    ftr = D["cv5_fold"] != ff
                    fte = D["cv5_fold"] == ff
                    cal_1d = dl.MKCalibrator(objective="ce", alpha=0.3, alpha_a=0.05, dirichlet_eta=0.05, use_quad=True, set_aware_prior=True)
                    cal_1d.fit(np.zeros((int(ftr.sum()), 0, 6)), np.column_stack([q_by_obj["pearson"][ftr] @ dl.GRID, D["is_new"][ftr]]), D["is_new"][ftr], D["P"][ftr])
                    q_pear_post[fte] = cal_1d.predict(np.zeros((int(fte.sum()), 0, 6)), np.column_stack([q_by_obj["pearson"][fte] @ dl.GRID, D["is_new"][fte]]), D["is_new"][fte])
                blk_pc = summarize_block(f"lora_pearson_postcal_{split_kind}", tasks_m, p_m, q_pear_post, q_ref_c, q_ref_f)
                lora_summary[split_kind]["pearson_postcal"] = blk_pc
                pt_pc = blk_pc["point"]
                log(f"  [{split_kind}] lora_pear_pc : RPS={pt_pc['RPS']:.4f} CE={pt_pc['CE']:.4f} TVD={pt_pc['TVD']:.4f} Brier={pt_pc['Brier']:.4f} r={pt_pc['Pearson']:.3f} ICC_A={pt_pc['ICC_A1']:.3f} Bias={pt_pc['Bias']:+.3f}")
                lora_summary[split_kind]["ce_vs_pearson_postcal"] = dl.task_cluster_bootstrap(tasks_m, p_m, q_by_obj["ce"], q_ref=q_pear_post, draws=10000, seed=20261126)["paired_vs_ref"]

            # Paired comparison CE/RPS vs Pearson
            lora_summary[split_kind]["ce_vs_pearson"] = dl.task_cluster_bootstrap(tasks_m, p_m, q_by_obj["ce"], q_ref=q_by_obj["pearson"], draws=10000, seed=20261126)["paired_vs_ref"]
            lora_summary[split_kind]["rps_vs_pearson"] = dl.task_cluster_bootstrap(tasks_m, p_m, q_by_obj["rps"], q_ref=q_by_obj["pearson"], draws=10000, seed=20261126)["paired_vs_ref"]
            cvp = lora_summary[split_kind]["ce_vs_pearson"]
            log(f"  [{split_kind}] paired CE - Pearson: dRPS={cvp['dRPS']['point']:+.4f} {cvp['dRPS']['ci95']} p={cvp['dRPS']['p_val_two_sided']:.4g} | dCE={cvp['dCE']['point']:+.4f} {cvp['dCE']['ci95']}")

    out = {
        "eval_seconds": round(time.time() - t0, 2),
        "exp27_split_test": exp27_summary,
        "cv5_nested_oof": cv5_summary,
        "nested_fold_selections": nested_selections,
        "calibration_bins_cv5_nested_set": calibration_bins(D["P"], q_nested_s_cv),
        "calibration_bins_cv5_nested_global": calibration_bins(D["P"], q_nested_g_cv),
        "set_breakdown_cv5": set_breakdown,
        "raw_dists_175": raw_175,
        "qwen3_4b_lora": lora_summary,
    }
    (de.RES_DIR / "final_results_11-26-2026.json").write_text(json.dumps(out, indent=2))
    (de.RES_DIR / "final_stdout_11-26-2026.txt").write_text("\n".join(lines) + "\n")
    print(f"\n[final_eval] Saved JSON & stdout in {out['eval_seconds']}s", flush=True)


if __name__ == "__main__":
    main()
