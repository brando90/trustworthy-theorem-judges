"""Experiment 28: Held-out & Strict Nested 5-Fold OOF Evaluation (Amendment 2 CPU remediation).

Evaluates:
  - Set-Aware & Global Constants
  - Exp 27 Comparators: F3_both (H3-free), F8_both_h3 (alpha=0, m=0),
    F9_both_h3_set at both Exp-27-selected (alpha=0, m=0.25) and F8 HPs (alpha=0, m=0)
  - Frozen Registered Judges: Global G9 (no is_new) & Set-Aware C7 (sensitivity),
    plus pure All-Frontier sensitivity candidates (ZERO Qwen, ZERO H3, judge_std3)
  - Strict H3-free nested 5-fold OOF selection across all 50 tasks (175 artifacts)
  - Strict matched-grid Priority 2 vs 4 (CE vs RPS vs Pearson) on (M+K) head & Qwen3-4B LoRA
    (leaky cv5 LoRA Pearson post-calibration removed/quarantined)
  - Single-pass Qwen3 logit readout vs M=1 argmax one-hot ablation.
"""
from __future__ import annotations

import json
import sys
import time
from pathlib import Path
import numpy as np

EXP27_SCRIPTS = (
    Path(__file__).resolve().parents[2]
    / "27_build_a_judge_that_beats_the_constant_forecast_on_held_out_tasks_old_new_ratings_start_24Nov2026"
    / "scripts"
)
sys.path.insert(0, str(EXP27_SCRIPTS))
import judgelib as jl27  # noqa: E402

import data_exp28 as de  # noqa: E402
import distlib as dl  # noqa: E402
from search_inner_cv import CANDIDATE_SPECS, build_lp_and_x, make_4fold_inner_tasks  # noqa: E402

# Pure 3-frontier-family pool: ZERO Qwen3-4B/8B, ZERO judge_std4, ZERO cached H3
FRONTIER_CANDIDATE_SPECS = [
    ("FG1_astra", ["h4_astra"], ["e_astra"], False),
    ("FG2_argon", ["h4_argon"], ["e_argon"], False),
    ("FG3_opus", ["h4_opus"], ["e_opus"], False),
    ("FG6_3fam", ["h4_astra", "h4_argon", "h4_opus"], ["e_astra", "e_argon", "e_opus"], False),
    ("FG6b_astra_argon", ["h4_astra", "h4_argon"], ["e_astra", "e_argon"], False),
    (
        "FG7_3fam_std3",
        ["h4_astra", "h4_argon", "h4_opus"],
        ["e_astra", "e_argon", "e_opus", "judge_std3", "astra_opus_gap"],
        False,
    ),
    (
        "FG8_3fam_struct",
        ["h4_astra", "h4_argon", "h4_opus"],
        ["e_astra", "e_argon", "e_opus", "judge_std3", "excess_thm_log", "cand_sorry_count", "ident_jaccard", "edit"],
        False,
    ),
    ("FS1_astra", ["h4_astra"], ["e_astra", "is_new"], True),
    ("FS2_argon", ["h4_argon"], ["e_argon", "is_new"], True),
    ("FS3_opus", ["h4_opus"], ["e_opus", "is_new"], True),
    ("FS6_3fam", ["h4_astra", "h4_argon", "h4_opus"], ["e_astra", "e_argon", "e_opus", "is_new"], True),
    ("FS6b_astra_argon", ["h4_astra", "h4_argon"], ["e_astra", "e_argon", "is_new"], True),
    (
        "FS7_3fam_std3",
        ["h4_astra", "h4_argon", "h4_opus"],
        ["e_astra", "e_argon", "e_opus", "judge_std3", "astra_opus_gap", "is_new"],
        True,
    ),
    (
        "FS8_3fam_struct",
        ["h4_astra", "h4_argon", "h4_opus"],
        [
            "e_astra", "e_argon", "e_opus", "judge_std3",
            "excess_thm_log", "cand_sorry_count", "ident_jaccard", "edit", "is_new",
        ],
        True,
    ),
]

MATCHED_ALPHAS = (1e-4, 1e-2, 0.3, 1.0, 3.0, 10.0)


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


def _spec_uses_h3(dkeys: list[str], fkeys: list[str]) -> bool:
    return ("h3_astra" in dkeys) or ("h3_e" in fkeys) or ("h3_s" in fkeys)


def select_best_on_subset(
    D_sub: dict,
    set_aware_filter: bool,
    exclude_h3: bool = True,
    frontier_only: bool = False,
) -> dict:
    """Strictly select candidate + HPs inside a training subset using 4 stratified inner folds."""
    inner_f = make_4fold_inner_tasks(D_sub)
    pool = FRONTIER_CANDIDATE_SPECS if frontier_only else CANDIDATE_SPECS
    best = None
    for cname, dkeys, fkeys, sa in pool:
        if sa != set_aware_filter:
            continue
        if exclude_h3 and _spec_uses_h3(dkeys, fkeys):
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


def select_matched_head_on_subset(
    D_sub: dict,
    dist_keys: list[str],
    feat_keys: list[str],
    set_aware: bool,
    objective: str,
) -> dict:
    """Select (alpha, eta, use_quad) via 4-fold inner-CV pooled RPS over a shared grid."""
    inner_f = make_4fold_inner_tasks(D_sub)
    lp, x = build_lp_and_x(D_sub, dist_keys, feat_keys)
    best = None
    for alpha in MATCHED_ALPHAS:
        for eta in (0.0, 0.05, 0.12):
            for uq in (True, False):
                q_oof = np.zeros((D_sub["n"], 6), dtype=np.float64)
                for f in range(4):
                    itr = inner_f != f
                    iva = inner_f == f
                    cal = dl.MKCalibrator(
                        objective=objective, alpha=alpha, alpha_a=0.05,
                        dirichlet_eta=eta, use_quad=uq, set_aware_prior=set_aware,
                    ).fit(lp[itr], x[itr], D_sub["is_new"][itr], D_sub["P"][itr])
                    q_oof[iva] = cal.predict(lp[iva], x[iva], D_sub["is_new"][iva])
                sc = float(dl.rps_items(D_sub["P"], q_oof).mean())
                if best is None or sc < best["inner_rps"]:
                    best = {
                        "inner_rps": sc,
                        "dist_keys": list(dist_keys),
                        "feat_keys": list(feat_keys),
                        "objective": objective,
                        "alpha": alpha,
                        "dirichlet_eta": eta,
                        "use_quad": uq,
                        "set_aware": set_aware,
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


def eval_exp27_ordinal(
    D: dict,
    tr_mask: np.ndarray,
    te_mask: np.ndarray,
    feat_cols: list[str],
    alpha: float = 0.0,
    m: float = 0.0,
) -> np.ndarray:
    """Evaluate Exp 27 jl27.Ordinal comparator (F3, F8, or F9) on specified split."""
    D27 = {
        "P": D["P"],
        "C": D["C"],
        "astra": D["feats"]["h2_astra"],
        "opus": D["feats"]["h2_opus"],
        "h3s": D["feats"]["h3_s"],
        "h3e": D["feats"]["h3_e"],
        "isnew": D["is_new"],
    }
    tr_idx = np.where(tr_mask)[0]
    te_idx = np.where(te_mask)[0]
    model = jl27.Ordinal(list(feat_cols), alpha=alpha, m=m).fit(D27, tr_idx)
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


def summarize_block(
    name: str,
    tasks: np.ndarray,
    p_emp: np.ndarray,
    q: np.ndarray,
    q_const: np.ndarray,
    q_f8: np.ndarray,
    q_f3: np.ndarray | None = None,
    seed: int = 20261126,
) -> dict:
    b_const = dl.task_cluster_bootstrap(tasks, p_emp, q, q_ref=q_const, draws=10000, seed=seed)
    b_f8 = dl.task_cluster_bootstrap(tasks, p_emp, q, q_ref=q_f8, draws=10000, seed=seed)
    out = {
        "name": name,
        "point": b_const["point"],
        "ci95": b_const["ci95"],
        "vs_const_set": b_const["paired_vs_ref"],
        "vs_exp27_f8": b_f8["paired_vs_ref"],
    }
    if q_f3 is not None:
        b_f3 = dl.task_cluster_bootstrap(tasks, p_emp, q, q_ref=q_f3, draws=10000, seed=seed)
        out["vs_exp27_f3_h3free"] = b_f3["paired_vs_ref"]
    return out


def _eval_matched_head_exp27(D: dict, tr27: np.ndarray, te27: np.ndarray, tasks_te: np.ndarray, P_te: np.ndarray, q_const_s_te: np.ndarray, q_f8_te: np.ndarray, q_f3_te: np.ndarray, spec: dict, label: str) -> dict:
    D_tr27 = slice_bundle(D, tr27)
    res = {}
    q_by_obj = {}
    sel_hps = {}
    for obj in ("ce", "rps", "pearson"):
        hp = select_matched_head_on_subset(D_tr27, spec["dist_keys"], spec["feat_keys"], spec["set_aware"], obj)
        sel_hps[obj] = hp
        q_by_obj[obj] = eval_mk_model(D, hp, tr27, te27)
        res[obj] = summarize_block(f"head_matched_{label}_{obj}", tasks_te, P_te, q_by_obj[obj], q_const_s_te, q_f8_te, q_f3_te)
    res["selected_hps"] = sel_hps
    res["ce_vs_pearson"] = dl.task_cluster_bootstrap(tasks_te, P_te, q_by_obj["ce"], q_ref=q_by_obj["pearson"], draws=10000, seed=20261126)["paired_vs_ref"]
    res["rps_vs_pearson"] = dl.task_cluster_bootstrap(tasks_te, P_te, q_by_obj["rps"], q_ref=q_by_obj["pearson"], draws=10000, seed=20261126)["paired_vs_ref"]
    return res


def main() -> None:
    t0 = time.time()
    D = de.load_bundle(include_test=True, require_complete=True)
    search_json = json.loads((de.RES_DIR / "inner_cv_search_11-26-2026.json").read_text())
    winner_set = search_json["winner_set_aware"]
    winner_global = search_json["winner_global"]

    lines: list[str] = []

    def log(msg: str) -> None:
        print(msg, flush=True)
        lines.append(msg)

    log(f"Experiment 28 Final Evaluation — Amendment 2 Clean Audit Run (n={D['n']} items, {len(set(D['task']))} tasks)")
    log(f"Frozen Global Winner (PREREG Primary):  {winner_global['candidate']} ({winner_global['objective']}, alpha={winner_global['alpha']}, eta={winner_global['dirichlet_eta']}, quad={winner_global['use_quad']})")
    log(f"Frozen Set-Aware Winner (Sensitivity):  {winner_set['candidate']} ({winner_set['objective']}, alpha={winner_set['alpha']}, eta={winner_set['dirichlet_eta']}, quad={winner_set['use_quad']})")

    # 1) exp27_split (train+val 30 tasks -> test 20 tasks)
    tr27 = D["exp27_split"] != "test"
    te27 = D["exp27_split"] == "test"
    D_tr27 = slice_bundle(D, tr27)
    tasks_te = D["task"][te27]
    P_te = D["P"][te27]

    q_const_s_te = eval_constant_preds(D, tr27, te27, True)
    q_const_g_te = eval_constant_preds(D, tr27, te27, False)
    q_f3_te = eval_exp27_ordinal(D, tr27, te27, ["astra", "opus"], alpha=0.0, m=0.0)
    q_f8_te = eval_exp27_ordinal(D, tr27, te27, ["astra", "opus", "h3s", "h3e"], alpha=0.0, m=0.0)
    q_f9_f8hp_te = eval_exp27_ordinal(D, tr27, te27, ["astra", "opus", "h3s", "h3e", "isnew"], alpha=0.0, m=0.0)
    q_f9_sel_te = eval_exp27_ordinal(D, tr27, te27, ["astra", "opus", "h3s", "h3e", "isnew"], alpha=0.0, m=0.25)

    q_win_g_te = eval_mk_model(D, winner_global, tr27, te27)
    q_win_s_te = eval_mk_model(D, winner_set, tr27, te27)
    best_c9b = min(
        (search_json["best_by_family"][k] for k in ("C9b_h4_astra_argon_q8b__ce", "C9b_h4_astra_argon_q8b__rps") if k in search_json["best_by_family"]),
        key=lambda r: r["inner_cv"]["RPS"],
    )
    q_c9b_te = eval_mk_model(D, best_c9b, tr27, te27)

    # Pure all-frontier (no Qwen, no judge_std4, no H3) selected strictly on 30 non-test tasks
    spec_frontier_g_27 = select_best_on_subset(D_tr27, set_aware_filter=False, exclude_h3=True, frontier_only=True)
    spec_frontier_s_27 = select_best_on_subset(D_tr27, set_aware_filter=True, exclude_h3=True, frontier_only=True)
    spec_c7_std3 = {
        "candidate": "FS7_3fam_std3",
        "dist_keys": ["h4_astra", "h4_argon", "h4_opus"],
        "feat_keys": ["e_astra", "e_argon", "e_opus", "judge_std3", "astra_opus_gap", "is_new"],
        "objective": "ce",
        "alpha": 0.3,
        "dirichlet_eta": 0.0,
        "use_quad": False,
        "set_aware": True,
    }
    q_front_g_te = eval_mk_model(D, spec_frontier_g_27, tr27, te27)
    q_front_s_te = eval_mk_model(D, spec_frontier_s_27, tr27, te27)
    q_c7_std3_te = eval_mk_model(D, spec_c7_std3, tr27, te27)

    exp27_summary = {
        "n_test_items": int(te27.sum()),
        "n_test_tasks": int(len(set(tasks_te))),
        "constant_global": summarize_block("constant_global", tasks_te, P_te, q_const_g_te, q_const_s_te, q_f8_te, q_f3_te),
        "constant_set_aware": summarize_block("constant_set_aware", tasks_te, P_te, q_const_s_te, q_const_s_te, q_f8_te, q_f3_te),
        "exp27_f3_h3free": summarize_block("exp27_f3_h3free", tasks_te, P_te, q_f3_te, q_const_s_te, q_f8_te, q_f3_te),
        "exp27_f8_refit250": summarize_block("exp27_f8_refit250", tasks_te, P_te, q_f8_te, q_const_s_te, q_f8_te, q_f3_te),
        "exp27_f9_selected": summarize_block("exp27_f9_selected", tasks_te, P_te, q_f9_sel_te, q_const_s_te, q_f8_te, q_f3_te),
        "exp27_f9_f8hp": summarize_block("exp27_f9_f8hp", tasks_te, P_te, q_f9_f8hp_te, q_const_s_te, q_f8_te, q_f3_te),
        "winner_global": summarize_block("winner_global", tasks_te, P_te, q_win_g_te, q_const_s_te, q_f8_te, q_f3_te),
        "winner_global_seed20261124": summarize_block("winner_global_seed20261124", tasks_te, P_te, q_win_g_te, q_const_s_te, q_f8_te, q_f3_te, seed=20261124),
        "winner_set_aware": summarize_block("winner_set_aware", tasks_te, P_te, q_win_s_te, q_const_s_te, q_f8_te, q_f3_te),
        "winner_set_aware_seed20261124": summarize_block("winner_set_aware_seed20261124", tasks_te, P_te, q_win_s_te, q_const_s_te, q_f8_te, q_f3_te, seed=20261124),
        "c9b_zero_opus_fallback": summarize_block("c9b_zero_opus_fallback", tasks_te, P_te, q_c9b_te, q_const_s_te, q_f8_te, q_f3_te),
        "frontier_global_selected": summarize_block("frontier_global_selected", tasks_te, P_te, q_front_g_te, q_const_s_te, q_f8_te, q_f3_te),
        "frontier_set_selected": summarize_block("frontier_set_selected", tasks_te, P_te, q_front_s_te, q_const_s_te, q_f8_te, q_f3_te),
        "frontier_set_c7_std3": summarize_block("frontier_set_c7_std3", tasks_te, P_te, q_c7_std3_te, q_const_s_te, q_f8_te, q_f3_te),
        "frontier_global_selected_spec": spec_frontier_g_27,
        "frontier_set_selected_spec": spec_frontier_s_27,
        "winner_set_aware_vs_f9_selected": dl.task_cluster_bootstrap(tasks_te, P_te, q_win_s_te, q_ref=q_f9_sel_te, draws=10000, seed=20261126)["paired_vs_ref"],
        "winner_set_aware_vs_f9_f8hp": dl.task_cluster_bootstrap(tasks_te, P_te, q_win_s_te, q_ref=q_f9_f8hp_te, draws=10000, seed=20261126)["paired_vs_ref"],
    }
    exp27_head_matched = _eval_matched_head_exp27(
        D, tr27, te27, tasks_te, P_te, q_const_s_te, q_f8_te, q_f3_te, winner_set, "exp27_c7"
    )

    log("\n=== PART 1: exp27_split Held-Out Test (20 tasks, 70 items) ===")
    for k, blk in exp27_summary.items():
        if not isinstance(blk, dict) or "point" not in blk:
            continue
        p = blk["point"]
        vc = blk["vs_const_set"]["dRPS"]
        vf = blk["vs_exp27_f8"]["dRPS"]
        log(f"  {k:28s}: RPS={p['RPS']:.4f} CE={p['CE']:.4f} TVD={p['TVD']:.4f} Brier={p['Brier']:.4f} r={p['Pearson']:.3f} rho={p['Spearman']:.3f} ICC_A={p['ICC_A1']:.3f} Bias={p['Bias']:+.3f} (J={p['Mean_Judge']:.3f}, H={p['Mean_Human']:.3f}) | dRPS_const={vc['point']:+.4f} {vc['ci95']} p={vc['p_val_two_sided']:.4g} | dRPS_f8={vf['point']:+.4f} {vf['ci95']}")

    # 2) cv5_fold Pooled Strict Nested 5-Fold OOF across all 50 tasks (175 artifacts)
    q_const_s_cv = np.zeros((D["n"], 6))
    q_const_g_cv = np.zeros((D["n"], 6))
    q_f3_cv = np.zeros((D["n"], 6))
    q_f8_cv = np.zeros((D["n"], 6))
    q_f9_sel_cv = np.zeros((D["n"], 6))
    q_win_g_fixed_cv = np.zeros((D["n"], 6))
    q_win_s_fixed_cv = np.zeros((D["n"], 6))
    q_c9b_fixed_cv = np.zeros((D["n"], 6))
    q_nested_g_cv = np.zeros((D["n"], 6))
    q_nested_s_cv = np.zeros((D["n"], 6))
    q_nested_front_g_cv = np.zeros((D["n"], 6))
    q_nested_front_s_cv = np.zeros((D["n"], 6))
    q_exp_head_pear_a03_cv = np.zeros((D["n"], 6))

    matched_objs = ("ce", "rps", "pearson")
    q_head_c7 = {obj: np.zeros((D["n"], 6)) for obj in matched_objs}
    q_head_g9 = {obj: np.zeros((D["n"], 6)) for obj in matched_objs}
    head_c7_hps = []
    head_g9_hps = []
    nested_selections = []

    for f in range(5):
        tr = D["cv5_fold"] != f
        te = D["cv5_fold"] == f
        D_tr = slice_bundle(D, tr)

        # H3-free nested re-selection inside outer training fold f (excludes C12_hybrid_h3_struct)
        n_best_g = select_best_on_subset(D_tr, set_aware_filter=False, exclude_h3=True, frontier_only=False)
        n_best_s = select_best_on_subset(D_tr, set_aware_filter=True, exclude_h3=True, frontier_only=False)
        n_front_g = select_best_on_subset(D_tr, set_aware_filter=False, exclude_h3=True, frontier_only=True)
        n_front_s = select_best_on_subset(D_tr, set_aware_filter=True, exclude_h3=True, frontier_only=True)
        nested_selections.append({
            "fold": f,
            "global": n_best_g,
            "set_aware_h3free": n_best_s,
            "frontier_global": n_front_g,
            "frontier_set_aware": n_front_s,
        })

        q_const_s_cv[te] = eval_constant_preds(D, tr, te, True)
        q_const_g_cv[te] = eval_constant_preds(D, tr, te, False)
        q_f3_cv[te] = eval_exp27_ordinal(D, tr, te, ["astra", "opus"], alpha=0.0, m=0.0)
        q_f8_cv[te] = eval_exp27_ordinal(D, tr, te, ["astra", "opus", "h3s", "h3e"], alpha=0.0, m=0.0)
        q_f9_sel_cv[te] = eval_exp27_ordinal(D, tr, te, ["astra", "opus", "h3s", "h3e", "isnew"], alpha=0.0, m=0.25)

        q_win_g_fixed_cv[te] = eval_mk_model(D, winner_global, tr, te)
        q_win_s_fixed_cv[te] = eval_mk_model(D, winner_set, tr, te)
        q_c9b_fixed_cv[te] = eval_mk_model(D, best_c9b, tr, te)

        q_nested_g_cv[te] = eval_mk_model(D, n_best_g, tr, te)
        q_nested_s_cv[te] = eval_mk_model(D, n_best_s, tr, te)
        q_nested_front_g_cv[te] = eval_mk_model(D, n_front_g, tr, te)
        q_nested_front_s_cv[te] = eval_mk_model(D, n_front_s, tr, te)

        q_exp_head_pear_a03_cv[te] = eval_mk_model(D, winner_set, tr, te, obj_override="pearson")

        fold_c7 = {"fold": f}
        fold_g9 = {"fold": f}
        for obj in matched_objs:
            hp_c7 = select_matched_head_on_subset(D_tr, winner_set["dist_keys"], winner_set["feat_keys"], True, obj)
            fold_c7[obj] = hp_c7
            q_head_c7[obj][te] = eval_mk_model(D, hp_c7, tr, te)

            hp_g9 = select_matched_head_on_subset(D_tr, winner_global["dist_keys"], winner_global["feat_keys"], False, obj)
            fold_g9[obj] = hp_g9
            q_head_g9[obj][te] = eval_mk_model(D, hp_g9, tr, te)
        head_c7_hps.append(fold_c7)
        head_g9_hps.append(fold_g9)

    cv5_summary = {
        "n_items": int(D["n"]),
        "n_tasks": int(len(set(D["task"]))),
        "constant_global": summarize_block("constant_global", D["task"], D["P"], q_const_g_cv, q_const_s_cv, q_f8_cv, q_f3_cv),
        "constant_set_aware": summarize_block("constant_set_aware", D["task"], D["P"], q_const_s_cv, q_const_s_cv, q_f8_cv, q_f3_cv),
        "exp27_f3_h3free": summarize_block("exp27_f3_h3free", D["task"], D["P"], q_f3_cv, q_const_s_cv, q_f8_cv, q_f3_cv),
        "exp27_f8_h3_exposed": summarize_block("exp27_f8_h3_exposed", D["task"], D["P"], q_f8_cv, q_const_s_cv, q_f8_cv, q_f3_cv),
        "exp27_f9_selected_h3_exposed": summarize_block("exp27_f9_selected_h3_exposed", D["task"], D["P"], q_f9_sel_cv, q_const_s_cv, q_f8_cv, q_f3_cv),
        "nested_winner_global": summarize_block("nested_winner_global", D["task"], D["P"], q_nested_g_cv, q_const_s_cv, q_f8_cv, q_f3_cv),
        "nested_winner_set_aware": summarize_block("nested_winner_set_aware", D["task"], D["P"], q_nested_s_cv, q_const_s_cv, q_f8_cv, q_f3_cv),
        "nested_frontier_global": summarize_block("nested_frontier_global", D["task"], D["P"], q_nested_front_g_cv, q_const_s_cv, q_f8_cv, q_f3_cv),
        "nested_frontier_set_aware": summarize_block("nested_frontier_set_aware", D["task"], D["P"], q_nested_front_s_cv, q_const_s_cv, q_f8_cv, q_f3_cv),
        "exploratory_fixed_hp_winner_global": summarize_block("exploratory_fixed_hp_winner_global", D["task"], D["P"], q_win_g_fixed_cv, q_const_s_cv, q_f8_cv, q_f3_cv),
        "exploratory_fixed_hp_winner_set_aware": summarize_block("exploratory_fixed_hp_winner_set_aware", D["task"], D["P"], q_win_s_fixed_cv, q_const_s_cv, q_f8_cv, q_f3_cv),
        "exploratory_fixed_hp_c9b": summarize_block("exploratory_fixed_hp_c9b", D["task"], D["P"], q_c9b_fixed_cv, q_const_s_cv, q_f8_cv, q_f3_cv),
        "exploratory_head_pearson_fixed_alpha03_collapsed": summarize_block("exploratory_head_pearson_fixed_alpha03_collapsed", D["task"], D["P"], q_exp_head_pear_a03_cv, q_const_s_cv, q_f8_cv, q_f3_cv),
    }

    head_matched_c7 = {
        obj: summarize_block(f"head_matched_c7_{obj}", D["task"], D["P"], q_head_c7[obj], q_const_s_cv, q_f8_cv, q_f3_cv)
        for obj in matched_objs
    }
    head_matched_c7["ce_vs_pearson"] = dl.task_cluster_bootstrap(D["task"], D["P"], q_head_c7["ce"], q_ref=q_head_c7["pearson"], draws=10000, seed=20261126)["paired_vs_ref"]
    head_matched_c7["rps_vs_pearson"] = dl.task_cluster_bootstrap(D["task"], D["P"], q_head_c7["rps"], q_ref=q_head_c7["pearson"], draws=10000, seed=20261126)["paired_vs_ref"]
    head_matched_c7["ce_vs_rps"] = dl.task_cluster_bootstrap(D["task"], D["P"], q_head_c7["ce"], q_ref=q_head_c7["rps"], draws=10000, seed=20261126)["paired_vs_ref"]
    head_matched_c7["selected_hps_by_fold"] = head_c7_hps

    head_matched_g9 = {
        obj: summarize_block(f"head_matched_g9_{obj}", D["task"], D["P"], q_head_g9[obj], q_const_s_cv, q_f8_cv, q_f3_cv)
        for obj in matched_objs
    }
    head_matched_g9["ce_vs_pearson"] = dl.task_cluster_bootstrap(D["task"], D["P"], q_head_g9["ce"], q_ref=q_head_g9["pearson"], draws=10000, seed=20261126)["paired_vs_ref"]
    head_matched_g9["rps_vs_pearson"] = dl.task_cluster_bootstrap(D["task"], D["P"], q_head_g9["rps"], q_ref=q_head_g9["pearson"], draws=10000, seed=20261126)["paired_vs_ref"]
    head_matched_g9["ce_vs_rps"] = dl.task_cluster_bootstrap(D["task"], D["P"], q_head_g9["ce"], q_ref=q_head_g9["rps"], draws=10000, seed=20261126)["paired_vs_ref"]
    head_matched_g9["selected_hps_by_fold"] = head_g9_hps

    log("\n=== PART 2: All-50-Task Strict H3-Free Nested 5-Fold OOF (175 items) ===")
    for k, blk in cv5_summary.items():
        if not isinstance(blk, dict) or "point" not in blk:
            continue
        p = blk["point"]
        vc = blk["vs_const_set"]["dRPS"]
        vf3 = blk["vs_exp27_f3_h3free"]["dRPS"]
        log(f"  {k:44s}: RPS={p['RPS']:.4f} CE={p['CE']:.4f} TVD={p['TVD']:.4f} Brier={p['Brier']:.4f} r={p['Pearson']:.3f} ICC_A={p['ICC_A1']:.3f} Bias={p['Bias']:+.3f} (J={p['Mean_Judge']:.3f}, H={p['Mean_Human']:.3f}) | dRPS_const={vc['point']:+.4f} {vc['ci95']} (n_ge0={vc['n_ge_zero']}) | dRPS_f3={vf3['point']:+.4f} {vf3['ci95']}")

    log("\n=== PART 2B: Matched-Grid (M+K) Head Priority 2 vs 4 ===")
    for lbl, hdict in (("exp27_test_c7", exp27_head_matched), ("cv5_nested_c7", head_matched_c7), ("cv5_nested_g9", head_matched_g9)):
        for obj in matched_objs:
            p = hdict[obj]["point"]
            log(f"  [{lbl}] {obj:7s}: RPS={p['RPS']:.4f} CE={p['CE']:.4f} TVD={p['TVD']:.4f} Brier={p['Brier']:.4f} r={p['Pearson']:.3f} ICC_A={p['ICC_A1']:.3f} Bias={p['Bias']:+.3f}")
        cvp = hdict["ce_vs_pearson"]
        rvp = hdict["rps_vs_pearson"]
        log(f"  [{lbl}] CE - Pearson : dRPS={cvp['dRPS']['point']:+.4f} {cvp['dRPS']['ci95']} p={cvp['dRPS']['p_val_two_sided']:.4g} | dCE={cvp['dCE']['point']:+.4f} {cvp['dCE']['ci95']} | dTVD={cvp['dTVD']['point']:+.4f} {cvp['dTVD']['ci95']}")
        log(f"  [{lbl}] RPS - Pearson: dRPS={rvp['dRPS']['point']:+.4f} {rvp['dRPS']['ci95']} p={rvp['dRPS']['p_val_two_sided']:.4g} | dCE={rvp['dCE']['point']:+.4f} {rvp['dCE']['ci95']}")

    # 3) Set breakdown (old vs new) on cv5 OOF (strict nested + comparators)
    set_breakdown = {}
    for st in ("old", "new"):
        m = D["set"] == st
        set_breakdown[st] = {
            "nested_winner_global": dl.evaluate_panel(D["P"][m], q_nested_g_cv[m]),
            "nested_frontier_global": dl.evaluate_panel(D["P"][m], q_nested_front_g_cv[m]),
            "nested_winner_set_aware": dl.evaluate_panel(D["P"][m], q_nested_s_cv[m]),
            "exploratory_fixed_hp_winner_set_aware": dl.evaluate_panel(D["P"][m], q_win_s_fixed_cv[m]),
            "constant_set_aware": dl.evaluate_panel(D["P"][m], q_const_s_cv[m]),
            "exp27_f3_h3free": dl.evaluate_panel(D["P"][m], q_f3_cv[m]),
            "exp27_f8_h3_exposed": dl.evaluate_panel(D["P"][m], q_f8_cv[m]),
        }

    # 4) Raw Frontier + Single-Pass Logit vs M=1 Argmax Ablation on all 175 items
    raw_175 = {}
    for k, q in D["dists"].items():
        raw_175[k] = summarize_block(f"raw_{k}", D["task"], D["P"], q, q_const_s_cv, q_f8_cv, q_f3_cv)
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
            q_ref_f3 = q_f3_te if split_kind == "exp27_test" else q_f3_cv
            items_m = D["item"][mask]
            tasks_m = D["task"][mask]
            p_m = D["P"][mask]
            q_by_obj = {}
            for obj in ("ce", "rps", "pearson"):
                mp = lora_obj[obj][key_map]
                q_by_obj[obj] = np.stack([np.asarray(mp[it]["probs"], dtype=np.float64) for it in items_m])
                blk = summarize_block(f"lora_{obj}_{split_kind}", tasks_m, p_m, q_by_obj[obj], q_ref_c, q_ref_f, q_ref_f3)
                lora_summary[split_kind][obj] = blk
                pt = blk["point"]
                log(f"  [{split_kind}] lora_{obj:7s}: RPS={pt['RPS']:.4f} CE={pt['CE']:.4f} TVD={pt['TVD']:.4f} Brier={pt['Brier']:.4f} r={pt['Pearson']:.3f} ICC_A={pt['ICC_A1']:.3f} Bias={pt['Bias']:+.3f}")

            if split_kind == "cv5_oof":
                # Leaky OOF-on-OOF 1D post-cal quarantined per Amendment 2 (requires saved inner-OOF LoRA preds to run leak-free)
                lora_summary[split_kind]["pearson_postcal_status"] = (
                    "quarantined_removed_amendment2_indirect_outer_fold_leakage_no_inner_oof_preds_saved"
                )

            lora_summary[split_kind]["ce_vs_pearson"] = dl.task_cluster_bootstrap(tasks_m, p_m, q_by_obj["ce"], q_ref=q_by_obj["pearson"], draws=10000, seed=20261126)["paired_vs_ref"]
            lora_summary[split_kind]["rps_vs_pearson"] = dl.task_cluster_bootstrap(tasks_m, p_m, q_by_obj["rps"], q_ref=q_by_obj["pearson"], draws=10000, seed=20261126)["paired_vs_ref"]
            lora_summary[split_kind]["ce_vs_rps"] = dl.task_cluster_bootstrap(tasks_m, p_m, q_by_obj["ce"], q_ref=q_by_obj["rps"], draws=10000, seed=20261126)["paired_vs_ref"]
            cvp = lora_summary[split_kind]["ce_vs_pearson"]
            rvp = lora_summary[split_kind]["rps_vs_pearson"]
            log(f"  [{split_kind}] paired CE - Pearson : dRPS={cvp['dRPS']['point']:+.4f} {cvp['dRPS']['ci95']} p={cvp['dRPS']['p_val_two_sided']:.4g} | dCE={cvp['dCE']['point']:+.4f} {cvp['dCE']['ci95']}")
            log(f"  [{split_kind}] paired RPS - Pearson: dRPS={rvp['dRPS']['point']:+.4f} {rvp['dRPS']['ci95']} p={rvp['dRPS']['p_val_two_sided']:.4g} | dCE={rvp['dCE']['point']:+.4f} {rvp['dCE']['ci95']}")

    out = {
        "amendment": "Amendment 2 post-hoc Mega QA remediation (H3-free cv5, pure all-frontier sensitivity, matched head HP search, Exp 27 F3 & F9 comparators, quarantined cv5 LoRA pearson_postcal)",
        "eval_seconds": round(time.time() - t0, 2),
        "exp27_split_test": exp27_summary,
        "exp27_head_matched": exp27_head_matched,
        "cv5_nested_oof": cv5_summary,
        "head_matched_cv5_c7": head_matched_c7,
        "head_matched_cv5_g9": head_matched_g9,
        "nested_fold_selections": nested_selections,
        "calibration_bins_cv5_nested_global": calibration_bins(D["P"], q_nested_g_cv),
        "calibration_bins_cv5_nested_frontier_global": calibration_bins(D["P"], q_nested_front_g_cv),
        "calibration_bins_cv5_nested_set_h3free": calibration_bins(D["P"], q_nested_s_cv),
        "set_breakdown_cv5": set_breakdown,
        "raw_dists_175": raw_175,
        "qwen3_4b_lora": lora_summary,
    }
    (de.RES_DIR / "final_results_11-26-2026.json").write_text(json.dumps(out, indent=2) + "\n")
    (de.RES_DIR / "final_stdout_11-26-2026.txt").write_text("\n".join(lines) + "\n")
    print(f"\n[final_eval] Saved JSON & stdout in {out['eval_seconds']}s", flush=True)


if __name__ == "__main__":
    main()
