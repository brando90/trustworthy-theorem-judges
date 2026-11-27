"""Experiment 28: Pre-freeze nested inner-CV search across 30 non-test tasks (zero sealed test access).

Reads ONLY data_exp28.load_bundle(include_test=False). Selects optimal distributional judge
candidate and hyperparameters by 4-fold stratified task-grouped inner-CV pooled RPS.
"""
from __future__ import annotations

import json
import time
from pathlib import Path
import numpy as np

import data_exp28 as de
import distlib as dl

CANDIDATE_SPECS = [
    ("C1_h4_astra", ["h4_astra"], ["e_astra", "is_new"], True),
    ("C2_h4_argon", ["h4_argon"], ["e_argon", "is_new"], True),
    ("C3_h4_opus", ["h4_opus"], ["e_opus", "is_new"], True),
    ("C4_qwen3_8b_logit", ["qwen3_8b"], ["e_q8b", "is_new"], True),
    ("C5_qwen3_4b_logit", ["qwen3_4b"], ["e_q4b", "is_new"], True),
    ("C6_h4_3fam", ["h4_astra", "h4_argon", "h4_opus"], ["e_astra", "e_argon", "e_opus", "is_new"], True),
    ("C6b_h4_astra_argon", ["h4_astra", "h4_argon"], ["e_astra", "e_argon", "is_new"], True),
    ("C7_h4_3fam_uncert", ["h4_astra", "h4_argon", "h4_opus"], ["e_astra", "e_argon", "e_opus", "judge_std4", "astra_opus_gap", "is_new"], True),
    ("C8_h4_3fam_struct", ["h4_astra", "h4_argon", "h4_opus"], ["e_astra", "e_argon", "e_opus", "judge_std4", "excess_thm_log", "cand_sorry_count", "ident_jaccard", "edit", "is_new"], True),
    ("C9_h4_3fam_q8b", ["h4_astra", "h4_argon", "h4_opus", "qwen3_8b"], ["e_astra", "e_argon", "e_opus", "e_q8b", "judge_std4", "is_new"], True),
    ("C9b_h4_astra_argon_q8b", ["h4_astra", "h4_argon", "qwen3_8b"], ["e_astra", "e_argon", "e_q8b", "is_new"], True),
    ("C10_h4_3fam_q8b_q4b", ["h4_astra", "h4_argon", "h4_opus", "qwen3_8b", "qwen3_4b"], ["e_astra", "e_argon", "e_opus", "e_q8b", "e_q4b", "judge_std4", "is_new"], True),
    ("C11_hybrid_struct", ["h4_astra", "h4_argon", "h4_opus", "qwen3_8b"], ["e_astra", "e_argon", "e_opus", "e_q8b", "judge_std4", "excess_thm_log", "cand_sorry_count", "ident_jaccard", "edit", "is_new"], True),
    ("C12_hybrid_h3_struct", ["h4_astra", "h4_argon", "h4_opus", "qwen3_8b", "h3_astra"], ["e_astra", "e_argon", "e_opus", "e_q8b", "h3_e", "judge_std4", "excess_thm_log", "edit", "is_new"], True),
    # Global (non-set-aware) variants
    ("G6_h4_3fam_global", ["h4_astra", "h4_argon", "h4_opus"], ["e_astra", "e_argon", "e_opus", "judge_std4"], False),
    ("G6b_h4_astra_argon_global", ["h4_astra", "h4_argon"], ["e_astra", "e_argon"], False),
    ("G9_h4_3fam_q8b_global", ["h4_astra", "h4_argon", "h4_opus", "qwen3_8b"], ["e_astra", "e_argon", "e_opus", "e_q8b", "judge_std4"], False),
    ("G9b_h4_astra_argon_q8b_global", ["h4_astra", "h4_argon", "qwen3_8b"], ["e_astra", "e_argon", "e_q8b"], False),
    ("G11_hybrid_struct_global", ["h4_astra", "h4_argon", "h4_opus", "qwen3_8b"], ["e_astra", "e_argon", "e_opus", "e_q8b", "judge_std4", "excess_thm_log", "cand_sorry_count", "ident_jaccard", "edit"], False),
]


def build_lp_and_x(D: dict, dist_keys: list[str], feat_keys: list[str]) -> tuple[np.ndarray, np.ndarray]:
    if dist_keys:
        lp_stack = np.stack([dl.centered_log_probs(D["dists"][k]) for k in dist_keys], axis=1)
    else:
        lp_stack = np.zeros((D["n"], 0, 6), dtype=np.float64)
    if feat_keys:
        x = np.column_stack([D["feats"][k] for k in feat_keys])
    else:
        x = np.zeros((D["n"], 0), dtype=np.float64)
    return lp_stack, x


def make_4fold_inner_tasks(D: dict) -> np.ndarray:
    """Assign 4 stratified task folds over non-test items strictly from train/val tasks."""
    tasks_old = sorted({t for t, s in zip(D["task"], D["set"]) if s == "old"})
    tasks_new = sorted({t for t, s in zip(D["task"], D["set"]) if s == "new"})
    task_to_fold = {}
    for idx, t in enumerate(tasks_old):
        task_to_fold[t] = idx % 4
    for idx, t in enumerate(tasks_new):
        task_to_fold[t] = (idx + 2) % 4
    return np.array([task_to_fold[t] for t in D["task"]], dtype=int)


def cv_score_candidate(
    D: dict,
    inner_fold: np.ndarray,
    dist_keys: list[str],
    feat_keys: list[str],
    objective: str,
    alpha: float,
    dirichlet_eta: float,
    use_quad: bool,
    set_aware: bool,
) -> tuple[dict, float]:
    lp_stack, x = build_lp_and_x(D, dist_keys, feat_keys)
    q_oof = np.zeros((D["n"], 6), dtype=np.float64)
    for f in range(4):
        tr = np.where(inner_fold != f)[0]
        va = np.where(inner_fold == f)[0]
        cal = dl.MKCalibrator(
            objective=objective, alpha=alpha, alpha_a=0.05, dirichlet_eta=dirichlet_eta,
            use_quad=use_quad, set_aware_prior=set_aware,
        )
        cal.fit(lp_stack[tr], x[tr], D["is_new"][tr], D["P"][tr])
        q_oof[va] = cal.predict(lp_stack[va], x[va], D["is_new"][va])

    # Also compute single exp27 train->val RPS for parity comparison
    tr27 = np.where(D["exp27_split"] == "train")[0]
    va27 = np.where(D["exp27_split"] == "val")[0]
    cal27 = dl.MKCalibrator(
        objective=objective, alpha=alpha, alpha_a=0.05, dirichlet_eta=dirichlet_eta,
        use_quad=use_quad, set_aware_prior=set_aware,
    ).fit(lp_stack[tr27], x[tr27], D["is_new"][tr27], D["P"][tr27])
    q_va27 = cal27.predict(lp_stack[va27], x[va27], D["is_new"][va27])
    va27_rps = float(dl.rps_items(D["P"][va27], q_va27).mean())

    return dl.evaluate_panel(D["P"], q_oof), va27_rps


def main() -> None:
    t0 = time.time()
    D = de.load_bundle(include_test=False)
    print(f"[search] Loaded {D['n']} non-test items ({len(set(D['task']))} tasks). lanes={D['has_lanes']} qwen={D['has_qwen']}", flush=True)
    inner_fold = make_4fold_inner_tasks(D)

    # Constant baseline on 4-fold inner CV
    q_const_global = np.zeros((D["n"], 6))
    q_const_set = np.zeros((D["n"], 6))
    for f in range(4):
        tr = np.where(inner_fold != f)[0]
        va = np.where(inner_fold == f)[0]
        pg = dl.smooth(D["C"][tr].sum(0) / D["C"][tr].sum())
        q_const_global[va] = pg
        for idx_i in va:
            mask = (inner_fold != f) & (D["is_new"] == D["is_new"][idx_i])
            c = D["C"][mask].sum(0)
            q_const_set[idx_i] = dl.smooth(c / c.sum()) if c.sum() > 0 else pg

    const_global_m = dl.evaluate_panel(D["P"], q_const_global)
    const_set_m = dl.evaluate_panel(D["P"], q_const_set)

    # Raw uncalibrated frontier / Qwen distributions on non-test 105 items
    raw_panel = {}
    for k, q_raw in D["dists"].items():
        raw_panel[k] = dl.evaluate_panel(D["P"], q_raw)

    results = []
    for cname, dkeys, fkeys, sa in CANDIDATE_SPECS:
        for obj in ("ce", "rps"):
            for alpha in (0.3, 1.0, 3.0, 10.0):
                for eta in (0.0, 0.05, 0.12):
                    for uq in (True, False):
                        m, va27_rps = cv_score_candidate(D, inner_fold, dkeys, fkeys, obj, alpha, eta, uq, sa)
                        results.append({
                            "candidate": cname,
                            "dist_keys": dkeys,
                            "feat_keys": fkeys,
                            "objective": obj,
                            "alpha": alpha,
                            "dirichlet_eta": eta,
                            "use_quad": uq,
                            "set_aware": sa,
                            "inner_cv": m,
                            "exp27_val_rps": va27_rps,
                        })

    results.sort(key=lambda r: r["inner_cv"]["RPS"])
    top15 = results[:15]

    # Best per candidate family (CE and RPS separately)
    best_by_family = {}
    for cname, _, _, _ in CANDIDATE_SPECS:
        for obj in ("ce", "rps"):
            sub = [r for r in results if r["candidate"] == cname and r["objective"] == obj]
            if sub:
                best_by_family[f"{cname}__{obj}"] = sub[0]

    # Also find best single-set (non-global vs global) overall winner
    winner_set = [r for r in results if r["set_aware"]][0]
    winner_global = [r for r in results if not r["set_aware"]][0]

    out = {
        "n_nontest_items": int(D["n"]),
        "n_nontest_tasks": int(len(set(D["task"]))),
        "search_seconds": round(time.time() - t0, 2),
        "has_lanes": D["has_lanes"],
        "has_qwen": D["has_qwen"],
        "constant_global_inner_cv": const_global_m,
        "constant_set_aware_inner_cv": const_set_m,
        "raw_dists_nontest": raw_panel,
        "winner_set_aware": winner_set,
        "winner_global": winner_global,
        "top15": top15,
        "best_by_family": best_by_family,
    }
    out_path = de.RES_DIR / "inner_cv_search_11-26-2026.json"
    out_path.write_text(json.dumps(out, indent=2))
    print(f"[search] Done in {out['search_seconds']}s -> {out_path}")
    print(f"  const_set RPS={const_set_m['RPS']:.4f} CE={const_set_m['CE']:.4f} TVD={const_set_m['TVD']:.4f}")
    print(f"  winner_set: {winner_set['candidate']} ({winner_set['objective']}, alpha={winner_set['alpha']}, eta={winner_set['dirichlet_eta']}, quad={winner_set['use_quad']}) -> RPS={winner_set['inner_cv']['RPS']:.4f} CE={winner_set['inner_cv']['CE']:.4f} TVD={winner_set['inner_cv']['TVD']:.4f} Pearson={winner_set['inner_cv']['Pearson']:.4f}")
    print(f"  winner_global: {winner_global['candidate']} ({winner_global['objective']}, alpha={winner_global['alpha']}, eta={winner_global['dirichlet_eta']}) -> RPS={winner_global['inner_cv']['RPS']:.4f} CE={winner_global['inner_cv']['CE']:.4f} TVD={winner_global['inner_cv']['TVD']:.4f} Pearson={winner_global['inner_cv']['Pearson']:.4f}")


if __name__ == "__main__":
    main()
