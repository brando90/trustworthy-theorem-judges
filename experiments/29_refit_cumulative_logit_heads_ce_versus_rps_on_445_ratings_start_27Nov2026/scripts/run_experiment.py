#!/usr/bin/env python3
"""Select on validation ranked probability score, then score the held-out tasks once.

Stages:
  select  — fit on the 20 training tasks, score the 10 validation tasks, write the grid.
            Does not compute a test metric.
  eval    — read the saved selection, refit on train+validation, score the 20 test tasks.
  nested  — 5-fold task out-of-fold with H3 removed. Selection stays inside each outer fold.
"""
from __future__ import annotations

import argparse
import csv
import json
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lib29 import (  # noqa: E402
    F8_FEATURES, LOGPOOL_SOURCES, NESTED_ORDINAL_FEATURES, ORDINAL_FEATURES, TEMPERATURES,
    better_val, ce, fit_config, iter_specs, marginal, primary_eligible, rps, score_rows,
    smooth, task_bootstrap, tvd,
)

EXP = Path(__file__).resolve().parents[1]
DATA = EXP / "data_11-27-2026/artifacts_11-27-2026.csv"
SEL_PATH = EXP / "results/validation_selection_11-27-2026.json"
GRID_PATH = EXP / "results/validation_grid_11-27-2026.csv"
EVAL_PATH = EXP / "results/heldout_eval_11-27-2026.json"
NESTED_PATH = EXP / "results/nested_oof_11-27-2026.json"
DRAWS = 10000
SEED = 20261127


def load_artifacts(rating_mode="all"):
    rows = list(csv.DictReader(DATA.open(newline="")))
    assert len(rows) == 175
    kept = []
    for row in rows:
        n_key = {"all": "n_all", "drop_blank": "n_drop_blank", "schema": "n_schema"}[rating_mode]
        r_key = {"all": "ratings_all", "drop_blank": "ratings_drop_blank", "schema": "ratings_schema"}[rating_mode]
        n = int(row[n_key])
        if n <= 0:
            continue
        ratings = [int(x) for x in row[r_key].split()]
        assert len(ratings) == n
        row = dict(row)
        row["ratings"] = ratings
        kept.append(row)
    n = len(kept)
    D = {
        "item": np.array([r["item"] for r in kept]),
        "task": np.array([r["task"] for r in kept]),
        "set": np.array([r["set"] for r in kept]),
        "split": np.array([r["split"] for r in kept]),
        "cv5_fold": np.array([int(r["cv5_fold"]) for r in kept]),
        "P": np.zeros((n, 6)),
        "C": np.zeros((n, 6)),
    }
    for i, row in enumerate(kept):
        D["C"][i] = np.bincount(row["ratings"], minlength=6)
        D["P"][i] = D["C"][i] / D["C"][i].sum()
    float_cols = [
        "astra", "opus", "h3_score", "h3_expected", "h4_astra", "h4_argon", "h4_opus",
        "thm_ratio", "excess_thm_log", "ident_jaccard", "edit_similarity",
    ]
    for col in float_cols:
        D[col] = np.array([float(r[col]) for r in kept])
    D["isnew"] = (D["set"] == "new").astype(float)
    for prefix in ("h2", "h3", "h4_astra", "h4_argon", "h4_opus"):
        D[prefix + "_prob"] = np.array([[float(r[f"{prefix}_p{k}"]) for k in range(6)] for r in kept])
    D["n"] = n
    return D


def index(D, split):
    return np.where(D["split"] == split)[0]


def constant_forecasts(D, fit_idx, eval_idx):
    sets = D["set"][eval_idx]
    per = {s: marginal(D["C"][fit_idx][D["set"][fit_idx] == s]) for s in ("old", "new")}
    pooled = marginal(D["C"][fit_idx])
    return {
        "constant_set": np.stack([per[s] for s in sets]),
        "constant_pooled": np.repeat(pooled[None, :], len(eval_idx), axis=0),
        "uniform": np.full((len(eval_idx), 6), 1.0 / 6.0),
    }


def eval_spec_on(D, fit_idx, score_idx, spec, temperature):
    model = fit_config(D, fit_idx, spec)
    Q = model.predict(D, score_idx, temperature)
    P = D["P"][score_idx]
    return model, Q, score_rows(P, Q)


def select(D):
    tr, va = index(D, "train"), index(D, "val")
    assert set(D["task"][tr]).isdisjoint(D["task"][va])
    assert set(D["task"][tr]).isdisjoint(D["task"][index(D, "test")])
    rows = []
    best_primary = None
    best_set = None
    best_ce = None
    best_rps = None
    specs = list(iter_specs(ORDINAL_FEATURES, LOGPOOL_SOURCES, include_set_aware=True))
    print(f"configs {len(specs)} x temperatures {len(TEMPERATURES)}", flush=True)
    for i, spec in enumerate(specs):
        model = fit_config(D, tr, spec)
        P = D["P"][va]
        for temperature in TEMPERATURES:
            Q = model.predict(D, va, temperature)
            sc = score_rows(P, Q)
            rec = {
                **{k: spec[k] for k in ("family", "feature_set", "objective", "alpha", "mix", "const_mode", "set_aware")},
                "features": spec["features"], "sources": spec["sources"],
                "temperature": temperature,
                "val_rps": sc["RPS"], "val_ce": sc["CE"], "val_tvd": sc["TVD"],
                "optimizer_success": model.optimizer_success,
                "primary_eligible": primary_eligible(spec),
            }
            rows.append(rec)
            if rec["primary_eligible"] and better_val(rec, best_primary):
                best_primary = rec
            if rec["set_aware"] and better_val(rec, best_set):
                best_set = rec
            if rec["primary_eligible"] and rec["family"] == "ordinal" and rec["objective"] == "ce" and better_val(rec, best_ce):
                best_ce = rec
            if rec["primary_eligible"] and rec["family"] == "ordinal" and rec["objective"] == "rps" and better_val(rec, best_rps):
                best_rps = rec
        if (i + 1) % 100 == 0:
            print(f"  fit {i+1}/{len(specs)} best primary val RPS {best_primary['val_rps']:.4f} {best_primary['feature_set']} {best_primary['objective']}", flush=True)
    # Fixed experiment-27 configuration, temperature 1, scored on validation only.
    f8 = {
        "family": "ordinal", "feature_set": "h2_h3", "features": list(F8_FEATURES), "sources": [],
        "objective": "ce", "alpha": 0.0, "mix": 0.0, "const_mode": "pooled", "set_aware": False,
        "temperature": 1.0,
    }
    _, _, f8_val = eval_spec_on(D, tr, va, f8, 1.0)
    f8["val_rps"], f8["val_ce"], f8["val_tvd"] = f8_val["RPS"], f8_val["CE"], f8_val["TVD"]
    const = constant_forecasts(D, tr, va)
    const_val = {k: score_rows(D["P"][va], Q) for k, Q in const.items()}
    payload = {
        "date": "11-27-2026",
        "selection_rule": "lowest validation ranked probability score; ties: lower validation cross-entropy, then smaller L2 penalty, then temperature closer to 1, then smaller mixture weight",
        "fit_tasks": "train (20 tasks)",
        "score_tasks": "val (10 tasks)",
        "test_metrics_computed": False,
        "primary": best_primary,
        "best_primary_ce_ordinal": best_ce,
        "best_primary_rps_ordinal": best_rps,
        "best_set_aware": best_set,
        "f8_ce_alpha0_mix0_T1": f8,
        "validation_constants": {k: {"RPS": v["RPS"], "CE": v["CE"], "TVD": v["TVD"]} for k, v in const_val.items()},
        "n_rows": len(rows),
    }
    SEL_PATH.write_text(json.dumps(payload, indent=2) + "\n")
    with GRID_PATH.open("w", newline="") as handle:
        fields = ["primary_eligible", "set_aware", "family", "feature_set", "objective", "alpha", "mix", "const_mode", "temperature", "val_rps", "val_ce", "val_tvd", "optimizer_success"]
        writer = csv.DictWriter(handle, fieldnames=fields, extrasaction="ignore", lineterminator="\n")
        writer.writeheader()
        for rec in sorted(rows, key=lambda r: (r["val_rps"], r["val_ce"])):
            writer.writerow(rec)
    print("PRIMARY", json.dumps(best_primary, indent=2))
    print("BEST CE ORDINAL", json.dumps(best_ce, indent=2))
    print("BEST RPS ORDINAL", json.dumps(best_rps, indent=2))
    print("BEST SET-AWARE", json.dumps(best_set, indent=2))
    print("F8 val", f8_val["RPS"], "const set", const_val["constant_set"]["RPS"])
    return payload


def pack_metrics(P, Q, tasks, sets):
    per = {
        "RPS": rps(P, Q), "CE": ce(P, Q), "TVD": tvd(P, Q),
    }
    out = {"n_artifacts": int(len(P)), "n_tasks": int(len(set(tasks.tolist()))), "cohorts": {}}
    for cohort in ("pooled", "old", "new"):
        mask = np.ones(len(P), dtype=bool) if cohort == "pooled" else sets == cohort
        cols = {m: per[m][mask] for m in per}
        point, ci, p_ge0, _ = task_bootstrap(tasks[mask], cols, DRAWS, SEED)
        block = {}
        for m in per:
            block[m] = {"point": point[m], "ci95": ci[m]}
        sc = score_rows(P[mask], Q[mask])
        block["bias_judge_minus_human"] = sc["bias_judge_minus_human"]
        block["mean_judge"] = sc["mean_judge"]
        block["mean_human"] = sc["mean_human"]
        block["mae"] = sc["mae"]
        block["spearman"] = sc["spearman"]
        block["pearson"] = sc["pearson"]
        block["rps_floor"] = sc["rps_floor"]
        block["n_artifacts"] = int(mask.sum())
        block["n_tasks"] = int(len(set(tasks[mask].tolist())))
        out["cohorts"][cohort] = block
    return out


def paired_against_constant(P, Q, Qconst, tasks, sets):
    diff = rps(P, Q) - rps(P, Qconst)
    diff_ce = ce(P, Q) - ce(P, Qconst)
    diff_tvd = tvd(P, Q) - tvd(P, Qconst)
    out = {}
    for cohort in ("pooled", "old", "new"):
        mask = np.ones(len(P), dtype=bool) if cohort == "pooled" else sets == cohort
        point, ci, p_ge0, _ = task_bootstrap(tasks[mask], {
            "dRPS": diff[mask], "dCE": diff_ce[mask], "dTVD": diff_tvd[mask],
        }, DRAWS, SEED)
        out[cohort] = {
            m: {"point": point[m], "ci95": ci[m], "p_ge0": p_ge0[m]}
            for m in ("dRPS", "dCE", "dTVD")
        }
    return out


def verdict(block, paired):
    d = paired["pooled"]["dRPS"]
    ce_ok = block["cohorts"]["pooled"]["CE"]["point"] < None or True
    return d, ce_ok


def evaluate(D, rating_mode, selection):
    fit_idx = np.where(D["split"] != "test")[0]
    te = index(D, "test")
    assert set(D["task"][fit_idx]).isdisjoint(D["task"][te])
    P = D["P"][te]
    tasks, sets = D["task"][te], D["set"][te]
    consts = constant_forecasts(D, fit_idx, te)
    named = {
        "f8_ce_refit": selection["f8_ce_alpha0_mix0_T1"],
        "primary": selection["primary"],
        "best_ce_ordinal": selection["best_primary_ce_ordinal"],
        "best_rps_ordinal": selection["best_primary_rps_ordinal"],
        "best_converged_primary": selection["best_converged_primary"],
        "best_set_aware": selection["best_set_aware"],
    }
    forecasts = {}
    fit_notes = {}
    for name, spec in named.items():
        model, Q, _ = eval_spec_on(D, fit_idx, te, spec, spec["temperature"])
        forecasts[name] = Q
        fit_notes[name] = {
            "optimizer_success": model.optimizer_success,
            "trainval_loss": model.train_loss,
            "config": {k: spec[k] for k in spec if k not in ("features", "sources")} | {
                "features": spec.get("features", []), "sources": spec.get("sources", []),
            },
        }
    for name, Q in consts.items():
        forecasts[name] = Q
    report = {
        "date": "11-27-2026",
        "rating_mode": rating_mode,
        "n_artifacts_loaded": int(D["n"]),
        "fit": "train+val, hyperparameters taken from the validation file, not re-selected",
        "bootstrap": {"draws": DRAWS, "seed": SEED, "unit": "task", "point": "mean over artifacts"},
        "models": {},
    }
    for name, Q in forecasts.items():
        report["models"][name] = pack_metrics(P, Q, tasks, sets)
        if name not in consts:
            report["models"][name]["paired_vs_constant_set"] = paired_against_constant(P, Q, consts["constant_set"], tasks, sets)
            report["models"][name]["fit"] = fit_notes[name]
    # Verdict uses the primary forecast only, on all-scores ratings.
    if rating_mode == "all":
        d = report["models"]["primary"]["paired_vs_constant_set"]["pooled"]["dRPS"]
        prim = report["models"]["primary"]["cohorts"]["pooled"]
        const = report["models"]["constant_set"]["cohorts"]["pooled"]
        ce_ok = prim["CE"]["point"] < const["CE"]["point"]
        tvd_ok = prim["TVD"]["point"] < const["TVD"]["point"]
        works = d["ci95"][1] < 0 and ce_ok and tvd_ok and d["point"] < 0
        promising = d["point"] < 0 and ce_ok and tvd_ok
        report["verdict"] = "works" if works else ("promising" if promising else "not_found")
        report["verdict_rule"] = "works if pooled paired RPS vs the set-aware constant has 95% task-bootstrap interval entirely below 0 and point CE and TVD are lower; promising if the three point estimates are lower but the RPS interval includes 0"
    return report


def nested(D):
    """H3-free 5-fold out-of-fold. Outer fold ids are the experiment 28 draw."""
    folds = sorted(set(D["cv5_fold"].tolist()))
    assert folds == [0, 1, 2, 3, 4]
    Q = np.zeros((D["n"], 6))
    chosen = []
    menu = list(iter_specs(NESTED_ORDINAL_FEATURES, {"h2_h4": LOGPOOL_SOURCES["h2_h4"], "h4": LOGPOOL_SOURCES["h4"]}, include_set_aware=False))
    # Same temperature is scored on every inner fold, so the selected temperature is the one whose mean inner ranked probability score won.
    temps = (1.0, 1.5)
    menu = [s for s in menu if s["alpha"] in (0.0, 1.0) and s["mix"] in (0.0, 0.25)]
    print(f"nested menu {len(menu)} configs x {len(temps)} temperatures", flush=True)
    for fold in folds:
        te = np.where(D["cv5_fold"] == fold)[0]
        train_mask = D["cv5_fold"] != fold
        train_tasks = sorted(set(D["task"][train_mask].tolist()))
        rng = np.random.default_rng(20261127 + fold)
        old_tasks = [t for t in train_tasks if np.any((D["task"] == t) & (D["set"] == "old"))]
        new_tasks = [t for t in train_tasks if np.any((D["task"] == t) & (D["set"] == "new"))]
        rng.shuffle(old_tasks)
        rng.shuffle(new_tasks)
        inner = {task: i % 4 for i, task in enumerate(old_tasks)}
        inner.update({task: i % 4 for i, task in enumerate(new_tasks)})
        task_inner = np.array([inner.get(t, -1) for t in D["task"]])
        best = None
        best_spec = None
        for spec in menu:
            fitted = []
            for inner_fold in range(4):
                fit_idx = np.where(train_mask & (task_inner != inner_fold) & (task_inner >= 0))[0]
                score_idx = np.where(task_inner == inner_fold)[0]
                fitted.append((fit_config(D, fit_idx, spec), score_idx))
            for temperature in temps:
                mean_rps = float(np.mean([
                    score_rows(D["P"][score_idx], model.predict(D, score_idx, temperature))["RPS"]
                    for model, score_idx in fitted
                ]))
                mean_ce = float(np.mean([
                    score_rows(D["P"][score_idx], model.predict(D, score_idx, temperature))["CE"]
                    for model, score_idx in fitted
                ]))
                rec = {
                    "val_rps": mean_rps, "val_ce": mean_ce, "temperature": temperature,
                    "alpha": spec["alpha"], "mix": spec["mix"], "feature_set": spec["feature_set"],
                    "objective": spec["objective"],
                }
                if better_val(rec, best):
                    best = rec
                    best_spec = dict(spec)
                    best_spec["temperature"] = temperature
        fit_idx = np.where(train_mask)[0]
        model = fit_config(D, fit_idx, best_spec)
        Q[te] = model.predict(D, te, best_spec["temperature"])
        chosen.append({"fold": fold, "n_test": int(len(te)), **{k: best_spec[k] for k in ("family", "feature_set", "objective", "alpha", "mix", "temperature")}, "inner_rps": best["val_rps"]})
        print(
            f"fold {fold} chose {best_spec['feature_set']} {best_spec['objective']} a={best_spec['alpha']} m={best_spec['mix']} T={best_spec['temperature']} inner RPS {best['val_rps']:.4f}",
            flush=True,
        )
    P, tasks, sets = D["P"], D["task"], D["set"]
    # Set-aware constant inside each fold, from that fold's training rows only.
    Qconst = np.zeros_like(Q)
    for fold in folds:
        te = np.where(D["cv5_fold"] == fold)[0]
        fit_idx = np.where(D["cv5_fold"] != fold)[0]
        Qconst[te] = constant_forecasts(D, fit_idx, te)["constant_set"]
    report = {
        "date": "11-27-2026",
        "description": "H3-free nested 5-fold. Each outer fold selects on an inner 4-fold of its 40 training tasks, then refits on those 40 and scores the 10 held-out tasks.",
        "h3_excluded": True,
        "menu_note": "alpha in {0, 1}, mix in {0, 0.25}, temperature in {1, 1.5}, ordinal features h2 / h4 / h2_h4 / h2_h4_struct and log-pool h2_h4 / h4",
        "chosen_per_fold": chosen,
        "models": {
            "nested_primary": pack_metrics(P, Q, tasks, sets),
            "constant_set": pack_metrics(P, Qconst, tasks, sets),
        },
    }
    report["models"]["nested_primary"]["paired_vs_constant_set"] = paired_against_constant(P, Q, Qconst, tasks, sets)
    d = report["models"]["nested_primary"]["paired_vs_constant_set"]["pooled"]["dRPS"]
    prim = report["models"]["nested_primary"]["cohorts"]["pooled"]
    const = report["models"]["constant_set"]["cohorts"]["pooled"]
    ce_ok = prim["CE"]["point"] < const["CE"]["point"]
    tvd_ok = prim["TVD"]["point"] < const["TVD"]["point"]
    works = d["ci95"][1] < 0 and ce_ok and tvd_ok and d["point"] < 0
    promising = d["point"] < 0 and ce_ok and tvd_ok
    report["verdict_vs_constant"] = "works" if works else ("promising" if promising else "not_found")
    NESTED_PATH.write_text(json.dumps(report, indent=2) + "\n")
    print("NESTED", report["verdict_vs_constant"], d)
    return report


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--stage", choices=("select", "eval", "nested"), required=True)
    args = parser.parse_args()
    if args.stage == "select":
        select(load_artifacts("all"))
        return
    if args.stage == "nested":
        nested(load_artifacts("all"))
        return
    selection = json.loads(SEL_PATH.read_text())
    if selection.get("test_metrics_computed"):
        raise RuntimeError("selection file unexpectedly marked as having test metrics")
    reports = {"all": evaluate(load_artifacts("all"), "all", selection)}
    for mode in ("drop_blank", "schema"):
        reports[mode] = evaluate(load_artifacts(mode), mode, selection)
    payload = {"selection_summary": {k: selection[k] for k in ("primary", "best_primary_ce_ordinal", "best_primary_rps_ordinal", "best_set_aware", "f8_ce_alpha0_mix0_T1", "validation_constants")}, "by_rating_mode": reports}
    EVAL_PATH.write_text(json.dumps(payload, indent=2) + "\n")
    prim = reports["all"]["models"]["primary"]
    f8 = reports["all"]["models"]["f8_ce_refit"]
    const = reports["all"]["models"]["constant_set"]
    print("VERDICT", reports["all"]["verdict"])
    for cohort in ("pooled", "old", "new"):
        print(cohort,
              "primary", round(prim["cohorts"][cohort]["RPS"]["point"], 4), prim["paired_vs_constant_set"][cohort]["dRPS"],
              "f8", round(f8["cohorts"][cohort]["RPS"]["point"], 4),
              "const", round(const["cohorts"][cohort]["RPS"]["point"], 4))


if __name__ == "__main__":
    main()
