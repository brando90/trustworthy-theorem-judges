# TLDR: Scores returned C15 warm-up sheets against the sealed May expert means under amendment C17 (qualify on W01a-c only, mean absolute difference <= 1.0; the six-file W01+W02 value is printed as a disclosed sensitivity, never a verdict), per rater: qualifying MAE, six-file MAE, per-folder MAE, verdict, Lean familiarity and minutes; a rater who was one of the three May experts is scored against the other two experts' mean (--leave-out-expert); refuses duplicate or incomplete sheets and any key whose digest is not the sealed one; zero model calls, writes nothing.
"""Usage from the trustworthy-theorem-judges root:
  python3 experiments/09_human_rating_collection/support/scripts/legacy/score_warmup.py private/SHEET.csv [private/SHEET2.csv ...] [--qualify-task W01] [--key PATH] [--synthetic-key]
  python3 experiments/09_human_rating_collection/support/scripts/legacy/score_warmup.py private/SHEET.csv --leave-out-expert K   (one sheet; K = 1, 2 or 3)
(Use the normalized copies written by import_rating_sheet.py.)

--qualify-task  folder(s) whose items decide qualification; default W01 (amendment C17); repeat the flag for more
                folders; ALL = every warm-up item (the pre-C17 C15 rule, now reported only as a sensitivity).
--key           the sealed key (default: the pinned private snapshot); its SHA-256 digest must equal
                sealed_key_sha256 in that snapshot's human_round/warmup/WARMUP_MANIFEST.json.
--synthetic-key self-test only: accept a key whose digest is not the sealed one; every line is then marked SYNTHETIC.
--allow-missing-nonqualifying  C17 addendum (10-20-2026): score a sheet whose only missing items lie outside the
                qualification task (W02 rows the importer recorded as N/A reference-issue rows); the verdict uses the
                qualification items as usual and the six-file sensitivity is printed as unavailable.
--leave-out-expert K  leave-one-out target for a rater who was May expert pK (p1-p3; the key's expert_scores_0_5
                are [p1, p2, p3]): every item's target becomes the mean of the other two experts' May scores, so the
                rater's own May rating never sits in their target (Brando, 10-20-2026). Scores exactly one sheet. The
                lenient May raters (p4, p5) and raters new to the May round keep the three-expert mean.

Never show a rater the key or other raters' results before every set-N sheet is in.
"""
import argparse
import csv
import hashlib
import io
import json
from pathlib import Path
from packet_release import require_release

# Use the pinned committed snapshot, not the stale shared VeriBench checkout.
EXP = (Path(__file__).resolve().parents[5] / "private/09_human_rating_collection/upstream_source"
       / "experiments/102_rescore_vbv1_paper_fsc_with_validated_judge_rewrite_tmlr_icml")
KEY = EXP / "human_round/warmup/sealed/WARMUP_KEY.json"
MANIFEST = EXP / "human_round/warmup/WARMUP_MANIFEST.json"
DEFAULT_QUALIFY = ["W01"]  # amendment C17, 10-13-2026


def read_rows(path):
    lines = Path(path).read_text().splitlines(keepends=True)
    i = 0
    while i < len(lines) and lines[i].startswith("#"):  # only the leading template comment
        i += 1
    return list(csv.DictReader(io.StringIO("".join(lines[i:]))))


def mae(scored, target, items):
    return sum(abs(s - target[i]) for i, s in scored if i in items) / len(items)


def main(paths, qualify_tasks, key_path, synthetic, allow_missing_nonqualifying=False, leave_out_expert=None):
    require_release("warmup")
    if leave_out_expert is not None and len(paths) != 1:
        raise SystemExit("--leave-out-expert scores one rater; pass exactly one sheet")
    key_bytes = Path(key_path).read_bytes()
    sealed = json.loads(MANIFEST.read_text())["sealed_key_sha256"]
    digest = hashlib.sha256(key_bytes).hexdigest()
    if digest != sealed and not synthetic:
        raise SystemExit(f"key {key_path} has digest {digest[:12]}..., not the sealed {sealed[:12]}...; refusing to score")
    tag = " [SYNTHETIC KEY, self-test only]" if digest != sealed else ""
    key = json.loads(key_bytes)
    cutoff = key["cutoff_mae_0_5"]
    target = {k["item_id"]: k["expert_mean_0_5"] for k in key["items"]}
    loo_txt = ""
    if leave_out_expert is not None:
        short = sorted(k["item_id"] for k in key["items"]
                       if len(k.get("expert_scores_0_5") or []) != 3 or None in k["expert_scores_0_5"])
        if short:
            raise SystemExit(f"--leave-out-expert needs three May expert scores per item; not available for {short}")
        target = {k["item_id"]: sum(s for j, s in enumerate(k["expert_scores_0_5"], 1) if j != leave_out_expert) / 2
                  for k in key["items"]}
        loo_txt = f" against the leave-one-out target (May expert p{leave_out_expert} omitted)"
    folders = sorted({i[:3] for i in target})
    q_tasks = folders if qualify_tasks == ["ALL"] else qualify_tasks
    unknown = [t for t in q_tasks if t not in folders]
    if unknown:
        raise SystemExit(f"--qualify-task {unknown} not in the warm-up folders {folders}")
    q_items = sorted(i for i in target if i[:3] in q_tasks)
    rule = f"C17 qualification on {', '.join(q_items)}" if q_tasks != folders else f"qualification on all {len(target)} items (C15 rule)"
    rule += loo_txt
    for p in paths:
        rows = [r for r in read_rows(p) if (r.get("item_id") or "").strip() in target]
        scored = [((r["item_id"] or "").strip(), float(r["final_score_0_5"])) for r in rows
                  if (r.get("final_score_0_5") or "").strip()]
        rater = next((r["rater_id"] for r in rows if (r.get("rater_id") or "").strip()), Path(p).stem)
        ids = [i for i, _ in scored]
        dups = sorted({i for i in ids if ids.count(i) > 1})
        missing = sorted(set(target) - set(ids))
        excused = allow_missing_nonqualifying and not dups and missing and not set(missing) & set(q_items)
        if (dups or missing) and not excused:
            print(f"{rater}: NOT SCORED (duplicates {dups}, missing {missing}){tag}")
            continue
        mae_q = mae(scored, target, q_items)
        mae_all = None if missing else mae(scored, target, sorted(target))
        have = {i for i, _ in scored}
        by_folder = ", ".join(f"{f} {mae(scored, target, [i for i in target if i[:3] == f]):.2f}"
                              if all(i in have for i in target if i[:3] == f) else f"{f} unavailable" for f in folders)
        fam = sorted({(r.get("lean_familiarity") or "").strip().lower() for r in rows} - {""})
        mins = [(r.get("minutes_spent") or "").strip() for r in rows]
        known = [float(m) for m in mins if m]
        mins_txt = f"{sum(known):g}" + (f" ({mins.count('')} of {len(mins)} files missing)" if mins.count("") else "")
        verdict = "QUALIFIES" if round(mae_q, 9) <= cutoff else "does not qualify (extra ratings only)"
        if mae_all is None:
            six_txt = f"unavailable (not rated: {', '.join(missing)}; C17 addendum 10-20-2026)"
        else:
            six_txt = f"{mae_all:.2f} (would {'QUALIFIES' if round(mae_all, 9) <= cutoff else 'does not qualify'})"
        print(f"{rater}: {rule}: mean abs diff {mae_q:.2f} (cutoff {cutoff}) -> {verdict}; "
              f"six-file sensitivity (C15 rule, not a target): {six_txt}; by folder: {by_folder}; "
              f"lean {fam or ['missing']}; minutes {mins_txt}{tag}")


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("sheets", nargs="+")
    ap.add_argument("--qualify-task", action="append", default=None)
    ap.add_argument("--key", default=str(KEY))
    ap.add_argument("--synthetic-key", action="store_true")
    ap.add_argument("--allow-missing-nonqualifying", action="store_true")
    ap.add_argument("--leave-out-expert", type=int, choices=(1, 2, 3), default=None)
    a = ap.parse_args()
    main(a.sheets, a.qualify_task or DEFAULT_QUALIFY, a.key, a.synthetic_key, a.allow_missing_nonqualifying,
         a.leave_out_expert)
