# TLDR: Scores returned C15 warm-up sheets against the sealed May expert means and prints, per rater, the mean absolute difference, whether they qualify (<= 1.0 point), their Lean familiarity and minutes; refuses duplicate or incomplete sheets; zero model calls, writes nothing.
"""Usage: python3 scripts/score_warmup.py SHEET.csv [SHEET2.csv ...]
(Use the normalized copies written by import_rating_sheet.py.)

Never show a rater the key or other raters' results before every set-N sheet is in.
"""
import csv
import io
import json
import sys
from pathlib import Path

EXP = Path(__file__).resolve().parents[1]
KEY = EXP / "human_round/warmup/sealed/WARMUP_KEY.json"


def read_rows(path):
    lines = open(path).read().splitlines(keepends=True)
    i = 0
    while i < len(lines) and lines[i].startswith("#"):  # only the leading template comment
        i += 1
    return list(csv.DictReader(io.StringIO("".join(lines[i:]))))


def main(paths):
    key = json.loads(KEY.read_text())
    cutoff = key["cutoff_mae_0_5"]
    target = {k["item_id"]: k["expert_mean_0_5"] for k in key["items"]}
    for p in paths:
        rows = [r for r in read_rows(p) if (r.get("item_id") or "").strip() in target]
        scored = [((r["item_id"] or "").strip(), float(r["final_score_0_5"])) for r in rows
                  if (r.get("final_score_0_5") or "").strip()]
        rater = next((r["rater_id"] for r in rows if (r.get("rater_id") or "").strip()), Path(p).stem)
        ids = [i for i, _ in scored]
        dups = sorted({i for i in ids if ids.count(i) > 1})
        missing = sorted(set(target) - set(ids))
        if dups or missing:
            print(f"{rater}: NOT SCORED (duplicates {dups}, missing {missing})")
            continue
        mae = sum(abs(s - target[i]) for i, s in scored) / len(scored)
        fam = sorted({(r.get("lean_familiarity") or "").strip().lower() for r in rows} - {""})
        mins = [(r.get("minutes_spent") or "").strip() for r in rows]
        known = [float(m) for m in mins if m]
        mins_txt = f"{sum(known):g}" + (f" ({mins.count('')} of {len(mins)} files missing)" if mins.count("") else "")
        verdict = "QUALIFIES" if mae <= cutoff else "does not qualify (extra ratings only)"
        print(f"{rater}: mean abs diff {mae:.2f} (cutoff {cutoff}) -> {verdict}; lean {fam or ['missing']}; minutes {mins_txt}")


if __name__ == "__main__":
    if len(sys.argv) < 2:
        raise SystemExit(__doc__)
    main(sys.argv[1:])
