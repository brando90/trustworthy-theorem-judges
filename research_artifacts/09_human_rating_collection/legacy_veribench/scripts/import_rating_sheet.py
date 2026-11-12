# TLDR: C15 item 11: check a rater's exported Google Sheet (CSV) against the packet's item ids, the rater's delivered folders and the allowed values, then keep immutable raw and normalized snapshots plus a provenance receipt in the git-ignored private_ratings_setN/; zero model calls.
"""Usage:
  python3 scripts/import_rating_sheet.py EXPORT.csv --rater T01 --packet setN|warmup \
      --file-id DRIVE_FILE_ID --source-modified DRIVE_MODIFIED_TIME [--all-folders] \
      [--out-dir human_round/private_ratings_setN] [--receipts <out-dir>/delivery/DELIVERY_RECEIPTS.jsonl]

Rejects the import (exit 1, nothing written) when:
  - required columns are missing, or no row has a final score;
  - a scored row has no item_id, or an item_id is unknown or appears twice;
  - a scored item lies outside the folders delivered to this rater (`--all-folders` only for A1, who rates everything);
  - the sheet names no rater, or more than one, in `rater_id`;
  - a value is outside its allowed set, minutes are not a nonnegative number, or lean_familiarity differs between rows;
  - a warm-up sheet does not score all six warm-up items.
Every accepted import is kept: raw/ and normalized/ get UTC-stamped snapshots that are never overwritten,
<packet>_<rater>.csv is the latest normalized copy, and RECEIPTS.jsonl logs each import.
"""
import argparse
import csv
import hashlib
import io
import json
import math
import sys
from datetime import datetime, timezone
from pathlib import Path

EXP = Path(__file__).resolve().parents[1]
TEMPLATES = {"setN": EXP / "human_round/sample_setN/rating_sheet_TEMPLATE.csv",  # packet v2+: template beside packet/
             "warmup": EXP / "human_round/warmup/rating_sheet_TEMPLATE.csv"}
REQUIRED = ("rater_id", "item_id", "final_score_0_5")
ALLOWED = {"A": {"y", "n"}, "B": {"y", "n"}, "C": {"y", "n"}, "D": {"handful", "dominates", "n/a"},
           "confidence": {"low", "med", "high"}, "lean_familiarity": {"none", "some", "fluent"}}
YESNO = {"yes": "y", "no": "n"}
CONTENT = ("final_score_0_5", "A", "B", "C", "D", "base_score_0_5", "confidence", "rationale", "problem_note", "minutes_spent")


def read_rows(text):
    """Skip only the leading template comment lines, so '#' inside a quoted multi-line note survives."""
    lines = text.splitlines(keepends=True)
    i = 0
    while i < len(lines) and lines[i].startswith("#"):
        i += 1
    reader = csv.DictReader(io.StringIO("".join(lines[i:])))
    return list(reader.fieldnames or []), list(reader)


def score(v):
    v = (v or "").strip()
    if v == "":
        return None
    f = float(v)
    if not math.isfinite(f) or f != int(f) or not 0 <= f <= 5:
        raise ValueError(v)
    return int(f)


def check(text, rater, expected_ids, allowed_folders, packet):
    fields, raw_rows = read_rows(text)
    errors, warnings, out, seen, names, fams = [], [], [], set(), set(), set()
    missing_cols = [c for c in REQUIRED if c not in fields]
    if missing_cols:
        return [], [f"missing required columns: {missing_cols}"], [], None
    for n, r in enumerate(raw_rows, start=2):
        r = {k: (v or "") for k, v in r.items() if k is not None}
        iid = r.get("item_id", "").strip()
        has_content = any(r.get(k, "").strip() for k in CONTENT)
        if not iid:
            if has_content:
                errors.append(f"row {n}: has ratings but no item_id")
            continue
        if iid not in expected_ids:
            errors.append(f"row {n}: unknown item_id {iid!r}")
            continue
        if not has_content:
            continue
        if iid in seen:
            errors.append(f"row {n}: duplicate item_id {iid!r}")
            continue
        seen.add(iid)
        try:
            fs, bs = score(r.get("final_score_0_5")), score(r.get("base_score_0_5"))
        except ValueError as e:
            errors.append(f"row {n} ({iid}): score must be a whole number 0-5, got {e.args[0]!r}")
            continue
        if fs is None:
            warnings.append(f"row {n} ({iid}): notes but no final_score_0_5 (row dropped)")
            continue
        folder = iid[:3]
        if allowed_folders is not None and folder not in allowed_folders:
            errors.append(f"row {n} ({iid}): folder {folder} was not delivered to this rater")
        for k, ok in ALLOWED.items():
            v = r.get(k, "").strip().lower()
            v = YESNO.get(v, v) if k in ("A", "B", "C") else v
            if v and v not in ok:
                errors.append(f"row {n} ({iid}): {k}={r.get(k)!r} not in {sorted(ok)}")
            if k in fields:
                r[k] = v
        mins = r.get("minutes_spent", "").strip()
        if mins:
            try:
                m = float(mins)
                if not math.isfinite(m) or m < 0:
                    raise ValueError
            except ValueError:
                errors.append(f"row {n} ({iid}): minutes_spent must be a nonnegative number, got {mins!r}")
        if r.get("lean_familiarity"):
            fams.add(r["lean_familiarity"])
        name = r.get("rater_id", "").strip()
        if name:
            names.add(name)
        r.update(item_id=iid, task_folder=r.get("task_folder", "").strip(), rater_id=rater,
                 final_score_0_5=fs, base_score_0_5="" if bs is None else bs)
        out.append(r)
    if not out:
        errors.append("no row has a final_score_0_5")
    if not names:
        errors.append("rater_id is empty on every rated row")
    elif len(names) > 1:
        errors.append(f"more than one rater_id in one sheet: {sorted(names)}")
    if len(fams) > 1:
        errors.append(f"lean_familiarity differs between rows: {sorted(fams)}")
    if packet == "warmup":
        missing = sorted(expected_ids - {r["item_id"] for r in out})
        if missing:
            errors.append(f"warm-up incomplete: no final score for {missing}")
    elif allowed_folders is not None:
        unrated = sorted(i for i in expected_ids if i[:3] in allowed_folders and i not in {r["item_id"] for r in out})
        if unrated:
            warnings.append(f"partial submission: {len(unrated)} delivered items unrated ({unrated[:5]}...)")
    return out, errors, warnings, (sorted(names)[0] if len(names) == 1 else None)


def delivered_folders(receipts, rater, packet):
    folders = None
    if receipts.exists():
        for line in receipts.read_text().splitlines():
            rec = json.loads(line)
            if rec.get("rater") == rater and rec.get("packet") == packet:
                folders = set(rec["folders"])  # the latest delivery wins
    return folders


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("export")
    ap.add_argument("--rater", required=True)
    ap.add_argument("--packet", choices=sorted(TEMPLATES), required=True)
    ap.add_argument("--file-id", required=True, help="Drive file id of the rater's shared sheet")
    ap.add_argument("--source-modified", required=True, help="the sheet's Drive modifiedTime at export")
    ap.add_argument("--all-folders", action="store_true", help="A1 only: rates every folder, no delivery receipt")
    ap.add_argument("--out-dir", default=str(EXP / "human_round/private_ratings_setN"))
    ap.add_argument("--receipts", default="")
    a = ap.parse_args()
    out_dir = Path(a.out_dir)
    receipts = Path(a.receipts) if a.receipts else out_dir / "delivery" / "DELIVERY_RECEIPTS.jsonl"
    raw = Path(a.export).read_bytes()
    text = raw.decode("utf-8-sig").replace("\r\n", "\n")
    tfields, trows = read_rows(TEMPLATES[a.packet].read_text())
    expected = {r["item_id"] for r in trows}
    allowed = None if a.all_folders else delivered_folders(receipts, a.rater, a.packet)
    if allowed is None and not a.all_folders:
        sys.exit(f"ERROR no delivery receipt for {a.rater}/{a.packet} in {receipts} (use --all-folders only for A1)")
    rows, errors, warnings, submitted = check(text, a.rater, expected, allowed, a.packet)
    for w in warnings:
        print("WARN", w)
    if errors:
        for e in errors:
            print("ERROR", e)
        sys.exit(1)
    buf = io.StringIO()
    w = csv.DictWriter(buf, fieldnames=tfields, extrasaction="ignore", lineterminator="\n")
    w.writeheader()
    w.writerows(sorted(rows, key=lambda r: r["item_id"]))
    norm = buf.getvalue().encode()
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    base = f"{a.packet}_{a.rater}"
    for sub, data in (("raw", raw), ("normalized", norm)):
        (out_dir / sub).mkdir(parents=True, exist_ok=True)
        snap = out_dir / sub / f"{base}_{stamp}.csv"
        if snap.exists():
            sys.exit(f"ERROR snapshot {snap} already exists; refusing to overwrite")
        snap.write_bytes(data)
    (out_dir / f"{base}.csv").write_bytes(norm)
    receipt = {"rater": a.rater, "submitted_rater_id": submitted, "packet": a.packet, "source_file_id": a.file_id,
               "source_modified": a.source_modified, "imported_utc": stamp,
               "folders_allowed": sorted(allowed) if allowed is not None else "all",
               "sha256_export": hashlib.sha256(raw).hexdigest(), "sha256_normalized": hashlib.sha256(norm).hexdigest(),
               "rows_rated": len(rows), "warnings": warnings,
               "snapshots": [f"raw/{base}_{stamp}.csv", f"normalized/{base}_{stamp}.csv"]}
    with open(out_dir / "RECEIPTS.jsonl", "a") as f:
        f.write(json.dumps(receipt) + "\n")
    print(f"OK {a.rater} ({submitted}) {a.packet}: {len(rows)} rated rows; snapshots {stamp}; "
          f"sha256 {receipt['sha256_normalized'][:12]}")


if __name__ == "__main__":
    main()
