# TLDR: C15 item 11: check a rater's exported Google Sheet (CSV), or the rating CSV a rater emailed back (--csv, 10-21-2026), against the packet's item ids, the rater's delivered folders and the allowed values, then keep immutable raw and normalized snapshots plus a provenance receipt in the git-ignored private_ratings_setN/; zero model calls.
"""Usage from the trustworthy-theorem-judges root (keep exports and outputs under private/):
  python3 experiments/09_human_rating_collection/scripts/legacy/import_rating_sheet.py private/EXPORT.csv --rater T01 --packet setN|warmup \
      --file-id DRIVE_FILE_ID --source-modified DRIVE_MODIFIED_TIME [--all-folders] \
      [--out-dir private/IMPORTS] [--receipts <out-dir>/delivery/DELIVERY_RECEIPTS.jsonl]
  python3 experiments/09_human_rating_collection/scripts/legacy/import_rating_sheet.py --csv private/EMAILED.csv --rater V01 --packet warmup \
      --source-message-id GMAIL_MESSAGE_ID --source-modified EMAIL_DATE_UTC [--out-dir private/IMPORTS] [--receipts ...]

The second form is the emailed-CSV route (`emailed_csv_v1_2026-10-21`, coordinator ruling 10-21-2026 09:12 PDT): a rater
whose delivery receipt says "return_route": "emailed_csv" fills the rating_sheet CSV from the zip and emails it back, so
there is no Drive sheet. The CSV attachment, saved byte for byte, is the export; the receipt records its sha256
(sha256_export), file name, the Gmail message id, the delivery thread and the email's date (source_modified). The Drive
route is unchanged. Receipt lines without "folders" (event notes such as a later "sent" record) are not deliveries and
are skipped.

Rejects the import (exit 1, nothing written) when:
  - required columns are missing, or no row has a final score;
  - a scored row has no item_id, or an item_id is unknown or appears twice;
  - a scored item lies outside the folders delivered to this rater (`--all-folders` only for A1, who rates everything);
  - the Drive file id is not the personal sheet delivered to this rater (packet v5 receipts carry sheet_id; A1 uses private coordinator sheet bindings),
    or `--all-folders` is used for anyone but A1;
  - `--csv` is used for a rater whose latest delivery receipt does not say "return_route": "emailed_csv", or a Drive
    export is given for one whose receipt does; the two routes never mix, and `--csv` takes no Drive file id;
  - the export is not UTF-8 text;
  - the sheet names no rater, or more than one, in `rater_id`;
  - a value is outside its allowed set or minutes are not a nonnegative number;
  - a warm-up sheet does not score all six warm-up items, except W02 items named with `--reference-issue-items`
    (C17 addendum of 10-20-2026): those rows must read N/A in final_score_0_5 and carry a stated reference problem
    in rationale or problem_note; they are kept in the raw snapshot and the receipt, never as scores, and W01 items
    (the C17 qualification task) can never be named.
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

# Use the pinned committed snapshot, not the stale shared VeriBench checkout.
EXP = (Path(__file__).resolve().parents[4] / "private/09_human_rating_collection/upstream_source"
       / "experiments/102_rescore_vbv1_paper_fsc_with_validated_judge_rewrite_tmlr_icml")
TEMPLATES = {"setN": EXP / "human_round/sample_setN/rating_sheet_TEMPLATE.csv",  # packet v2+: template beside packet/
             "warmup": EXP / "human_round/warmup/rating_sheet_TEMPLATE.csv"}
REQUIRED = ("rater_id", "item_id", "final_score_0_5")
A1_SHEETS_PATH = EXP / "personal_sheet_ids.json"  # Private coordinator sheet bindings.
ALLOWED = {"A": {"y", "n"}, "B": {"y", "n"}, "C": {"y", "n"}, "D": {"handful", "dominates", "n/a"},
           "confidence": {"low", "med", "high"},
           "independent_rating_attestation": {"yes", "no", "unsure"}}
YESNO = {"yes": "y", "no": "n"}
SYNONYMS = {"confidence": {"medium": "med"}}  # C17 addendum 10-20-2026: the spelled-out value of the template's "med"
NA = {"n/a", "na"}
QUALIFY_TASKS = ("W01",)  # amendment C17: these warm-up items can never be excused as reference-issue rows
CSV_ROUTE = "emailed_csv_v1_2026-10-21"  # coordinator ruling 10-21-2026 09:12 PDT: a rating_sheet CSV returned by email
CONTENT = ("final_score_0_5", "A", "B", "C", "D", "base_score_0_5", "confidence", "rationale", "problem_note", "minutes_spent",
           "model_assistance", "independent_rating_attestation")


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


def normalized_csv(rows, template_fields, submitted_fields):
    """Retain submitted metadata as well as legacy fields; never silently drop new columns."""
    fields = list(dict.fromkeys([*template_fields, *submitted_fields,
                                *(k for row in rows for k in row)]))
    buf = io.StringIO()
    writer = csv.DictWriter(buf, fieldnames=fields, lineterminator="\n")
    writer.writeheader()
    writer.writerows(sorted(rows, key=lambda r: r["item_id"]))
    return buf.getvalue().encode()


def check(text, rater, expected_ids, allowed_folders, packet, ref_issue_items=frozenset()):
    fields, raw_rows = read_rows(text)
    errors, warnings, out, seen, names, fams = [], [], [], set(), set(), set()
    ref_issue = {}
    missing_cols = [c for c in REQUIRED if c not in fields]
    if missing_cols:
        return [], [f"missing required columns: {missing_cols}"], [], None, {}
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
        if iid in ref_issue_items:
            note = " / ".join(x for x in (r.get("rationale", "").strip(), r.get("problem_note", "").strip()) if x)
            if r.get("final_score_0_5", "").strip().lower() not in NA:
                errors.append(f"row {n} ({iid}): named as a reference-issue row but final_score_0_5 is not N/A")
            elif not note:
                errors.append(f"row {n} ({iid}): reference-issue row states no problem in rationale or problem_note")
            else:
                ref_issue[iid] = note
                name = r.get("rater_id", "").strip()
                if name:
                    names.add(name)
            continue
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
            v = YESNO.get(v, v) if k in ("A", "B", "C") else SYNONYMS.get(k, {}).get(v, v)
            if v and v not in ok:
                errors.append(f"row {n} ({iid}): {k}={r.get(k)!r} not in {sorted(ok)}")
            if k in fields:
                r[k] = v
        if {"model_assistance", "independent_rating_attestation"} & set(fields):
            for k in ("model_assistance", "independent_rating_attestation"):
                if not r.get(k, "").strip():
                    warnings.append(f"row {n} ({iid}): new-form metadata missing: {k}; rating retained")
            if r.get("independent_rating_attestation") in {"no", "unsure"}:
                warnings.append(f"row {n} ({iid}): attestation needs coordinator review; rating retained")
        mins = r.get("minutes_spent", "").strip()
        if mins:
            try:
                m = float(mins)
                if not math.isfinite(m) or m < 0:
                    raise ValueError
            except ValueError:
                errors.append(f"row {n} ({iid}): minutes_spent must be a nonnegative number, got {mins!r}")
        if r.get("lean_familiarity"):
            # Preserve descriptive answers verbatim; keep historical label normalization.
            background = r["lean_familiarity"].strip()
            if background.lower() in {"none", "some", "fluent"}:
                r["lean_familiarity"] = background.lower()
            fams.add(r["lean_familiarity"].strip())
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
        warnings.append(f"lean_familiarity has multiple entries; preserve and review as one person's background: {sorted(fams)}")
    if packet == "warmup":
        missing = sorted(expected_ids - {r["item_id"] for r in out} - set(ref_issue))
        if missing:
            errors.append(f"warm-up incomplete: no final score for {missing}")
    elif allowed_folders is not None:
        unrated = sorted(i for i in expected_ids if i[:3] in allowed_folders and i not in {r["item_id"] for r in out})
        if unrated:
            warnings.append(f"partial submission: {len(unrated)} delivered items unrated ({unrated[:5]}...)")
    unused = sorted(set(ref_issue_items) - set(ref_issue))
    if unused:
        errors.append(f"--reference-issue-items {unused} are not N/A reference-issue rows in this sheet")
    return out, errors, warnings, (sorted(names)[0] if len(names) == 1 else None), ref_issue


def latest_receipt(receipts, rater, packet):
    """The rater's latest delivery receipt for this packet, or None. A line without "folders" is an event note
    (for example a later "sent" record), not a delivery, and is skipped."""
    found = None
    if receipts.exists():
        for line in receipts.read_text().splitlines():
            if not line.strip():
                continue
            rec = json.loads(line)
            if rec.get("rater") == rater and rec.get("packet") == packet and "folders" in rec:
                found = rec  # the latest delivery wins
    return found


def delivered_folders(receipts, rater, packet):
    rec = latest_receipt(receipts, rater, packet)
    return set(rec["folders"]) if rec else None


def delivered_sheet(receipts, rater, packet):
    rec = latest_receipt(receipts, rater, packet)
    return rec.get("sheet_id") if rec else None


def personal_sheet(packet):
    if not A1_SHEETS_PATH.is_file():
        raise SystemExit("ERROR private coordinator sheet configuration is missing; restore it before importing")
    return json.loads(A1_SHEETS_PATH.read_text())[packet]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("export", nargs="?", help="CSV exported from the rater's Drive sheet (Drive route)")
    ap.add_argument("--csv", metavar="PATH", help=f"emailed-CSV route ({CSV_ROUTE}): the rating_sheet CSV the rater "
                    "emailed back, saved byte for byte; needs --source-message-id and --source-modified")
    ap.add_argument("--rater", required=True)
    ap.add_argument("--packet", choices=sorted(TEMPLATES), required=True)
    ap.add_argument("--file-id", help="Drive route: Drive file id of the rater's shared sheet")
    ap.add_argument("--source-modified", help="the sheet's Drive modifiedTime at export (with --csv: the date of the email "
                    "that carries the CSV, UTC)")
    ap.add_argument("--source-message-id", help="--csv only: Gmail message id of the rater's email that carries the CSV")
    ap.add_argument("--all-folders", action="store_true", help="A1 only: rates every folder, no delivery receipt")
    ap.add_argument("--out-dir", default=str(EXP / "human_round/private_ratings_setN"))
    ap.add_argument("--receipts", default="")
    ap.add_argument("--reference-issue-items", default="",
                    help="warm-up only (C17 addendum 10-20-2026): comma-separated W02 item ids left N/A for a stated reference problem")
    a = ap.parse_args()
    if a.csv:
        clash = [f for f, v in (("EXPORT", a.export), ("--file-id", a.file_id), ("--all-folders", a.all_folders)) if v]
        if clash:
            ap.error(f"--csv (emailed-CSV route) cannot be combined with {', '.join(clash)}")
        need = (("--source-message-id", a.source_message_id), ("--source-modified", a.source_modified))
    else:
        if a.source_message_id:
            ap.error("--source-message-id belongs to the emailed-CSV route (--csv)")
        need = (("export", a.export), ("--file-id", a.file_id), ("--source-modified", a.source_modified))
    missing = [f for f, v in need if not v]
    if missing:
        ap.error(f"the following arguments are required: {', '.join(missing)}")
    ref_items = frozenset(x.strip() for x in a.reference_issue_items.split(",") if x.strip())
    out_dir = Path(a.out_dir)
    receipts = Path(a.receipts) if a.receipts else out_dir / "delivery" / "DELIVERY_RECEIPTS.jsonl"
    raw = Path(a.csv or a.export).read_bytes()
    try:
        text = raw.decode("utf-8-sig").replace("\r\n", "\n")
    except UnicodeDecodeError as e:
        sys.exit(f"ERROR the export is not UTF-8 text ({e}); ask the rater to save it as CSV UTF-8")
    tfields, trows = read_rows(TEMPLATES[a.packet].read_text())
    expected = {r["item_id"] for r in trows}
    allowed = None if a.all_folders else delivered_folders(receipts, a.rater, a.packet)
    if allowed is None and not a.all_folders:
        sys.exit(f"ERROR no delivery receipt for {a.rater}/{a.packet} in {receipts} (use --all-folders only for A1)")
    if a.all_folders and a.rater != "A1":
        sys.exit("ERROR --all-folders is only for rater A1")
    delivery = None if a.all_folders else latest_receipt(receipts, a.rater, a.packet)
    route = (delivery or {}).get("return_route")
    if a.csv and route != "emailed_csv":
        sys.exit(f"ERROR --csv: the delivery receipt for {a.rater}/{a.packet} does not say return_route emailed_csv")
    if not a.csv and route == "emailed_csv":
        sys.exit(f"ERROR {a.rater}/{a.packet} returns an emailed CSV (delivery receipt return_route); import it with --csv")
    if not a.csv:
        # A1 rates from fixed personal sheets; every other rater's sheet comes from their delivery receipt (packet v5).
        sheet = personal_sheet(a.packet) if a.all_folders else delivered_sheet(receipts, a.rater, a.packet)
        if not sheet:
            sys.exit(f"ERROR the delivery receipt for {a.rater}/{a.packet} has no sheet id (pre-v5 delivery); re-deliver with make_rater_zip.py")
        if sheet != a.file_id:
            sys.exit(f"ERROR file id {a.file_id} is not the sheet delivered to {a.rater}/{a.packet} ({sheet})")
    if ref_items and a.packet != "warmup":
        sys.exit("ERROR --reference-issue-items is only for the warm-up packet")
    bad = sorted(i for i in ref_items if i not in expected or i.startswith(QUALIFY_TASKS))
    if bad:
        sys.exit(f"ERROR --reference-issue-items {bad}: unknown, or in the C17 qualification task {QUALIFY_TASKS}")
    rows, errors, warnings, submitted, ref_issue = check(text, a.rater, expected, allowed, a.packet, ref_items)
    for w in warnings:
        print("WARN", w)
    if errors:
        for e in errors:
            print("ERROR", e)
        sys.exit(1)
    norm = normalized_csv(rows, tfields, read_rows(text)[0])
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    base = f"{a.packet}_{a.rater}"
    for sub, data in (("raw", raw), ("normalized", norm)):
        (out_dir / sub).mkdir(parents=True, exist_ok=True)
        snap = out_dir / sub / f"{base}_{stamp}.csv"
        if snap.exists():
            sys.exit(f"ERROR snapshot {snap} already exists; refusing to overwrite")
        snap.write_bytes(data)
    (out_dir / f"{base}.csv").write_bytes(norm)
    source = {"source_file_id": a.file_id, "source_modified": a.source_modified}
    if a.csv:  # emailed-CSV route: no Drive file, and sha256_export below is the emailed CSV's sha256
        source = {"source_route": CSV_ROUTE, "source_file_id": None, "source_csv_name": Path(a.csv).name,
                  "source_message_id": a.source_message_id, "source_thread_id": delivery.get("thread_id"),
                  "source_modified": a.source_modified}
    receipt = {"rater": a.rater, "submitted_rater_id": submitted, "packet": a.packet, **source, "imported_utc": stamp,
               "folders_allowed": sorted(allowed) if allowed is not None else "all",
               "sha256_export": hashlib.sha256(raw).hexdigest(), "sha256_normalized": hashlib.sha256(norm).hexdigest(),
               "rows_rated": len(rows), "warnings": warnings,
               **({"reference_issue_items": ref_issue, "reference_issue_rule": "C17 addendum 10-20-2026"} if ref_issue else {}),
               "snapshots": [f"raw/{base}_{stamp}.csv", f"normalized/{base}_{stamp}.csv"]}
    with open(out_dir / "RECEIPTS.jsonl", "a") as f:
        f.write(json.dumps(receipt) + "\n")
    print(f"OK {a.rater} ({submitted}) {a.packet}: {len(rows)} rated rows; snapshots {stamp}; "
          f"sha256 {receipt['sha256_normalized'][:12]}")


if __name__ == "__main__":
    main()
