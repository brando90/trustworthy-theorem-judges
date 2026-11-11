#!/usr/bin/env python3
"""Add verified display names to already imported ratings; never read live Sheets."""
import argparse
import csv
import hashlib
import io
import json
import re
from pathlib import Path

EXPERIMENT = Path(__file__).resolve().parents[1]
ROOT = EXPERIMENT.parents[1]


def named_export(source, identities):
    match = re.fullmatch(r"(warmup|setN)_([A-Z][0-9]+)\.csv", source.name)
    if not match:
        raise ValueError(f"Not a normalized import filename: {source.name}")
    packet, rid = match.groups()
    if rid not in identities:
        raise ValueError(f"No verified name for {rid}; update RATER_IDENTITIES.json first")
    identity = identities[rid]
    name, stem = identity["rater_name"], identity["filename_stem"]
    if not name.strip() or not re.fullmatch(r"[A-Za-z0-9_-]+", stem):
        raise ValueError(f"Invalid display identity for {rid}")
    raw = source.read_bytes()
    reader = csv.DictReader(io.StringIO(raw.decode("utf-8-sig")))
    fields, rows = reader.fieldnames or [], list(reader)
    if not {"rater_id", "item_id", "final_score_0_5"}.issubset(fields):
        raise ValueError("Expected an already validated, normalized rating import")
    if "rater_name" in fields or len(fields) != len(set(fields)):
        raise ValueError("Source must have unique original columns without rater_name")
    seen = set()
    for row in rows:
        if None in row or any(v is None for v in row.values()):
            raise ValueError("Malformed CSV row")
        if row["rater_id"] != rid:
            raise ValueError(f"Row identity disagrees with filename {source.name}")
        if not row["item_id"] or row["item_id"] in seen:
            raise ValueError("Missing or duplicate item identity")
        seen.add(row["item_id"])
    buf = io.StringIO(newline="")
    writer = csv.DictWriter(buf, fieldnames=["rater_name", *fields], lineterminator="\n")
    writer.writeheader()
    writer.writerows({"rater_name": name, **row} for row in rows)
    data = buf.getvalue().encode()
    restored = list(csv.DictReader(io.StringIO(data.decode())))
    assert [{k: v for k, v in row.items() if k != "rater_name"} for row in restored] == rows
    filename = f"{stem}__{packet}_{rid}.csv"
    return filename, data, {
        "rater_id": rid, "rater_name": name, "file": filename, "rows": len(rows),
        "sha256": hashlib.sha256(data).hexdigest(),
        "original_import_file": source.name,
        "original_import_sha256": hashlib.sha256(raw).hexdigest(),
        "transformation": "Added rater_name as the first column; all original fields and rows preserved.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-dir", type=Path, default=ROOT / "private/09_human_rating_collection/legacy_veribench/human_round/private_ratings_setN")
    parser.add_argument("--out-dir", type=Path, default=EXPERIMENT / "ratings")
    parser.add_argument("--identities", type=Path, default=EXPERIMENT / "RATER_IDENTITIES.json")
    args = parser.parse_args()
    identities = json.loads(args.identities.read_text())
    sources = sorted(p for p in args.input_dir.glob("*.csv") if p.name.startswith(("warmup_", "setN_")))
    if not sources:
        parser.error("No normalized imports found; no output written")
    # Validate the whole batch before replacing any named export.
    exports = [named_export(source, identities) for source in sources]
    args.out_dir.mkdir(parents=True, exist_ok=True)
    for filename, data, receipt in exports:
        (args.out_dir / filename).write_bytes(data)
        print(f"{receipt['rater_name']}: {receipt['rows']} existing rows -> {filename}")
    (args.out_dir / "NAMED_EXPORT_MANIFEST.json").write_text(json.dumps({
        "scope": "Display-name enrichment of existing imports only; not a live collection or new observations.",
        "collected_files": [receipt for _, _, receipt in exports],
    }, indent=2) + "\n")


if __name__ == "__main__":
    main()
