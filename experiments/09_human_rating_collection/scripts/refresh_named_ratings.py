#!/usr/bin/env python3
"""Add names and sourced coordinator background to imports; never read live Sheets."""
import argparse
import csv
import hashlib
import io
import json
import re
from pathlib import Path

EXPERIMENT = Path(__file__).resolve().parents[1]
ROOT = EXPERIMENT.parents[1]


def named_export(source, identities, timing_estimates=None):
    match = re.fullmatch(r"(warmup|setN)_([A-Z][0-9]+)\.csv", source.name)
    if not match:
        raise ValueError(f"Not a normalized import filename: {source.name}")
    packet, rid = match.groups()
    if rid not in identities:
        raise ValueError(f"No verified name for {rid}; update RATER_IDENTITIES.json first")
    identity = identities[rid]
    name, stem = identity["rater_name"], identity["filename_stem"]
    enrichment = {"rater_name": name}
    for field in ("programming_languages_background", "background_source"):
        if identity.get(field):
            enrichment[field] = identity[field]
    if not name.strip() or not re.fullmatch(r"[A-Za-z0-9_-]+", stem):
        raise ValueError(f"Invalid display identity for {rid}")
    raw = source.read_bytes()
    reader = csv.DictReader(io.StringIO(raw.decode("utf-8-sig")))
    fields, rows = reader.fieldnames or [], list(reader)
    if not {"rater_id", "item_id", "final_score_0_5"}.issubset(fields):
        raise ValueError("Expected an already validated, normalized rating import")
    if (set(enrichment) - {"rater_name"}) & set(fields) or len(fields) != len(set(fields)):
        raise ValueError("Source must have unique original columns without coordinator enrichment fields")
    seen = set()
    for row in rows:
        if None in row or any(v is None for v in row.values()):
            raise ValueError("Malformed CSV row")
        if row["rater_id"] != rid:
            raise ValueError(f"Row identity disagrees with filename {source.name}")
        if "rater_name" in fields and row["rater_name"] != name:
            raise ValueError(f"Submitted rater_name disagrees with verified identity for {rid}")
        if not row["item_id"] or row["item_id"] in seen:
            raise ValueError("Missing or duplicate item identity")
        seen.add(row["item_id"])
    timing = (timing_estimates or {}).get(source.name)
    extra_fields = []
    export_rows = [{**enrichment, **row} for row in rows]
    if timing:
        extra_fields = ["minutes_spent_original", "minutes_spent_source", "minutes_spent_estimate_basis"]
        if "minutes_spent" not in fields or set(extra_fields) & set(fields):
            raise ValueError("Timing estimates require original minutes_spent without annotation fields")
        allocations = timing["items"]
        if set(allocations) != seen:
            raise ValueError("Timing allocation must cover exactly the imported items")
        minutes = [entry["minutes"] for entry in allocations.values()]
        if any(type(value) is not int or value <= 0 for value in minutes):
            raise ValueError("Timing allocations must be positive integer minutes")
        if sum(minutes) != timing["reported_total_minutes"]:
            raise ValueError("Timing allocations must sum to the reported packet total")
        for row in export_rows:
            if row["minutes_spent"].strip():
                raise ValueError("Do not overwrite nonblank imported timing; reconcile its provenance first")
            entry = allocations[row["item_id"]]
            row["minutes_spent_original"] = row["minutes_spent"]
            row["minutes_spent"] = str(entry["minutes"])
            row["minutes_spent_source"] = "coordinator_estimate_from_approximate_packet_total"
            row["minutes_spent_estimate_basis"] = entry["basis"]
    buf = io.StringIO(newline="")
    output_fields = ["rater_name", "rater_id", *(k for k in fields if k not in {"rater_name", "rater_id"}),
                     *(k for k in enrichment if k != "rater_name"), *extra_fields]
    writer = csv.DictWriter(buf, fieldnames=output_fields, lineterminator="\n")
    writer.writeheader()
    writer.writerows(export_rows)
    data = buf.getvalue().encode()
    restored = list(csv.DictReader(io.StringIO(data.decode())))
    restored_originals = [{k: row[k] for k in fields} for row in restored]
    if timing:
        for original, annotated in zip(restored_originals, restored):
            original["minutes_spent"] = annotated["minutes_spent_original"]
    assert restored_originals == rows
    filename = f"{stem}__{packet}_{rid}.csv"
    return filename, data, {
        "rater_id": rid, "rater_name": name, "file": filename, "rows": len(rows),
        "sha256": hashlib.sha256(data).hexdigest(),
        "original_import_file": source.name,
        "original_import_sha256": hashlib.sha256(raw).hexdigest(),
        "transformation": ("Added sourced name/background and explicit coordinator timing estimates; original timing retained in minutes_spent_original; all scores, notes and source bytes preserved."
                           if timing else
                           "Placed verified rater_name first and rater_id second; all original fields and rows preserved."
                           if len(enrichment) == 1 else
                           "Placed verified rater_name first and rater_id second, with sourced coordinator background appended; all original fields and rows preserved."),
        **({"background_enrichment": {k: v for k, v in enrichment.items() if k != "rater_name"}}
           if len(enrichment) > 1 else {}),
        **({"timing_estimates": timing} if timing else {}),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-dir", type=Path, default=ROOT / "private/09_human_rating_collection/legacy_veribench/human_round/private_ratings_setN")
    parser.add_argument("--out-dir", type=Path, default=EXPERIMENT / "ratings")
    parser.add_argument("--identities", type=Path, default=EXPERIMENT / "RATER_IDENTITIES.json")
    parser.add_argument("--timing-estimates", type=Path, default=EXPERIMENT / "RATING_TIME_ESTIMATES.json")
    args = parser.parse_args()
    identities = json.loads(args.identities.read_text())
    timing_estimates = json.loads(args.timing_estimates.read_text()) if args.timing_estimates.exists() else {}
    sources = sorted(p for p in args.input_dir.glob("*.csv") if p.name.startswith(("warmup_", "setN_")))
    if not sources:
        parser.error("No normalized imports found; no output written")
    # Validate the whole batch before replacing any named export.
    exports = [named_export(source, identities, timing_estimates) for source in sources]
    args.out_dir.mkdir(parents=True, exist_ok=True)
    for filename, data, receipt in exports:
        (args.out_dir / filename).write_bytes(data)
        print(f"{receipt['rater_name']}: {receipt['rows']} existing rows -> {filename}")
    (args.out_dir / "NAMED_EXPORT_MANIFEST.json").write_text(json.dumps({
        "scope": "Named existing imports with sourced background and explicitly labelled coordinator timing estimates; not new rating observations.",
        "collected_files": [receipt for _, _, receipt in exports],
    }, indent=2) + "\n")


if __name__ == "__main__":
    main()
