#!/usr/bin/env python3
"""Add the source_label column to the rating CSV exports so every round stays in one place and can be filtered.

source_label names the round a row came from. It is an export-only column (the raters' Sheets do not carry it):
  warm-up          warm-up packet files (`*__warmup_<id>.csv`)
  main             current 100-file main round (`*__native_main_<id>.csv`)
  historical_main  original 125-row main round, October 2026 (`*__setN_<id>.csv`)
  May              May 2026 judge-paper ratings (195 expert ratings; label reserved for when they are imported here)
The column is appended last, so every original column, cell and row order is unchanged. Nothing is dropped.

Usage (from anywhere):
  python3 source_label.py check            # verify every ratings/*.csv and ratings/analysis/*.csv carries it
  python3 source_label.py apply            # add it to files that lack it, refresh hashes in the manifests (idempotent)
"""
import argparse
import csv
import hashlib
import io
import json
import re
from pathlib import Path

EXPERIMENT = Path(__file__).resolve().parents[2]
RATINGS = EXPERIMENT / "ratings"
COLUMN = "source_label"
LABELS = ("warm-up", "main", "historical_main", "May")
PACKET_LABEL = {"warmup": "warm-up", "native_main": "main", "setN": "historical_main"}
FILENAME = re.compile(r"__?(warmup|native_main|setN)_([A-Z][0-9]+)\.csv$")
MANIFESTS = (RATINGS / "RAW_MANIFEST.json", RATINGS / "SUMMARY.json", RATINGS / "analysis/NAMED_EXPORT_MANIFEST.json")


def label_for_packet(packet):
    """Label for a packet name as used in RAW_MANIFEST ("warmup", "native_main", "setN")."""
    return PACKET_LABEL[packet]


def label_for_filename(name):
    match = FILENAME.search(name)
    if not match:
        raise ValueError(f"Cannot tell the round from {name}")
    return label_for_packet(match.group(1))


def add_label(rows, label):
    """rows: list of csv rows with a header first. Returns new rows with source_label appended; originals untouched."""
    if label not in LABELS:
        raise ValueError(f"Unknown source_label {label!r}; allowed: {LABELS}")
    if COLUMN in rows[0]:
        existing = {row[rows[0].index(COLUMN)] for row in rows[1:]}
        if existing - {label}:
            raise ValueError(f"{COLUMN} already present with other values: {existing}")
        return rows
    return [[*rows[0], COLUMN]] + [[*row, label] for row in rows[1:]]


def dumps(rows):
    buffer = io.StringIO(newline="")
    csv.writer(buffer, lineterminator="\n").writerows(rows)
    return buffer.getvalue().encode()


def read_rows(path):
    return list(csv.reader(io.StringIO(path.read_bytes().decode("utf-8-sig"), newline="")))


def export_files():
    return sorted([*RATINGS.glob("*.csv"), *(RATINGS / "analysis").glob("*.csv")])


def check():
    problems = []
    for path in export_files():
        rows = read_rows(path)
        expected = label_for_filename(path.name)
        if rows[0][-1] != COLUMN:
            problems.append(f"{path.name}: no {COLUMN} column")
        elif any(len(row) != len(rows[0]) or row[-1] != expected for row in rows[1:]):
            problems.append(f"{path.name}: rows do not all carry {expected!r}")
    return problems


def replace_hash(node, old, new):
    if isinstance(node, dict):
        return {k: replace_hash(v, old, new) for k, v in node.items()}
    if isinstance(node, list):
        return [replace_hash(v, old, new) for v in node]
    return new if node == old else node


def apply():
    changed = {}
    for path in export_files():
        before = path.read_bytes()
        rows = read_rows(path)
        assert dumps(rows) == before, f"{path.name} does not round-trip byte for byte; not touched"
        labeled = add_label(rows, label_for_filename(path.name))
        if labeled is rows:
            continue
        data = dumps(labeled)
        assert [r[:-1] for r in read_rows_from(data)] == rows, f"{path.name}: original cells changed"
        path.write_bytes(data)
        changed[path] = (hashlib.sha256(before).hexdigest(), hashlib.sha256(data).hexdigest())
    if not changed:
        print("nothing to do: every export already carries source_label")
        return
    manifests = {p: json.loads(p.read_text()) for p in MANIFESTS}
    for old, new in changed.values():
        for path, data in manifests.items():
            manifests[path] = replace_hash(data, old, new)
    raw = manifests[RATINGS / "RAW_MANIFEST.json"]
    for entry in raw["files"]:
        if RATINGS / entry["filename"] in changed:
            entry["csv_columns"] = [*entry["columns"], COLUMN]
            entry["source_label"] = label_for_packet(entry["packet"])
    raw["source_label_revision"] = {
        "date": "11-18-2026",
        "requested_by": 'Brando, 11-18-2026: "Make sure these things are recorded in the repo so when we collect the data it\'s easy to do stuff with it" and "all data is valuable btw"',
        "change": f"Appended a {COLUMN} column (last) to every rating CSV: warm-up, main, historical_main (original 125-row round) or May. "
                  "Original columns, cells and row order unchanged; the raters' Sheets are untouched and 'columns' still lists the Sheet columns, "
                  "'csv_columns' the CSV columns. Hashes of the changed files refreshed; earlier hashes stay in git history.",
        "files_changed": len(changed),
        "allowed_values": list(LABELS)}
    named = manifests[RATINGS / "analysis/NAMED_EXPORT_MANIFEST.json"]
    for entry in named.get("collected_files", []):
        if RATINGS / "analysis" / entry["file"] in changed:
            entry["source_label"] = label_for_filename(entry["file"])
    for path, data in manifests.items():
        path.write_text(json.dumps(data, **({"indent": 2} if path.parent.name == "analysis" else {"indent": 1, "ensure_ascii": False})) + "\n")
    print(f"added {COLUMN} to {len(changed)} files")


def read_rows_from(data):
    return list(csv.reader(io.StringIO(data.decode("utf-8"), newline="")))


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("command", choices=("check", "apply"))
    args = parser.parse_args()
    if args.command == "apply":
        apply()
    problems = check()
    print("\n".join(problems) or f"ok: {len(export_files())} files carry {COLUMN}")
    raise SystemExit(1 if problems else 0)


if __name__ == "__main__":
    main()
