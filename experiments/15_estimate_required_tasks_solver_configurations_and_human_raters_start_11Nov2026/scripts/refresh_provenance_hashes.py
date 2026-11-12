#!/usr/bin/env python3
"""Keep the `public_files` hash inventory in provenance.json equal to this folder's files.

    python3 refresh_provenance_hashes.py           verify; exit 1 when a file changed
    python3 refresh_provenance_hashes.py --write   record current paths, hashes and sizes

Only `public_files` is rewritten. Capture, review and Google-synchronization records in
provenance.json are historical receipts and are never touched.
"""
import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

EXPERIMENT = Path(__file__).resolve().parents[1]
PROVENANCE = EXPERIMENT / "provenance.json"


def current_inventory():
    listed = subprocess.run(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard"],
        cwd=EXPERIMENT, check=True, capture_output=True, text=True).stdout.splitlines()
    inventory = []
    for name in sorted(set(listed)):
        path = EXPERIMENT / name
        if name == PROVENANCE.name or not path.is_file():
            continue
        data = path.read_bytes()
        inventory.append({"path": name, "sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)})
    return inventory


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--write", action="store_true", help="record the current inventory")
    arguments = parser.parse_args()
    record = json.loads(PROVENANCE.read_text())
    inventory = current_inventory()
    if arguments.write:
        record["public_files"] = inventory
        PROVENANCE.write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n")
        print(f"Recorded {len(inventory)} files in {PROVENANCE.name}.")
        return
    saved = {entry["path"]: entry for entry in record["public_files"]}
    now = {entry["path"]: entry for entry in inventory}
    changed = sorted(path for path in saved.keys() | now.keys() if saved.get(path) != now.get(path))
    if changed:
        sys.exit("provenance.json is stale for: " + ", ".join(changed) + f". Rerun {Path(__file__).name} --write.")
    print(f"Provenance hashes match {len(inventory)} files.")


if __name__ == "__main__":
    main()
