"""Package assigned folders from the frozen human-rating delivery with a blank sheet."""

import argparse
import csv
import hashlib
import io
import re
from pathlib import Path
from zipfile import ZIP_DEFLATED, ZipFile

MANIFEST_SHA256 = "0e4166045463dac71c2d7e70702f9c8b58ffccedeacdbff13ef4e57b8e85efa4"
COLUMNS = (
    "rater_id item_id task_folder candidate_file A B C D base_score_0_5 "
    "final_score_0_5 confidence rationale problem_note"
).split()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, help="Extracted original personal packet")
    parser.add_argument("output", type=Path, help="New team ZIP file")
    parser.add_argument("--folders", nargs="+", type=int, choices=range(1, 26),
                        default=range(1, 26), metavar="1..25")
    args = parser.parse_args()
    manifest = (args.source / "FILES.sha256").read_bytes()
    if hashlib.sha256(manifest).hexdigest() != MANIFEST_SHA256:
        parser.error("Source manifest differs from the frozen delivery.")

    folders = {f"Files_To_Rate{number:02}" for number in args.folders}
    members = {}
    rows = []
    for line in manifest.decode().splitlines():
        digest, name = line.split("  ", 1)
        path = Path(name)
        if path.parts[0] not in folders and name not in {"Rating_Instructions.md", "START_HERE.md"}:
            continue
        data = (args.source / path).read_bytes()
        if hashlib.sha256(data).hexdigest() != digest:
            parser.error(f"Source file differs from its delivery manifest: {name}")
        members[name] = data
        if path.parent.name == "agent_lean":
            rows.append(["", path.stem, path.parts[0], path.name] + [""] * (len(COLUMNS) - 4))

    # Replace only the personal submission instructions. Preserve the scoring rubric.
    rubric = members["Rating_Instructions.md"].decode()
    rubric, count = re.subn(r"^Open \[your personal rating sheet\].+$",
                            "Fill in your own copy of ratings.csv, one row per candidate.",
                            rubric, flags=re.MULTILINE)
    if count != 1 or len(rows) != 5 * len(folders):
        parser.error("Unexpected rubric or candidate count.")
    members["Rating_Instructions.md"] = rubric.encode()
    assistance = members["START_HERE.md"].decode().split("## Assistance and reference problems\n\n", 1)[1]
    members["START_HERE.md"] = (
        "# Rate theorem coverage\n\n"
        "Read Rating_Instructions.md. In each assigned folder, read the Python source and the "
        "gold Lean theorem statements, then rate each candidate under agent_lean. The files in "
        "gold_lean_dependencies, when present, support the reference.\n\n"
        "Open ratings.csv in a spreadsheet editor. Enter your rater ID and final_score_0_5 "
        "for each assigned file. Keep the item IDs and filenames intact. Record any reference "
        "problem in problem_note. Return your completed CSV privately to Brando.\n\n"
        "## Assistance and reference problems\n\n" + assistance
    ).encode()
    sheet = io.StringIO(newline="")
    writer = csv.writer(sheet)
    writer.writerow(COLUMNS)
    writer.writerows(rows)
    members["ratings.csv"] = sheet.getvalue().encode()
    members["FILES.sha256"] = "".join(
        f"{hashlib.sha256(data).hexdigest()}  {name}\n" for name, data in sorted(members.items())
    ).encode()
    with ZipFile(args.output, "x", compression=ZIP_DEFLATED) as archive:
        for name, data in sorted(members.items()):
            archive.writestr(name, data)
    print(f"{args.output}: {len(folders)} folders, {len(rows)} candidates")


if __name__ == "__main__":
    main()
