"""Package assigned folders from the frozen human-rating delivery with a blank sheet."""

import argparse
import csv
import hashlib
import io
import json
import re
from pathlib import Path
from zipfile import ZIP_DEFLATED, ZipFile
from revise_rating_packet import current_form_rubric

MANIFEST_SHA256 = "0e4166045463dac71c2d7e70702f9c8b58ffccedeacdbff13ef4e57b8e85efa4"
FORM_HOME = Path(__file__).resolve().parents[2]
COLUMNS = json.loads((FORM_HOME / "support/RATING_FORM_SCHEMA.json").read_text())["columns"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, help="Extracted original personal packet")
    parser.add_argument("output", type=Path, help="New team ZIP file")
    parser.add_argument("--rater", help="Verified rater ID to prefill the name and ID; omit only for an unassigned template")
    parser.add_argument("--folders", nargs="+", type=int, choices=range(1, 26),
                        default=range(1, 26), metavar="1..25")
    args = parser.parse_args()
    identities = json.loads((FORM_HOME / "support/RATER_IDENTITIES.json").read_text())
    if args.rater and args.rater not in identities:
        parser.error("Unknown rater; add the verified name to RATER_IDENTITIES.json first.")
    rater_name = identities[args.rater]["rater_name"] if args.rater else ""
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
            rows.append({"rater_name": rater_name, "rater_id": args.rater or "",
                         "item_id": path.stem, "task_folder": path.parts[0], "candidate_file": path.name})

    schema = json.loads((FORM_HOME / "support/RATING_FORM_SCHEMA.json").read_text())
    guide = (FORM_HOME / "rating_task_packet/RATING_FORM_GUIDE.md").read_text()
    if any(field not in guide for field in schema["required_new_responses"]):
        raise ValueError("Form guide does not match required response fields")
    if len(rows) != 5 * len(folders):
        parser.error("Unexpected candidate count.")
    rubric = re.sub(r"^Open \[your personal rating sheet\].+$",
                    "Fill the assigned ratings.csv form.", members["Rating_Instructions.md"].decode(), flags=re.MULTILINE)
    members["Rating_Instructions.md"] = current_form_rubric(rubric).encode()
    members["START_HERE.md"] = (
        "# Rate theorem coverage\n\n"
        "Read RATING_FORM_GUIDE.md first for the current fields and assistance policy; "
        "it supersedes older submission/assistance instructions below.\n\n"
        "Read Rating_Instructions.md. In each assigned folder, read the Python source and the "
        "gold Lean theorem statements, then rate each candidate under agent_lean. The files in "
        "gold_lean_dependencies, when present, support the reference.\n\n"
        "Open ratings.csv in a spreadsheet editor. Check your name and rater ID, then enter final_score_0_5 "
        "and ai_assisted_rating_attestation for each assigned file. Please estimate minutes_spent and confidence; rationale is preferred but optional. Use problem_note for issues. "
        "Keep the prefilled identifiers intact. Email reference problems to Brando. "
        "Return your completed CSV privately to Brando.\n"
    ).encode()
    members["RATING_FORM_GUIDE.md"] = (FORM_HOME / "rating_task_packet/RATING_FORM_GUIDE.md").read_bytes()
    sheet = io.StringIO(newline="")
    writer = csv.DictWriter(sheet, fieldnames=COLUMNS)
    writer.writeheader()
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
