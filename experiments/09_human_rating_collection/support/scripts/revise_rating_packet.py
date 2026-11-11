"""Create a versioned common-form packet from an immutable delivered archive."""
import argparse
import csv
import hashlib
import io
import json
import re
from pathlib import Path
from zipfile import ZipFile, ZIP_DEFLATED

HOME = Path(__file__).resolve().parents[2]


def required_only_rubric(text):
    """Update submission directions only; preserve every scoring section verbatim."""
    output = ("## Output format (required)\n\n"
              "Use your personal sheet linked in START_HERE.md, or the assigned ratings.csv return route. "
              "Fill only final_score_0_5 and ai_assisted_rating_attestation; "
              "RATING_FORM_GUIDE.md explains these answers. Identifiers are prefilled. "
              "The checklist and base score remain scoring steps, not separate form entries.\n\n")
    text = re.sub(r"## Current form headers[\s\S]*$", "", text)
    if "## Output format (required)" in text:
        text, count = re.subn(r"## Output format \(required\)[\s\S]*?(?=## Tie-break rule)", lambda _: output, text)
        if count != 1:
            raise ValueError("Unexpected rubric output section")
        return text
    return text + "\n\n" + output


def revise(source, output, rater, sheet_url):
    schema = json.loads((HOME / "support/RATING_FORM_SCHEMA.json").read_text())
    guide = (HOME / "rating_task_packet/RATING_FORM_GUIDE.md").read_text()
    if any(field not in guide for field in schema["required_new_responses"]):
        raise ValueError("Form guide does not match required response fields")
    identities = json.loads((HOME / "support/RATER_IDENTITIES.json").read_text())
    if rater not in identities or not identities[rater]["rater_name"].strip():
        raise ValueError(f"No verified name for {rater}; update RATER_IDENTITIES.json first")
    rater_name = identities[rater]["rater_name"]
    with ZipFile(source) as z:
        raw = {n: z.read(n) for n in z.namelist() if not n.endswith("/")}
    roots = {n.split("/")[0] for n in raw}
    root = next(iter(roots)) + "/" if len(roots) == 1 and all("/" in n for n in raw) else ""
    files = {n[len(root):]: b for n, b in raw.items()}
    listing = dict((n, digest) for digest, n in
                   (line.split("  ", 1) for line in files["FILES.sha256"].decode().splitlines() if line.strip()))
    for n, digest in listing.items():
        if hashlib.sha256(files[n]).hexdigest() != digest:
            raise ValueError(f"Source hash mismatch: {n}")
    path_map = json.loads((HOME / "support/WARMUP_PATHS.json").read_text())["paths"]
    original_names = {path_map.get(n, n): n for n in files}
    files = {path_map.get(n, n): b for n, b in files.items()}
    candidates = sorted((n for n in files if "/agent_lean/" in n and n.endswith(".lean")),
                        key=lambda n: [int(x) if x.isdigit() else x for x in re.split(r"(\d+)", n)])
    if not candidates:
        raise ValueError("No candidates")
    rubric = "Rating_Instructions.md" if "Rating_Instructions.md" in files else "human_judgements_prompt.md"
    files[rubric] = required_only_rubric(files[rubric].decode()).encode()
    # Delivered scientific payload is copied byte-for-byte, never regenerated.
    protected = {n: b for n, b in files.items() if n.endswith((".lean", ".py"))}
    files["RATING_FORM_GUIDE.md"] = (HOME / "rating_task_packet/RATING_FORM_GUIDE.md").read_bytes()
    files["START_HERE.md"] = (
        "# Start your human ratings\n\n"
        f"This packet has {len(candidates)} candidate files. Form revision: 11-11-2026.\n\n"
        f"1. [Open your personal Google Sheet]({sheet_url}) for {rater_name} ({rater}). Use that existing sheet; no copy is needed.\n"
        "2. Read RATING_FORM_GUIDE.md for the shared warm-up/main fields and assistance policy. "
        "It supersedes older submission links and assistance wording.\n"
        f"3. Read {rubric} for the unchanged 0–5 scoring rubric. "
        "Read Python source, gold theorem statements and candidate theorem statements in each task folder. "
        "Rate statements, not proofs.\n"
        "4. Fill one row per candidate in your Google Sheet. Use AI for localized assistance. "
        "Make the comparison, choose the score and answer the attestation yourself.\n\n"
        "The included ratings.csv is a blank form with the same columns; the personal Google Sheet is your return route.\n"
    ).encode()
    # The personal link lives in START_HERE; remove the redundant legacy pointer.
    files.pop("YOUR_RATING_SHEET.txt", None)
    # Remove superseded blank form copies from the new archive only.
    for n in list(files):
        if n.endswith(".csv") and ("rating" in Path(n).name.lower()):
            del files[n]
    buf = io.StringIO(newline="")
    w = csv.DictWriter(buf, fieldnames=schema["columns"], lineterminator="\n")
    w.writeheader()
    for n in candidates:
        p = Path(n)
        w.writerow({"rater_name": rater_name, "rater_id": rater, "item_id": Path(original_names[n]).stem, "task_folder": p.parts[0],
                    "candidate_file": n if p.parts[0].startswith(("W", "warm_up_")) else p.name})
    files["ratings.csv"] = buf.getvalue().encode()
    files["FILES.sha256"] = "".join(
        f"{hashlib.sha256(b).hexdigest()}  {n}\n" for n, b in sorted(files.items())
        if n != "FILES.sha256").encode()
    with ZipFile(output, "x", compression=ZIP_DEFLATED) as z:
        for n, b in sorted(files.items()):
            z.writestr(output.stem + "/" + n, b)
    with ZipFile(output) as z:
        for n, b in protected.items():
            assert z.read(output.stem + "/" + n) == b
        for line in files["FILES.sha256"].decode().splitlines():
            digest, n = line.split("  ", 1)
            assert hashlib.sha256(z.read(output.stem + "/" + n)).hexdigest() == digest
    receipt = {"schema_version": schema["version"], "source": str(source),
               "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
               "output": str(output), "output_sha256": hashlib.sha256(output.read_bytes()).hexdigest(),
               "rater_name": rater_name, "rater_id": rater, "sheet_url": sheet_url, "candidate_count": len(candidates),
               "preserved_scientific_files": len(protected), "columns": schema["columns"]}
    output.with_suffix(".receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    return receipt


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("source", type=Path)
    p.add_argument("output", type=Path)
    p.add_argument("--rater", required=True)
    p.add_argument("--sheet-url", required=True)
    a = p.parse_args()
    print(json.dumps(revise(a.source, a.output, a.rater, a.sheet_url), indent=2))
