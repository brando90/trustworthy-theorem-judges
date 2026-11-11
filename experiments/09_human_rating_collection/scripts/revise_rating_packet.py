"""Create a versioned common-form packet from an immutable delivered archive."""
import argparse
import csv
import hashlib
import io
import json
from pathlib import Path
from zipfile import ZipFile, ZIP_DEFLATED

HOME = Path(__file__).resolve().parents[1]


def revise(source, output, rater, sheet_url):
    schema = json.loads((HOME / "RATING_FORM_SCHEMA.json").read_text())
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
    candidates = sorted(n for n in files if "/agent_lean/" in n and n.endswith(".lean"))
    if not candidates:
        raise ValueError("No candidates")
    rubric = "Rating_Instructions.md" if "Rating_Instructions.md" in files else "human_judgements_prompt.md"
    # Delivered scientific payload is copied byte-for-byte, never regenerated.
    protected = {n: b for n, b in files.items() if n.endswith((".lean", ".py"))}
    files["RATING_FORM_GUIDE.md"] = (HOME / "RATING_FORM_GUIDE.md").read_bytes()
    files["START_HERE.md"] = (
        "# Start your human ratings\n\n"
        f"This packet has {len(candidates)} candidate files. Form revision: 11-11-2026.\n\n"
        "1. Open the personal Google Sheet in YOUR_RATING_SHEET.txt. Use that existing sheet; no copy is needed.\n"
        "2. Read RATING_FORM_GUIDE.md for the shared warm-up/main fields and assistance policy. "
        "It supersedes older submission links and assistance wording.\n"
        f"3. Read {rubric} for the unchanged 0–5 scoring rubric. "
        "Read Python source, gold theorem statements and candidate theorem statements in each task folder. "
        "Rate statements, not proofs.\n"
        "4. Fill one row per candidate in your Google Sheet. Model assistance for localized questions is encouraged. "
        "Record the help and answer the attestation yourself.\n\n"
        "The included ratings.csv is a blank form with the same columns; the personal Google Sheet is your return route.\n"
    ).encode()
    files["YOUR_RATING_SHEET.txt"] = (
        f"Personal rating sheet for {rater}\n{sheet_url}\n\n"
        "Fill final_score_0_5, model_assistance and independent_rating_attestation for each completed item.\n"
        "The sheet saves automatically; keep the prefilled identifiers unchanged.\n"
    ).encode()
    # Remove superseded blank form copies from the new archive only.
    for n in list(files):
        if n.endswith(".csv") and ("rating" in Path(n).name.lower()):
            del files[n]
    buf = io.StringIO(newline="")
    w = csv.DictWriter(buf, fieldnames=schema["columns"], lineterminator="\n")
    w.writeheader()
    for n in candidates:
        p = Path(n)
        w.writerow({"rater_id": rater, "item_id": p.stem, "task_folder": p.parts[0],
                    "candidate_file": n if p.stem.startswith("W") else p.name})
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
               "rater_id": rater, "sheet_url": sheet_url, "candidate_count": len(candidates),
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
