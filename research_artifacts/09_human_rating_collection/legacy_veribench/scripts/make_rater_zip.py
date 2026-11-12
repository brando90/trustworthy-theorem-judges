# TLDR: C15 item 11 delivery: builds one rater's self-contained zip (the v3 packet's instructions plus only that rater's assigned folders, byte-identical to the repo, with a matching FILES.sha256) and logs its contents and SHA-256 in DELIVERY_RECEIPTS.jsonl; zero model calls.
"""Usage:
  python3 scripts/make_rater_zip.py --packet setN --rater T01 --folders N03,N17 [--out-dir human_round/private_ratings_setN/delivery]
  python3 scripts/make_rater_zip.py --packet warmup --rater T01
"""
import argparse
import hashlib
import io
import json
import zipfile
from datetime import datetime, timezone
from pathlib import Path

EXP = Path(__file__).resolve().parents[1]
PACKETS = {"setN": EXP / "human_round/sample_setN/packet", "warmup": EXP / "human_round/warmup/packet"}
DOCS = ("START_HERE.md", "human_judgements_prompt.md")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--packet", choices=sorted(PACKETS), required=True)
    ap.add_argument("--rater", required=True)
    ap.add_argument("--folders", default="", help="setN: required comma-separated assigned folders; warmup: always every folder")
    ap.add_argument("--out-dir", default=str(EXP / "human_round/private_ratings_setN/delivery"))
    a = ap.parse_args()
    pk = PACKETS[a.packet]
    listing = {line[66:].strip(): line[:64] for line in (pk / "FILES.sha256").read_text().splitlines() if line.strip()}
    all_folders = sorted({p.split("/")[0] for p in listing if "/" in p})
    asked = [f.strip() for f in a.folders.split(",") if f.strip()]
    if a.packet == "setN" and not asked:
        raise SystemExit("--folders is required for setN (the rater's assigned folders)")
    if a.packet == "warmup" and asked and sorted(asked) != all_folders:
        raise SystemExit("the warm-up always ships complete; omit --folders")
    folders = asked or all_folders
    missing = [f for f in folders if f not in all_folders]
    if missing:
        raise SystemExit(f"unknown folders: {missing}")
    chosen = [p for p in listing if p in DOCS or p.split("/")[0] in folders]
    for p in chosen:  # every shipped file must still match the committed packet
        if hashlib.sha256((pk / p).read_bytes()).hexdigest() != listing[p]:
            raise SystemExit(f"{p} differs from FILES.sha256; refusing")
    top = f"VeriBench_{a.packet}_{a.rater}"
    sub_listing = "".join(f"{listing[p]}  {p}\n" for p in sorted(chosen))
    buf = io.BytesIO()
    with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as z:
        for p in sorted(chosen):
            info = zipfile.ZipInfo(f"{top}/{p}", date_time=(2026, 10, 8, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            z.writestr(info, (pk / p).read_bytes())
        info = zipfile.ZipInfo(f"{top}/FILES.sha256", date_time=(2026, 10, 8, 0, 0, 0))
        z.writestr(info, sub_listing)
    out = Path(a.out_dir)
    out.mkdir(parents=True, exist_ok=True)
    dest = out / f"{top}.zip"
    dest.write_bytes(buf.getvalue())
    receipt = {"rater": a.rater, "packet": a.packet, "folders": folders, "files": len(chosen) + 1,
               "zip": dest.name, "zip_sha256": hashlib.sha256(buf.getvalue()).hexdigest(),
               "files_sha256_listing": hashlib.sha256(sub_listing.encode()).hexdigest(),
               "built_utc": datetime.now(timezone.utc).isoformat(timespec="seconds")}
    with open(out / "DELIVERY_RECEIPTS.jsonl", "a") as f:
        f.write(json.dumps(receipt) + "\n")
    print(f"OK {dest} ({len(folders)} folders, {len(chosen) + 1} files, sha256 {receipt['zip_sha256'][:12]})")


if __name__ == "__main__":
    main()
