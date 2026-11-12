# TLDR: C15 item 11 delivery: builds one rater's self-contained zip (the packet's instructions plus only that rater's assigned folders, byte-identical to the repo, plus YOUR_RATING_SHEET.txt with the rater's personal Google Sheet link, all listed in a matching FILES.sha256) and logs its contents, sheet and SHA-256 in DELIVERY_RECEIPTS.jsonl; zero model calls.
"""Usage from the trustworthy-theorem-judges root:
  python3 experiments/09_human_rating_collection/support/scripts/legacy/make_rater_zip.py --packet setN --rater T01 --folders N03,N17 --sheet-url URL --share-email EMAIL [--out-dir research_artifacts/NEW_DELIVERY]
  python3 experiments/09_human_rating_collection/support/scripts/legacy/make_rater_zip.py --packet warmup --rater T01 --sheet-url URL --share-email EMAIL

URL is the rater's personal sheet for that packet (owned by the coordinator, shared with the rater's Google account(s) as editor, rater code pre-filled);
add --share-email with those account(s).
"""
import argparse
import hashlib
import io
import json
import re
import zipfile
from urllib.parse import urlsplit
from datetime import datetime, timezone
from pathlib import Path
from packet_release import require_release

# Use the pinned committed snapshot, not the stale shared VeriBench checkout.
EXP = (Path(__file__).resolve().parents[5] / "research_artifacts/09_human_rating_collection/upstream_source"
       / "experiments/102_rescore_vbv1_paper_fsc_with_validated_judge_rewrite_tmlr_icml")
PACKETS = {"setN": EXP / "human_round/sample_setN/packet", "warmup": EXP / "human_round/warmup/packet"}
DOCS = ("START_HERE.md", "human_judgements_prompt.md")
SHEET_PATH = re.compile(r"^/spreadsheets/d/([A-Za-z0-9_-]{20,})(/[A-Za-z]*)?/?$")
SHEET_NOTE = """Your rating sheet (rater {rater}), for this packet only:
{url}

It is shared with you as an editor ({emails}); open it while signed in to Google with {that}.
Type straight into it; it saves as you go. There is nothing to copy, share or send.
Please don't forward this link.
"""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--packet", choices=sorted(PACKETS), required=True)
    ap.add_argument("--rater", required=True)
    ap.add_argument("--folders", default="", help="setN: required comma-separated assigned folders; warmup: always every folder")
    ap.add_argument("--sheet-url", required=True, help="the rater's personal Google Sheet for this packet")
    ap.add_argument("--share-email", required=True, help="comma-separated Google account(s) the sheet is shared with as editor")
    ap.add_argument("--out-dir", default=str(EXP / "human_round/private_ratings_setN/delivery"))
    a = ap.parse_args()
    require_release(a.packet)
    u = urlsplit(a.sheet_url.strip())  # query strings and #gid fragments are dropped
    m = SHEET_PATH.match(u.path) if (u.scheme, u.netloc) == ("https", "docs.google.com") else None
    if not m:
        raise SystemExit(f"--sheet-url must be a Google Sheets link, got {a.sheet_url!r}")
    sheet_id = m.group(1)
    sheet_url = f"https://docs.google.com/spreadsheets/d/{sheet_id}/edit"
    pk = PACKETS[a.packet]
    if b"YOUR_RATING_SHEET.txt" not in (pk / "START_HERE.md").read_bytes():
        raise SystemExit(f"{a.packet} packet START_HERE.md predates v5 (no personal-sheet step); rebuild the packet first")
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
    emails = [e.strip() for e in a.share_email.split(",") if e.strip()]
    if not emails or not all(re.fullmatch(r"[^@\s]+@[^@\s]+\.[^@\s]+", e) for e in emails):
        raise SystemExit(f"--share-email must list email addresses, got {a.share_email!r}")
    note = SHEET_NOTE.format(rater=a.rater, url=sheet_url, emails=" or ".join(emails),
                              that="that address" if len(emails) == 1 else "one of those addresses").encode()
    entries = {p: listing[p] for p in chosen}
    entries["YOUR_RATING_SHEET.txt"] = hashlib.sha256(note).hexdigest()
    sub_listing = "".join(f"{entries[p]}  {p}\n" for p in sorted(entries))
    stamp = (2026, 10, 9, 0, 0, 0)
    buf = io.BytesIO()
    with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as z:
        for p in sorted(chosen):
            info = zipfile.ZipInfo(f"{top}/{p}", date_time=stamp)
            info.compress_type = zipfile.ZIP_DEFLATED
            z.writestr(info, (pk / p).read_bytes())
        for name, data in (("YOUR_RATING_SHEET.txt", note), ("FILES.sha256", sub_listing.encode())):
            info = zipfile.ZipInfo(f"{top}/{name}", date_time=stamp)
            info.compress_type = zipfile.ZIP_DEFLATED
            z.writestr(info, data)
    out = Path(a.out_dir)
    out.mkdir(parents=True, exist_ok=True)
    dest = out / f"{top}.zip"
    with dest.open("xb") as stream:  # A delivered archive is immutable; use a new output directory.
        stream.write(buf.getvalue())
    receipt = {"rater": a.rater, "packet": a.packet, "folders": folders, "files": len(chosen) + 2,
               "sheet_id": sheet_id, "sheet_url": sheet_url, "shared_with": emails,
               "zip": dest.name, "zip_sha256": hashlib.sha256(buf.getvalue()).hexdigest(),
               "files_sha256_listing": hashlib.sha256(sub_listing.encode()).hexdigest(),
               "built_utc": datetime.now(timezone.utc).isoformat(timespec="seconds")}
    with open(out / "DELIVERY_RECEIPTS.jsonl", "a") as f:
        f.write(json.dumps(receipt) + "\n")
    print(f"OK {dest} ({len(folders)} folders, {len(chosen) + 2} files, sheet {sheet_id[:10]}..., sha256 {receipt['zip_sha256'][:12]})")


if __name__ == "__main__":
    main()
