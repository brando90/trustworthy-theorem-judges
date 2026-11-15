#!/usr/bin/env python3
"""Preflight and gated sender for the 31 full-team 75-file rating emails.

Default mode is --dry-run (verifies all 31 manifests, Sheet readback release gates,
unique recipient URLs/emails, .zip SHA-256 digests, and credential availability
without sending any email). Sending requires explicit --confirm-send plus --all
or --only <RATER_ID ...>.
"""
from __future__ import annotations

import argparse
from email.message import EmailMessage
from email.utils import make_msgid
import hashlib
import json
from pathlib import Path
import smtplib
import sys
import time

REPO = Path(__file__).resolve().parents[4]
PREP = REPO / "research_artifacts/09_human_rating_collection/preparation_11-09-2026"
FULL = PREP / "full_team_11-14-2026"
DEFAULT_MANIFEST = FULL / "DISPATCH_MANIFEST_31_RATERS.json"
DEFAULT_RECEIPTS = FULL / "SENT_RECEIPTS.jsonl"
DEFAULT_PASSWORD_FILE = Path.home() / "keys/gmail_app_password.txt"


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate_manifest(manifest: list[dict]) -> None:
    if len(manifest) != 31:
        raise ValueError(f"Expected 31 outgoing raters in manifest, got {len(manifest)}")
    seen_ids: set[str] = set()
    seen_to: set[str] = set()
    seen_sheets: set[str] = set()
    seen_zips: set[str] = set()

    for entry in manifest:
        rid = entry["rater_id"]
        if rid == "A1":
            raise ValueError("Coordinator A1 must not be in outgoing 31-rater dispatch manifest")
        for key in ("rater_id", "rater_name", "from", "to", "bcc", "subject", "sheet_url", "attachment_path", "attachment_sha256", "assembly_receipt_path", "body"):
            if not entry.get(key):
                raise ValueError(f"{rid}: missing required manifest field {key}")

        to_lower = entry["to"].strip().lower()
        if rid in seen_ids or to_lower in seen_to or entry["sheet_url"] in seen_sheets or entry["attachment_path"] in seen_zips:
            raise ValueError(f"{rid}: duplicate id/email/sheet/zip across recipients")
        seen_ids.add(rid)
        seen_to.add(to_lower)
        seen_sheets.add(entry["sheet_url"])
        seen_zips.add(entry["attachment_path"])

        if entry["sheet_url"] not in entry["body"]:
            raise ValueError(f"{rid}: personal sheet_url not found in email body")
        if "TLDR-end:" in entry["body"] or "TLDR-start:" in entry["body"]:
            raise ValueError(f"{rid}: chat TLDR marker leaked into external email body")

        zip_path = REPO / entry["attachment_path"]
        receipt_path = REPO / entry["assembly_receipt_path"]
        if not zip_path.is_file():
            raise FileNotFoundError(f"{rid}: missing zip {zip_path}")
        if not receipt_path.is_file():
            raise FileNotFoundError(f"{rid}: missing assembly receipt {receipt_path}")

        actual_zip_sha = sha256_file(zip_path)
        if actual_zip_sha != entry["attachment_sha256"]:
            raise ValueError(f"{rid}: zip SHA-256 mismatch ({actual_zip_sha} != {entry['attachment_sha256']})")

        receipt = json.loads(receipt_path.read_text())
        if receipt.get("release_ready") is not True:
            raise ValueError(f"{rid}: ASSEMBLY_RECEIPT release_ready is not True")
        if receipt.get("sheet_url") != entry["sheet_url"]:
            raise ValueError(f"{rid}: receipt sheet_url mismatch")
        if receipt.get("archive_sha256") != actual_zip_sha:
            raise ValueError(f"{rid}: receipt archive_sha256 mismatch")
        if (receipt.get("task_count"), receipt.get("artifact_count")) != (25, 75):
            raise ValueError(f"{rid}: unexpected packet counts {(receipt.get('task_count'), receipt.get('artifact_count'))}")


def load_sent_ids(receipts_path: Path) -> set[str]:
    if not receipts_path.exists():
        return set()
    sent = set()
    for line in receipts_path.read_text().splitlines():
        if line.strip():
            rec = json.loads(line)
            if rec.get("status") == "SENT":
                sent.add(rec["rater_id"])
    return sent


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--receipts", type=Path, default=DEFAULT_RECEIPTS)
    parser.add_argument("--password-file", type=Path, default=DEFAULT_PASSWORD_FILE)
    parser.add_argument("--dry-run", action="store_true", help="Verify preflight without sending (default behavior)")
    parser.add_argument("--confirm-send", action="store_true", help="Actually send approved emails over SMTP")
    parser.add_argument("--all", action="store_true", help="Target all 31 recipients (with --confirm-send or --dry-run)")
    parser.add_argument("--only", nargs="+", help="Specific rater IDs to target")
    args = parser.parse_args()

    if not args.confirm_send:
        dry_run = True
    else:
        dry_run = args.dry_run
        if not dry_run and not args.all and not args.only:
            parser.error("--confirm-send requires --all or --only <RATER_ID ...>")

    manifest = json.loads(args.manifest.read_text())
    validate_manifest(manifest)

    if not args.password_file.is_file() or not args.password_file.read_text().strip():
        raise RuntimeError(f"Gmail app password file missing or empty at {args.password_file}")

    if args.only:
        wanted = set(args.only)
        unknown = wanted - {e["rater_id"] for e in manifest}
        if unknown:
            raise ValueError(f"Unknown rater IDs in --only: {sorted(unknown)}")
        targets = [e for e in manifest if e["rater_id"] in wanted]
    else:
        targets = manifest

    sent_ids = load_sent_ids(args.receipts)

    if dry_run:
        for entry in targets:
            already = " [already SENT]" if entry["rater_id"] in sent_ids else ""
            print(
                f"[DRY-RUN OK] {entry['rater_id']:3s} | {entry['rater_name']:24s} | "
                f"To={entry['to']:28s} | variant={entry['body_variant']:8s} | "
                f"zip_sha256={entry['attachment_sha256'][:12]}{already}"
            )
        print(f"Preflight passed for {len(targets)}/{len(manifest)} recipients (0 emails sent).")
        return 0

    password = args.password_file.read_text().strip()
    sender = targets[0]["from"]
    args.receipts.parent.mkdir(parents=True, exist_ok=True)
    with smtplib.SMTP_SSL("smtp.gmail.com", 465, timeout=30) as smtp:
        smtp.login(sender, password)
        for entry in targets:
            rid = entry["rater_id"]
            if rid in sent_ids:
                print(f"[SKIP already SENT] {rid} ({entry['to']})")
                continue
            zip_path = REPO / entry["attachment_path"]
            msg = EmailMessage()
            msg["From"] = f"Brando Miranda <{entry['from']}>"
            msg["To"] = entry["to"]
            msg["Bcc"] = ", ".join(entry["bcc"])
            msg["Subject"] = entry["subject"]
            msg["Message-ID"] = make_msgid(domain="gmail.com")
            msg.set_content(entry["body"])
            msg.add_attachment(
                zip_path.read_bytes(),
                maintype="application",
                subtype="zip",
                filename=zip_path.name,
            )
            smtp.send_message(msg)
            rec = {
                "timestamp_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                "status": "SENT",
                "rater_id": rid,
                "rater_name": entry["rater_name"],
                "from": entry["from"],
                "to": entry["to"],
                "bcc": entry["bcc"],
                "subject": entry["subject"],
                "message_id": msg["Message-ID"],
                "sheet_url": entry["sheet_url"],
                "attachment": entry["attachment_path"],
                "attachment_sha256": entry["attachment_sha256"],
            }
            with args.receipts.open("a") as fh:
                fh.write(json.dumps(rec) + "\n")
            print(f"[SENT] {rid} ({entry['rater_name']}) -> {entry['to']} | msg_id={msg['Message-ID']}")
            time.sleep(0.5)
    return 0


if __name__ == "__main__":
    sys.exit(main())
