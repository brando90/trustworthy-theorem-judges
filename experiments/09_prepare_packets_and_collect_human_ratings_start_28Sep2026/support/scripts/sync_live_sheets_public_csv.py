#!/usr/bin/env python3
"""Sync all 33 live native_main Google Sheets into ratings/ via public CSV export.

TLDR: Downloads the 33 Anyone-with-the-link Sheets in RAW_MANIFEST.json via Google's
public CSV export endpoint, validates exact version-7 15-column headers and set-level
immutable row identities fail-closed (preserving live Sheet row ordering and verbatim
participant cells), preserves every changed pre-sync revision, appends export-only `source_label=main`,
and refreshes RAW_MANIFEST.json, SUMMARY.json, ratings/README.md, and experiments/09_.../README.md.
Leaves T30 (restricted, HTTP 401) explicitly marked unverified when OAuth is unavailable.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import re
import sys
import time
import urllib.error
import urllib.request
from collections import Counter
from collections.abc import Mapping
from datetime import datetime, timezone
from pathlib import Path
from zoneinfo import ZoneInfo

HERE = Path(__file__).resolve().parent
EXPERIMENT = HERE.parents[1]
sys.path.insert(0, str(HERE))
from source_label import add_label, dumps as csv_dumps, read_rows_from  # noqa: E402

DEFAULT_BACKUP_DIR = EXPERIMENT / "support/sheet_exports/11-24-2026_before_first_ratings_sync"
STATUS_START = "<!-- grading-status:start -->"
STATUS_END = "<!-- grading-status:end -->"
VALID_SCORES = frozenset({"0", "1", "2", "3", "4", "5"})
SCHEMA_ATTESTATIONS = frozenset({"yes", "no", "unsure"})
# Inspected participant edit in column E (`candidate_file`); raw cell preserved verbatim in ratings/.
KNOWN_CANDIDATE_FILE_ANOMALIES = {("T06", "native-heavy-11-11-2026__item020"): "this one has borderline spam."}


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def fetch_sheet_csv(spreadsheet_id: str, timeout: int = 20, retries: int = 3) -> list[list[str]]:
    """Fetch a public Google Sheet tab as parsed CSV rows."""
    url = f"https://docs.google.com/spreadsheets/d/{spreadsheet_id}/export?format=csv"
    last_err: Exception | None = None
    for attempt in range(retries):
        if attempt:
            time.sleep(1.5 * attempt)
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                raw = resp.read().decode("utf-8-sig")
            return list(csv.reader(io.StringIO(raw, newline="")))
        except urllib.error.HTTPError as exc:
            last_err = exc
            if exc.code not in (429, 500, 502, 503, 504):
                raise
        except Exception as exc:  # noqa: BLE001
            last_err = exc
    raise RuntimeError(f"Failed fetching sheet {spreadsheet_id}: {last_err}") from last_err


def _validate_row(
    row_num: int,
    raw_row: list[str],
    ncols: int,
    rater_id: str,
    old_by_item: dict[str, list[str]],
    seen_items: set[str],
    score_idx: int,
    att_idx: int,
    min_idx: int,
    known_candidate_anomalies: Mapping[tuple[str, str], str],
    canonical_candidates: dict[str, str] | None,
) -> tuple[list[str], dict[str, object]]:
    """Validate one fetched sheet row against pre-sync identity and score rules."""
    if len(raw_row) > ncols:
        raise ValueError(f"{rater_id} row {row_num}: {len(raw_row)} columns exceeds {ncols}")
    row = raw_row + [""] * (ncols - len(raw_row))
    item_id = row[2]
    if item_id in seen_items:
        raise ValueError(f"{rater_id}: duplicate item_id {item_id!r}")
    if item_id not in old_by_item:
        raise ValueError(f"{rater_id} row {row_num}: unknown item_id {item_id!r}")
    old_row = old_by_item[item_id]
    if row[:4] != old_row[:4]:
        raise ValueError(f"{rater_id} row {row_num}: immutable identity mismatch {row[:4]!r} != {old_row[:4]!r}")
    if row[1] != rater_id:
        raise ValueError(f"{rater_id} row {row_num}: rater_id {row[1]!r} != {rater_id!r}")

    expected_cand = canonical_candidates.get(item_id, old_row[4]) if canonical_candidates else old_row[4]
    anomaly: dict[str, str] | None = None
    if row[4] != expected_cand:
        if known_candidate_anomalies.get((rater_id, item_id)) != row[4]:
            raise ValueError(
                f"{rater_id} row {row_num} ({item_id}): uninspected candidate_file edit "
                f"{row[4]!r} != {expected_cand!r}"
            )
        anomaly = {
            "rater_id": rater_id,
            "item_id": item_id,
            "expected_candidate_file": expected_cand,
            "live_candidate_file": row[4],
            "note": "Preserved verbatim in raw CSV; downstream joins key on (rater_id, item_id).",
        }

    score_val = row[score_idx].strip()
    is_numeric = score_val in VALID_SCORES
    is_na = score_val.upper() == "N/A"
    if not (is_numeric or is_na or score_val == ""):
        raise ValueError(f"{rater_id} item {item_id}: invalid final_score_0_5 {score_val!r}")

    return row, {
        "item_id": item_id,
        "anomaly": anomaly,
        "is_numeric": is_numeric,
        "is_na": is_na,
        "att_val": row[att_idx].strip() if (is_numeric or is_na) else None,
        "has_minutes": row[min_idx].strip() != "",
        "any_response": any(cell.strip() != "" for cell in row[5:]),
    }


def validate_and_normalize_table(
    raw_table: list[list[str]],
    expected_header: list[str],
    existing_csv_bytes: bytes,
    rater_id: str,
    known_candidate_anomalies: Mapping[tuple[str, str], str] = KNOWN_CANDIDATE_FILE_ANOMALIES,
    canonical_candidates: dict[str, str] | None = None,
) -> tuple[list[list[str]], dict]:
    """Verify exact v7 header, 4-col immutable identity set, and valid scores fail-closed."""
    if not raw_table:
        raise ValueError(f"{rater_id}: empty CSV table")
    ncols = len(expected_header)
    if len(raw_table[0]) > ncols:
        raise ValueError(f"{rater_id}: header has {len(raw_table[0])} columns, expected {ncols}")
    header = raw_table[0] + [""] * (ncols - len(raw_table[0]))
    if header != expected_header:
        raise ValueError(f"{rater_id}: unexpected header {header!r} != {expected_header!r}")

    existing_rows = read_rows_from(existing_csv_bytes)
    if len(raw_table) != len(existing_rows):
        raise ValueError(f"{rater_id}: row count {len(raw_table) - 1} != expected {len(existing_rows) - 1}")

    old_by_item: dict[str, list[str]] = {}
    old_order: list[str] = []
    for old_row in existing_rows[1:]:
        item_id = old_row[2]
        if item_id in old_by_item:
            raise ValueError(f"{rater_id}: duplicate pre-sync item_id {item_id!r}")
        old_by_item[item_id] = old_row
        old_order.append(item_id)

    table: list[list[str]] = [header]
    new_order: list[str] = []
    seen_items: set[str] = set()
    anomalies: list[dict[str, str]] = []

    score_idx = expected_header.index("final_score_0_5")
    att_idx = expected_header.index("ai_assisted_rating_attestation (AI help is allowed)")
    min_idx = expected_header.index("minutes_spent")

    numeric = 0
    not_applicable = 0
    any_response_rows = 0
    minutes_entries = 0
    attestation_counts: Counter[str] = Counter()

    for row_num, raw_row in enumerate(raw_table[1:], start=1):
        row, flags = _validate_row(
            row_num, raw_row, ncols, rater_id, old_by_item, seen_items,
            score_idx, att_idx, min_idx, known_candidate_anomalies, canonical_candidates,
        )
        item_id = str(flags["item_id"])
        seen_items.add(item_id)
        new_order.append(item_id)
        if flags["anomaly"] is not None:
            anomalies.append(flags["anomaly"])  # type: ignore[arg-type]
        if flags["is_numeric"]:
            numeric += 1
        if flags["is_na"]:
            not_applicable += 1
        if flags["att_val"] is not None:
            attestation_counts[str(flags["att_val"])] += 1
        if flags["has_minutes"]:
            minutes_entries += 1
        if flags["any_response"]:
            any_response_rows += 1
        table.append(row)

    if len(seen_items) != len(old_by_item):
        raise ValueError(f"{rater_id}: item count mismatch {len(seen_items)} != {len(old_by_item)}")

    reordered = new_order != old_order
    prior_has_responses = any(any(cell.strip() for cell in row[5:ncols]) for row in existing_rows[1:])
    if any_response_rows == 0 and not prior_has_responses and reordered:
        old_sorted = sorted((r[:ncols] for r in existing_rows[1:]), key=lambda r: r[2])
        new_sorted = sorted(table[1:], key=lambda r: r[2])
        if new_sorted != old_sorted:
            raise ValueError(f"{rater_id}: blank reordered sheet differs on non-empty cells after sorting by item_id")

    att_schema_valid = sum(c for k, c in attestation_counts.items() if k.lower() in SCHEMA_ATTESTATIONS)
    att_blank = attestation_counts.get("", 0)
    att_nonschema = {k: c for k, c in attestation_counts.items() if k != "" and k.lower() not in SCHEMA_ATTESTATIONS}

    stats = {
        "assigned_rows": len(table) - 1,
        "numeric_ratings": numeric,
        "not_applicable_rows": not_applicable,
        "any_response_rows": any_response_rows,
        "prior_has_responses": prior_has_responses,
        "minutes_entries": minutes_entries,
        "reordered_by_rater": reordered,
        "identity_cell_anomalies": anomalies,
        "attestation_breakdown_when_scored": dict(sorted(attestation_counts.items())),
        "attestation_schema_valid_when_scored": att_schema_valid,
        "attestation_blank_when_scored": att_blank,
        "attestation_nonschema_when_scored": att_nonschema,
    }
    return table, stats


def write_pre_sync_backup(
    backup_dir: Path,
    manifest_bytes: bytes,
    summary_bytes: bytes,
    changed_entries: list[tuple[dict, bytes, dict]],
    today_str: str,
) -> Path | None:
    """Preserve each changed revision without replacing the first-sync archive."""
    if not changed_entries:
        return None
    first_sync = not (backup_dir / "MANIFEST.json").exists()
    if not first_sync:
        revision_hash = sha256_bytes(manifest_bytes + b"".join(b for _, b, _ in changed_entries))[:16]
        backup_dir = backup_dir / f"{today_str}_revision_{revision_hash}"
    manifest_file = backup_dir / "MANIFEST.json"
    if manifest_file.exists():
        # A retry may reuse a completed archive only when every prior response matches.
        records = json.loads(manifest_file.read_text())["files"]
        if len(records) != len(changed_entries):
            raise ValueError("Existing pre-sync archive has an unexpected number of files")
        for record, (_, old_bytes, _) in zip(records, changed_entries):
            if (backup_dir / record["archived_snapshot"]).read_bytes() != old_bytes:
                raise ValueError("Existing pre-sync archive does not match the prior responses")
        return manifest_file
    backup_dir.mkdir(parents=True, exist_ok=True)
    (backup_dir / "RAW_MANIFEST_before_sync.json").write_bytes(manifest_bytes)
    (backup_dir / "SUMMARY_before_sync.json").write_bytes(summary_bytes)
    archived = []
    for entry, old_bytes, st in changed_entries:
        stem = Path(entry["filename"]).stem
        suffix = "before_first_ratings_sync" if first_sync else "before_sync"
        snap_name = f"{stem}_{suffix}.csv"
        (backup_dir / snap_name).write_bytes(old_bytes)
        archived.append({
            "rater_id": entry["rater_id"],
            "rater_name": entry["rater_name"],
            "previous_repo_path": f"experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026/{entry['path']}",
            "archived_snapshot": snap_name,
            "spreadsheet_id": entry["spreadsheet_id"],
            "previous_sha256": entry["sha256"],
            "previous_numeric_ratings": entry.get("numeric_ratings", 0),
            "new_numeric_ratings": st["numeric_ratings"],
            "reordered_by_rater": st["reordered_by_rater"],
        })
    record = {
        "archived_date": today_str,
        "reason": "Preserve exact pre-sync snapshots before importing live main-round human ratings and rater-sorted sheets via public CSV export.",
        "zero_observations_overwritten": all(entry.get("numeric_ratings", 0) == 0 for entry, _, _ in changed_entries),
        "files": archived,
    }
    manifest_file.write_text(json.dumps(record, indent=1, ensure_ascii=False) + "\n")
    return manifest_file


def _attestation_summary_text(stats_by_rater: dict[str, dict]) -> str:
    agg: Counter[str] = Counter()
    for st in stats_by_rater.values():
        agg.update(st["attestation_breakdown_when_scored"])
    total = sum(agg.values())
    if total == 0:
        return ""
    schema_counts: Counter[str] = Counter()
    nonschema: dict[str, int] = {}
    blank = agg.get("", 0)
    for k, v in agg.items():
        if k == "":
            continue
        kl = k.lower()
        if kl in SCHEMA_ATTESTATIONS:
            schema_counts[kl] += v
        else:
            nonschema[k] = v
    parts: list[str] = []
    for key in ("yes", "no", "unsure"):
        if schema_counts[key]:
            parts.append(f"{schema_counts[key]} `{key}`")
    for k, v in sorted(nonschema.items()):
        parts.append(f"{v} `{k}` (non-dropdown free text)")
    if blank:
        parts.append(f"{blank} blank")
    return f"{', '.join(parts)} across {total} scored rows"


def update_experiment_readme(
    text: str,
    stats_by_rater: dict[str, dict],
    today_str: str,
    time_str: str,
    t30_status: str,
) -> str:
    """Refresh the grading-status table and coordinator flags in experiment 09 README.md."""
    if text.count(STATUS_START) != 1 or text.count(STATUS_END) != 1:
        raise ValueError("Experiment 09 README must contain one grading-status block")
    before, rest = text.split(STATUS_START, 1)
    block, after = rest.split(STATUS_END, 1)
    lines = block.splitlines()
    total_scored = sum(s["numeric_ratings"] + s["not_applicable_rows"] for s in stats_by_rater.values())
    total_assigned = sum(s["assigned_rows"] for s in stats_by_rater.values())
    n_sheets = len(stats_by_rater)
    new_lines = []
    seen_raters: set[str] = set()
    for line in lines:
        if line.startswith("Live progress read from"):
            new_lines.append(
                f"Live progress read from the {n_sheets} Sheets via public CSV export on {today_str} at {time_str}; "
                "refresh with `python3 support/scripts/sync_live_sheets_public_csv.py` "
                "(or `build_full_team_packets.py status` once OAuth is renewed). "
                f"Scored = rows with a `final_score_0_5` entry. Total scored: **{total_scored}** of {total_assigned}."
            )
            continue
        m = re.match(r"^\| `([^`]+)` \|", line)
        if m and m.group(1) in stats_by_rater:
            rid = m.group(1)
            s = stats_by_rater[rid]
            done = s["numeric_ratings"] + s["not_applicable_rows"]
            parts = line.split("|")
            if rid in seen_raters or len(parts) != 10:
                raise ValueError(f"Experiment README has a duplicate or malformed row for {rid}")
            seen_raters.add(rid)
            parts[7] = f" **{done}/{s['assigned_rows']}** "
            new_lines.append("|".join(parts))
            continue
        new_lines.append(line)
    if seen_raters != set(stats_by_rater):
        raise ValueError(f"Experiment README is missing rater rows: {sorted(set(stats_by_rater) - seen_raters)}")
    updated_block = "\n".join(new_lines).rstrip("\n") + "\n"
    after = re.sub(
        r"(Also rating: `T30` Max Sieb.*?)(?:0/100 scored on 11-18-2026|unverified [^;]+)",
        rf"\1{t30_status}",
        after,
        count=1,
    )
    att_text = _attestation_summary_text(stats_by_rater)
    anomalies = [a for s in stats_by_rater.values() for a in s["identity_cell_anomalies"]]
    if att_text or anomalies:
        att_part = f"Attestations (`ai_assisted_rating_attestation (AI help is allowed)`): {att_text}; " if att_text else ""
        if anomalies:
            anom_items = ", ".join(f"`{a['rater_id']}` (`{a['item_id']}`)" for a in anomalies)
            verb = "has" if len(anomalies) == 1 else "have"
            anom_str = (
                f" {anom_items} {verb} participant text in `candidate_file` preserved verbatim "
                "(canonical path resolved by `item_id`)."
            )
        else:
            anom_str = ""
        coord_line = (
            f"<!-- coordinator_sync_flags --> **Coordinator check ({today_str}):** "
            f"{att_part}"
            f"preserved verbatim per raw-response policy and flagged for coordinator review (no rater emails sent).{anom_str}"
        )
        if "<!-- coordinator_sync_flags -->" in after:
            # Earlier exports put the policy on the same line; retain it on refresh.
            after = re.sub(
                r"<!-- coordinator_sync_flags -->[^\n]*?(?= Rater data policy \(|\n|$)",
                lambda _: coord_line,
                after,
                count=1,
            )
        elif "Rater data policy (" in after:
            after = after.replace("Rater data policy (", coord_line + "\n\nRater data policy (", 1)
    return before + STATUS_START + updated_block + STATUS_END + after


def update_ratings_readme(
    text: str,
    stats_by_rater: dict[str, dict],
    total_numeric: int,
    warmup_na: int,
    today_str: str,
    warmup_numeric: int = 15,
) -> str:
    """Update counts and checked date in ratings/README.md."""
    main_numeric = sum(s["numeric_ratings"] for s in stats_by_rater.values())
    main_scored = sum(s["numeric_ratings"] + s["not_applicable_rows"] for s in stats_by_rater.values())
    total_assigned = sum(s["assigned_rows"] for s in stats_by_rater.values())
    raters_nonzero = sum(1 for s in stats_by_rater.values() if s["numeric_ratings"] > 0)
    raters_scored = sum(
        1 for s in stats_by_rater.values() if s["numeric_ratings"] + s["not_applicable_rows"] > 0
    )
    att_text = _attestation_summary_text(stats_by_rater)
    att_clause = f" Attestations: {att_text}." if att_text else ""
    anomalies = [a for s in stats_by_rater.values() for a in s["identity_cell_anomalies"]]
    if anomalies:
        if len(anomalies) == 1 and anomalies[0]["rater_id"] == "T06" and anomalies[0]["item_id"] == "native-heavy-11-11-2026__item020":
            anom_clause = (
                " All submitted values, blanks, rater row orders, and `T06` `item020`'s edited `candidate_file` cell "
                "are preserved verbatim per raw-response policy and flagged for coordinator review."
            )
        else:
            anom_items = ", ".join(f"`{a['rater_id']}` `{a['item_id']}`" for a in anomalies)
            anom_clause = (
                f" All submitted values, blanks, rater row orders, and edited `candidate_file` cells ({anom_items}) "
                "are preserved verbatim per raw-response policy and flagged for coordinator review."
            )
    else:
        anom_clause = " All submitted values, blanks, and rater row orders are preserved verbatim per raw-response policy."
    text = re.sub(
        r"\*\*Checked: [^*]+\*\*[^\n]*",
        f"**Checked: {today_str} via public CSV export.** The collection holds **{warmup_numeric} numeric warm-up ratings, "
        f"{warmup_na} warm-up `N/A` entries, and {main_numeric} numeric main-round ratings** "
        f"({total_numeric} numeric ratings total across {raters_nonzero} active main-round raters; "
        f"`T30` Max Sieb stays unverified under expired Sheets OAuth with HTTP 401 on public CSV export).{att_clause}"
        f"{anom_clause}",
        text,
        count=1,
    )
    text = re.sub(
        r"All \*\*\d+\*\* current main Google Sheets \([^)]+\) have \*\*\d+\*\* rows \([^)]+\)",
        f"All **{len(stats_by_rater)}** current main Google Sheets (`A1` author plus `32` team, new co-author invitees and Vals raters; "
        f"`V04` Vaibhav Mahajan added 11-17-2026) have **100** rows (`25` tasks x `4` agents; "
        f"**{main_scored}/{total_assigned}** scored across {raters_scored} raters on {today_str})",
        text,
        count=1,
    )
    out_lines = []
    seen_raters: set[str] = set()
    for line in text.splitlines():
        m = re.match(r"^\| `([^`]+)` \|", line)
        if m and m.group(1) in stats_by_rater:
            rid = m.group(1)
            s = stats_by_rater[rid]
            done = s["numeric_ratings"] + s["not_applicable_rows"]
            parts = line.split("|")
            if rid in seen_raters or len(parts) != 7:
                raise ValueError(f"Ratings README has a duplicate or malformed row for {rid}")
            seen_raters.add(rid)
            parts[5] = re.sub(r"\d+/\d+", f"{done}/{s['assigned_rows']}", parts[5], count=1)
            out_lines.append("|".join(parts))
        else:
            out_lines.append(line)
    if seen_raters != set(stats_by_rater):
        raise ValueError(f"Ratings README is missing rater rows: {sorted(set(stats_by_rater) - seen_raters)}")
    return "\n".join(out_lines) + ("\n" if text.endswith("\n") else "")


def _apply_sync_outputs(
    experiment_dir: Path,
    backup_dir: Path,
    schema: dict,
    manifest: dict,
    manifest_bytes: bytes,
    summary: dict,
    summary_bytes: bytes,
    pending_writes: list[tuple[dict, bytes, bytes, list[list[str]], dict]],
    changed_entries: list[tuple[dict, bytes, dict]],
    stats_by_rater: dict[str, dict],
    reordered_raters: list[str],
    agg_att: Counter[str],
    all_anomalies: list[dict[str, str]],
    today_str: str,
    time_str: str,
    now_utc: str,
) -> None:
    """Persist backup, synced CSVs, RAW_MANIFEST.json, SUMMARY.json, and collection READMEs."""
    ratings_dir = experiment_dir / "ratings"
    outputs: dict[Path, bytes] = {}
    for entry, _, new_bytes, table, st in pending_writes:
        outputs[experiment_dir / entry["path"]] = new_bytes
        status_str = (
            "prepared blank form (reordered in place by rater; 0 responses)"
            if st["any_response_rows"] == 0 and st["reordered_by_rater"]
            else (
                "prepared blank form, not a completed observation"
                if st["any_response_rows"] == 0
                else "live table; participant responses preserved as entered"
            )
        )
        entry.update({
            "columns": table[0],
            "csv_columns": [*table[0], "source_label"],
            "source_label": "main",
            "form_version": schema["version"],
            "range": f"Ratings!A1:O{len(table)}",
            "assigned_rows": st["assigned_rows"],
            "rows": st["assigned_rows"],
            "numeric_ratings": st["numeric_ratings"],
            "not_applicable_rows": st["not_applicable_rows"],
            "sha256": sha256_bytes(new_bytes),
            "source_readback_sha256": st["readback_sha"],
            "status": status_str,
        })

    total_numeric = sum(f.get("numeric_ratings", 0) for f in manifest["files"])
    total_na = sum(f.get("not_applicable_rows", 0) for f in manifest["files"])
    main_numeric = sum(s["numeric_ratings"] for s in stats_by_rater.values())
    main_na = sum(s["not_applicable_rows"] for s in stats_by_rater.values())
    active_raters = sorted(
        rid for rid, s in stats_by_rater.items() if s["numeric_ratings"] + s["not_applicable_rows"] > 0
    )

    manifest["numeric_observations"] = total_numeric
    manifest["not_applicable_rows"] = total_na
    manifest["checked_date"] = today_str
    manifest["recorded_utc"] = now_utc
    rev = manifest.get("full_team_100_native_revision", {})
    rev.update({
        "date": today_str,
        "sheets_verified": len(stats_by_rater),
        "main_numeric_observations": main_numeric,
        "main_not_applicable_rows": main_na,
        "active_raters": active_raters,
        "reordered_by_rater": reordered_raters,
        "attestation_breakdown_when_scored": dict(sorted(agg_att.items())),
        "identity_cell_anomalies": all_anomalies,
        "sync_method": "public CSV export (gspread_authorized_user.json invalid_grant; T30 HTTP 401 unverified)",
    })
    manifest["full_team_100_native_revision"] = rev
    outputs[ratings_dir / "RAW_MANIFEST.json"] = (json.dumps(manifest, indent=1, ensure_ascii=False) + "\n").encode()

    summary["checked_date"] = today_str
    summary["recorded_utc"] = now_utc
    summary["full_team_100_native_sync"] = {
        "date": today_str,
        "artifacts": 100,
        "tasks": 25,
        "agents_per_task": 4,
        "sheets_verified": len(stats_by_rater),
        "main_numeric_observations": main_numeric,
        "main_not_applicable_rows": main_na,
        "active_raters": active_raters,
        "reordered_by_rater": reordered_raters,
        "attestation_breakdown_when_scored": dict(sorted(agg_att.items())),
        "identity_cell_anomalies": all_anomalies,
        "emails_sent": "A1 to self + 32",
        "t30_status": f"unverified {today_str} (HTTP 401 on public CSV export; Sheets OAuth expired)",
    }
    outputs[ratings_dir / "SUMMARY.json"] = (json.dumps(summary, indent=1, ensure_ascii=False) + "\n").encode()

    t30_note = f"unverified {today_str} (HTTP 401; Sheets OAuth expired)"
    exp_readme_path = experiment_dir / "README.md"
    if exp_readme_path.exists():
        outputs[exp_readme_path] = update_experiment_readme(
            exp_readme_path.read_text(), stats_by_rater, today_str, time_str, t30_note
        ).encode()
    ratings_readme_path = ratings_dir / "README.md"
    if ratings_readme_path.exists():
        warmup_numeric = sum(
            f.get("numeric_ratings", 0) for f in manifest["files"] if f.get("packet") == "warmup"
        )
        warmup_na = sum(
            f.get("not_applicable_rows", 0) for f in manifest["files"] if f.get("packet") == "warmup"
        )
        outputs[ratings_readme_path] = update_ratings_readme(
                ratings_readme_path.read_text(),
                stats_by_rater,
                total_numeric,
                warmup_na,
                today_str,
                warmup_numeric=warmup_numeric,
            ).encode()

    # Validate and render every dependent output before replacing any raw responses.
    write_pre_sync_backup(backup_dir, manifest_bytes, summary_bytes, changed_entries, today_str)
    for path, data in outputs.items():
        path.write_bytes(data)


def run_sync(
    dry_run: bool = False,
    fetcher=fetch_sheet_csv,
    experiment_dir: Path = EXPERIMENT,
    backup_dir: Path = DEFAULT_BACKUP_DIR,
    known_candidate_anomalies: Mapping[tuple[str, str], str] = KNOWN_CANDIDATE_FILE_ANOMALIES,
) -> dict:
    """Execute fail-closed public-CSV sync across all 33 native_main sheets."""
    schema = json.loads((experiment_dir / "support/RATING_FORM_SCHEMA.json").read_text())
    expected_header = schema["main_form_v7_columns"]
    ratings_dir = experiment_dir / "ratings"
    manifest_bytes = (ratings_dir / "RAW_MANIFEST.json").read_bytes()
    summary_bytes = (ratings_dir / "SUMMARY.json").read_bytes()
    manifest = json.loads(manifest_bytes)
    summary = json.loads(summary_bytes)

    native_entries = [entry for entry in manifest["files"] if entry.get("packet") == "native_main"]
    prior_bytes: dict[str, bytes] = {}
    for entry in native_entries:
        old_bytes = (experiment_dir / entry["path"]).read_bytes()
        if sha256_bytes(old_bytes) != entry["sha256"]:
            raise ValueError(f"{entry['rater_id']}: pre-sync CSV does not match its manifest SHA-256")
        rows = read_rows_from(old_bytes)
        if not rows or rows[0] != [*expected_header, "source_label"] or any(len(row) != len(rows[0]) for row in rows[1:]):
            raise ValueError(f"{entry['rater_id']}: malformed pre-sync CSV table")
        prior_bytes[entry["path"]] = old_bytes

    canonical_candidates: dict[str, str] | None = None
    a1_entry = next((entry for entry in native_entries if entry["rater_id"] == "A1"), None)
    if a1_entry is not None:
        canonical_candidates = {r[2]: r[4] for r in read_rows_from(prior_bytes[a1_entry["path"]])[1:]}

    now_pt = datetime.now(ZoneInfo("America/Los_Angeles"))
    now_utc = datetime.now(timezone.utc).isoformat()
    today_str = now_pt.strftime("%m-%d-%Y")
    time_str = now_pt.strftime("%H:%M %Z")

    pending_writes: list[tuple[dict, bytes, bytes, list[list[str]], dict]] = []
    stats_by_rater: dict[str, dict] = {}

    for entry in native_entries:
        rid = entry["rater_id"]
        old_bytes = prior_bytes[entry["path"]]
        raw_table = fetcher(entry["spreadsheet_id"])
        table, stats = validate_and_normalize_table(
            raw_table,
            expected_header,
            old_bytes,
            rid,
            known_candidate_anomalies=known_candidate_anomalies,
            canonical_candidates=canonical_candidates,
        )
        new_bytes = csv_dumps(add_label(table, "main"))
        if stats["any_response_rows"] == 0 and not stats["prior_has_responses"] and not stats["reordered_by_rater"] and sha256_bytes(new_bytes) != entry["sha256"]:
            raise ValueError(
                f"{rid}: untouched blank sheet SHA-256 {sha256_bytes(new_bytes)} != manifest {entry['sha256']}"
            )
        readback_sha = sha256_bytes(json.dumps(table, ensure_ascii=False, separators=(",", ":")).encode())
        stats_by_rater[rid] = stats
        pending_writes.append((entry, old_bytes, new_bytes, table, {**stats, "readback_sha": readback_sha}))

    changed_entries = [
        (entry, old_bytes, st)
        for entry, old_bytes, new_bytes, _, st in pending_writes
        if old_bytes != new_bytes
    ]
    all_anomalies = [a for st in stats_by_rater.values() for a in st["identity_cell_anomalies"]]
    reordered_raters = sorted(rid for rid, st in stats_by_rater.items() if st["reordered_by_rater"])

    agg_att: Counter[str] = Counter()
    for st in stats_by_rater.values():
        agg_att.update(st["attestation_breakdown_when_scored"])

    if not dry_run:
        _apply_sync_outputs(
            experiment_dir,
            backup_dir,
            schema,
            manifest,
            manifest_bytes,
            summary,
            summary_bytes,
            pending_writes,
            changed_entries,
            stats_by_rater,
            reordered_raters,
            agg_att,
            all_anomalies,
            today_str,
            time_str,
            now_utc,
        )

    return {
        "sheets_verified": len(stats_by_rater),
        "changed_files": [e["filename"] for e, _, _ in changed_entries],
        "main_numeric_observations": sum(s["numeric_ratings"] for s in stats_by_rater.values()),
        "main_not_applicable_rows": sum(s["not_applicable_rows"] for s in stats_by_rater.values()),
        "reordered_by_rater": reordered_raters,
        "attestation_breakdown_when_scored": dict(sorted(agg_att.items())),
        "identity_cell_anomalies": all_anomalies,
        "per_rater": {
            rid: st for rid, st in stats_by_rater.items() if st["numeric_ratings"] + st["not_applicable_rows"] > 0
        },
        "dry_run": dry_run,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--dry-run", action="store_true", help="Fetch and validate without writing files")
    args = parser.parse_args()
    result = run_sync(dry_run=args.dry_run)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
