"""Build a new, blinded rating packet from an explicitly frozen private cohort.

The coordinator supplies artifacts, hashes and terminal-output classifications;
this builder never selects by scores, runs a model, or edits existing packets.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
from pathlib import Path
import re
import sys
from urllib.parse import urlsplit
from zipfile import ZIP_DEFLATED, ZipFile, ZipInfo


EXPERIMENT = Path(__file__).resolve().parents[3]
COLUMNS = [
    "rater_name", "rater_id", "item_id", "task_folder", "candidate_file",
    "final_score_0_5", "ai_assisted_rating_attestation", "minutes_spent",
    "confidence", "problem_note", "rationale (optional)",
]  # form version 6 (11-17-2026): rationale last, header `rationale (optional)`


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def checked_file(record: dict, base: Path) -> tuple[bytes, str]:
    """Read only a real, hash-verified file; absence never becomes an empty answer."""
    require(isinstance(record.get("path"), str) and bool(record["path"]),
            "Every artifact needs an explicit source path")
    require(isinstance(record.get("sha256"), str)
            and bool(re.fullmatch(r"[0-9a-f]{64}", record["sha256"])),
            "Every source needs a lowercase SHA256")
    path = Path(record["path"])
    path = (base / path).resolve() if not path.is_absolute() else path.resolve()
    require(path.is_file(), f"Missing source file: {path}")
    data = path.read_bytes()
    require(digest(data) == record["sha256"], f"Source hash mismatch: {path}")
    return data, str(path)


def permutation_key(seed: str, kind: str, identity: str) -> str:
    return digest(json.dumps([seed, kind, identity], separators=(",", ":")).encode())


def display_layout(artifacts: list[dict], seed: str) -> dict:
    """Derive neutral paths before filtering missing outputs or assignments."""
    tasks = {}
    for artifact in artifacts:
        tasks.setdefault(artifact["task_id"], []).append(artifact)
    result = {}
    for number, tid in enumerate(sorted(tasks, key=lambda t: permutation_key(seed, "task", t)), 1):
        description = tasks[tid][0]["task_description"]
        require(all(a["task_description"] == description for a in tasks[tid]),
                "One task has inconsistent descriptions")
        slug = re.sub(r"[^a-z0-9]+", "_", description.lower()).strip("_")[:80]
        require(bool(slug), "Task description needs a readable name")
        folder = f"task_{number:02d}_{slug}"
        for index, artifact in enumerate(sorted(tasks[tid], key=lambda a:
                permutation_key(seed, "candidate", a["item_id"])), 1):
            require(artifact["item_id"] not in result, "Duplicate item ID")
            result[artifact["item_id"]] = {
                "task_folder": folder, "candidate_file": f"{folder}/agent_lean/agent_{index}.lean"}
    return result


def checked_display_layout(cohort: dict, base: Path) -> dict:
    """A ratable subset must bind its paths to the original complete inventory."""
    if "display_layout" not in cohort:
        require(not cohort.get("excluded_item_ids"), "A filtered cohort needs the original display layout")
        return display_layout(cohort["artifacts"], cohort["shuffle_seed"])
    raw, _ = checked_file(cohort["planned_cohort"], base)
    planned = json.loads(raw)
    require(planned["round_id"] == cohort["round_id"]
            and planned["shuffle_seed"] == cohort["shuffle_seed"], "Display-layout round/seed mismatch")
    expected = display_layout(planned["artifacts"], planned["shuffle_seed"])
    require(cohort["display_layout"] == expected, "Frozen display layout changed")
    originals = {a["item_id"]: a for a in planned["artifacts"]}
    # Optional, explicit amendments (absent in earlier cohorts, whose behavior is unchanged):
    # layout_additions places new cells beside the planned ones without renumbering them;
    # configuration_substitutions records a planned cell filled from another declared configuration.
    additions = cohort.get("layout_additions", {})
    substitutions = cohort.get("configuration_substitutions", {})
    require(isinstance(additions, dict) and isinstance(substitutions, dict), "Invalid layout amendment")
    by_item = {a["item_id"]: a for a in cohort["artifacts"]}
    require(set(additions) <= set(by_item) and not set(additions) & set(originals),
            "A layout addition must be a new cohort item")
    require(set(substitutions) <= set(by_item) & set(originals), "A substitution must fill a planned cell")
    for artifact in cohort["artifacts"]:
        item = artifact["item_id"]
        if item in additions:
            continue
        original = originals.get(item, {})
        keys = ("task_id", "task_description", "python", "gold") + (
            () if item in substitutions else ("configuration_id",))
        require(all(artifact[k] == original.get(k) for k in keys),
                "Filtered cohort changed a planned identity or source")
        if item in substitutions:
            record = substitutions[item]
            require(record.get("planned_configuration_id") == original.get("configuration_id")
                    and record.get("actual_configuration_id") == artifact["configuration_id"]
                    and bool(record.get("reason")), "Incomplete configuration substitution record")
    folder_by_task = {originals[i]["task_id"]: place["task_folder"] for i, place in expected.items()}
    used = {place["candidate_file"] for place in expected.values()}
    merged = dict(expected)
    for item, place in additions.items():
        folder = folder_by_task.get(by_item[item]["task_id"])
        require(folder is not None and place.get("task_folder") == folder,
                "A layout addition must use its task's planned folder")
        name = place.get("candidate_file", "")
        require(bool(re.fullmatch(re.escape(folder) + r"/agent_lean/agent_[0-9]+\.lean", name))
                and name not in used, "A layout addition needs a new neutral file name")
        used.add(name)
        merged[item] = {"task_folder": folder, "candidate_file": name}
    return merged


RUBRIC_URL = ("https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/"
              "09_prepare_packets_and_collect_human_ratings_start_28Sep2026/rating_task_packet/human_judgements_prompt.md")
ATTESTATION = ("I used AI for localized assistance. I personally compared the specifications and chose the final score; "
               "I did not delegate the rating task to AI.")


def start_here(name: str, sheet_url: str, tasks: int, items: int, empty: bool, skipped: bool = False) -> bytes:
    # Brando, 11-17-2026: the packet is START_HERE.md plus the task folders only. The rubric is linked (one copy, on
    # GitHub); there is no column guide, no ratings.csv and no FILES.sha256 in the zip.
    text = (
        f"# Main rating task: {items} files in {tasks} task folders\n\n"
        f"1. [Open your personal rating sheet]({sheet_url}) for {name}.\n"
        f"2. Read [the scoring rubric]({RUBRIC_URL}). Compare theorem statements, not proofs.\n"
        "3. Follow the numbered task folders. In each, read `python_source/source.py`, "
        "the reference statements in `gold_lean/reference.lean`, and each file in `agent_lean/`.\n"
        "4. In your sheet, for each file enter `final_score_0_5` (0 to 5) and answer `ai_assisted_rating_attestation` "
        f"with yes, no or unsure to: \"{ATTESTATION}\" If you rated a file without any AI, answer no and write "
        "\"rated personally without AI\" in `problem_note`. Please also estimate `minutes_spent` and `confidence` "
        "(low, medium or high). `rationale (optional)`, the last column, is welcome but optional.\n\n"
        "Your sheet saves automatically; there is nothing to send back. Leave unfinished scores blank. "
        "If a reference looks wrong, leave its score blank, describe it in `problem_note` and email brandojazz@gmail.com.\n"
    )
    if empty:
        text += "\nAn empty candidate file records an empty solver output. Apply the same rubric; no score is prefilled.\n"
    if skipped:
        text += "\nFile numbers can skip; rate only the files listed in your Sheet.\n"
    return text.encode()


def build_packet(cohort_path: Path, output_dir: Path, *, rater_name: str,
                 rater_id: str, sheet_url: str, task_ids: list[str] | None = None,
                 form_home: Path = EXPERIMENT, row_order: list[str] | None = None) -> dict:
    """Create output_dir/rating_task_packet, its ZIP, and a private join receipt.

    Cohort schema: {schema_version:1, round_id, shuffle_seed, expected_artifacts,
    configurations:{id:{...}}, artifacts:[{task_id, task_description, item_id,
    configuration_id, python:{path,sha256}, gold:{path,sha256},
    candidate:{path,sha256,status:'nonempty'|'empty'}, provenance:{...}}]}.
    Item IDs have the neutral form '<round_id>__item001'. Per-task filenames and
    item IDs remain identical in subset packets and the complete packet.
    """
    cohort_path, output_dir = cohort_path.resolve(), output_dir.resolve()
    require(not output_dir.exists(), f"Refusing to overwrite existing build: {output_dir}")
    require(bool(re.fullmatch(r"[A-Za-z0-9_-]+", rater_id)), "Invalid rater ID")
    require(bool(rater_name.strip()) and rater_name == rater_name.strip()
            and not any(c in rater_name for c in "\r\n<>[]"), "Invalid rater name")
    url = urlsplit(sheet_url)
    require(url.scheme == "https" and url.netloc == "docs.google.com"
            and bool(re.match(r"^/spreadsheets/d/[A-Za-z0-9_-]+(?:/|$)", url.path))
            and not re.search(r"[\s<>()\[\]]", sheet_url), "Use the personal Google Sheets URL")
    raw = cohort_path.read_bytes()
    cohort = json.loads(raw)
    require(cohort.get("schema_version") == 1, "Unsupported cohort schema")
    require(cohort.get("buildable") is True and cohort.get("status") in
            {"FINAL_FULL_COHORT", "FINAL_RATABLE_SUBSET"}, "Use a finalized, buildable cohort")
    round_id, seed = cohort.get("round_id", ""), cohort.get("shuffle_seed")
    require(bool(re.fullmatch(r"[a-z0-9][a-z0-9_-]{2,70}", round_id)), "Invalid round ID")
    require(isinstance(seed, str) and bool(seed), "A fixed shuffle seed is required")
    artifacts = cohort.get("artifacts", [])
    require(bool(artifacts) and len(artifacts) == cohort.get("expected_artifacts"),
            "Cohort count does not match expected_artifacts")
    configurations = cohort.get("configurations", {})
    require(isinstance(configurations, dict) and bool(configurations), "Missing private configurations")
    layout = checked_display_layout(cohort, cohort_path.parent)

    schema_path = form_home / "support/RATING_FORM_SCHEMA.json"
    schema_bytes = schema_path.read_bytes()
    schema = json.loads(schema_bytes)
    require(schema["columns"] == COLUMNS, "Current form schema changed; review the builder")
    require(schema["required_new_responses"] == COLUMNS[5:7], "Required fields changed")
    rubric = (form_home / "rating_task_packet/human_judgements_prompt.md").read_bytes()

    tasks, seen, pairs, loaded = {}, set(), set(), {}
    for artifact in artifacts:
        tid, item = artifact.get("task_id"), artifact.get("item_id", "")
        require(isinstance(tid, str) and bool(tid), "Missing task ID")
        require(bool(re.fullmatch(re.escape(round_id) + r"__item[0-9]{3,}", item)),
                "Use neutral, stable, new-round item IDs")
        require(item not in seen, "Duplicate item ID")
        seen.add(item)
        require(artifact.get("configuration_id") in configurations, "Unknown configuration ID")
        pair = (tid, artifact["configuration_id"])
        require(pair not in pairs, "Duplicate task/configuration cell")
        pairs.add(pair)
        description = artifact.get("task_description", "")
        require(isinstance(description, str) and bool(description.strip()), "Missing task description")
        slug = re.sub(r"[^a-z0-9]+", "_", description.lower()).strip("_")[:80]
        require(bool(slug), "Task description needs a readable name")
        py, py_path = checked_file(artifact["python"], cohort_path.parent)
        gold, gold_path = checked_file(artifact["gold"], cohort_path.parent)
        candidate, candidate_path = checked_file(artifact["candidate"], cohort_path.parent)
        status = artifact["candidate"].get("status")
        require(status in ("nonempty", "empty"), "Candidate status must be nonempty or empty")
        require((status == "empty") == (len(candidate) == 0), "Candidate status contradicts bytes")
        require(bool(py) and bool(gold), "Python and reference must be nonempty")
        task = tasks.setdefault(tid, {"description": description, "slug": slug,
                                     "python": py, "gold": gold, "items": []})
        require((task["description"], task["python"], task["gold"]) == (description, py, gold),
                "One task has inconsistent source/reference/description")
        task["items"].append(artifact)
        loaded[item] = {"data": candidate, "source_paths": {
            "python": py_path, "gold": gold_path, "candidate": candidate_path}}

    selected = set(tasks) if task_ids is None else set(task_ids)
    require(bool(selected) and selected <= set(tasks), "Unknown or empty assigned task subset")
    require(task_ids is None or len(selected) == len(task_ids), "Duplicate assigned task ID")
    ordered_tasks = sorted(tasks, key=lambda tid: permutation_key(seed, "task", tid))
    members, response_rows, joins = {}, [], []
    for tid in ordered_tasks:
        if tid not in selected:
            continue
        task = tasks[tid]
        folder = layout[task["items"][0]["item_id"]]["task_folder"]
        members[f"{folder}/python_source/source.py"] = task["python"]
        members[f"{folder}/gold_lean/reference.lean"] = task["gold"]
        ordered_items = sorted(task["items"], key=lambda a: permutation_key(seed, "candidate", a["item_id"]))
        for artifact in ordered_items:
            item = artifact["item_id"]
            candidate_name = layout[item]["candidate_file"]
            members[candidate_name] = loaded[item]["data"]
            response_rows.append(dict(zip(COLUMNS[:5], [rater_name, rater_id, item, folder, candidate_name])))
            hashes = {k: artifact[k]["sha256"] for k in ("python", "gold", "candidate")}
            content_key = digest(json.dumps({"task_id": tid, **hashes}, sort_keys=True).encode())
            joins.append({"round_id": round_id, "rater_id": rater_id, "item_id": item,
                          "task_id": tid, "task_folder": folder, "candidate_file": candidate_name,
                          "configuration_id": artifact["configuration_id"],
                          "candidate_status": artifact["candidate"]["status"],
                          "hashes": hashes, "source_paths": loaded[item]["source_paths"],
                          "payload_content_key": content_key,
                          "observation_key": [round_id, rater_id, item],
                          "provenance": artifact.get("provenance", {})})

    if row_order is not None:
        # Per-rater Sheet row order only; files, labels and joins are unchanged.
        by_row = {row["item_id"]: row for row in response_rows}
        require(len(row_order) == len(by_row) and set(row_order) == set(by_row),
                "Row order must list each assigned item exactly once")
        response_rows = [by_row[item] for item in row_order]
    members["START_HERE.md"] = start_here(rater_name, sheet_url, len(selected), len(joins),
                                           any(j["candidate_status"] == "empty" for j in joins),
                                           bool(cohort.get("excluded_item_ids")))
    sheet = io.StringIO(newline="")
    writer = csv.DictWriter(sheet, fieldnames=COLUMNS, lineterminator="\n")
    writer.writeheader()
    writer.writerows(response_rows)
    sheet_table = sheet.getvalue().encode()  # coordinator-only: the exact table each live Sheet must match
    # Refuse known identity leaks; never redact or rewrite scientific input bytes.
    labels = "\n".join(members) + "\n" + sheet.getvalue()
    attribution = re.compile(r"\b(?:Claude|Gemini|GPT|OpenAI|Anthropic|Grok|Kimi|Codex|Terminus)\b", re.I)
    pi_attribution = re.compile(r"\b(?:generated|written|created|produced|authored)\s+by\s+Pi\b", re.I)
    require(not attribution.search(labels) and not pi_attribution.search(labels),
            "Participant labels contain a recognizable solver identity")
    for item, content in loaded.items():
        text = content["data"].decode("utf-8", errors="replace")
        require(not attribution.search(text) and not pi_attribution.search(text),
                f"Candidate {item} contains a recognizable solver identity; preserve bytes and resolve blinding before release")
    for config_id, config in configurations.items():
        tokens = [config_id, config.get("model", ""), config.get("harness", ""),
                  *config.get("identity_tokens", [])]
        require(all(isinstance(token, str) for token in tokens), "Identity tokens must be strings")
        require(not any(len(token) >= 4 and token.lower() in labels.lower() for token in tokens),
                "A generated participant label exposes a configuration identity")
        require(not any(len(token) >= 4 and token.lower().encode() in data.lower()
                        for token in tokens for data in members.values()),
                "Participant payload contains a known configuration identity; resolve without rewriting candidate bytes")
    member_sha256 = {name: digest(data) for name, data in sorted(members.items())}  # kept outside the zip
    archive_name = f"rating_packet_{round_id}_{rater_id}.zip"
    output_dir.mkdir(parents=True, exist_ok=False)
    packet_dir = output_dir / "rating_task_packet"
    for name, data in sorted(members.items()):
        destination = packet_dir / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(data)
    archive_path = output_dir / archive_name
    sheet_table_path = output_dir / "SHEET_TABLE.csv"
    sheet_table_path.write_bytes(sheet_table)
    with ZipFile(archive_path, "x", compression=ZIP_DEFLATED, compresslevel=9) as archive:
        for name, data in sorted(members.items()):
            info = ZipInfo(name, date_time=(1980, 1, 1, 0, 0, 0))
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            info.compress_type = ZIP_DEFLATED
            archive.writestr(info, data, compress_type=ZIP_DEFLATED, compresslevel=9)
    with ZipFile(archive_path) as archive:
        require(set(archive.namelist()) == set(members), "Archive member mismatch")
        for name, data in members.items():
            require(archive.read(name) == data and (packet_dir / name).read_bytes() == data,
                    "Packaged bytes changed")
    receipt = {
        "schema_version": 1, "status": "BUILT_AWAITING_SHEET_READBACK", "release_ready": False, "round_id": round_id,
        "cohort_path": str(cohort_path), "cohort_sha256": digest(raw), "shuffle_seed": seed,
        "rater_name": rater_name, "rater_id": rater_id, "sheet_url": sheet_url,
        "task_count": len(selected), "artifact_count": len(joins),
        "row_order": row_order,
        "empty_artifact_count": sum(j["candidate_status"] == "empty" for j in joins),
        "packet_directory": str(packet_dir), "archive_path": str(archive_path),
        "archive_sha256": digest(archive_path.read_bytes()),
        "member_sha256": member_sha256,
        "sheet_table_path": str(sheet_table_path), "sheet_table_sha256": digest(sheet_table),
        "form_schema_version": schema["version"], "form_schema_sha256": digest(schema_bytes),
        "linked_rubric_url": RUBRIC_URL, "linked_rubric_sha256": digest(rubric),
        "configurations": configurations, "artifact_joins": joins,
        "deduplication": "Use observation_key for repeated exports/subset copies; preserve provenance for historical joins. Packet copies are not new ratings.",
        "identity_scope": "Coordinator-only receipt. Labels are neutral and known model/harness/identity tokens are checked. Scientific bytes are unchanged; literal-token checks do not establish absence of every indirect authorship cue.",
    }
    (output_dir / "ASSEMBLY_RECEIPT.json").write_text(json.dumps(receipt, indent=2) + "\n")
    return receipt


def verify_sheet_readback(build_dir: Path, readback_path: Path) -> dict:
    """Gate release on exact Sheet table values, padding only omitted blank cells.

    Readback JSON: {sheet_url: str, range: str, values: [[cell,...],...]}. The
    coordinator obtains this from a fresh Sheet read, after updating its rows.
    No network or Sheet mutation occurs here; a mismatch marks the build held.
    """
    build_dir, readback_path = build_dir.resolve(), readback_path.resolve()
    receipt_path = build_dir / "ASSEMBLY_RECEIPT.json"
    receipt = json.loads(receipt_path.read_text())
    data = readback_path.read_bytes()
    readback = json.loads(data)
    archive_path = Path(receipt["archive_path"])
    require(digest(archive_path.read_bytes()) == receipt["archive_sha256"], "Built archive changed")
    csv_bytes = Path(receipt["sheet_table_path"]).read_bytes()
    require(digest(csv_bytes) == receipt["sheet_table_sha256"], "Sheet table changed since the build")
    expected = list(csv.reader(io.StringIO(csv_bytes.decode())))
    require(expected and expected[0] == COLUMNS, "Built CSV schema mismatch")
    values = readback.get("values")
    valid_rows = isinstance(values, list) and all(isinstance(row, list) and len(row) <= len(COLUMNS) for row in values)
    observed = ([[str(value) if value is not None else "" for value in row] + [""] * (len(COLUMNS) - len(row))
                 for row in values] if valid_rows else [])
    equal = (valid_rows and readback.get("sheet_url") == receipt["sheet_url"]
             and isinstance(readback.get("range"), str) and bool(readback["range"]) and observed == expected)
    check = {"status": "MATCH" if equal else "MISMATCH", "sheet_csv_equal": equal,
             "sheet_url": receipt["sheet_url"], "range": readback.get("range"),
             "source_readback": {"path": str(readback_path), "sha256": digest(data)},
             "archive_sha256": receipt["archive_sha256"], "sheet_table_sha256": digest(csv_bytes),
             "expected_table_rows": len(expected), "observed_table_rows": len(observed),
             "normalization": "Only absent trailing cells within each returned row are padded as empty strings. No row dropping, trimming, case changes or reordered columns."}
    check_path = build_dir / f"SHEET_MATCH_{digest(data)[:16]}.json"
    encoded = (json.dumps(check, indent=2) + "\n").encode()
    require(not check_path.exists() or check_path.read_bytes() == encoded, "Refusing to overwrite Sheet verification evidence")
    if not check_path.exists():
        with check_path.open("xb") as handle:
            handle.write(encoded)
    receipt.update(release_ready=equal,
                   status="BUILT_SHEET_MATCHED_NOT_SENT" if equal else "HELD_SHEET_MISMATCH",
                   sheet_verification={"path": str(check_path), "sha256": digest(encoded), "sheet_csv_equal": equal})
    temporary = receipt_path.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(receipt, indent=2) + "\n")
    temporary.replace(receipt_path)
    require(equal, "Live Sheet readback differs from the build's Sheet table; release is held")
    return check


def table_digest(rows: list[list[str]]) -> str:
    """Digest of an exact table: compact JSON of rows padded to the form width."""
    padded = [[str(v) for v in row] + [""] * (len(COLUMNS) - len(row)) for row in rows]
    return digest(json.dumps(padded, separators=(",", ":"), ensure_ascii=False).encode())


def verify_sheet_digest(build_dir: Path, observed_digest: str, observed_rows: int, source: str) -> dict:
    """Gate release on a digest of the live Sheet table computed where it was read.

    Use when the live table cannot be saved locally (for example it was read in the
    owner's signed-in browser). The digest must equal table_digest of the build's Sheet table.
    """
    build_dir = build_dir.resolve()
    receipt_path = build_dir / "ASSEMBLY_RECEIPT.json"
    receipt = json.loads(receipt_path.read_text())
    archive_path = Path(receipt["archive_path"])
    require(digest(archive_path.read_bytes()) == receipt["archive_sha256"], "Built archive changed")
    csv_bytes = Path(receipt["sheet_table_path"]).read_bytes()
    require(digest(csv_bytes) == receipt["sheet_table_sha256"], "Sheet table changed since the build")
    expected = list(csv.reader(io.StringIO(csv_bytes.decode())))
    require(expected and expected[0] == COLUMNS, "Built CSV schema mismatch")
    equal = observed_digest == table_digest(expected) and observed_rows == len(expected)
    check = {"status": "MATCH" if equal else "MISMATCH", "sheet_csv_equal": equal,
             "method": "table digest computed at the live read; no local readback file",
             "source": source, "sheet_url": receipt["sheet_url"],
             "expected_table_digest": table_digest(expected), "observed_table_digest": observed_digest,
             "expected_table_rows": len(expected), "observed_table_rows": observed_rows,
             "archive_sha256": receipt["archive_sha256"], "sheet_table_sha256": digest(csv_bytes)}
    encoded = (json.dumps(check, indent=2) + "\n").encode()
    (build_dir / f"SHEET_DIGEST_MATCH_{observed_digest[:16]}.json").write_bytes(encoded)
    receipt.update(release_ready=equal,
                   status="BUILT_SHEET_MATCHED_NOT_SENT" if equal else "HELD_SHEET_MISMATCH",
                   sheet_verification={"sha256": digest(encoded), "sheet_csv_equal": equal, "method": check["method"]})
    temporary = receipt_path.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(receipt, indent=2) + "\n")
    temporary.replace(receipt_path)
    require(equal, "Live Sheet digest differs from the build's Sheet table; release is held")
    return check


def main() -> None:
    if len(sys.argv) > 1 and sys.argv[1] == "verify-sheet":
        parser = argparse.ArgumentParser(description="Verify exact live-Sheet readback against a built packet CSV")
        parser.add_argument("--build-dir", required=True, type=Path)
        parser.add_argument("--sheet-readback", required=True, type=Path)
        args = parser.parse_args(sys.argv[2:])
        print(json.dumps(verify_sheet_readback(args.build_dir, args.sheet_readback), indent=2))
        return
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cohort", required=True, type=Path)
    parser.add_argument("--output-dir", required=True, type=Path, help="New private build directory; must not exist")
    parser.add_argument("--rater-name", required=True)
    parser.add_argument("--rater-id", required=True)
    parser.add_argument("--sheet-url", required=True)
    parser.add_argument("--tasks", nargs="+", help="Assigned task IDs; omit for the full cohort")
    parser.add_argument("--row-order-json", type=Path, help="Optional JSON list of item_ids specifying the Sheet row order")
    args = parser.parse_args()
    row_order = json.loads(args.row_order_json.read_text()) if args.row_order_json else None
    receipt = build_packet(args.cohort, args.output_dir, rater_name=args.rater_name,
                           rater_id=args.rater_id, sheet_url=args.sheet_url, task_ids=args.tasks,
                           row_order=row_order)
    print(json.dumps({key: receipt[key] for key in
                      ("status", "task_count", "artifact_count", "empty_artifact_count", "archive_path", "archive_sha256")}, indent=2))


if __name__ == "__main__":
    main()
