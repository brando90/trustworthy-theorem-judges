"""Freeze the complete 25-task x 3-agent cohort (75 files) for the full-team round.

Starts from the frozen 54-file ratable cohort and fills the 21 open cells with
existing, hash-verified files from the sealed set N file of record (earlier
Terminus 2 runs). No model is run, no file is edited and no score is read.

- 6 planned Claude Code cells that ended at the response cap are filled with the
  same model's Terminus 2 file (a recorded configuration substitution).
- 15 tasks without a Grok file get the Grok file of record as a new item
  (item086..item100, file label agent_4), beside the planned files.

The resulting item IDs and file names are asserted against the rows already in
the live 75-row rating Sheets, so existing Sheets stay valid.
"""

from __future__ import annotations

import hashlib
import json
import zipfile
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[5]
PREP = REPO / "research_artifacts/09_human_rating_collection/preparation_11-09-2026"
NATIVE = PREP / "native_harness_packet_11-11-2026"
OUT = PREP / "full_team_11-14-2026"
SEALED = OUT / "sealed"
OLD_PREFIX = "/Users/brandomiranda/trustworthy-theorem-judges/private/"
ROUND = "native-heavy-11-11-2026"

# The 21 added rows exactly as read from the live 75-row Sheet on 11-14-2026.
LIVE_ADDED_ROWS = {
    "item047": "task_01_heap_sort/agent_lean/agent_4.lean",
    "item035": "task_02_edit_distance/agent_lean/agent_1.lean",
    "item052": "task_08_base32_encoding/agent_lean/agent_1.lean",
    "item004": "task_15_prime_fibonacci_search/agent_lean/agent_1.lean",
    "item033": "task_17_heapsort_algorithm/agent_lean/agent_4.lean",
    "item019": "task_18_topological_sorting/agent_lean/agent_2.lean",
    "item086": "task_04_integer_string_sequence/agent_lean/agent_4.lean",
    "item087": "task_05_factorial/agent_lean/agent_4.lean",
    "item088": "task_06_counting_sort/agent_lean/agent_4.lean",
    "item089": "task_07_transport_layer_security_downgrade/agent_lean/agent_4.lean",
    "item090": "task_09_sum_of_digits/agent_lean/agent_4.lean",
    "item091": "task_10_lower_median/agent_lean/agent_4.lean",
    "item092": "task_11_html_escaping/agent_lean/agent_4.lean",
    "item093": "task_14_statistical_quantiles/agent_lean/agent_4.lean",
    "item094": "task_15_prime_fibonacci_search/agent_lean/agent_4.lean",
    "item095": "task_16_certificate_hostname/agent_lean/agent_4.lean",
    "item096": "task_19_string_prefixes/agent_lean/agent_4.lean",
    "item097": "task_21_tor_hidden_service/agent_lean/agent_4.lean",
    "item098": "task_23_duplicate_characters/agent_lean/agent_4.lean",
    "item099": "task_24_trusted_platform_module_hash_safe/agent_lean/agent_4.lean",
    "item100": "task_25_maximum_list_element/agent_lean/agent_4.lean",
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def find_by_hash(wanted: dict[str, tuple[str, str]]) -> dict[str, bytes]:
    """Locate file-of-record bytes locally (loose files, then packet archives); the hash is the only authority."""
    found: dict[str, bytes] = {}
    sources: dict[str, str] = {}
    roots = [PREP, Path.home() / "veribench/experiments"]
    for root in roots:
        for path in sorted(root.rglob("*.lean")):
            if SEALED in path.parents or ".lake" in path.parts:
                continue
            data = path.read_bytes()
            if sha(data) in wanted and sha(data) not in found:
                found[sha(data)], sources[sha(data)] = data, str(path)
        if set(found) == set(wanted):
            break
        for archive_path in sorted(root.rglob("*.zip")):
            if SEALED in archive_path.parents:
                continue
            try:
                with zipfile.ZipFile(archive_path) as archive:
                    for name in archive.namelist():
                        if name.endswith(".lean"):
                            data = archive.read(name)
                            if sha(data) in wanted and sha(data) not in found:
                                found[sha(data)], sources[sha(data)] = data, f"{archive_path}::{name}"
            except zipfile.BadZipFile:
                continue
        if set(found) == set(wanted):
            break
    find_by_hash.sources = sources
    return found


def main() -> None:
    cohort_path = NATIVE / "finalization/RATABLE_COHORT.json"
    cohort = json.loads(cohort_path.read_text())
    planned_path = NATIVE / "PLANNED_COHORT_VALID_ENV_V2.json"
    planned = json.loads(planned_path.read_text())
    assert sha(planned_path.read_bytes()) == cohort["planned_cohort"]["sha256"]
    record_path = SEALED / "setN_file_of_record_v3.json"
    record = json.loads(record_path.read_text())
    of_record = {system: {row["task_id"]: row for row in rows} for system, rows in record["systems"].items()}

    layout = cohort["display_layout"]
    planned_by_item = {a["item_id"]: a for a in planned["artifacts"]}
    tasks = sorted({a["task_id"] for a in cohort["artifacts"]})
    assert len(tasks) == 25
    present = {(a["task_id"], a["configuration_id"]) for a in cohort["artifacts"]}
    task_template = {a["task_id"]: a for a in cohort["artifacts"] if a["configuration_id"] == "historical_codex_astra"}
    folder = {a["task_id"]: layout[a["item_id"]]["task_folder"] for a in cohort["artifacts"]}

    need: list[dict] = []
    # (1) Claude Code cells with no file: same model, Terminus 2 file of record.
    for item_id, a in planned_by_item.items():
        if a["configuration_id"] == "native_claude_fable" and (a["task_id"], "native_claude_fable") not in present:
            need.append({"item_id": item_id, "task_id": a["task_id"], "system": "t2_fable51",
                         "configuration_id": "historical_terminus_fable",
                         "candidate_file": layout[item_id]["candidate_file"], "kind": "substitution"})
    assert len(need) == 6, len(need)
    # (2) Tasks without a Grok file: new items after the planned 85, label agent_4.
    no_grok = sorted((t for t in tasks if (t, "historical_terminus_grok") not in present), key=lambda t: folder[t])
    assert len(no_grok) == 15, len(no_grok)
    for number, task_id in enumerate(no_grok, 86):
        need.append({"item_id": f"{ROUND}__item{number:03d}", "task_id": task_id, "system": "t2_grok47",
                     "configuration_id": "historical_terminus_grok",
                     "candidate_file": f"{folder[task_id]}/agent_lean/agent_4.lean", "kind": "addition"})
    observed = {n["item_id"].split("__")[1]: n["candidate_file"] for n in need}
    assert observed == LIVE_ADDED_ROWS, "Derived cells differ from the rows in the live Sheets"

    wanted = {of_record[n["system"]][n["task_id"]]["file_sha256"]: (n["system"], n["task_id"]) for n in need}
    assert len(wanted) == 21
    found = find_by_hash(wanted)
    assert set(found) == set(wanted), "A file of record is not available locally"

    artifacts = [json.loads(json.dumps(a)) for a in cohort["artifacts"]]
    additions, substitutions = {}, {}
    for n in need:
        row = of_record[n["system"]][n["task_id"]]
        data = found[row["file_sha256"]]
        assert sha(data) == row["file_sha256"] and len(data) == row["file_bytes"] and data
        destination = SEALED / "candidates" / n["configuration_id"] / n["task_id"] / "candidate.lean"
        destination.parent.mkdir(parents=True, exist_ok=True)
        if not destination.exists():
            destination.write_bytes(data)
        assert sha(destination.read_bytes()) == row["file_sha256"]
        base = task_template[n["task_id"]]
        artifacts.append({
            "task_id": n["task_id"], "task_description": base["task_description"], "item_id": n["item_id"],
            "configuration_id": n["configuration_id"], "python": base["python"], "gold": base["gold"],
            "candidate": {"path": str(destination), "sha256": row["file_sha256"], "status": "nonempty"},
            "provenance": {"source": "sealed set N file of record v3", "system": n["system"],
                           "file_of_record": row, "local_copy_found_at": find_by_hash.sources[row["file_sha256"]],
                           "file_of_record_sha256": sha(record_path.read_bytes()),
                           "full_grid_fill": n["kind"]},
        })
        if n["kind"] == "addition":
            additions[n["item_id"]] = {"task_folder": folder[n["task_id"]], "candidate_file": n["candidate_file"]}
        else:
            substitutions[n["item_id"]] = {
                "planned_configuration_id": "native_claude_fable",
                "actual_configuration_id": "historical_terminus_fable",
                "reason": "The planned Claude Code attempt ended at the declared response cap with no file; "
                          "the same model's earlier Terminus 2 file of record fills the cell. Harness differs.",
            }

    per_task = {}
    for a in artifacts:
        per_task.setdefault(a["task_id"], set()).add(a["configuration_id"])
    for task_id, configs in per_task.items():
        assert "historical_codex_astra" in configs and "historical_terminus_grok" in configs
        assert len(configs) == 3 and configs & {"native_claude_fable", "historical_terminus_fable"}, task_id

    configurations = dict(cohort["configurations"])
    configurations["historical_terminus_grok"] = {
        **configurations["historical_terminus_grok"], "expected_artifacts": 25,
        "full_grid_note": "10 files were in the 54-file cohort; 15 more come from the same file of record."}
    configurations["historical_terminus_fable"] = {
        "harness": "Terminus 2", "model": "claude-fable-5-1", "effort": "xhigh", "instruction_version": 7,
        "expected_artifacts": 6, "cohort": "historical",
        "source_manifest": {"path": str(record_path), "sha256": sha(record_path.read_bytes())},
        "condition_note": "Effort and instruction version are those recorded for the set N Terminus 2 round "
                          "(same round as the Grok files); not re-derived here.",
    }
    filled = {n["item_id"] for n in need}
    full = {**cohort,
            "status": "FINAL_RATABLE_SUBSET", "buildable": True, "expected_artifacts": 75,
            "configurations": configurations, "artifacts": artifacts,
            "layout_additions": additions, "configuration_substitutions": substitutions,
            "excluded_item_ids": [i for i in cohort["excluded_item_ids"] if i not in filled],
            "actual_counts_by_configuration": {
                "historical_codex_astra": 25, "native_claude_fable": 19,
                "historical_terminus_fable": 6, "historical_terminus_grok": 25},
            "full_grid_amendment": {
                "recorded": "11-14-2026", "parent_cohort": {"path": str(cohort_path), "sha256": sha(cohort_path.read_bytes())},
                "rule": "Every task has one file from each of three agents: GPT-6 Astra (Codex), "
                        "Claude Fable 5.1 (Claude Code where a file exists, else Terminus 2) and Grok 4.7 (Terminus 2). "
                        "Added files are existing files of record chosen by cell, never by content or score.",
                "caveat": "Instruction versions differ across agents (5, 8, 7); harness differs for 6 Fable cells. "
                          "Model comparisons from this round are confounded with prompt version and harness."},
            }
    text = json.dumps(full, indent=1).replace(OLD_PREFIX + "09_human_rating_collection", str(PREP.parent))
    full_check = json.loads(text)
    # python/gold records must stay byte-identical to the planned inventory (path strings included).
    for a in full_check["artifacts"]:
        if a["item_id"] in planned_by_item:
            a["python"], a["gold"] = planned_by_item[a["item_id"]]["python"], planned_by_item[a["item_id"]]["gold"]
        else:
            a["python"], a["gold"] = task_template[a["task_id"]]["python"], task_template[a["task_id"]]["gold"]
    full_check["planned_cohort"] = cohort["planned_cohort"]
    full_check["display_layout"] = cohort["display_layout"]
    target = SEALED / "FULL_GRID_COHORT_75.json"
    target.write_text(json.dumps(full_check, indent=1) + "\n")
    commitment = {"round_id": ROUND, "cohort_file": "sealed/FULL_GRID_COHORT_75.json",
                  "cohort_sha256": sha(target.read_bytes()), "artifacts": 75, "tasks": 25,
                  "agents_per_task": 3, "added_from_file_of_record": 21,
                  "file_of_record_sha256": sha(record_path.read_bytes()),
                  "candidate_sha256_by_item": {a["item_id"]: a["candidate"]["sha256"] for a in full_check["artifacts"]},
                  "note": "Public commitment only. The item-to-agent key stays in sealed/ while raters score."}
    (OUT / "COHORT_COMMITMENT.json").write_text(json.dumps(commitment, indent=1, sort_keys=True) + "\n")
    print(json.dumps({k: commitment[k] for k in ("cohort_sha256", "artifacts", "tasks", "added_from_file_of_record")}))


if __name__ == "__main__":
    sys.exit(main())
