"""Freeze the 25-task x 4-agent cohort (100 files): add the Google column.

Starts from the 75-file cohort of record (25 tasks x GPT-6 Astra, Claude Fable 5.1,
Grok 4.7) and fills the 25 planned Google cells. The planned Google run (Pi with
Gemini 3.8 Flash) produced no file for any task, so its planned file names were
skipped. Google's frontier model has an existing, hash-verified Terminus 2 file for
every task in the sealed set N file of record (VeriBench experiment 107, system
t2_gemini_frontier; Vals approved its files for the rating packet on 10-07-2026).
Its model name stays out of Git, as in VeriBench; the selector is in experiment
107's private/INTERNAL_MODELS.json.

No model is run, no file is edited and no score is read. Item IDs and file names
come from the frozen planned layout, so the 75 existing items keep their IDs and
names and every task ends with agent_1..agent_4 (no skipped numbers).
"""

from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import build_full_grid_cohort as grid  # noqa: E402  (reuses find_by_hash and the paths)

PARENT = grid.SEALED / "RATABLE_COHORT_75_V2.json"
PARENT_SHA256 = "3f63a713b664cb2c31eaebd4785f910d373b66243efccc8484f1350bd687cff1"
TARGET = grid.SEALED / "RATABLE_COHORT_100_FOUR_AGENTS.json"
COMMITMENT = grid.OUT / "COHORT_100_COMMITMENT.json"
PLANNED_GOOGLE = "pi_gemini_flash"
GOOGLE = "historical_terminus_gemini"


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    parent_bytes = PARENT.read_bytes()
    assert sha(parent_bytes) == PARENT_SHA256, "The 75-file cohort of record changed"
    cohort = json.loads(parent_bytes)
    planned_path = grid.NATIVE / "PLANNED_COHORT_VALID_ENV_V2.json"
    planned = json.loads(planned_path.read_text())
    assert sha(planned_path.read_bytes()) == cohort["planned_cohort"]["sha256"]
    record_path = grid.SEALED / "setN_file_of_record_v3.json"
    record = json.loads(record_path.read_text())
    google_rows = {row["task_id"]: row for row in record["systems"]["t2_gemini_frontier"]}

    present = {a["item_id"] for a in cohort["artifacts"]}
    cells = [a for a in planned["artifacts"] if a["configuration_id"] == PLANNED_GOOGLE]
    assert len(cells) == 25 and not present & {c["item_id"] for c in cells}
    assert {c["task_id"] for c in cells} == set(google_rows) == {a["task_id"] for a in cohort["artifacts"]}
    assert all(google_rows[t]["status"] == "measured" and google_rows[t]["file_bytes"] > 0 for t in google_rows)

    wanted = {google_rows[c["task_id"]]["file_sha256"]: ("t2_gemini_frontier", c["task_id"]) for c in cells}
    found = grid.find_by_hash(wanted)
    assert set(found) == set(wanted), "A Google file of record is not available locally"

    artifacts = [json.loads(json.dumps(a)) for a in cohort["artifacts"]]
    substitutions = dict(cohort["configuration_substitutions"])
    for cell in sorted(cells, key=lambda c: c["item_id"]):
        row = google_rows[cell["task_id"]]
        data = found[row["file_sha256"]]
        assert sha(data) == row["file_sha256"] and len(data) == row["file_bytes"]
        destination = grid.SEALED / "candidates" / GOOGLE / cell["task_id"] / "candidate.lean"
        destination.parent.mkdir(parents=True, exist_ok=True)
        if not destination.exists():
            destination.write_bytes(data)
        assert sha(destination.read_bytes()) == row["file_sha256"]
        artifacts.append({
            "task_id": cell["task_id"], "task_description": cell["task_description"], "item_id": cell["item_id"],
            "configuration_id": GOOGLE, "python": cell["python"], "gold": cell["gold"],
            "candidate": {"path": str(destination), "sha256": row["file_sha256"], "status": "nonempty"},
            "provenance": {"source": "sealed set N file of record v3", "system": "t2_gemini_frontier",
                           "file_of_record": row, "local_copy_found_at": grid.find_by_hash.sources[row["file_sha256"]],
                           "file_of_record_sha256": sha(record_path.read_bytes()),
                           "full_grid_fill": "substitution"},
        })
        substitutions[cell["item_id"]] = {
            "planned_configuration_id": PLANNED_GOOGLE, "actual_configuration_id": GOOGLE,
            "reason": "The planned Pi + Gemini 3.8 Flash run produced no file for any task (0 of 25); Google's "
                      "frontier model's existing Terminus 2 file of record (set N, VeriBench experiment 107) fills "
                      "the planned Google cell. Harness, model and instruction version differ from the plan.",
        }

    per_task: dict[str, set[str]] = {}
    for a in artifacts:
        per_task.setdefault(a["task_id"], set()).add(a["configuration_id"])
    for task_id, configs in per_task.items():
        assert len(configs) == 4 and {"historical_codex_astra", "historical_terminus_grok", GOOGLE} <= configs, task_id
        assert configs & {"native_claude_fable", "historical_terminus_fable"}, task_id

    configurations = dict(cohort["configurations"])
    configurations[GOOGLE] = {
        "harness": "Terminus 2", "model": "t2_gemini_frontier",
        "model_note": "Google's frontier model through Vals early access; name kept out of Git as in VeriBench "
                      "experiment 107 (selector in its private/INTERNAL_MODELS.json).",
        "effort": "high", "instruction_version": 7, "expected_artifacts": 25, "cohort": "historical",
        "source_manifest": {"path": str(record_path), "sha256": sha(record_path.read_bytes())},
        "condition_note": "Effort and instruction version are those recorded for the set N Terminus 2 round "
                          "(the same round as the Grok files); not re-derived here.",
    }
    flagged = sorted((cohort["display_layout"].get(a["item_id"]) or cohort["layout_additions"][a["item_id"]])
                     ["candidate_file"] for a in artifacts
                     if a.get("provenance", {}).get("file_of_record", {}).get("isolation_pass") is False)
    full = {**cohort,
            "status": "FINAL_RATABLE_SUBSET", "buildable": True, "expected_artifacts": 100,
            "configurations": configurations, "artifacts": artifacts,
            "configuration_substitutions": substitutions, "excluded_item_ids": [],
            "actual_counts_by_configuration": {
                "historical_codex_astra": 25, "native_claude_fable": 19, "historical_terminus_fable": 6,
                "historical_terminus_grok": 25, GOOGLE: 25},
            "four_agent_amendment": {
                "recorded": "11-16-2026", "requested_by": "Brando (chat, 11-16-2026: Google's model must be in the grid)",
                "parent_cohort": {"path": str(PARENT), "sha256": sha(parent_bytes)},
                "rule": "Every task has one file from each of four agents: GPT-6 Astra (Codex), Claude Fable 5.1 "
                        "(Claude Code where a file exists, else Terminus 2), Grok 4.7 (Terminus 2) and Google's "
                        "frontier model (Terminus 2). Added files are existing files of record chosen by cell, "
                        "never by content or score.",
                "caveat": "Instruction versions differ across agents (5, 8 or 7, 7, 7) and harnesses differ (Codex, "
                          "Claude Code or Terminus 2, Terminus 2, Terminus 2). Agent comparisons from this round are "
                          "confounded with prompt version and harness.",
                "isolation_flagged_files": flagged,
                "isolation_note": "VeriBench experiment 102 amendment C13: these files' isolation receipts show egress "
                                  "beyond the gateway was not blocked; they held no reference Lean and no tests and their "
                                  "transcripts contain no network commands. Included and flagged for a sensitivity analysis.",
                "prior_exposure_note": "Set N files (including these 25) were also in the earlier set N FormV5 packet; "
                                       "record each rater's prior exposure at analysis.",
            }}
    TARGET.write_text(json.dumps(full, indent=1) + "\n")
    commitment = {"round_id": cohort["round_id"], "cohort_file": "sealed/" + TARGET.name,
                  "cohort_sha256": sha(TARGET.read_bytes()), "parent_cohort_sha256": sha(parent_bytes),
                  "artifacts": 100, "tasks": 25, "agents_per_task": 4, "added_google_files": 25,
                  "file_of_record_sha256": sha(record_path.read_bytes()),
                  "candidate_sha256_by_item": {a["item_id"]: a["candidate"]["sha256"] for a in artifacts},
                  "note": "Public commitment only. The item-to-agent key stays in sealed/ while raters score."}
    COMMITMENT.write_text(json.dumps(commitment, indent=1, sort_keys=True) + "\n")
    print(json.dumps({k: commitment[k] for k in ("cohort_sha256", "artifacts", "tasks", "added_google_files")}
                     | {"isolation_flagged_files": flagged}))


if __name__ == "__main__":
    sys.exit(main())
