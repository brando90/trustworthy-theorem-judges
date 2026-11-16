"""Replace the 6 Terminus 2 Fable fallback items with pure native Claude Code V3 outputs.

Starts from sealed/RATABLE_COHORT_100_FOUR_AGENTS.json and swaps only the 6 items
where V2 native Claude Code hit its 16,384 single-response output cap, using verified
outputs from native_harness_packet_11-11-2026/claude_code_valid_v3/ produced under
CC_CONDITION_VALID_V3.json (max_response_tokens=64000).
"""

from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import build_full_grid_cohort as grid  # noqa: E402

PARENT = grid.SEALED / "RATABLE_COHORT_100_FOUR_AGENTS.json"
PARENT_SHA256 = "5a997b0168e3c13dc084c09bc8ae29bef8dad42d55ce2f981ff28f07f405587a"
TARGET = grid.SEALED / "RATABLE_COHORT_100_PURE_CC_V2.json"
COMMITMENT = grid.OUT / "COHORT_100_COMMITMENT.json"
COND_V3 = grid.NATIVE / "CC_CONDITION_VALID_V3.json"
OUT_V3 = grid.NATIVE / "claude_code_valid_v3"
SUMMARY_V3 = grid.NATIVE / "claude_code_readiness/CC_VALID_V3_SUMMARY.json"

SWAPPED_CFG_OLD = "historical_terminus_fable"
SWAPPED_CFG_NEW = "native_claude_fable_v3"


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    parent_bytes = PARENT.read_bytes()
    assert sha(parent_bytes) == PARENT_SHA256, "Unexpected RATABLE_COHORT_100_FOUR_AGENTS.json SHA-256"
    cohort = json.loads(parent_bytes)
    cond_v3 = json.loads(COND_V3.read_text())
    cond_v3_sha = sha(COND_V3.read_bytes())

    artifacts = [json.loads(json.dumps(a)) for a in cohort["artifacts"]]
    substitutions = dict(cohort["configuration_substitutions"])
    swapped = []

    for artifact in artifacts:
        if artifact["configuration_id"] != SWAPPED_CFG_OLD:
            continue
        task_id = artifact["task_id"]
        cand_path = OUT_V3 / task_id / "candidate.lean"
        rec_path = OUT_V3 / task_id / "receipt.json"
        assert cand_path.is_file() and rec_path.is_file(), f"Missing V3 output for {task_id}"
        receipt = json.loads(rec_path.read_text())
        assert receipt.get("status") == "TERMINAL" and receipt.get("candidate_captured") is True, task_id
        assert receipt.get("model_identity_verified") is True, task_id
        assert receipt.get("condition_sha256") == cond_v3_sha, task_id
        data = cand_path.read_bytes()
        assert len(data) > 0 and sha(data) == receipt["candidate_sha256"], task_id

        artifact["configuration_id"] = SWAPPED_CFG_NEW
        artifact["candidate"] = {
            "path": str(cand_path),
            "sha256": receipt["candidate_sha256"],
            "status": "nonempty",
        }
        artifact["provenance"] = {
            "source": "prospective native Claude Code V3 cap amendment",
            "condition": str(COND_V3),
            "condition_sha256": cond_v3_sha,
            "receipt": str(rec_path),
            "receipt_sha256": sha(rec_path.read_bytes()),
            "stop_reason": receipt["stop_reason"],
            "replaced_configuration_id": SWAPPED_CFG_OLD,
        }
        substitutions[artifact["item_id"]] = {
            "planned_configuration_id": "native_claude_fable",
            "actual_configuration_id": SWAPPED_CFG_NEW,
            "reason": (
                "Native Claude Code v8 hit 16384 single-response token cap in V2; generated with native "
                "Claude Code 2.1.322 (claude-fable-5-1, max, prompt v8) under CC_CONDITION_VALID_V3.json "
                "(max_response_tokens=64000)."
            ),
        }
        swapped.append(task_id)

    assert set(swapped) == set(cond_v3["task_order"]), (swapped, cond_v3["task_order"])
    per_task: dict[str, set[str]] = {}
    for a in artifacts:
        per_task.setdefault(a["task_id"], set()).add(a["configuration_id"])
    for tid, cfgs in per_task.items():
        assert len(cfgs) == 4, (tid, cfgs)
        assert {"historical_codex_astra", "historical_terminus_grok", "historical_terminus_gemini"} <= cfgs, tid
        assert cfgs & {"native_claude_fable", SWAPPED_CFG_NEW}, tid

    configurations = dict(cohort["configurations"])
    configurations.pop(SWAPPED_CFG_OLD, None)
    configurations[SWAPPED_CFG_NEW] = {
        "harness": "Claude Code",
        "model": cond_v3["model"],
        "effort": cond_v3["effort"],
        "cli_version": cond_v3["cli_version"],
        "instruction_version": 8,
        "max_response_tokens": cond_v3["max_response_tokens"],
        "expected_artifacts": len(swapped),
        "cohort": "prospective_v3_cap_amendment",
        "output_root": str(OUT_V3),
        "condition_snapshot": {"path": str(COND_V3), "sha256": cond_v3_sha},
        "summary_snapshot": str(SUMMARY_V3),
        "billing_route": cond_v3["billing_route"],
    }

    pure_cc = {
        **cohort,
        "status": "FINAL_RATABLE_SUBSET",
        "buildable": True,
        "expected_artifacts": 100,
        "configurations": configurations,
        "artifacts": artifacts,
        "configuration_substitutions": substitutions,
        "excluded_item_ids": [],
        "actual_counts_by_configuration": {
            "historical_codex_astra": 25,
            "native_claude_fable": 19,
            SWAPPED_CFG_NEW: 6,
            "historical_terminus_grok": 25,
            "historical_terminus_gemini": 25,
        },
        "pure_cc_amendment": {
            "recorded": "11-16-2026",
            "requested_by": "Brando (chat, 11-16-2026: make all 25 Anthropic files native Claude Code v8)",
            "parent_cohort": {"path": str(PARENT), "sha256": PARENT_SHA256},
            "condition_v3_sha256": cond_v3_sha,
            "replaced_tasks": sorted(swapped),
            "note": (
                "Replaces the 6 Terminus 2 v7 Fable fallbacks with native Claude Code 2.1.322 "
                "(claude-fable-5-1, max, prompt v8) generated under CC_CONDITION_VALID_V3.json "
                "(max_response_tokens=64000). All 25 Anthropic files are now native Claude Code v8."
            ),
        },
    }
    TARGET.write_text(json.dumps(pure_cc, indent=1) + "\n")

    commitment = {
        "round_id": cohort["round_id"],
        "cohort_file": "sealed/" + TARGET.name,
        "cohort_sha256": sha(TARGET.read_bytes()),
        "parent_cohort_sha256": PARENT_SHA256,
        "condition_v3_sha256": cond_v3_sha,
        "artifacts": 100,
        "tasks": 25,
        "agents_per_task": 4,
        "pure_native_claude_code_files": 25,
        "terminus_fable_fallbacks": 0,
        "added_google_files": 25,
        "file_of_record_sha256": cohort["four_agent_amendment"]["parent_cohort"]["sha256"],
        "candidate_sha256_by_item": {a["item_id"]: a["candidate"]["sha256"] for a in artifacts},
        "note": "Public commitment only. The item-to-agent key stays in sealed/ while raters score.",
    }
    COMMITMENT.write_text(json.dumps(commitment, indent=1, sort_keys=True) + "\n")
    print(json.dumps({
        "cohort_sha256": commitment["cohort_sha256"],
        "artifacts": commitment["artifacts"],
        "pure_native_claude_code_files": commitment["pure_native_claude_code_files"],
        "replaced": sorted(swapped),
    }))


if __name__ == "__main__":
    sys.exit(main())
