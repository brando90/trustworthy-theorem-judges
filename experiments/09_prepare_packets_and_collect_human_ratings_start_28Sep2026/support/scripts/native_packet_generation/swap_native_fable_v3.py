"""Make all 25 Claude Fable 5.1 files native Claude Code: swap in the 6 V3 recovery files.

On 11-11-2026, 6 planned Claude Code cells hit the declared 16,384-token single-response
cap (V2 condition) and returned no file; the 100-file cohort filled them with the same
model's earlier Terminus 2 files. Brando asked (11-16-2026) for all 25 Anthropic files to
come from native Claude Code. Those 6 cells were re-run once under condition amendment V3
(identical to V2 except max_response_tokens). This script verifies the 6 V3 receipts and
files and writes a new cohort in which the 6 items keep their item IDs and file names, so
every rater's Sheet rows are unchanged; only those 6 files' contents change.

Usage: swap_native_fable_v3.py <V3 output root containing <task_id>/receipt.json> <V3 condition JSON>
"""

from __future__ import annotations

import difflib
import hashlib
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import build_full_grid_cohort as grid  # noqa: E402
import build_packet as bp  # noqa: E402

PARENT = grid.SEALED / "RATABLE_COHORT_100_FOUR_AGENTS.json"
TARGET = grid.SEALED / "RATABLE_COHORT_100_FOUR_AGENTS_V2.json"
COMMITMENT = grid.OUT / "COHORT_100_V2_COMMITMENT.json"
V2_CONDITION = grid.NATIVE / "CC_CONDITION_VALID_V2.json"
NEW = "native_claude_fable_v3"


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def lean_brackets_ok(text: str) -> bool:
    """Single pass that skips nested /- -/ comments, -- comments, strings and char literals."""
    i, n, stack = 0, len(text), []
    pair = {")": "(", "]": "[", "}": "{"}
    while i < n:
        if text.startswith("/-", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if text.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif text.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            continue
        if text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
            continue
        c = text[i]
        if c == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
            continue
        if c == "'":
            j = text.find("'", i + 1, i + 12)
            body = text[i + 1:j] if j > 0 else ""
            if j > 0 and "\n" not in body and (len(body) == 1 or (body.startswith("\\") and len(body) <= 10)):
                i = j + 1
                continue
        if c in "([{":
            stack.append(c)
        elif c in ")]}":
            if not stack or stack[-1] != pair[c]:
                return False
            stack.pop()
        i += 1
    return not stack


def main() -> None:
    v3_root, v3_condition_path = Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve()
    parent_bytes = PARENT.read_bytes()
    cohort = json.loads(parent_bytes)
    v2, v3 = json.loads(V2_CONDITION.read_text()), json.loads(v3_condition_path.read_text())
    changed = sorted(k for k in set(v2) | set(v3) if v2.get(k) != v3.get(k))
    print("V2 -> V3 condition keys that differ:", changed)
    layout = {**cohort["display_layout"], **cohort["layout_additions"]}
    items = {i: s for i, s in cohort["configuration_substitutions"].items()
             if s["actual_configuration_id"] == "historical_terminus_fable"}
    assert len(items) == 6, items
    by_item = {a["item_id"]: a for a in cohort["artifacts"]}
    artifacts, replaced = [], {}
    for artifact in cohort["artifacts"]:
        item = artifact["item_id"]
        if item not in items:
            artifacts.append(artifact)
            continue
        task = artifact["task_id"]
        receipt_path = v3_root / task / "receipt.json"
        receipt = json.loads(receipt_path.read_text())
        candidate_path = v3_root / task / "candidate.lean"
        data = candidate_path.read_bytes()
        assert receipt["status"] == "TERMINAL" and receipt.get("candidate_captured") is True, (task, receipt.get("status"))
        assert receipt["candidate_sha256"] == sha(data) and receipt["candidate_bytes"] == len(data) > 0, task
        assert receipt.get("condition_sha256") == sha(v3_condition_path.read_bytes()), f"{task}: receipt not bound to the V3 condition"
        assert receipt.get("model_identity_verified") is True, f"{task}: model identity not verified"
        assert receipt["cli_version"].split()[0] == v2["cli_version"], task
        text = data.decode("utf-8", errors="replace")
        folder = layout[item]["task_folder"]
        gold = (grid.REPO / "experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026/rating_task_packet/"
                "main_rating_task" / folder / "gold_lean/reference.lean").read_text()
        theorems = len(re.findall(r"^\s*(?:@\[[^\]]*\]\s*)*(?:private |protected |noncomputable )*(?:theorem|lemma)\s",
                                  text, re.M))
        leak = re.findall(r"\b(Claude|Anthropic|Fable|GPT|OpenAI|Codex|Grok|xAI|Gemini|Google|Kimi|Terminus)\b", text, re.I)
        overlap = difflib.SequenceMatcher(None, [l.strip() for l in text.splitlines() if l.strip()],
                                          [l.strip() for l in gold.splitlines() if l.strip()], autojunk=False).ratio()
        assert theorems > 0 and not leak and lean_brackets_ok(text) and overlap < 0.8, (task, theorems, leak, overlap)
        destination = grid.SEALED / "candidates" / NEW / task / "candidate.lean"
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(data)
        new = json.loads(json.dumps(by_item[item]))
        new["configuration_id"] = NEW
        new["candidate"] = {"path": str(destination), "sha256": sha(data), "status": "nonempty"}
        new["provenance"] = {"source": "Claude Code V3 recovery run (11-16-2026)", "receipt_path": str(receipt_path),
                             "receipt_sha256": sha(receipt_path.read_bytes()), "stop_reason": receipt.get("stop_reason"),
                             "condition_path": str(v3_condition_path), "condition_sha256": sha(v3_condition_path.read_bytes()),
                             "replaced_terminus2_sha256": by_item[item]["candidate"]["sha256"],
                             "content_checks": {"theorems": theorems, "reference_line_overlap": round(overlap, 3)}}
        artifacts.append(new)
        replaced[item] = {"task_folder": folder, "candidate_file": layout[item]["candidate_file"],
                          "old_sha256": by_item[item]["candidate"]["sha256"], "new_sha256": sha(data),
                          "stop_reason": receipt.get("stop_reason"), "theorems": theorems}
    substitutions = dict(cohort["configuration_substitutions"])
    for item in items:
        substitutions[item] = {
            "planned_configuration_id": "native_claude_fable", "actual_configuration_id": NEW,
            "reason": "The V2 Claude Code attempt hit the declared 16,384-token single-response cap with no file; "
                      "the cell was re-run once under condition amendment V3 (only change: the response cap). "
                      "Harness, model, effort and prompt version match the other 19 Claude Code files."}
    configurations = {k: v for k, v in cohort["configurations"].items() if k != "historical_terminus_fable"}
    gemini = {k: v for k, v in configurations["historical_terminus_gemini"].items() if k != "model_note"}
    configurations["historical_terminus_gemini"] = {
        **gemini, "model": "google/gemini-4-argon", "model_label": "Gemini 4 Argon",
        "model_source": "VeriBench experiment 107 private/INTERNAL_MODELS.json and CONDITIONS_t2v2_full.json "
                        "(read 11-16-2026); named in Git per Brando, 11-16-2026"}
    configurations[NEW] = {**configurations["native_claude_fable"], "expected_artifacts": 6,
                           "condition_snapshot": {"path": str(v3_condition_path), "sha256": sha(v3_condition_path.read_bytes())},
                           "condition_change_from_v2": {k: [v2.get(k), v3.get(k)] for k in changed},
                           "finalization_note": "V3 recovery of the 6 cap-truncated V2 cells only."}
    full = {**cohort, "configurations": configurations, "artifacts": artifacts,
            "configuration_substitutions": substitutions,
            "actual_counts_by_configuration": {"historical_codex_astra": 25, "native_claude_fable": 19, NEW: 6,
                                               "historical_terminus_grok": 25, "historical_terminus_gemini": 25},
            "native_fable_v3_amendment": {
                "recorded": "11-16-2026", "requested_by": "Brando (chat, 11-16-2026: all Anthropic files native Claude Code)",
                "parent_cohort": {"path": str(PARENT), "sha256": sha(parent_bytes)}, "replaced_items": replaced,
                "note": "Item IDs and file names are unchanged, so Sheet rows are unchanged; only these 6 files' "
                        "contents differ from the 100-file packet of 11-16-2026 (first version)."}}
    full["four_agent_amendment"] = {**cohort["four_agent_amendment"], "caveat": (
        "Instruction versions differ across agents (5, 8, 7, 7) and harnesses differ (Codex, Claude Code, "
        "Terminus 2, Terminus 2). Agent comparisons from this round are confounded with prompt version and harness.")}
    TARGET.write_text(json.dumps(full, indent=1) + "\n")
    assert len(full["artifacts"]) == 100 and len({a["item_id"] for a in full["artifacts"]}) == 100
    commitment = {"round_id": cohort["round_id"], "cohort_file": "sealed/" + TARGET.name,
                  "cohort_sha256": sha(TARGET.read_bytes()), "parent_cohort_sha256": sha(parent_bytes),
                  "artifacts": 100, "tasks": 25, "agents_per_task": 4, "replaced_files": 6,
                  "candidate_sha256_by_item": {a["item_id"]: a["candidate"]["sha256"] for a in full["artifacts"]},
                  "note": "Public commitment only. The item-to-agent key stays in sealed/ while raters score."}
    COMMITMENT.write_text(json.dumps(commitment, indent=1, sort_keys=True) + "\n")
    print(json.dumps({"cohort_sha256": commitment["cohort_sha256"],
                      "replaced": {i: (r["candidate_file"], r["stop_reason"], r["theorems"]) for i, r in replaced.items()}}))


if __name__ == "__main__":
    sys.exit(main())
