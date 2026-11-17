"""Build the all-native 100-file cohort: every agent's files come from its vendor's own harness.

Brando, 11-16-2026: "Re-run natively". Starting from the 100-file cohort of record
(RATABLE_COHORT_100_FOUR_AGENTS.json), replace, keeping every item ID and file name (so Sheet rows
are unchanged and only these files' contents change):
- fable:  the 6 Claude Fable 5.1 Terminus 2 fallbacks -> Claude Code V3 reruns (claude_code_runner receipts)
- grok:   the 25 Grok 4.7 Terminus 2 files -> xAI Grok CLI (native_cli_runner receipts)
- gemini: the 25 Gemini 4 Argon Terminus 2 files -> Google Antigravity CLI (native_cli_runner receipts)
A group is applied only when every one of its cells has a verified file, so no agent mixes harnesses.
Per NATIVE_ATTEMPTS_AMENDMENT_11-16-2026.json, a cell without a usable attempt-1 file may use attempt 2 or 3
(identical frozen condition, folders <root>_attempt2/ and <root>_attempt3/); the first usable attempt wins.

Usage: build_native_cohort.py [--fable ROOT CONDITION] [--grok ROOT CONDITION] [--gemini ROOT CONDITION]
"""

from __future__ import annotations

import argparse
import difflib
import hashlib
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import build_full_grid_cohort as grid  # noqa: E402
from swap_native_fable_v3 import lean_brackets_ok  # noqa: E402

PARENT = grid.SEALED / "RATABLE_COHORT_100_FOUR_AGENTS.json"
PARENT_SHA256 = "5a997b0168e3c13dc084c09bc8ae29bef8dad42d55ce2f981ff28f07f405587a"
TARGET = grid.SEALED / "RATABLE_COHORT_100_NATIVE.json"
COMMITMENT = grid.OUT / "COHORT_100_NATIVE_COMMITMENT.json"
ATTEMPTS = grid.NATIVE / "NATIVE_ATTEMPTS_AMENDMENT_11-16-2026.json"
PACKET = grid.REPO / "experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026/rating_task_packet/main_rating_task"
LEAK = re.compile(r"\b(Claude|Anthropic|Fable|GPT|OpenAI|Codex|Grok|xAI|SpaceXAI|Gemini|Google|DeepMind|Antigravity|"
                  r"Argon|Kimi|Terminus)\b", re.I)
GROUPS = {
    "fable": {"old": "historical_terminus_fable", "new": "native_claude_fable_v3", "count": 6,
              "label": "Claude Fable 5.1 in Claude Code (V3 rerun: response cap raised)"},
    "grok": {"old": "historical_terminus_grok", "new": "native_grok_cli", "count": 25,
             "label": "Grok 4.7 in xAI's Grok CLI"},
    "gemini": {"old": "historical_terminus_gemini", "new": "native_antigravity_gemini", "count": 25,
               "label": "Gemini 4 Argon in Google's Antigravity CLI"},
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def norm(text: str) -> str:
    return re.sub(r"[^a-z0-9]", "", text.lower())


def check_file(task_folder: str, data: bytes) -> dict:
    """Same content screens as the 75/100-file rounds; raises on any failure."""
    text = data.decode("utf-8", errors="replace")
    gold = (PACKET / task_folder / "gold_lean/reference.lean").read_text()
    python = (PACKET / task_folder / "python_source/source.py").read_text()
    names = {n for n in re.findall(r"^\s*def\s+([A-Za-z_]\w*)", python, re.M) if n != "main" and len(norm(n)) >= 4}
    theorems = len(re.findall(r"^\s*(?:@\[[^\]]*\]\s*)*(?:private |protected |noncomputable )*(?:theorem|lemma)\s",
                              text, re.M))
    overlap = difflib.SequenceMatcher(None, [l.strip() for l in text.splitlines() if l.strip()],
                                      [l.strip() for l in gold.splitlines() if l.strip()], autojunk=False).ratio()
    leak = sorted(set(m.group(0) for m in LEAK.finditer(text)))
    problems = [p for p, bad in [("no theorem", theorems == 0), (f"names {leak}", bool(leak)),
                                 ("unbalanced brackets", not lean_brackets_ok(text)),
                                 (f"reference overlap {overlap:.2f}", overlap >= 0.8),
                                 ("never names the task function", bool(names) and not any(norm(n) in norm(text) for n in names))]
                if bad]
    assert not problems, (task_folder, problems)
    return {"theorems": theorems, "reference_line_overlap": round(overlap, 3), "bytes": len(data)}


def cell_receipt(root: Path, task_id: str, condition_path: Path, model: str) -> tuple[bytes, dict, Path]:
    receipt_path = root / task_id / "receipt.json"
    receipt = json.loads(receipt_path.read_text())
    assert receipt["status"] == "TERMINAL" and receipt.get("candidate_captured") is True, (task_id, receipt.get("status"),
                                                                                          receipt.get("stop_reason"))
    data = (root / task_id / "candidate.lean").read_bytes()
    assert receipt["candidate_sha256"] == sha(data) and receipt["candidate_bytes"] == len(data) > 0, task_id
    assert receipt.get("condition_sha256") == sha(condition_path.read_bytes()), f"{task_id}: not bound to this condition"
    # "<synthetic>" marks messages Claude Code writes itself (API errors, limit notices); every model that
    # answered must be the frozen one. The runner's own model_identity_verified flag is kept in provenance.
    real = set(receipt.get("actual_models", [])) - {"<synthetic>"}
    assert real and all(model in m for m in real), (task_id, receipt.get("actual_models"))
    return data, receipt, receipt_path


def attempt_roots(root: Path, last: int = 3) -> list[Path]:
    """NATIVE_ATTEMPTS_AMENDMENT_11-16-2026: attempt k > 1 of a cell lives in <root>_attempt<k>/."""
    return [root] + [root.with_name(f"{root.name}_attempt{k}") for k in range(2, last + 1)]


def amendment_decisions() -> tuple[set, set]:
    """Cells Brando approved for attempts 4-6, and cells he chose to keep on their Terminus 2 file."""
    amendment = json.loads(ATTEMPTS.read_text())
    extended = {(e["cell"]["group"], e["cell"]["task_id"]) for e in [amendment.get("grok_html_escape_extension")]
                if e and e.get("approved_by_brando")}
    keep = {(c["group"], c["task_id"]) for c in amendment.get("keep_terminus2_cells", []) if c.get("approved_by_brando")}
    return extended, keep


def first_usable_attempt(root: Path, task_id: str, task_folder: str, condition_path: Path, model: str,
                         extended: bool = False):
    """Attempts 1-3 ran one after another: the first usable one wins and a later one may exist only if every earlier
    one failed. For an approved extended cell, attempts 4-6 ran concurrently after 1-3 failed: the lowest-numbered
    usable one wins and the other concurrent attempts are recorded as unused."""
    roots = attempt_roots(root, 6 if extended else 3)
    stray = [r for r in attempt_roots(root, 6)[len(roots):] if (r / task_id).exists()]
    assert not stray, f"{task_id}: attempts beyond 3 exist without Brando's approval ({stray})"
    failures = []
    for number, attempt_root in enumerate(roots, start=1):
        if not (attempt_root / task_id).exists():
            break
        try:
            data, receipt, receipt_path = cell_receipt(attempt_root, task_id, condition_path, model)
            checks = check_file(task_folder, data)
        except (AssertionError, FileNotFoundError, KeyError, ValueError) as exc:
            failures.append({"attempt": number, "folder": str(attempt_root / task_id), "reason": repr(exc)[:400]})
            continue
        later = [r for r in roots[number:] if (r / task_id).exists()]
        if number <= 3:
            assert not later, f"{task_id}: attempt {number} is usable, so no later attempt may exist ({later})"
        unused = [{"attempt": roots.index(r) + 1, "folder": str(r / task_id), "reason": "concurrent attempt, not used"}
                  for r in later]
        return data, receipt, receipt_path, checks, number, failures + unused
    raise AssertionError(f"{task_id}: no usable attempt: {failures}")


def main() -> None:
    parser = argparse.ArgumentParser()
    for name in GROUPS:
        parser.add_argument(f"--{name}", nargs=2, metavar=("ROOT", "CONDITION"))
    args = parser.parse_args()
    parent_bytes = PARENT.read_bytes()
    assert sha(parent_bytes) == PARENT_SHA256, "The 100-file cohort of record changed"
    cohort = json.loads(parent_bytes)
    layout = {**cohort["display_layout"], **cohort["layout_additions"]}
    configurations = dict(cohort["configurations"])
    substitutions = dict(cohort["configuration_substitutions"])
    artifacts = {a["item_id"]: json.loads(json.dumps(a)) for a in cohort["artifacts"]}
    replaced: dict[str, dict] = {}
    applied = []
    extended, keep_terminus2 = amendment_decisions()
    kept = []
    for group, spec in GROUPS.items():
        given = getattr(args, group)
        if not given:
            continue
        root, condition_path = Path(given[0]).resolve(), Path(given[1]).resolve()
        condition = json.loads(condition_path.read_text())
        items = [i for i, a in artifacts.items() if a["configuration_id"] == spec["old"]]
        assert len(items) == spec["count"], (group, len(items))
        staged = {}
        for item in items:
            artifact = artifacts[item]
            if (group, artifact["task_id"]) in keep_terminus2:  # Brando's explicit per-cell exception
                kept.append({"group": group, "task_id": artifact["task_id"], "item_id": item,
                             "configuration_id": spec["old"]})
                continue
            staged[item] = first_usable_attempt(root, artifact["task_id"], layout[item]["task_folder"], condition_path,
                                                condition["model"], (group, artifact["task_id"]) in extended)
        for item, (data, receipt, receipt_path, checks, attempt, failures) in staged.items():  # all verified: apply
            artifact = artifacts[item]
            destination = grid.SEALED / "candidates" / spec["new"] / artifact["task_id"] / "candidate.lean"
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(data)
            replaced[item] = {"group": group, "task_folder": layout[item]["task_folder"],
                              "candidate_file": layout[item]["candidate_file"], "attempt": attempt,
                              "old_sha256": artifact["candidate"]["sha256"], "new_sha256": sha(data), **checks}
            artifact["configuration_id"] = spec["new"]
            artifact["candidate"] = {"path": str(destination), "sha256": sha(data), "status": "nonempty"}
            artifact["provenance"] = {"source": spec["label"], "receipt_path": str(receipt_path),
                                      "receipt_sha256": sha(receipt_path.read_bytes()),
                                      "attempt": attempt, "earlier_attempts": failures,
                                      "runner_model_identity_verified": receipt.get("model_identity_verified"),
                                      "stop_reason": receipt.get("stop_reason"), "actual_models": receipt.get("actual_models"),
                                      "egress_hosts": receipt.get("egress_hosts"),
                                      "egress_denied": receipt.get("egress_denied"),
                                      "condition_path": str(condition_path),
                                      "condition_sha256": sha(condition_path.read_bytes()),
                                      "replaced_terminus2_sha256": replaced[item]["old_sha256"], "content_checks": checks}
            original = substitutions.get(item)
            if original:  # planned cell: keep the planned configuration, record the native one as actual
                substitutions[item] = {**original, "actual_configuration_id": spec["new"],
                                       "reason": f"Native-harness rerun (Brando, 11-16-2026): {spec['label']}."}
            elif item in cohort["display_layout"]:  # planned with this configuration originally (10 Grok cells)
                substitutions[item] = {"planned_configuration_id": spec["old"], "actual_configuration_id": spec["new"],
                                       "reason": f"Native-harness rerun (Brando, 11-16-2026): {spec['label']}."}
        if not any(k["group"] == group for k in kept):  # a kept Terminus 2 cell still needs its configuration
            configurations.pop(spec["old"], None)
        configurations[spec["new"]] = {
            "harness": condition.get("harness_label") or {"grok": "Grok CLI", "antigravity": "Antigravity CLI"}.get(
                condition.get("harness"), "Claude Code"),
            "model": condition["model"], "effort": condition["effort"], "cli_version": condition["cli_version"],
            "instruction_version": 8, "expected_artifacts": spec["count"], "cohort": "prospective",
            "condition_snapshot": {"path": str(condition_path), "sha256": sha(condition_path.read_bytes())}}
        applied.append(group)
    assert applied, "Give at least one group"
    full = {**cohort, "configurations": configurations, "artifacts": list(artifacts.values()),
            "configuration_substitutions": substitutions,
            "actual_counts_by_configuration": {c: sum(a["configuration_id"] == c for a in artifacts.values())
                                               for c in configurations},
            "native_amendment": {"recorded": "11-16-2026", "requested_by": "Brando (chat, 11-16-2026: re-run natively)",
                                 "parent_cohort": {"path": str(PARENT), "sha256": sha(parent_bytes)},
                                 "attempts_amendment": {"path": str(ATTEMPTS), "sha256": sha(ATTEMPTS.read_bytes()),
                                                        "cells_using_a_later_attempt": sorted(
                                                            i for i, r in replaced.items() if r["attempt"] > 1),
                                                        "cells_kept_on_terminus2": kept},
                                 "groups_applied": applied, "replaced_items": replaced}}
    assert len(full["artifacts"]) == 100
    TARGET.write_text(json.dumps(full, indent=1) + "\n")
    commitment = {"round_id": cohort["round_id"], "cohort_file": "sealed/" + TARGET.name,
                  "cohort_sha256": sha(TARGET.read_bytes()), "parent_cohort_sha256": sha(parent_bytes),
                  "artifacts": 100, "tasks": 25, "agents_per_task": 4, "groups_applied": applied,
                  "replaced_files": len(replaced),
                  "candidate_sha256_by_item": {i: a["candidate"]["sha256"] for i, a in artifacts.items()},
                  "note": "Public commitment only. The item-to-agent key stays in sealed/ while raters score."}
    COMMITMENT.write_text(json.dumps(commitment, indent=1, sort_keys=True) + "\n")
    print(json.dumps({"cohort_sha256": commitment["cohort_sha256"], "groups_applied": applied,
                      "replaced": len(replaced), "counts": full["actual_counts_by_configuration"]}))


if __name__ == "__main__":
    sys.exit(main())
