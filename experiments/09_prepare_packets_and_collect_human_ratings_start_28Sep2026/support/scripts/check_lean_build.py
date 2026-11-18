#!/usr/bin/env python3
"""TLDR: Read a `lake build --keep-going` log, report which rating-packet Lean modules failed, and exit 1 only if a gold reference (not an agent file) is newly broken."""
import re
import sys
from pathlib import Path

KNOWN_GOLD_FAILURES = {
    # Brando 11-18-2026: imports project-local `veribench.cs_set.*` modules that the packet does not ship; fix by shipping them or inlining.
    "main_rating_task.task_17_heapsort_algorithm.gold_lean.reference",
}


def main(log_path: str) -> int:
    log = Path(log_path).read_text(errors="replace")
    failed = set(re.findall(r"^✖ \[\d+/\d+\] Building (\S+)", log, re.M))
    # lake ends a failed build with a list of "- module" lines that also includes modules whose imports are missing
    failed |= {m for m in re.findall(r"^- (\S+)$", log, re.M) if m.startswith(("main_rating_task.", "warmup_task."))}
    missing_imports = sorted(set(re.findall(r"^- (Mathlib\.\S+)$", log, re.M)))
    failed = sorted(failed)
    gold = [m for m in failed if ".gold_lean." in m]
    agent = [m for m in failed if ".agent_lean." in m]
    new_gold = [m for m in gold if m not in KNOWN_GOLD_FAILURES]
    print(f"modules that failed to compile: {len(failed)} (gold {len(gold)}, agent {len(agent)})")
    print("Agent files that do not compile are rating data, not CI failures (proofs are not rated):")
    for m in agent:
        print("  agent:", m)
    if missing_imports:
        print("Modules imported by some files that do not exist in this Mathlib (written for another version):", ", ".join(missing_imports))
    for m in gold:
        print("  gold :", m, "(known)" if m in KNOWN_GOLD_FAILURES else "(NEW)")
    return 1 if new_gold else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
