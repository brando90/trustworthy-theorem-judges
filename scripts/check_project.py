#!/usr/bin/env python3
"""Verify project instructions, design arithmetic, evidence hashes, and paper inputs."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    assert (ROOT / "AGENTS.md").read_bytes() == (ROOT / "CLAUDE.md").read_bytes(), "Entry points differ"
    subprocess.run([sys.executable, str(ROOT / "experiments/02_probabilistic_ordinal_judge/scripts/validate_design.py")], check=True)
    subprocess.run([sys.executable, "-m", "unittest", "discover", "-s",
                    str(ROOT / "experiments/09_human_rating_collection/support/tests")], check=True)
    legacy = ROOT / "experiments/archive/01_legacy_veribench_judge"
    manifest = json.loads((legacy / "SOURCE_MANIFEST.json").read_text())
    for filename, key in manifest["byte_exact_copies"].items():
        assert digest(legacy / filename) == manifest["source_files"][key]["sha256"], filename
    source = ROOT / "experiments/02_probabilistic_ordinal_judge/sources"
    provenance = json.loads((source / "provenance.json").read_text())
    assert digest(source / provenance["file"]) == provenance["sha256"], "Pasted plan changed"
    paper = ROOT / "paper_latex/AAAI_2027_Evaluation_AI_Scientists"
    for filename, expected in {
        "aaai2027.sty": "01990f8d3716f8e39c5b28a7478f3ac6e28630d1161de6105a7217f5e7f60e43",
        "aaai2027.bst": "5db7765ba99de5c1e4686f9b3940a0add9c5e702f2164514462bec130ccb6e3c",
    }.items():
        assert digest(paper / "vendor" / filename) == expected, filename
    main_source = (paper / "00_main.tex").read_text()
    for filename in re.findall(r"\\input\{([^}]+)\}", main_source):
        assert (paper / (filename + ".tex")).is_file(), filename
    texts = "\n".join(p.read_text() for p in paper.glob("*.tex"))
    assert not re.search(r"calibrat\w*", texts, re.I), "Use project judge-selection terminology"
    assert "Anonymous Submission" in main_source
    assert r"\usepackage[submission]{aaai2027}" in main_source, "Anonymous style option is required"
    assert "14,848" in texts and "pending" in texts
    for path in ROOT.rglob("*.json"):
        if "private" not in path.parts and ".git" not in path.parts:
            json.loads(path.read_text())
    print("Project checks passed: design, mirrored instructions, source hashes, official style, and paper inputs.")


if __name__ == "__main__":
    main()
