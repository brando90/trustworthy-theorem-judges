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
    subprocess.run([sys.executable, str(ROOT / "experiments/02_design_a_judge_that_predicts_human_ratings_0_to_5_start_06Nov2026/scripts/validate_design.py")], check=True)
    subprocess.run([sys.executable, "-m", "unittest", "discover", "-s",
                    str(ROOT / "experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026/support/tests")], check=True)
    sizing = ROOT / "experiments/15_estimate_required_tasks_solver_configurations_and_human_raters_start_04Nov2026/scripts"
    for script in ("costed_allocation.py", "refresh_provenance_hashes.py"):
        subprocess.run([sys.executable, str(sizing / script)], check=True)
    legacy = ROOT / "experiments/archive/01_veribench_25_tasks_3_samples_5_raters_judge_evaluation_start_03May2026_end_29Sep2026"
    manifest = json.loads((legacy / "SOURCE_MANIFEST.json").read_text())
    for filename, key in manifest["byte_exact_copies"].items():
        assert digest(legacy / filename) == manifest["source_files"][key]["sha256"], filename
    source = ROOT / "experiments/02_design_a_judge_that_predicts_human_ratings_0_to_5_start_06Nov2026/sources"
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
    # The historical budget is validated above; it need not be the current paper design.
    assert "pending" in texts, "Keep the prospective study status explicit"
    tmlr = ROOT / "paper_latex/TMLR_2026_Formal_Specification_Coverage_Judge_Audit"
    for filename, expected in {
        "tmlr.sty": "816214ff5919aa457b6b443bee52b15d9561421417b7f8a50cc84651519f0002",
        "tmlr.bst": "306fd454cf40771bee01293eeb98d2c1cd5f4e11ed0cd7296b335f354fc45206",
    }.items():
        assert digest(tmlr / "vendor" / filename) == expected, filename
    tmlr_main = (tmlr / "00_main.tex").read_text()
    for filename in re.findall(r"\\input\{([^}]+)\}", tmlr_main):
        assert (tmlr / (filename + ".tex")).is_file(), filename
    assert "\\usepackage{tmlr}" in tmlr_main, "Keep the anonymous TMLR submission mode"
    tmlr_texts = "\n".join(p.read_text() for p in tmlr.glob("*.tex"))
    assert not re.search(r"calibrat\w*", tmlr_texts, re.I), "Use project judge-selection terminology"
    for figure in re.findall(r"\\includegraphics(?:\[[^\]]*\])?\{([^}]+)\}", tmlr_texts):
        assert (tmlr / figure).is_file(), figure
    # The TMLR audit's numbers come from this post hoc file; it must parse and keep its denominators.
    audit = json.loads((ROOT / "experiments/archive/19_audit_gpt_5_3_codex_rubric_judge_on_75_rated_outputs_start_12Nov2026_end_12Nov2026" / "POSTHOC_CLI_RUBRIC_JUDGE_AGREEMENT_11-12-2026.json").read_text())
    assert (audit["n_items"], audit["n_tasks"]) == (75, 25)
    assert audit["input_audit"]["artifacts_with_rating_era_reference_statements"] == 51
    for path in ROOT.rglob("*.json"):
        if not {"private", "research_artifacts", ".git"}.intersection(path.parts):
            json.loads(path.read_text())
    print("Project checks passed: design, mirrored instructions, sizing arithmetic, source hashes, official style, and paper inputs.")


if __name__ == "__main__":
    main()
