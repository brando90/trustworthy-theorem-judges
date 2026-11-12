#!/usr/bin/env python3
"""Build each paper draft (AAAI-27 workshop and TMLR) in scratch and publish only its current PDF."""
from pathlib import Path
import argparse
import os
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
# Paper directory -> official vendor style files copied beside its sources.
PAPERS = {
    "AAAI_2027_Evaluation_AI_Scientists": ("aaai2027.sty", "aaai2027.bst"),
    "TMLR_2026_Formal_Specification_Coverage_Judge_Audit": ("tmlr.sty", "tmlr.bst"),
}


def build(name, styles, latexmk):
    paper = ROOT / "paper_latex" / name
    with tempfile.TemporaryDirectory(prefix="ttj-paper-build-") as temporary:
        scratch = Path(temporary)
        for source in paper.glob("*.tex"):
            shutil.copy2(source, scratch / source.name)
        shutil.copy2(paper / "references.bib", scratch / "references.bib")
        for filename in styles:
            shutil.copy2(paper / "vendor" / filename, scratch / filename)
        if (paper / "figures").is_dir():
            (scratch / "figures").mkdir()
            for figure in (paper / "figures").glob("*.pdf"):
                shutil.copy2(figure, scratch / "figures" / figure.name)
        environment = dict(os.environ)
        # Stable PDF dates for identical source; does not change the protocol date.
        environment["SOURCE_DATE_EPOCH"] = "1793923200"
        environment["FORCE_SOURCE_DATE"] = "1"
        result = subprocess.run(
            [latexmk, "-pdf", "-interaction=nonstopmode", "-halt-on-error", "00_main.tex"],
            cwd=scratch, env=environment, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, text=True,
        )
        log = (scratch / "00_main.log").read_text(errors="replace") if (scratch / "00_main.log").exists() else result.stdout
        faults = [line for line in log.splitlines() if any(word in line for word in (
            "Overfull", "Undefined control sequence", "There were undefined references",
            "There were undefined citations", "multiply defined"))]
        if result.returncode or faults:
            print(result.stdout[-12000:])
            print("\n".join(faults))
            raise SystemExit(result.returncode or 1)
        shutil.copy2(scratch / "00_main.pdf", paper / "00_main.pdf")
        print(f"Built {paper / '00_main.pdf'}; no overfull boxes or unresolved references.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", action="append", choices=sorted(PAPERS),
                        help="Paper directory to build; repeat for several. Default: every paper.")
    args = parser.parse_args()
    latexmk = shutil.which("latexmk")
    if not latexmk:
        raise SystemExit("latexmk is required; install a TeX distribution with the AAAI-27 and TMLR dependencies.")
    for name in args.paper or sorted(PAPERS):
        build(name, PAPERS[name], latexmk)


if __name__ == "__main__":
    main()
