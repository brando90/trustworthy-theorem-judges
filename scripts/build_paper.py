#!/usr/bin/env python3
"""Build the anonymous AAAI-27 draft in scratch and publish only its current PDF."""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "paper_latex/AAAI_2027_Evaluation_AI_Scientists"


def main():
    latexmk = shutil.which("latexmk")
    if not latexmk:
        raise SystemExit("latexmk is required; install a TeX distribution with AAAI-27 dependencies.")
    with tempfile.TemporaryDirectory(prefix="ttj-paper-build-") as temporary:
        scratch = Path(temporary)
        for source in PAPER.glob("*.tex"):
            shutil.copy2(source, scratch / source.name)
        shutil.copy2(PAPER / "references.bib", scratch / "references.bib")
        for filename in ("aaai2027.sty", "aaai2027.bst"):
            shutil.copy2(PAPER / "vendor" / filename, scratch / filename)
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
        shutil.copy2(scratch / "00_main.pdf", PAPER / "00_main.pdf")
        print(f"Built {PAPER / '00_main.pdf'}; no overfull boxes or unresolved references.")


if __name__ == "__main__":
    main()
