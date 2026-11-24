#!/bin/bash
# Build the paper: pdflatex, bibtex, pdflatex x2. Prints errors, undefined references and page count.
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode 00_main.tex >build0.log 2>&1
bibtex 00_main >bib.log 2>&1
pdflatex -interaction=nonstopmode 00_main.tex >build.log 2>&1
pdflatex -interaction=nonstopmode 00_main.tex >build.log 2>&1
grep -n -e "^!" -e "Undefined" -e "undefined" -e "Overfull" build.log | head -30
grep -n -i -e "warning" -e "error" bib.log | head
pdfinfo 00_main.pdf | grep Pages
