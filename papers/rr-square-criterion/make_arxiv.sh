#!/bin/bash
# Build paper.pdf twice with pdflatex, then an arXiv source tarball (inline bibliography, no .bbl).
set -euo pipefail
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode paper.tex >/dev/null && pdflatex -interaction=nonstopmode paper.tex > build.log
grep -E "^!|Output written|LaTeX Warning: (Reference|Citation)|Overfull" build.log || true
rm -rf arxiv && mkdir -p arxiv
{ grep -q '^\\pdfoutput=1' paper.tex || printf '%s\n' '\pdfoutput=1'; cat paper.tex; } > arxiv/paper.tex
tar -czf arxiv.tar.gz -C arxiv paper.tex && rm -rf arxiv
rm -f paper.aux paper.log paper.out build.log
echo "wrote paper.pdf and arxiv.tar.gz"
