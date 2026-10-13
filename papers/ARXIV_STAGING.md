# arXiv staging

All three papers are prepared for arXiv and **staged, not submitted**. The author submits them, from their own arXiv
account. No arXiv identifiers exist yet, and none is claimed anywhere in this repository. The Zenodo DOIs are the
citable records until then.

Each paper directory holds three things:

- `ARXIV.md`, the submission sheet: title, authors, categories, MSC classes, comments, abstract and licence, ready to paste.
- `make_arxiv.sh`, which rebuilds `paper.pdf` with pdflatex (twice) and writes the source package.
- `arxiv.tar.gz`, the source package: one `paper.tex` with `\pdfoutput=1` on line 1, an inline bibliography, and no
  figures or `.bbl`.

The two sheets were written for the papers' own release repositories, so the paths they mention (`paper/...`) mean
the paper's directory here.

| paper | directory | package | primary / cross-list | MSC | status |
|---|---|---|---|---|---|
| A kernel-checked bound Λ ≤ 9/32 for the de Bruijn–Newman constant from OpenAI's quasi-Riemann hypothesis (v1.1.0, with Λ ≤ 0.2811857) | `qrh-debruijn-newman/` | `arxiv.tar.gz`, 18 pages | math.NT / cs.LO | 11M26; 03B35, 11Y35 | staged, not submitted; the author submits |
| Newman's conjecture, kernel-checked: Λ ≥ 0 for the de Bruijn–Newman constant in Lean 4 along Dobner's proof (v1.1.0) | `newman-lambda-nonneg/` | `arxiv.tar.gz`, 15 pages | math.NT / cs.LO | 11M26; 03B35, 11M06, 33B15 | staged, not submitted; the author submits |
| A kernel-checked Riemann–Roch-square criterion for the Riemann Hypothesis | `rr-square-criterion/` | `arxiv.tar.gz`, 13 pages | math.NT / cs.LO | 11M26; 03B35 | staged, not submitted; the author submits |

**Check, done 2026-10-13.** All three packages were unpacked into an empty directory and compiled with pdflatex
twice. All three produced the paper (18, 15 and 13 pages) with no errors and no undefined references. Each packaged `paper.tex`
is the `paper.tex` beside it, plus the `\pdfoutput=1` line.
