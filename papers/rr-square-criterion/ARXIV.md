# arXiv submission sheet

**Status: staged, not submitted.** The author submits from their own arXiv account. No arXiv identifier exists yet,
and none is claimed anywhere.

Everything the arXiv form asks for, ready to paste. The source package is `arxiv.tar.gz` in this directory. It holds
one file, `paper.tex`, with `\pdfoutput=1` on line 1 and an inline bibliography; there are no figures and no `.bbl`.
Rebuild with `make_arxiv.sh`; the page count below is from that build. The package was unpacked into an empty
directory and compiled with pdflatex twice: 13 pages, no errors, no undefined references, no overfull boxes.

## Upload

- **File:** `arxiv.tar.gz`.
- **Processing:** pdflatex (arXiv autodetects from `\pdfoutput=1`).

## Metadata

- **Title:** A kernel-checked Riemann-Roch-square criterion for the Riemann Hypothesis
  (TeX form: `A kernel-checked Riemann--Roch-square criterion for the Riemann Hypothesis`)
- **Authors:** Peter W. Murphy
- **Primary category:** math.NT (Number Theory)
- **Cross-list:** cs.LO (Logic in Computer Science)
- **MSC classes:** 11M26 (primary); 03B35 (secondary)
- **ACM classes:** F.4.1
- **Comments:** 13 pages. A conditional, kernel-checked reduction, not a proof of the Riemann Hypothesis and not
  progress towards one: under RH the windows exist trivially, and RH is equivalent to their existence (also
  kernel-checked). Lean 4 sources in the Arda repository, https://github.com/DrMurphyIsIn/Arda, commit
  50b1000254c6bb74bf12d21fa66483bd9fc14aeb (telperion/examples/weil_form_enclosure/lean and
  telperion/examples/rvm_bridge/lean). All theorems depend only on propext, Classical.choice and Quot.sound.
- **License:** CC BY 4.0.
- **Report number / journal ref / DOI fields:** leave blank.

## Abstract (plain text with light TeX, as arXiv renders it)

For a curve over a finite field, Weil's proof of the Riemann Hypothesis runs through the Hodge index theorem on the surface $C \times C$, and Grothendieck derived that inequality from Riemann-Roch on the surface. We isolate, in Lean 4, the dimension-level axioms that this argument uses and ask what an analogue over $\mathbb{Q}$ would have to supply. On a real vector space $V$ with a bilinear form $B$ and a degree class $f$, we state Riemann-Roch-square axioms: a degree on a larger divisor space vanishing on principal divisors, an effectivity clause, numerical triviality of principal divisors in $V$, and a Riemann-Roch index identity with Serre duality whose quadratic term is $B$. We prove that these axioms together with either a degree bound $h^0 \le \beta(\deg)$ or a no-zero-divisor clause imply the Hodge index ($B(v,f) = 0 \Rightarrow B(v,v) \le 0$). A countermodel shows that the extra clause cannot be dropped. Function-field instances test the axioms: a genus-2 curve over $\mathbb{F}_5$ satisfies them, with an exact sum-of-squares certificate; an off-circle fake zeta function does not; and an on-circle fake with a negative point count does, which shows that the axioms cannot see the effectivity of the Frobenius graphs. On the arithmetic side we prove a converse of Weil's criterion restricted to pole-free test functions (those whose Fourier transform vanishes at $\pm i/2$). We compose the two: a family of RR-square windows covering every pole-free test implies Mathlib's RiemannHypothesis. This is a conditional, kernel-checked reduction. Under RH such windows exist trivially (collapse), and this is also kernel-checked, so RH is equivalent to their existence and all the content is the construction of windows without reference to the zeros. No such construction is known. This is not progress on RH. Every theorem depends only on propext, Classical.choice and Quot.sound.

## After the identifier is assigned

1. Add `arXiv:XXXX.XXXXX` to the `\date` line of `paper.tex` and to this repository's `README.md` paper table and
   `papers/ARXIV_STAGING.md`.
2. Rebuild with `make_arxiv.sh` and commit.
