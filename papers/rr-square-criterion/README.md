# The RR-square criterion paper (placeholder)

This directory will hold the third paper: the conditional Riemann–Roch-square criterion for the Riemann
Hypothesis, in the same layout as the two papers beside it: `paper.tex`, `paper.pdf`, `make_arxiv.sh`, an arXiv
source package `arxiv.tar.gz` that compiles standalone, and an `ARXIV.md` submission sheet (staged, not submitted). The paper was still being written when this repository was assembled, so nothing is here yet.

Until it lands, the mathematics it describes can already be read and checked in Lean:

- the RR-square statements, the countermodel and the function-field instances in
  `telperion/examples/weil_form_enclosure/lean/RRSquare*.lean`;
- the composition "RR-square on a family of windows covering every pole-free test implies RH",
  `RvMBridgePF.rh_of_rr_windows` in `telperion/examples/rvm_bridge/lean/PFConverseC.lean`;
- the two research memos in `telperion/research/rr_square/`.

`formalization/README.md` lists each theorem with its status. The criterion is **conditional**: nobody has
constructed the windows it asks for, and the Riemann Hypothesis remains open.
