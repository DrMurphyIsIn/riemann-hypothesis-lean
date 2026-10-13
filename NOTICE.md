# Notice and provenance

- **What this is.** A collection of kernel-checked results around the Riemann Hypothesis. It is **not** a
  proof of RH, which remains open. The unconditional results are 0 ≤ Λ ≤ 0.2811857 for the de Bruijn–Newman
  constant, Newman's conjecture for Dobner's extended Selberg class, and pole-free Weil positivity on the
  finite HODGE-1 window. The conditional ones are Weil's criterion on pole-free tests, the frontier
  equivalence outside that window, and the Riemann–Roch-square criterion. `formalization/README.md` says
  which is which.
- **Origin.** The Lean islands and the Telperion engine were developed in the author's development
  repository, Arda (<https://github.com/DrMurphyIsIn/Arda>), and are copied here from commit
  `50b1000254c6bb74bf12d21fa66483bd9fc14aeb`. Only comments, docstrings and prose were reworded
  (`CENSORING.md`), and `scripts/materialize.sh` checks this against that commit.
- **The de Bruijn–Newman constant.** N. G. de Bruijn, *The roots of trigonometric integrals*, Duke Math. J.
  17 (1950). C. M. Newman, *Fourier transforms with only real zeros*, Proc. AMS 61 (1976). Newman's conjecture
  Λ ≥ 0 is the theorem of B. Rodgers and T. Tao, Forum Math. Pi 8 (2020), e6. The proof formalized here is
  A. Dobner's, *A proof of Newman's conjecture for the extended Selberg class*, arXiv:2005.05142. For scale,
  D. H. J. Polymath, Res. Math. Sci. 6 (2019), 31 (Λ ≤ 0.22), and D. Platt and T. Trudgian, Bull. LMS 53
  (2021) (Λ ≤ 0.2). Neither numerical bound is formalized here.
- **OpenAI.** The zero-free half-plane Re s > 7/8 behind Λ ≤ 9/32 is OpenAI's, from *The Quasi-Riemann
  Hypothesis* (OpenAI Math Release preprint, 2026) and <https://github.com/openai/math> at commit
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a` (Apache-2.0). It is fetched at build time and not vendored.
- **Baiying Liu.** The improved half-plane behind Λ ≤ 0.2811857 is Liu's, from *Slightly improved zero-free
  half-planes for the quasi-Riemann hypothesis*, arXiv:2610.12234, with Lean at
  <https://github.com/liubaiying101/Slightly-improved-zero-free-half-planes-for-the-quasi-Riemann-hypothesis>,
  commit `7d10420de90efa2f082a06a342fc7accbd57ab37`. It is fetched at build time and not vendored; see
  `LICENSING.md` for its licence status.
- **Zeta23.** The explicit formula and Riemann–von Mangoldt machinery used by `rvm_bridge` come from Zeta23
  (anthropics/formal-math, `zeta23/`, Apache-2.0; mathematics by L. Alpöge and R. Furman,
  arXiv:2608.13637), fetched by Lake and not vendored.
- **LiCriterion.** N. Bulka, `li-criterion-rh-equivalence-lean`, commit `35df682f` (Apache-2.0), supplies the
  ξ vocabulary and Hadamard's exp-polynomial theorem to the `dbn` island.
- **Weil and the RR-square idea.** Weil's explicit formula and positivity criterion; the Riemann–Roch-square
  statements formalize a Grothendieck-style Hodge-index argument. The research memos in
  `telperion/research/rr_square/` cite their sources (Connes–Consani, Cartwright, Sumi and others).
- **Lean and Mathlib.** Lean 4 and Mathlib (Apache-2.0), at the pins listed in `formalization/README.md`.
  Comparator (Lean FRO and OpenAI), lean4export and nanoda (C. Kernan) were used for the independent judging
  recorded in the development repository.
- **Machine assistance.** The formalization, the tooling, the audit trail and the papers were produced with
  extensive use of AI coding assistants (Claude, Anthropic), running as parallel sessions under the direction of
  the author. The ten de Bruijn–Newman and half-plane statements were read back by the author (a human); eleven
  further statements by a separate AI session; the rest only by the AI session that wrote them
  (`docs/PROGRESS.md`, section 10). The Lean kernel is the sole trusted component: every claim here is either a
  kernel-checked theorem or explicitly labelled otherwise. None of this work has had external review or been refereed.
