# Kernel-checked results on the Riemann Hypothesis: de Bruijn–Newman bounds and a conditional Riemann–Roch-square criterion

**The Riemann Hypothesis is open, and nothing in this repository proves it.** This repository collects Lean 4
theorems *around* RH that the Lean kernel has checked: some are unconditional facts strictly weaker than RH,
some are equivalences that restate what remains open, and one is a criterion that would imply RH if someone
could construct the object it asks for. Every theorem is labelled as one of these, here and in
[`formalization/README.md`](formalization/README.md).

It brings together the Lean developments, the three papers written about them, and a copy of Telperion, the
certificate engine that produced a good part of the Lean.

## Where things stand

The Riemann Hypothesis says that every non-trivial zero of ζ(s) lies on the line Re s = 1/2. It has been open
since 1859. There are many equivalent forms. Three of them organise this repository.

**The de Bruijn–Newman constant.** De Bruijn (1950) deformed Riemann's ξ function along the backward heat
equation into a family H_t. He proved that every zero of H_t is real once t ≥ 1/2. Newman (1976) showed there
is a constant Λ such that the zeros of H_t are all real exactly when t ≥ Λ, and RH is the statement Λ ≤ 0.
Newman conjectured Λ ≥ 0, "RH, if true, is only barely true". Rodgers and Tao proved it in 2018. So RH is
exactly Λ = 0, and every upper bound on Λ measures how far the known zero-free regions are from RH.

Here, kernel-checked: **0 ≤ Λ ≤ 0.2811857**.

- The lower bound `dbn_newman` follows Dobner's 2020 proof of Newman's conjecture. It comes with Dobner's
  extension to the whole extended Selberg class (`selberg_newman`, `selberg_newman_sharp`), with the class
  stated as a Lean structure and ζ as the control instance.
- The upper bound combines a formalization of de Bruijn's theorem with a converter: a zero-free half-plane
  Re s > θ for ζ gives real zeros of H_t for t ≥ 2(θ − 1/2)². Fed OpenAI's quasi-Riemann hypothesis (θ = 7/8),
  it gives Λ ≤ 9/32. Fed Baiying Liu's improved half-plane (θ ≈ 0.874957), it gives Λ ≤ 0.2811857.
- These bounds are weaker than the best numerical bounds
  (Λ ≤ 0.22 by Polymath15, Λ ≤ 0.2 by Platt and Trudgian), which are not formalized. Each theorem was also
  replayed by a second, independent kernel (nanoda) through Comparator, against a challenge whose type is
  the registered statement.

**Weil's positivity criterion.** Weil showed that RH is equivalent to the positivity of a quadratic form, the
explicit formula evaluated on autocorrelations g ∗ g̃ of test functions. In Lean:

- RH is equivalent to Weil positivity on *pole-free* tests, those whose transform vanishes at ±i/2
  (`rh_iff_poleFree_weil_positivity`).
- The HODGE-1 work proves that positivity outright for every pole-free test supported in [−0.5493, 0.5493],
  a window just short of (log 3)/2, so that 2 is the only prime that enters. The proof is an exact kernel
  certificate.
- Combining the two gives the honest frontier: RH is equivalent to Weil positivity for the pole-free tests
  whose support reaches *outside* that window (`rh_iff_poleFree2_outside_window5493`).

The window theorem is real, checked mathematics, but it is verification on a fixed finite window. The
frontier theorem is a reformulation of RH, not progress towards it.

**The Riemann–Roch-square criterion.** For curves over finite fields, Weil's proof of the analogue of RH runs
through the Hodge index theorem on the surface C × C, and that theorem follows from Riemann–Roch on the
surface. The RR-square criterion asks what an analogue for ζ would have to provide, and makes that precise
enough to check.

- The kernel-checked part: abstract Riemann–Roch-type axioms on a "window" imply the Hodge index. This works
  with either a degree bound or a no-zero-divisors condition (`RRSquare.hodge_index`,
  `hodge_index_of_domain`).
- A countermodel shows the extra condition is necessary.
- A collapse lemma shows that merely asserting such a structure exists is circular, so the content has to be
  an actual construction.
- Function-field instances: a genus-2 curve over F₅ satisfies the axioms; two fake zeta functions show what
  the axioms can and cannot see.
- `rh_of_rr_windows`: a family of RR-square windows covering every pole-free test would imply RH.
- The converse, that RH gives such a family, is trivial by the collapse lemma. It is formalized in the
  RR-square paper's development and is not part of this snapshot.

**The criterion is conditional, and its hypothesis is open: nobody has constructed the windows.**

## What is not proved

- The Riemann Hypothesis, or equivalently Λ = 0.
- Weil positivity for pole-free tests supported beyond the HODGE-1 window.
- The existence of an RR-square family covering all pole-free tests.

These are all the same open problem in different clothes.

## The papers

| | paper | DOI |
|---|---|---|
| 1 | *A kernel-checked bound Λ ≤ 9/32 for the de Bruijn–Newman constant from OpenAI's quasi-Riemann hypothesis* (v1.1.0 adds Λ ≤ 0.2811857 from Liu's half-plane), [`papers/qrh-debruijn-newman/`](papers/qrh-debruijn-newman/) | [10.5281/zenodo.23269134](https://doi.org/10.5281/zenodo.23269134) (all versions; v1.1.0: 10.5281/zenodo.23324360) |
| 2 | *Newman's conjecture, kernel-checked: Λ ≥ 0 for the de Bruijn–Newman constant in Lean 4 along Dobner's proof* (v1.1.0 adds the extended Selberg class), [`papers/newman-lambda-nonneg/`](papers/newman-lambda-nonneg/) | [10.5281/zenodo.23287832](https://doi.org/10.5281/zenodo.23287832) (all versions; v1.1.0: 10.5281/zenodo.23292885) |
| 3 | The Riemann–Roch-square criterion, [`papers/rr-square-criterion/`](papers/rr-square-criterion/) | not yet released |

Each paper directory has the LaTeX source, the PDF, the build script and its arXiv submission sheet. The first
two papers were released with their own repositories,
[qrh-debruijn-newman](https://github.com/DrMurphyIsIn/qrh-debruijn-newman) and
[newman-lambda-nonneg](https://github.com/DrMurphyIsIn/newman-lambda-nonneg). Those repositories also carry
the Comparator judge bundles and CI transcripts for the de Bruijn–Newman results.

## What is in this repository

```
papers/          the three papers (LaTeX, PDF, build script)
formalization/   the theorem index (README.md) and the pinned source commit (ARDA_SOURCE)
telperion/       the Telperion engine, its tests, and the Lean islands under telperion/examples/
scripts/         materialize.sh (clone the source commit, check the copy), the copy checker, the axiom checker
CENSORING.md     every comment that was reworded in the Telperion copy, and why
```

The Lean lives in six islands under `telperion/examples/`: `dbn`, `oai_qrh_bridge`, `liu_dbn_bridge`,
`rvm_bridge`, `weil_form_enclosure` and `quasicrystal`. Each is its own Lake project, because the upstream work
each one builds on is pinned to a different Lean. OpenAI's and Liu's Lean code is never stored here. The
island scripts fetch it at pinned commits and check every file by hash.

## Checking it

The trust model is the usual one for formal proofs: **the Lean kernel is the only trusted component.** You
still have to read the statements and decide whether they say what the prose says. `formalization/README.md`
gives each one in plain words next to its exact Lean name, to make that easier.

```sh
scripts/materialize.sh          # clone the development repository at the pinned commit and check that
                                # telperion/ differs from it only in comments, docstrings and listed prose

cd telperion/examples/weil_form_enclosure/lean
lake exe cache get && lake build
lake env lean AxiomGuardRRSquare.lean   # every line: [propext, Classical.choice, Quot.sound] or a subset
```

The other islands work the same way; `formalization/README.md` has the commands. On GitHub,
`.github/workflows/verify.yml` builds the RR-square, dbn and rvm_bridge islands on every change. On manual
dispatch it also builds the HODGE-1 certificates and the two half-plane bridges, which take hours.
`.github/workflows/telperion.yml` runs the engine's test suite: about 3,600 tests, with 131 that need the
development repository skipped and listed.

## Provenance and machine assistance

The Lean developments and the engine were written in the author's development repository, Arda
(<https://github.com/DrMurphyIsIn/Arda>). They are copied here from commit `b17b3c68f` of 2026-10-13. Before
publishing, the copy was scanned for references to an unrelated private project and for private file paths,
and those comments were reworded. No code, statement or proof changed. [`CENSORING.md`](CENSORING.md) lists
every file, and `scripts/check_telperion_copy.py` proves the claim mechanically against that commit.

All of this work was produced with extensive use of an AI coding assistant (Claude, Anthropic) under the
direction of the author: the Lean, the certificates, the engine, the audits and the papers. Several of the
read-backs of registered statements were done by a separate AI session; they are labelled as such in the
development repository's registry. None of the work has been refereed. The mathematics being formalized is,
in the main, other people's: de Bruijn, Newman, Rodgers and Tao, Dobner, Weil, OpenAI and Baiying Liu.
[`NOTICE.md`](NOTICE.md) gives the credits.

## Licensing

The mathematics (Lean, scripts, certificates) is Apache-2.0. The papers and prose are CC-BY-4.0. The Telperion
engine is under the Business Source License 1.1, free for research, teaching and evaluation. See
[`LICENSING.md`](LICENSING.md).

## Citing

See [`CITATION.cff`](CITATION.cff). Please also cite the papers above and the original authors in
[`NOTICE.md`](NOTICE.md).
