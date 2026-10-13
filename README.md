# Kernel-checked results on the Riemann Hypothesis: de Bruijn–Newman bounds and a conditional Riemann–Roch-square criterion

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23352050.svg)](https://doi.org/10.5281/zenodo.23352050)

**The Riemann Hypothesis is open, and nothing in this repository proves it.** What is here is a body of Lean 4 work *around*
RH, every piece checked by the Lean kernel. Some of it is unconditional and strictly weaker than RH. Some of it is
equivalences that restate exactly what remains open. One piece is a criterion that would imply RH if anyone could construct
the object it asks for. The rest is a research record, including the routes we tried and closed. Each item below is labelled
as one of these.

The repository brings together the Lean developments, the three papers written about them, and a copy of Telperion, the
certificate engine that produced much of the Lean. [`docs/PROGRESS.md`](docs/PROGRESS.md) is the complete record. It has
exact Lean names, files, pull requests, judge runs and review status for everything summarised here, plus an inventory of all
142 registry nodes.

## At a glance

| | what | status |
|---|---|---|
| **0 ≤ Λ ≤ 0.2811857** | the de Bruijn–Newman constant, both bounds | unconditional; kernel-checked; judged by two kernels; human read-back |
| Newman for the Selberg class | Dobner's theorem for every element of the extended Selberg class | unconditional; judged; human read-back |
| Λ ≤ 1/2, Hadamard, effective Theorem 4 | de Bruijn 1950 and the heat-flow foundations | unconditional; kernel-checked |
| Weil positivity on windows | outright positivity for tests supported in [−L, L], up to L = 0.5493 | unconditional, finite-window; not progress on RH |
| zeros up to height 8000 | every zero with 0 < Im ρ ≤ 8000 is on the line, with no numerical oracle | unconditional finite verification |
| RH ⇔ pole-free Weil positivity | Weil's criterion, including the converse on pole-free tests | **equivalence** |
| the HODGE-1 frontier | RH ⇔ positivity for tests reaching outside [−0.5493, 0.5493] | **equivalence**: exactly what is open |
| the RR-square criterion | windows covering all pole-free tests ⇒ RH, and RH ⇔ such windows exist | **conditional / equivalence**: the content is a construction, and none is known |
| research notes | the 7/8 method's limit, gates 0–10, SCALE-1, LY-1 | **not proofs**; mostly negative results |

## 1. Where RH stands

The Riemann Hypothesis says every non-trivial zero of ζ(s) lies on the line Re s = 1/2. It has been open since 1859.

This programme is a sustained, machine-checked effort around the problem, run by one author directing parallel AI sessions.
Its development repository keeps a flag, `conjecture1_proved`, and the flag is `False`.

The project's own assessment is blunt. Every proved item is one of three things:

- a finite-window statement;
- a converter applied to someone else's zero-free half-plane;
- a formalization of known mathematics.

None of them touches the part of RH that is hard. The value is elsewhere:

- exact, checkable statements of what is known;
- equivalences that isolate what is not known;
- a record of which roads are closed.

## 2. Headline kernel-checked results

**The de Bruijn–Newman constant.** De Bruijn (1950) deformed Riemann's ξ along the backward heat equation into a family
H_t. Newman (1976) showed there is a constant Λ such that the zeros of H_t are all real exactly when t ≥ Λ. RH is the
statement Λ ≤ 0, and Rodgers and Tao proved Λ ≥ 0 in 2018. So RH is exactly Λ = 0, and every upper bound on Λ measures how
far the known zero-free regions are from RH. Here, kernel-checked:

- **Λ ≥ 0**: `dbn_newman`, following Dobner's 2020 proof.
- **Λ ≤ 9/32**: `dbn_real_zeros_of_qrh_unconditional`, from OpenAI's quasi-Riemann hypothesis (ζ ≠ 0 for Re s > 7/8)
  through a formalized converter. A zero-free half-plane Re s > θ gives real zeros for t ≥ 2(θ − 1/2)².
- **Λ ≤ 0.2811857**: `dbn_real_zeros_ge_2811857`, from Baiying Liu's slightly larger half-plane (θ ≈ 0.874957).
- Each was judged by Comparator with a second kernel (nanoda), and each was read back by the author.

These bounds are weaker than the best numerical bounds, Λ ≤ 0.22 (Polymath15) and Λ ≤ 0.2 (Platt–Trudgian), which are not
formalized.

**Newman's conjecture for the Selberg class.** Dobner proved Λ ≥ 0 for every element of the extended Selberg class. This is
formalized in full, with the class stated as a Lean structure and ζ as the control instance (`selberg_newman`,
`selberg_newman_sharp`).

**De Bruijn's Λ ≤ 1/2** (`dbn_debruijn_real_zeros`), together with Hadamard factorisation for even functions of order below 2,
H_0 = ξ/8, and the RH ⇔ real-zeros equivalences. An **effective Theorem 4** makes Dobner's height explicit. Its accompanying
note records why an effective Newman theorem is out of reach on that route.

## 3. Criteria and reductions (conditional or equivalences)

- **Weil's criterion, both halves.** It includes a new converse on *pole-free* tests: test functions whose transform
  vanishes at ±i/2, which kills both pole terms. Statement: RH ⇔ Weil positivity on pole-free tests
  (`rh_iff_poleFree_weil_positivity`).
- **The HODGE-1 frontier.** Positivity is proved outright for pole-free tests supported in [−0.5493, 0.5493], a window just
  short of (log 3)/2, where 2 is the only prime that enters. So RH is equivalent to positivity for the tests whose support
  reaches outside it (`rh_iff_poleFree2_outside_window5493`). That is a precise statement of the open content. It is not
  progress.
- **The Riemann–Roch-square criterion.** For curves over finite fields, Weil's proof runs through the Hodge index on C × C,
  which follows from Riemann–Roch on the surface. The RR-square criterion asks what an analogue over ℚ would have to supply.
  - Kernel-checked: abstract RR axioms with a degree bound, or with no zero divisors, imply the Hodge index.
  - A countermodel shows that condition is needed.
  - A collapse lemma shows that merely asserting such a structure exists is circular, so the content has to be a
    construction.
  - Function-field instances test the axioms.
  - `rh_of_rr_windows`: windows covering every pole-free test would imply RH. **No one has constructed them.**
  - The trivial converse is kernel-checked too (`rh_iff_exists_rr_windows`, merged in #726), so RH ⇔ RR-square windows exist.
    That equivalence is deliberately empty: the windows built from RH are read off from Weil positivity and carry no
    geometry. The content of the criterion is a *construction* of windows defined without reference to the zeros.
- **Li's criterion and the Li/Weil dictionary.** Bombieri–Lagarias's explicit formula, the ξ partial fraction, and Li's
  forward half. The "Li ladder" turns verified zeros into nonnegative Li coefficients.

## 4. Weil positivity, proved on windows

Weil's form is shown positive outright for every test supported in [−L, L]:

- **2L ≤ log 2**: the prime-free window, full test class, exact kernel certificates.
- **2L ≤ 4/5**: the first prime present and accounted for exactly.
- **L ≤ 9/20 and L ≤ 0.5493** on pole-free tests (HODGE-1).
- Connes and Consani's archimedean positivity (their Corollary 2.3), formalized for every support.
- L ≤ 1/2 is proved in a heavy module on the development repository. It is not built by CI and not registered, so it is
  listed but not counted.

The project measured why windows cannot become a route. The positivity margin on a window *is* the sum over zeros, so a
window of half-width L only verifies RH up to a height of roughly e^{2L}.

The explicit-formula machinery these rest on is also formalized: unconditional Riemann–von Mangoldt, the corridor bound, the
limit explicit formula, the local count sum, and Zhu's window inputs.

## 5. Other formalizations

- **Every zero up to height 8000 lies on the line.** These are compact kernel certificates with no hypothesis and no
  numerical oracle, replayed independently. There is also a zero in (14, 15) computed by the kernel alone. This is finite
  verification. Classical computation goes much higher.
- **Zero-free regions.** The effective de la Vallée Poussin region, an elementary γ⁻⁵ region and a polylog improvement, the
  near-line bound |ζ| ≤ 6(1 + log|t|), and low-height boxes.
- **The Dyson quasicrystal island.** Lee–Yang core, Kurasov–Sarnak construction, two-frequency rigidity, off-line Euler
  factors as negative controls, Satake degree two.
- **BraggDefect.** The explicit formula in diffraction form, and a certified defect witness with no remaining numerical
  hypothesis.
- **The Euler-model strip.** No zeros near the line above an explicit height for the finite Euler-product model. Open pull
  request #725, **not merged**.
- **Complementary-series positivity for PGL₂(ℂ)**, built on AxiomMath's metaplectic library.

## 6. Verification infrastructure

- **The missions registry.** Every formal statement has a status, an artifact, a read-back record, a grant and a Comparator
  record.
  - The grant gate checks hashes.
  - Since 2026-09-23 it refuses a read-back from the same session or identity as the author.
  - Earlier read-backs were relabelled `unverified` after an audit found they were not independent.
- **The Comparator judge.** For each node, a challenge whose *type* is the registered statement, replayed in Lean's kernel and
  nanoda. A separate heavy judge runs the Lean kernel alone, for certificates nanoda cannot handle.
- **Independent replays.**
  - OpenAI's quasi-Riemann-hypothesis challenges: accepted by both kernels.
  - Liu's Lean: replayed before composition.
  - AxiomMath's Dedekind zero-free library (Cureton–Thorner): the proof replays, but its shipped Comparator challenge fails.
    An instance path, `instCommCStarAlgebraComplex`, makes the challenge and solution syntactically different though
    definitionally equal, and a one-line fix makes it pass.
- **Axiom guards** on every island, enforced in CI.
- **The Telperion registry explorer** at <https://drmurphyisin.github.io/Arda/explorer/>, including its "Riemann's missing
  surface" tab.

## 7. Research programme and negative results

These are research notes, not proofs: AI work, most of it without human review. The main findings:

- **OpenAI's 7/8 method is exhausted.** Its boundary comes from the order-6 apparatus (Gauss sums and cubic theta
  coefficients exist in usable form only there), not from a tunable constant. With proved inputs, its best value is exactly
  Liu's 0.874957.
- **The strip survey.** No known technique gives a half-plane strong enough to beat the numerical Λ bounds.
- **Effective Newman: NO-GO** on Dobner's route.
- **Gates 0–10** tested whether any geometry could supply Weil's sign for ℚ: function-field controls, automorphic forms,
  Connes–Consani's arithmetic site, tropical and local "star" constructions, eighteen candidate geometries, and the
  archimedean end of the adele class space. Every candidate either reduced to Weil's criterion or failed. The common pattern
  is **modulus versus phase**: every sign mechanism found controls the size √p of the Frobenius return maps, never their
  phases.
- **SCALE-1.** A three-way obstruction: the needed cohomology, nef cone and non-toric H¹ never coexist in any known object.
- **LY-1.** Torus-wide Lee–Yang conditions cannot single out ζ, because they are invariant under twisting the primes'
  phases.
- **TWOLEG.** The search for a "two-leg" object over ℚ, an analogue of C × C. Two gates came back negative. Weil's own
  sign on C × C constrains only the size of the Frobenius eigenvalues, and the phases are pinned by intersection numbers
  derived from geometry. The surface around Borger's Witt-vector "square" turns out to be the ruled cyclotomic surface,
  with no derived Δ². The missing piece is an arithmetic analogue of the absolute point Spec k over which
  Spec ℤ × Spec ℤ would be a genuine product.

## 8. Papers

| | paper | DOI |
|---|---|---|
| 1 | *A kernel-checked bound Λ ≤ 9/32 for the de Bruijn–Newman constant from OpenAI's quasi-Riemann hypothesis* (v1.1.0 adds Λ ≤ 0.2811857), [`papers/qrh-debruijn-newman/`](papers/qrh-debruijn-newman/) | [10.5281/zenodo.23269134](https://doi.org/10.5281/zenodo.23269134) (all versions; v1.1.0: 10.5281/zenodo.23324360) |
| 2 | *Newman's conjecture, kernel-checked: Λ ≥ 0 for the de Bruijn–Newman constant in Lean 4 along Dobner's proof* (v1.1.0 adds the Selberg class), [`papers/newman-lambda-nonneg/`](papers/newman-lambda-nonneg/) | [10.5281/zenodo.23287832](https://doi.org/10.5281/zenodo.23287832) (all versions; v1.1.0: 10.5281/zenodo.23292885) |
| 3 | *A kernel-checked Riemann–Roch-square criterion for the Riemann Hypothesis*, [`papers/rr-square-criterion/`](papers/rr-square-criterion/) | [10.5281/zenodo.23352050](https://doi.org/10.5281/zenodo.23352050) (this repository; v1.0.0: 10.5281/zenodo.23352051) |

**arXiv: staged, not yet submitted.** Each paper has an arXiv source package and a submission sheet, and the author
submits them. See [`papers/ARXIV_STAGING.md`](papers/ARXIV_STAGING.md). No arXiv identifiers exist yet; cite the Zenodo DOIs.

## 9. How to build and check

The trust model is the usual one for formal proofs: **the Lean kernel is the only trusted component.** You still have to read
the statements and decide whether they say what the prose says. [`formalization/README.md`](formalization/README.md) gives
each headline theorem in plain words next to its exact Lean name.

```sh
scripts/materialize.sh          # clone the development repository at the pinned commit and check that telperion/
                                # differs from it only in comments, docstrings and listed prose

cd telperion/examples/weil_form_enclosure/lean
lake exe cache get && lake build
lake env lean AxiomGuardRRSquare.lean   # every line: [propext, Classical.choice, Quot.sound] or a subset
```

The other islands work the same way. `.github/workflows/verify.yml` builds the RR-square, dbn and rvm_bridge islands on
every change. On manual dispatch it also builds the HODGE-1 certificates and the two half-plane bridges, which take hours.
`.github/workflows/telperion.yml` runs the engine's test suite.

The repository is laid out as follows:

```
papers/          the three papers (LaTeX, PDF, build script, arXiv package and sheet)
docs/            PROGRESS.md: the complete record
formalization/   the theorem index and the pinned source commit
telperion/       the Telperion engine, its tests, and six Lean islands under telperion/examples/
scripts/         materialize.sh, the copy checker, the axiom checker
CENSORING.md     every comment that was reworded in the Telperion copy, and why
```

OpenAI's and Liu's Lean code is never stored here. The island scripts fetch it at pinned commits and check every file by hash.

## 10. Provenance, AI assistance and review status

The Lean developments and the engine were written in the author's development repository, Arda
(<https://github.com/DrMurphyIsIn/Arda>). They are copied here from commit `50b100025` of 2026-10-13. References to an
unrelated private project and private file paths were reworded in comments only. [`CENSORING.md`](CENSORING.md) lists every
file, and `scripts/check_telperion_copy.py` proves mechanically that no code changed.

All of this work was produced with extensive use of AI coding assistants (Claude, Anthropic), running as parallel sessions
under the author's direction: the Lean, the certificates, the engine, the audits, the research notes and the papers. The
review is mostly AI review, and we want to be precise about how much:

- **Human read-back.** The ten de Bruijn–Newman and zero-free half-plane statements behind 0 ≤ Λ ≤ 0.2811857 and the Selberg
  class were read back by the author, a human. This is the strongest review here.
- **AI read-back by a separate session.** Eleven statements, including the HODGE-1 frontier and the RR-square chain.
- **AI read-back by the authoring session.** The remaining 109 registry statements. The registry labels them `unverified`.
- **No external review.** No mathematician outside the project has reviewed any of it, and none of it has been refereed.
- **The research notes** have had no human review.

The mathematics being formalized is, in the main, other people's: de Bruijn, Newman, Rodgers and Tao, Dobner, Weil, Bombieri
and Lagarias, Li, Connes and Consani, OpenAI, Baiying Liu, Alpöge and Furman. [`NOTICE.md`](NOTICE.md) gives the credits.

## Licensing and citing

The mathematics (Lean, scripts, certificates) is Apache-2.0. The papers and prose are CC-BY-4.0. The Telperion engine is under
the Business Source License 1.1, free for research, teaching and evaluation. See [`LICENSING.md`](LICENSING.md) and
[`CITATION.cff`](CITATION.cff).
