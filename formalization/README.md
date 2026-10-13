# The formalization: what is kernel-checked, where, and on what

None of this is a proof of the Riemann Hypothesis. RH is open. Every theorem below is either unconditional
and strictly weaker than RH, or conditional on a hypothesis that is itself open (equivalent to RH, or
stronger). The status column says which.

## Where the Lean lives

All the Lean sources are in `telperion/examples/`, in six islands. Each island is a separate Lake project with
its own Lean and Mathlib pins, because the upstream projects they build on use different pins:

| island | Lean | depends on (fetched by Lake or by the island's script, never vendored) |
|---|---|---|
| `dbn` | v4.34.0-rc1 | Mathlib `de5ce8a9`, LiCriterion `35df682f` (Apache-2.0) |
| `oai_qrh_bridge` | v4.34.1 | openai/math `adc7f124` (Apache-2.0), fetched and hash-checked by `materialize.sh` |
| `liu_dbn_bridge` | v4.34.1 | openai/math `adc7f124` and Baiying Liu's Lean `7d10420d`, fetched by `liu_materialize.sh` |
| `rvm_bridge` | v4.33.0-rc2 | Zeta23 (anthropics/formal-math `fbdc36bb`, Apache-2.0) |
| `weil_form_enclosure` | v4.32.0 | Mathlib v4.32.0 |
| `quasicrystal` | v4.32.0 | Mathlib v4.32.0 (supporting work; no headline theorem below) |

The files are those of the Arda development repository at commit `8fc6a33e6eede73bdfee31c130aa0aa16841c594`
(`ARDA_SOURCE`), with comments reworded in ten Lean files (`../CENSORING.md`). `../scripts/materialize.sh`
clones that commit and checks the claim: every Lean file must be byte-identical or identical once comments
are stripped. The theorems, definitions and proofs are untouched.

"Standard axioms" below means `#print axioms` lists a subset of `[propext, Classical.choice, Quot.sound]`: no
`sorryAx`, no `Lean.ofReduceBool` (so no `native_decide`), and no added axioms. "Judged" means the Arda missions
registry's Comparator job built a challenge whose *type* is the registered statement, imported only the
upstream library, and replayed the proof through Lean's kernel. Where it says nanoda, a second, independent
kernel replayed it as well.

## Headline theorems

This is the short index. `../docs/PROGRESS.md` has every result of the programme, including those on islands not vendored
here, and the full registry inventory.

### The de Bruijn–Newman constant: 0 ≤ Λ ≤ 0.2811857

| theorem (exact Lean name) | file | statement | status | axioms / checks |
|---|---|---|---|---|
| `dbn_newman` | `dbn/lean/DBNNewman.lean` | `∀ t < 0, ∃ z, DBN.H t z = 0 ∧ z.im ≠ 0` (Newman's conjecture, Λ ≥ 0; Rodgers–Tao's theorem along Dobner's proof) | unconditional | standard; judged, nanoda (run 38062595826) |
| `selberg_newman` | `dbn/lean/DBNSelbergNewman.lean` | the same for every `F : DBNSelberg.ExtSelbergData` (Dobner's extended Selberg class) | unconditional (for each element of the class) | standard; judged, nanoda (run 38133404121) |
| `selberg_newman_sharp` | `dbn/lean/DBNSelbergSharpStrip.lean` | the same for every `S : DBNSelberg.SelbergSharp` | unconditional (for each element of the class) | standard; judged, nanoda (run 38133404121) |
| `dbn_newman_of_sharp` | `dbn/lean/DBNSelbergSharpZeta.lean` | ζ as an instance of the sharp class recovers `dbn_newman` | unconditional | standard |
| `dbn_debruijn_real_zeros` | `dbn/lean/DBNHadamardApprox.lean` | `∀ t ≥ 1/2, ∀ z, DBN.H t z = 0 → z.im = 0` (de Bruijn 1950, Λ ≤ 1/2) | unconditional | standard; judged, nanoda (run 36707277853) |
| `dbn_real_zeros_of_qrh_unconditional` | `oai_qrh_bridge/lean/ArdaDBNUnconditional.lean` | `∀ t ≥ 9/32, ∀ z, DBN.H t z = 0 → z.im = 0` (Λ ≤ 9/32, from OpenAI's zero-free half-plane Re s > 7/8) | unconditional; trusts the pinned openai/math tree as code | standard; judged, nanoda (run 37955041118) |
| `dbn_real_zeros_of_liu_unconditional` | `liu_dbn_bridge/lean/ArdaDBNLiu.lean` | the same for `t ≥ 2((1507 − 2√921)/1653 − 1/2)²` (from Liu's half-plane) | unconditional; trusts the pinned openai/math and Liu trees as code | standard; judged, nanoda (run 38179118143) |
| `dbn_real_zeros_ge_2811857` | `liu_dbn_bridge/lean/ArdaDBNLiu.lean` | the same for `t ≥ 2811857/10000000` (Λ ≤ 0.2811857) | unconditional, as above | standard; judged, nanoda (run 38179118143) |

Together: 0 ≤ Λ ≤ 0.2811857, kernel-checked. Λ = 0 is equivalent to RH and is not proved. The numerical
bounds Λ ≤ 0.22 (Polymath15) and Λ ≤ 0.2 (Platt–Trudgian) are better and are not formalized here.

### Weil's criterion on pole-free tests, and the HODGE-1 window

Notation: `IsWeilTest g` means `g : ℝ → ℂ` is smooth with compact support; `weilForm (autocorr g)` is Weil's
explicit-formula functional on the autocorrelation of `g`; `PoleFree g` (= `Hodge1.PoleFree2 g`, definitionally)
means `paperFT g (±i/2) = 0`, so that both pole terms vanish. `RiemannHypothesis` is Mathlib's definition.

| theorem | file | statement | status | axioms / checks |
|---|---|---|---|---|
| `RvMBridgePF.weil_positivity_poleFree_implies_rh` | `rvm_bridge/lean/PFConverseC.lean` | Weil positivity on every pole-free test ⇒ `RiemannHypothesis` | **conditional** (the hypothesis is equivalent to RH) | standard; registry node `MM_polefree_weil_converse` granted (#729), AI read-back by a separate session, Comparator record not yet made |
| `RvMBridgePF.rh_iff_poleFree_weil_positivity` | `rvm_bridge/lean/PFConverseC.lean` | `RiemannHypothesis ↔` Weil positivity on every pole-free test | an equivalence (a reformulation) | standard; CI guard, not judged |
| `Hodge1.re_weilForm_eq_archW_sub_prime` | `rvm_bridge/lean/Hodge1_Reduction.lean` (registry shape `Hodge1_RegOnePrime.lean`) | exact one-prime identity on the window 2L ≤ log 3 | unconditional | standard; judged, nanoda (run 38402969515) |
| `Hodge1.weil_positivity_poleFree2_window45` | `rvm_bridge/lean/Hodge1_Window45.lean` | Weil positivity for pole-free tests supported in [−L, L], L ≤ 9/20 | unconditional (a finite-window statement) | standard; judged, Lean kernel only (heavy certificates; run 38404702485) |
| `Hodge1.weil_positivity_poleFree2_window5493` | `rvm_bridge/lean/Hodge1_Window5493.lean` | the same for L ≤ 5493/10000 (just below (log 3)/2; p = 2 the only prime) | unconditional (a finite-window statement) | standard; judged, Lean kernel only (run 38404695545) |
| `Hodge1.rh_iff_poleFree2_outside_window5493` | `rvm_bridge/lean/Hodge1_RHReduction.lean` | `RiemannHypothesis ↔` Weil positivity for every pole-free test whose support is **not** inside [−0.5493, 0.5493] | an equivalence: the frontier, not progress on RH | standard; judged, Lean kernel only (run 38404699182) |

The window theorems are verification on a fixed finite window; they say nothing about zeros of ζ. The last
row is the honest frontier: what remains is exactly Weil positivity for tests reaching beyond that window,
which is RH.

### The Riemann–Roch-square criterion (conditional)

| theorem | file | statement | status | axioms / checks |
|---|---|---|---|---|
| `RRSquare.hodge_index` | `weil_form_enclosure/lean/RRSquare.lean` | the RR axioms with a degree bound `h0 ≤ β(deg)` imply the Hodge index (Grothendieck's argument) | unconditional (abstract linear algebra) | standard; CI guard (13 anchors) |
| `RRSquare.hodge_index_of_domain` | same | the same with "no zero divisors" in place of the degree bound | unconditional (abstract) | standard |
| `RRSquare.countermodel` | same | without the degree-bound/domain clause, the axioms have a model violating the Hodge index | unconditional | standard |
| `RRSquare.collapse` | same | with `Div = V`, the bounded axioms are satisfiable iff the Hodge index holds (so an existence statement is circular; the content must be a construction) | unconditional | standard |
| `RRSquare.FF.G2F5_hodge`, `G2F5_model`, `FK3_*`, `FK2_*` | `weil_form_enclosure/lean/RRSquareFF.lean` | function-field instances: a genus-2 curve over F₅ and two fakes | unconditional (finite) | standard |
| `RRSquare.weil_positive_of_rr` | `weil_form_enclosure/lean/RRSquareLink.lean` | RR-square on one window ⇒ Weil positivity for the pole-free tests in it | **conditional** on the window | standard |
| `RvMBridgePF.rh_of_rr_windows` | `rvm_bridge/lean/PFConverseC.lean` | a family of RR-square windows covering every pole-free test ⇒ `RiemannHypothesis` | **conditional**: no such family has been constructed | standard; node `MM_rr_windows_imply_rh` granted (#729), AI read-back by a separate session, Comparator record not yet made |

The registry shapes of the five RR-chain theorems (`rr_square_hodge_index`, `rr_square_hodge_index_domain`,
`rr_square_collapse`, `polefree_weil_converse`, `rr_windows_imply_rh`) are in `rvm_bridge/lean/RegRRChain.lean` and were
granted on 2026-10-13 (#727-#729). The converse direction (RH ⇒ such a family exists, trivially, by the collapse lemma;
`rr_windows_of_rh`, `rh_iff_exists_rr_windows` in `PFConverseD.lean`) is in open Arda PR #726, not in this snapshot, and is not
claimed here.

## Checking it yourself

`.github/workflows/verify.yml` does all of this on GitHub-hosted runners; the commands are the same locally.

```sh
scripts/materialize.sh                          # clone Arda at the pin; check the copy (comments-only diff)

cd telperion/examples/weil_form_enclosure/lean  # each of these three fits Arda CI's 90-minute hosted-runner budget
lake exe cache get && lake build
lake env lean AxiomGuardRRSquare.lean           # 13 lines, each [propext, Classical.choice, Quot.sound] or a subset

cd ../../dbn/lean
lake exe cache get && lake build
lake env lean AxiomGuardDBN.lean | grep -E "dbn_newman|selberg_newman|dbn_debruijn_real_zeros"

cd ../../rvm_bridge/lean                        # Zeta23 compiles from source
lake exe cache get && lake build
lake env lean AxiomGuardRvMBridge.lean | grep RvMBridgePF
while read -r m; do [ -n "$m" ] && lake build "$m"; done < hodge1_heavy_modules.txt   # one at a time; each <= 10.4 GB RSS (measured)
lake env lean Hodge1_Guard.lean

cd ../../oai_qrh_bridge && ./materialize.sh     # then see its README (several CPU-hours cold)
cd ../liu_dbn_bridge && ./liu_materialize.sh    # then see its README
```

The Comparator challenges and the registry records live in the development repository
(`telperion/missions/` at the pinned commit); the two earlier release repositories,
[qrh-debruijn-newman](https://github.com/DrMurphyIsIn/qrh-debruijn-newman) and
[newman-lambda-nonneg](https://github.com/DrMurphyIsIn/newman-lambda-nonneg), carry the judge bundles and CI
transcripts for the de Bruijn–Newman results.
