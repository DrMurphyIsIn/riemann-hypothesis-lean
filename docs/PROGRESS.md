# Progress record: everything done on the Riemann Hypothesis programme to date

This document is the complete record behind the repository's README. It was checked against the Arda development
repository at commit `50b1000254c6bb74bf12d21fa66483bd9fc14aeb` (2026-10-13), the commit `telperion/` is copied from. Every
"merged" below is a merge into Arda's `main` that can be found in its history. Every theorem name was found in the source at
that commit. Anything not on `main` is marked as such.

**The Riemann Hypothesis is open. Nothing here proves it.** In the development repository's own bookkeeping, the flag
`conjecture1_proved` is `False` and every document repeats it.

Some vocabulary used throughout:

- **Island.** A self-contained Lean 4 project under `telperion/examples/<name>/lean`, with its own Lean and Mathlib pins. Six
  islands are copied into this repository (`dbn`, `oai_qrh_bridge`, `liu_dbn_bridge`, `rvm_bridge`, `weil_form_enclosure`,
  `quasicrystal`). Islands marked † below live only in the development repository (`li_positivity`, `zeta_reflection`,
  `zeta_zero_localization`, `axiom_metaplectic`). They were left out of this copy because of their size: one of them has
  27,000 generated files.
- **Standard axioms.** `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound` (or fewer). So there is no
  `sorry`, no `native_decide` (`Lean.ofReduceBool`), and no added axiom. This holds for every theorem named in this document
  unless stated otherwise. CI checks it with an axiom guard on every island.
- **Registry node, grant, judge.** The development repository keeps a missions registry. Each node is a formal statement with
  a status, a proof artifact and a provenance record. "Granted" means the node passed the registry's gate, which checks
  hashes of the statement and the artifact. "Judged" means Comparator built a challenge whose *type* is the registered
  statement, importing only the upstream libraries, and replayed the proof through Lean's kernel. "nanoda" means a second,
  independent kernel replayed it as well. "Lean kernel only" is used for nodes whose certificates are too heavy for nanoda.
- **Read-back.** A reader checks that the formal statement says what its title claims, which the kernel cannot check. The
  read-back column says who read it:
  - **human (author)**: the author's own operator read-back.
  - **AI, separate session**: an AI read-back by a different AI session from the one that wrote the proof.
  - **AI, not independent**: written by, or by a sub-agent of, the session that wrote the proof. Most early nodes are
    in this category, and the registry itself records them as `independence = "unverified"`.

## 1. Where RH stands

RH says that every non-trivial zero of ζ lies on Re s = 1/2. It is open. This programme has produced three kinds of thing,
and it helps to keep them apart:

1. **Unconditional theorems strictly weaker than RH.** Bounds on the de Bruijn–Newman constant, positivity of Weil's form on
   finite windows, zero-free regions, the verification that all zeros up to height 8000 lie on the line, formalizations of
   classical theorems.
2. **Equivalences and reductions.** Kernel-checked statements of the form "RH ⇔ X" or "X ⇒ RH". They are useful because they
   pin down exactly what is open. They are not progress on RH, since X is as hard as RH.
3. **Research notes, including negative results.** Measurements and literature studies that ruled routes out. These are
   not proofs, and most have had no human review.

The development repository's own assessment says it bluntly. Every proved item is a finite-window statement, a converter
applied to someone else's half-plane, or a formalization of known mathematics, and none of it touches the hard part of RH.

## 2. Headline kernel-checked results

### 2.1 The de Bruijn–Newman constant: 0 ≤ Λ ≤ 0.2811857

De Bruijn deformed Riemann's ξ along the backward heat equation into a family H_t (here `DBN.H t`). Newman showed that a
constant Λ exists with all zeros of H_t real exactly for t ≥ Λ. RH is Λ ≤ 0, and Rodgers and Tao proved Λ ≥ 0 (2018). So RH is
exactly Λ = 0.

| result | Lean name | file (island) | merged | judged | read-back |
|---|---|---|---|---|---|
| **Λ ≥ 0** (Newman's conjecture; Rodgers–Tao's theorem, formalized along Dobner 2020) | `dbn_newman : ∀ t < 0, ∃ z, DBN.H t z = 0 ∧ z.im ≠ 0` | `dbn/lean/DBNNewman.lean` | #679 (ddf2ecff0) | nanoda, run 38062595826 | human |
| **Λ ≤ 9/32**, from OpenAI's zero-free half-plane Re s > 7/8 | `dbn_real_zeros_of_qrh_unconditional : ∀ t ≥ 9/32, ∀ z, DBN.H t z = 0 → z.im = 0` | `oai_qrh_bridge/lean/ArdaDBNUnconditional.lean` | #662, #666, #667 (records #669) | nanoda, run 37955041118 | human |
| **Λ ≤ 0.2811857**, from Baiying Liu's improved half-plane Re s > (1507 − 2√921)/1653 ≈ 0.874957 | `dbn_real_zeros_of_liu_unconditional` (exact threshold 2(θ − 1/2)²), `dbn_real_zeros_ge_2811857` (t ≥ 2811857/10⁷) | `liu_dbn_bridge/lean/ArdaDBNLiu.lean` | #692, #697, #698 | nanoda, run 38179118143 | human |
| the converter: a zero-free half-plane Re s > θ gives real zeros for t ≥ 2(θ − 1/2)² | `dbn_real_zeros_of_zeta_halfplane`, `dbn_real_zeros_of_qrh` | `dbn/lean/DBNZeroFreeHalfplane.lean` | #662 | nanoda, run 37955041118 | human |
| OpenAI's half-plane, re-exported with its binder closed | `qrh_seven_eighths` (proof entirely OpenAI's `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`) | `oai_qrh_bridge/lean/ArdaQRHBridge.lean` | #662 | nanoda, run 37955041118 | human |
| Liu's half-plane, with the pole at s = 1 closed | `liu_zeta_zero_free` | `liu_dbn_bridge/lean/ArdaLiuBridge.lean` | #692 | nanoda, run 38179118143 | human |

Some context on these numbers:

- Λ ≤ 0.2811857 is weaker than the best numerical bounds: Λ ≤ 0.22 (Polymath15) and Λ ≤ 0.2 (Platt–Trudgian). Neither of
  those is formalized.
- OpenAI's and Liu's code is not in this repository. The two bridge islands fetch it at pinned commits and check every file
  by hash. Before the bridge was built, a parallel AI session replayed OpenAI's four quasi-Riemann-hypothesis challenges
  through Comparator with nanoda switched on. Both kernels accepted all four (not sandboxed).
- A separate study, recorded under §7, found that Liu's θ is exactly the best that OpenAI's method can give with its proved
  inputs.

### 2.2 Newman's conjecture for the extended Selberg class

Dobner proved Newman's conjecture for every element of the extended Selberg class, and that theorem is formalized in full.
The class is stated as a Lean structure, and ζ is the control instance that recovers `dbn_newman`. Merged as #682
(c1b2a013b).

| Lean name | file | judged | read-back |
|---|---|---|---|
| `selberg_newman (F : DBNSelberg.ExtSelbergData) : ∀ t < 0, ∃ z, F.flow t z = 0 ∧ z.im ≠ 0` | `dbn/lean/DBNSelbergNewman.lean` | nanoda, run 38133404121 | human |
| `selberg_newman_sharp (S : DBNSelberg.SelbergSharp)`, the class S♯ as Kaczorowski–Perelli define it | `dbn/lean/DBNSelbergSharpStrip.lean` | nanoda, run 38133404121 | human |
| `dbn_newman_of_sharp`: ζ as an element of S♯ recovers `dbn_newman` | `dbn/lean/DBNSelbergSharpZeta.lean` | axiom guard only | — |

One simplification remains in the definition of `SelbergSharp`: the finite-order condition is stated on Re s ≥ 1/2. No
Dirichlet L-function instance was attempted.

### 2.3 De Bruijn's Λ ≤ 1/2, Hadamard factorisation, and the heat-flow foundations

| result | Lean name | file | merged | judged |
|---|---|---|---|---|
| de Bruijn 1950: every zero of H_t is real for t ≥ 1/2 | `dbn_debruijn_real_zeros` | `dbn/lean/DBNHadamardApprox.lean` | #608 | nanoda, run 36707277853 |
| Hadamard factorisation, even case of order < 2 | `DBN.evenHadamardData_of_order_lt_two` | `dbn/lean/DBNHadamard.lean` | #608 | axiom guard |
| parametric de Bruijn; the up-set property | `dbn_debruijn_parametric`, `dbn_real_zeros_upset` | `dbn/lean/DBNM1Parametric.lean` | yes | nanoda (granted) |
| H_0 = ξ/8 | `dbn_H0_eq_xi` | `dbn/lean/DBNXi.lean` | yes | nanoda |
| RH ⇔ all zeros of H_0 real; RH ⇔ all zeros of H_t real for every t ≥ 0 | `dbn_rh_iff_H0_real_zeros`, `dbn_rh_iff_real_zeros_nonneg_t` | `dbn/lean/DBNRealZerosIffFinal.lean`, `DBNM1RHIff.lean` | yes | nanoda |

The read-backs for these are AI, not independent.

### 2.4 Effective Theorem 4

Dobner's Theorem 4 approximates H at negative time by a Dirichlet-series profile above a height Y. Here it is made explicit:
`DBNSaddle.theorem4_explicit`, with Y = `Yeff c x₀ ε` in closed form, and `DBNSaddle.theorem4_fully_explicit`. Both are in
`dbn/lean/DBNTheorem4Effective.lean`, merged with #682, and their axioms are guarded.

The note that comes with them (Arda `telperion/docs/EFFECTIVE_THEOREM4_2026-10-10.md`) records a negative result:
**an effective Newman theorem as t → 0⁻ is a NO-GO on Dobner's route.** The Bohr-almost-periodicity step is doubly
exponential in 1/|t|, and the zero it produces has no explicit location.

## 3. Criteria and reductions (conditional; labelled)

Everything in this section is either an equivalence with RH or an implication whose hypothesis is open.

### 3.1 Weil's criterion, kernel-checked, including the pole-free converse

| statement | Lean name | file | merged | status |
|---|---|---|---|---|
| RH ⇒ Weil positivity (forward half) | `RvMBridge5.rh_implies_weil_positivity` | `rvm_bridge/lean/E6Bridge5.lean` | #593–#598 series | judged, nanoda; AI read-back, not independent |
| Weil positivity on Hermitian autocorrelations ⇒ RH (Weil 1952; Bombieri 2000) | `RvMBridge9.weil_positivity_implies_rh` | `rvm_bridge/lean/E6Bridge9.lean` | same | judged, nanoda |
| the registry's goal statement ⇔ RH (Weil's criterion as a dictionary) | `RvMBridge9.zeta_comb_membership_iff_rh` | `rvm_bridge/lean/E6Bridge9.lean` | same | judged, nanoda |
| **Weil positivity on pole-free tests ⇒ RH** | `RvMBridgePF.weil_positivity_poleFree_implies_rh` | `rvm_bridge/lean/PFConverseC.lean` | #712 (ed3ae9349) | **conditional**; registry node `MM_polefree_weil_converse` granted (#729), AI read-back by a separate session (#728), Comparator record not yet made |
| RH ⇔ Weil positivity on pole-free tests | `RvMBridgePF.rh_iff_poleFree_weil_positivity` | same | #712 | equivalence |

"Pole-free" means that the transform of the test function vanishes at ±i/2, which kills both pole terms of the explicit
formula. The converse needed an approximation of the Gaussian test family by pole-free tests (`RvMBridgePF.weighted_approx`)
and a weighted dominance estimate (`RvMBridgePF.weighted_dominance`), both in `PFConverseA/B.lean`.

Other RH equivalences on the same island, all merged, judged with nanoda, and read back by AI (not independent):

- RH ⇔ Gaussian positivity in two real parameters: `RvMBridge10.rh_iff_gaussian_positivity`.
- RH as a prime-side inequality with no zeros in it: `RvMBridge10.rh_iff_gaussian_prime_le_arch`.
- The "wall map": `RvMBridge13.rh_iff_gaussian_positivity_above_lam₀`.
- The theta face: `RvMBridge17.rh_iff_theta_positivity` and `RvMBridge17.rh_iff_thetaWidths_eq`.

### 3.2 The Riemann–Roch-square criterion and its converse

For curves over finite fields, Weil's proof runs through the Hodge index on C × C, which follows from Riemann–Roch on the
surface. The RR-square criterion states abstractly what an analogue over ℚ would have to supply, and checks the logic.

| statement | Lean name | file | merged | status |
|---|---|---|---|---|
| RR axioms + degree bound ⇒ Hodge index | `RRSquare.hodge_index` (and the registry shape `rr_square_hodge_index`) | `weil_form_enclosure/lean/RRSquare.lean`; `rvm_bridge/lean/RegRRChain.lean` | #711 (f9b35d7e2); registry shapes #727 | unconditional (abstract linear algebra); node `MM_rr_square_hodge_index` granted (#729), AI read-back by a separate session |
| the same with "no zero divisors" in place of the degree bound | `RRSquare.hodge_index_of_domain` / `rr_square_hodge_index_domain` | same | same | as above, node `MM_rr_square_hodge_index_domain` |
| without that clause the axioms have a model violating the Hodge index | `RRSquare.countermodel` | `RRSquare.lean` | #711 | unconditional |
| collapse: with Div = V, the axioms are satisfiable iff the Hodge index holds, so a bare existence claim is circular | `RRSquare.collapse` / `rr_square_collapse` | `RRSquare.lean`, `RegRRChain.lean` | #711, #727 | unconditional; node `MM_rr_square_collapse` granted |
| function-field instances: a genus-2 curve over F₅ satisfies the axioms; two fake zeta functions | `RRSquare.FF.G2F5_hodge`, `G2F5_model`, `FK3_*`, `FK2_*` | `RRSquareFF.lean` (generated) | #711 | unconditional |
| RR-square on one window ⇒ Weil positivity on its pole-free tests | `RRSquare.weil_positive_of_rr` | `RRSquareLink.lean` | #711 | **conditional** |
| **a family of RR-square windows covering every pole-free test ⇒ RH** | `RvMBridgePF.rh_of_rr_windows` / `rr_windows_imply_rh` | `PFConverseC.lean`, `RegRRChain.lean` | #712, #727 | **conditional**: no such family has been constructed; node `MM_rr_windows_imply_rh` granted (#729), AI read-back by a separate session |
| the trivial converse, RH ⇒ such a family exists, hence **RH ⇔ RR-square windows exist** | `RvMBridgePF.rr_windows_of_rh`, `RvMBridgePF.rh_iff_exists_rr_windows` (with `RvMBridgePF.RRSquare.collapse_bounded`, `lineWindow`) | `rvm_bridge/lean/PFConverseD.lean` | #726 (50b100025) | **equivalence**: the windows it builds are read off from Weil positivity and carry no geometry (no sections, no effective divisors, no ample class), so the existence form is Weil's criterion in another notation. The open content is a *construction* of windows defined without reference to the zeros. Axiom-guarded in CI; not a registry node |

The five RR-chain nodes were granted on 2026-10-13 (#729). Their Comparator records are pending from main's judge run. The
converse (#726) is what makes the equivalence literal, and it is also what shows that existence alone is empty: everything
turns on the construction.

### 3.3 The HODGE-1 frontier

HODGE-1 studied the first window where a prime enters Weil's form: test functions supported in [−L, L] with 2L ≤ log 3, so
that only p = 2 appears. The Lean was merged in #704 (one-prime reduction, window 9/20) and #710 (window 0.5493). The four registry
nodes were added and granted in #718, #720 and #722, and their Comparator records written in #724. Each has an AI read-back by
a separate session (#715, #721).

| statement | Lean name (registry theorem) | file | judged |
|---|---|---|---|
| exact one-prime identity on the pole-free window 2L ≤ log 3 | `Hodge1.re_weilForm_eq_archW_sub_prime` | `rvm_bridge/lean/Hodge1_Reduction.lean` (registry shape `Hodge1_RegOnePrime.lean`) | nanoda, run 38402969515 |
| pole-free Weil positivity for supports in [−L, L], L ≤ 9/20 | `Hodge1.weil_positivity_poleFree2_window45` | `Hodge1_Window45.lean` | Lean kernel only (heavy certificates), run 38404702485 |
| the same for L ≤ 5493/10000, just below (log 3)/2 | `Hodge1.weil_positivity_poleFree2_window5493` | `Hodge1_Window5493.lean` | Lean kernel only, run 38404695545 |
| **RH ⇔ pole-free Weil positivity for tests whose support is not inside [−0.5493, 0.5493]** | `Hodge1.rh_iff_poleFree2_outside_window5493` | `Hodge1_RHReduction.lean` | Lean kernel only, run 38404699182 |

The last row is the honest frontier: what is left is exactly RH. The window theorems are verification on a fixed window, not
a route. The development repository's assessment adds that the positivity margin on such windows *is* the sum over zeros, so
a window of half-width L verifies RH only up to a height of roughly e^{2L}.

### 3.4 Li's criterion and the Li / Weil dictionary (#593–#598)

The series #593–#598 (merged 2026-09-21/22) built the dictionary between Weil's form, Li's coefficients and the
Bombieri–Lagarias explicit formula on the `rvm_bridge` island. Its parts:

- the Bombieri–Lagarias explicit formula on Li's test class, `RvMBridge27.bl_explicit_formula`;
- the value identity, unconditional: `RvMBridge27.liValue`;
- the ξ partial fraction in derivative form, unconditional: `RvMBridge27.xi_logDeriv_deriv_eq`;
- Li's forward half, `RvMBridge15.rh_implies_liLimit_re_nonneg`;
- the "Li ladder": zeros on the line up to height T imply nonnegativity of the first Li coefficients, in a sharp form,
  `RvMBridge29.liLimit_re_nonneg_of_line_below_sharp`.

All are judged with nanoda, with AI read-backs that are not independent.

On the `li_positivity` island† there are more pieces:

- Li rungs 0..4 with no hypothesis: `RH_li_rungs_lt_five`.
- Twenty rung certificates, each **conditional** on a numerical enclosure: `RH_li_rung_certificates`.
- Rungs up to 25,128, conditional on the height-4000 certificates: `RH_li_rungs_of_height_4000_sharp`.

## 4. Weil positivity proved unconditionally on windows

Weil's form is shown positive outright on every test supported in a small window. These are finite-window statements. They
say nothing about zeros of ζ, and the registry titles say so.

| window | Lean name | file | merged | status |
|---|---|---|---|---|
| prime-free window 2L ≤ log 2, full test class, kernel-native certificate | `weil_positivity_prime_free_window` | `rvm_bridge/lean/KWin_Bridge.lean` | #604 and the KWin series | granted, judged (Lean kernel only); AI read-back, not independent |
| the earlier prime-free window L ≤ 1/10 (E6Bridge31–34) | `weil_positivity_window_tenth_of_prime_free` | `E6Bridge31–34.lean`, `KWin_Bridge.lean` | #604 | the node `MM_weil_positivity_window_tenth` is still a **draft** |
| past the first prime, 2L ≤ 4/5 (the p = 2 term present, accounted exactly) | `weil_positivity_window_two_fifths` | `KWin2_Bridge.lean` | yes | granted, judged (Lean kernel only) |
| 2L ≤ 9/10 and 2L ≤ 1 (L ≤ 1/2) | `weil_positivity_window_nine_twentieths`, `weil_positivity_window_half` | `KWin2_BridgeHeavy.lean` | on main | **heavy module (about 19 GB, about 50 CPU-minutes): not built by CI and not registered**; it checks locally, but there is no CI record |
| pole-free one-prime windows L ≤ 9/20 and L ≤ 0.5493 | see §3.3 | `Hodge1_*` | #704, #710 | granted, judged, recorded |
| Connes–Consani Corollary 2.3: archimedean positivity for every support (not Weil positivity: no primes) | `cc_cor_2_3` | `rvm_bridge/lean/ArchRegistry_CCCor23.lean` (stages `ArchS*`) | #699 | granted, judged (nanoda); AI read-back by a separate session |
| Gaussian windows: positivity for small widths, and a width 15,000 times larger | `RvMBridge11.re_weilForm_gauss_nonneg`, `RvMBridge30.gaussian_positivity_small_lam_3e3` | `E6Bridge11.lean`, `E6Bridge30.lean` | #593–#598 | judged, nanoda |

The Connes–Consani programme (#699) formalized the archimedean Sonin route. It includes certified prolate spheroidal data and
a spectral certificate. It is a formalization of known mathematics, made rigorous where the papers rely on floating-point
computation.

**Inputs from the explicit-formula and counting machinery** (all on `rvm_bridge`, merged, judged with nanoda):

- the corridor bound, `RvMBridge3.corridor_bound`;
- unconditional Riemann–von Mangoldt, `RvMBridge2.rvm_unconditional`;
- the limit explicit formula, `RvMBridge4.limit_explicit_formula`;
- the local count sum, `RvMBridge23.local_count_sum`;
- the strip derivative bound, `RvMBridge24.stripDerivBound`;
- no real zero in (0, 1), `RvMBridge25.noRealZeroInUnitInterval`.

These build on Zeta23 (Alpöge–Furman; anthropics/formal-math), which is a Lake dependency.

**Zhu's window inputs** (#606, merged) feed the reduction `RH_weil_window_floor_of_certified_block`, which is still a **draft**
node. The window floors `weil_window_floor_two_fifths` and `weil_window_floor_half` are the certified inputs.

## 5. Other formalizations bearing on RH

**Finite verification and kernel reflection** (`zeta_reflection`†, registry ANDURIL):

- **Every non-trivial zero with 0 < Im ρ ≤ 8000 lies on the line, with no hypothesis and no numerical oracle**:
  `Arb4_Compose_h8000.ladder_h8000_of_bands`. These are compact certificates in eight segments, 29 MB in all. The node is
  granted and judged (Lean kernel only), and an independent leanchecker replay covered all 164 modules.
- The same to height 1000 with nanoda: `AllZerosKernel_h1000.all_nontrivial_zeros_up_to_height_1000`.
- A zero in (14, 15) computed purely by the kernel: `ForgeFirstZeroKernel.first_zero_kernel`.
- No zero with 0 < Im ρ < 55/16: `HeightFloor.height_floor`.

This is finite verification. Classical numerical verification goes far higher.

**Zero-free regions and growth** (`li_positivity`†, all proved):

- the de la Vallée Poussin region, effective and self-contained: `RH_dlvp_zero_free_region`;
- the elementary region β ≤ 1 − c/γ⁵, and a polylog-improved region;
- the near-line bound |ζ(σ + it)| ≤ 6(1 + log|t|);
- Backlund's S(T) = O(log T);
- low-height boxes: every zero has |Im ρ| ≥ √3/2.

**The Dyson quasicrystal island** (`quasicrystal`, vendored here; registry MIRRORMERE):

- `LeeYangCore`, `KSConstruction`;
- `TwoFreqRigidity`: a two-frequency exponential sum is real-rooted iff its coefficients have equal modulus,
  `MM_twofreq_realrooted_iff`;
- `OfflineDiscs`, the torus-section ladder, `EulerFactorOffline` / `EulerFactorSectionOffline` (the Euler factor at p = 2,
  read on the critical line, is off-line: a negative control);
- `LeakageNode`, `SatakeDegreeTwo`, `DedekindQuadratic`, `LemmaO`;
- the unconditional statement that the zeta ordinates are not uniformly discrete,
  `RvMBridge.zeta_ordinates_not_uniformly_discrete`, on `rvm_bridge`.

All are proved and kernel-checked. Most were read back only by AI, not independently.

**BraggDefect** (`zeta_zero_localization`†):

- the finite-height explicit formula in diffraction form (`MM_bragg_bridge`);
- a certified defect witness: the all-on-line configuration has defect exactly 0, and an off-line pair drives it negative.
  Its last numerical hypothesis was discharged in the kernel by the `scaled_interval_eval` emitter (#689; node
  `MM_bragg_defect_witness_sie`, AI read-back by a separate session).

**The Euler-model strip** (`DBNEulerModelRH.lean`, **open PR #725, not merged**). It shows that the holomorphic finite
Euler-product model Z_X = E_X + χE_X(1 − s) has no zeros near the critical line above an explicit height. This is a
folklore-grade companion to Gonek's 2012 model theorem. A forward-citation search is still needed before any claim of novelty.

**The Axiom metaplectic island** (`axiom_metaplectic`†, #706). This is complementary-series positivity for PGL₂(ℂ):
`Arda.AxiomMetaplectic.compSeries_Ktype_eigenvalues`, for every 0 < ν < 1. It is classical representation theory, now
formal, built on AxiomMath's DedekindZetaZeroFree library. It is not in CI.

## 6. Verification infrastructure

- **The missions registry.** Statements, artifacts, read-backs, grants and Comparator records live in TOML files under
  `telperion/missions/` in the development repository. Arda's `telperion/docs/MISSIONS_HOWTO.md` and
  `AUDIT_INDEPENDENCE_2026-09-23.md` describe them.
  - The grant gate checks hashes of the statement and the artifact.
  - Since 2026-09-23 it refuses a read-back from the same session or identity as the author.
  - At that point an audit found that every earlier "blind" read-back had been a sub-agent of the authoring session. All
    117 earlier read-backs were relabelled `unverified`, and the relabelling is still in place.
- **The Comparator judge.** `missions-comparator.yml` builds, for each proved node, a bridge module whose type is the
  registered statement. It exports the environment, checks the axiom whitelist, and replays the proof in Lean's kernel and in
  nanoda. Heavy certificate nodes use a separate "heavy" job with the Lean kernel only. Every judged node above has a recorded
  run ID, and the log and head commit were checked when the record was written.
- **Independent replays of other groups' work.**
  - OpenAI's quasi-Riemann-hypothesis challenges: all four accepted by nanoda and Lean's kernel in a local replay.
  - Liu's Lean: replayed before composition.
  - AxiomMath's DedekindZetaZeroFree (Cureton–Thorner, hexagon:2610.00200): the proof replays with standard axioms, and both
    kernels accept it. But the shipped Challenge/Solution pair *fails* Comparator. Inside the library's imports,
    `NormedCommRing ℂ` elaborates through a different instance path (`instCommCStarAlgebraComplex`), and Comparator compares
    expressions syntactically, not up to definitional equality. Adding `attribute [-instance] instCommCStarAlgebraComplex`
    to the solution fixes it. The finding is recorded in Arda's `axiom_metaplectic/lean/README.md` and
    `telperion/research/watch/TRIAGE.md`.
- **Axiom guards.** Every island has an `AxiomGuard*.lean`. CI fails on `sorryAx`, on any axiom outside the standard three, on
  too few printed lines (so a guard that silently printed nothing cannot pass), and, on the main islands, on any proved
  registry node missing from the guard output.
- **The Telperion registry explorer.** <https://drmurphyisin.github.io/Arda/explorer/> is generated from the registry. It
  has a de Bruijn–Newman tab and a "Riemann's missing surface" tab, which presents the research report summarised in §7.

## 7. Research programme and negative results

**These are research notes, not proofs.** They are AI work from parallel sessions under the author's direction, and most of
them have had no human review. They are summarised because they record what was ruled out and why.

- **The sextic bottleneck of the 7/8 method** (#684, merged). The 7/8 boundary of OpenAI's zero-free method is set by the
  order k = 6 of its sextic apparatus: Gauss sums and Patterson's cubic theta coefficients exist in usable form only there.
  It is not a tuning constant. Within k = 6, sweeping every parameter shows 7/8 is a two-sided vertex. The best value
  reachable with proved inputs is exactly Liu's 0.874957 (the same √921). So Λ ≤ 0.2811856 is this route's limit. An earlier
  claim of 13/15 was withdrawn.
- **The strip survey** (56 sources). No published or preprint technique reaches a half-plane that would beat Λ ≤ 0.22 or 0.2.
  - Zero-density estimates and classical regions structurally cannot give a half-plane.
  - The only sub-0.85 route on paper rests on a sextic large-sieve conjecture that the literature expects to be false.
- **Effective Newman: NO-GO** on Dobner's route (§2.4).
- **Gate 0.** Finite Weil rungs are verification in disguise. The minimal eigenvalue on a window is the sum over zeros,
  decays like exp(−cL²), and shows no step when a prime enters. The Davenport–Heilbronn function, which has off-line zeros,
  passes every rung up to L ≈ 1.7. Pólya–type approximants and heat-flow averaging are blind to the Euler product.
- **Gates 1–10.** Each gate asked whether some geometry could supply Weil's sign for ℚ.
  - Gate 1: function-field controls, cone geometry, interpolation bases.
  - Gate 2: stacks of norms, polarized dynamics, Div¹.
  - Gate 3: archimedean polarization coupled to the primes.
  - Gates 4–5: automorphic offsets. Every construction puts ζ in the trivial, non-tempered slot, at integer shifts d ≥ 1.
  - Gate 6: transporting Weil's proof. It first fails at the Hodge index, which is how Conjecture RR-square (§3.2) arose.
  - Gates 7–8: Cartwright-style local stars, prime-edge complexes, the Connes–Consani square. All reduce to Weil's
    criterion or fail on content.
  - Gate 9: eighteen candidate geometries.
  - Gate 10: the archimedean end of the adele class space.

  The common finding, stated as **modulus versus phase**: every sign mechanism found controls the modulus √p of the Frobenius
  return maps, and none controls their phases, which is where the arithmetic lives. And no object found has both a sign and
  ζ's zeros as its derived spectrum.
- **SCALE-1: a three-way obstruction.** A similitude polarization is RR-square restated. Weil's Jacobian route needs three
  things at once:
  1. a cohomology where a connected scaling family acts with multiplier e^t;
  2. a nef cone preserved geometrically;
  3. a non-toric H¹.

  Every existing object supplies at most two. Ampleness of the relevant χ was proved to be equivalent to RH.
- **LY-1: torus Lee–Yang, NO-GO.** Lee–Yang / Hermite–Biehler conditions over the whole Bohr torus fail for ζ's own lifts.
  They are invariant under the unimodular twists z_p ↦ e^{iθ_p}z_p, so they cannot single out ζ. This gave the "twist guard"
  G5 that later candidates must pass. The heat flow acts as a Curie–Weiss coupling with no feature at Λ.
- **TWOLEG (in progress).** The search for a "two-leg" object over ℚ: an analogue of C × C with partial Frobenii, carrying a
  sign that constrains phases and not just moduli. Phase 0 is a landscape survey. Nothing has been concluded.

## 8. Papers and DOIs

| paper | DOI |
|---|---|
| *A kernel-checked bound Λ ≤ 9/32 for the de Bruijn–Newman constant from OpenAI's quasi-Riemann hypothesis* (v1.1.0 adds Λ ≤ 0.2811857) | concept 10.5281/zenodo.23269134; v1.1.0 10.5281/zenodo.23324360 |
| *Newman's conjecture, kernel-checked: Λ ≥ 0 … along Dobner's proof* (v1.1.0 adds the Selberg class) | concept 10.5281/zenodo.23287832; v1.1.0 10.5281/zenodo.23292885 |
| The Riemann–Roch-square criterion | not yet released |

## 9. How to build and check

See `formalization/README.md` and `.github/workflows/verify.yml`. `scripts/materialize.sh` checks this repository's copy
against the development repository. The four islands marked † are built from the development repository at the pinned commit.

## 10. Provenance, AI assistance and review

All of the Lean, the certificates, the engine, the audits, the research notes and the papers were produced with extensive use
of AI coding assistants (Claude, Anthropic), working as parallel sessions under the author's direction. The Lean kernel is
the only trusted component.

The honest summary of review:

- **Human read-back.** The ten de Bruijn–Newman and half-plane nodes (§2.1, §2.2) were read back by the author, a human
  operator. This is the strongest review anything here has had.
- **AI read-back by a separate session.** Eleven nodes: the four HODGE-1 nodes, the five RR-square chain nodes, the
  Connes–Consani corollary and the hypothesis-free Bragg defect witness. These are AI reviewing AI.
- **AI, not independent.** The remaining 109 proved nodes. The registry itself labels them `unverified`.
- **No external human review.** No mathematician outside the project has reviewed any of it, and none of it has been
  refereed.

## Appendix: the complete registry inventory

Generated from the registry at the pinned commit. Titles are the registry's own, abridged. † = island not vendored here.
"Comparator: not recorded" means the proof is kernel-checked and axiom-guarded in CI, but the node has no Comparator record.

### RH campaign (`missions/rh`)

67 proved nodes.

| node | judged theorem | artifact (under `telperion/examples/`) | Comparator (kernel, run) | read-back | registry title (abridged, verbatim) |
|---|---|---|---|---|---|
| `RH_backlund_s_log` | - | `li_positivity/lean/RvMBacklundLogCont.lean` † | not recorded | AI, not independent | Backlund S(T) = O(log T) carrying only zeta-nonvanishing on the segment: \|S(T)\| <= log((4T+19)/\|F_T(2)\|)/log(7/6) + 2 for T >= 4 |
| `RH_bl_closed_form_five_nonneg` | `RvMBridge28.archSide_add_finiteSide_five_re_nonneg` | `rvm_bridge/lean/E6Bridge28.lean` | nanoda (36707277853) | AI, not independent | BOMBIERI-LAGARIAS CLOSED FORM, RUNG 5, NO HYPOTHESIS (rvm_bridge island, E6Bridge28, 2026-09-21): 0 <= Re(archSide 5 + finiteSide 5), i.e. the explicit expression in gamm… |
| `RH_bl_explicit_formula` | `RvMBridge27.bl_explicit_formula` | `rvm_bridge/lean/E6Bridge27.lean` | nanoda (36707277853) | AI, not independent | The BOMBIERI-LAGARIAS EXPLICIT FORMULA on Li's test class (routes-roadmap B7-ii, the B6 -> B7 test-class extension of E8): for every n >= 1 the SYMMETRIC window sums sum_… |
| `RH_bl_explicit_formula_of_livalue` | `RvMBridge15.bl_explicit_formula_of` | `rvm_bridge/lean/E6Bridge15.lean` | nanoda (36707277853) | AI, not independent | B7 REDUCED (2026-09-21): the node RH_bl_explicit_formula holds verbatim GIVEN the named value obligation LiValue n : liLimit n = archSide n + finiteSide n (Bombieri-Lagar… |
| `RH_bl_explicit_formula_of_partial_fraction` | `RvMBridge19.bl_explicit_formula_of_partialFraction` | `rvm_bridge/lean/E6Bridge19.lean` | nanoda (36707277853) | AI, not independent | B7 (RH_bl_explicit_formula) holds GIVEN the derivative partial fraction of xi and no real zero in (0,1); with E6Bridge22 the partial fraction rests on LocalCountSum + Str… |
| `RH_bl_explicit_formula_of_strip` | `RvMBridge26.bl_explicit_formula_of_strip` | `rvm_bridge/lean/E6Bridge26.lean` | nanoda (36707277853) | AI, not independent | B7 (RH_bl_explicit_formula) MODULO STRIPDERIVBOUND ALONE (2026-09-21): the Bombieri-Lagarias explicit formula on Li's class holds given one remaining classical inequality… |
| `RH_bl_finite_multiset` | - | `li_positivity/lean/RvMBlFiniteMultiset.lean` † | not recorded | AI, not independent | Routes-roadmap B7-i (the Bombieri-Lagarias finite core): for a finite set of points avoiding 0 and 1 and symmetric under rho -> 1 - conj(rho), the Li-type sums Re sum (1 … |
| `RH_borel_caratheodory_deriv` | - | `li_positivity/lean/DlvpBCDeriv.lean` † | not recorded | AI, not independent | Borel-Caratheodory + Cauchy derivative bound: \|deriv h c\| <= 2M'/(R-r) from the real-part sup on a disk |
| `RH_companion_bragg_reduction` | - | `li_positivity/lean/RvMCompanionBraggLimit.lean` † | not recorded | AI, not independent | Route P D2b-3 CONDITIONAL reduction: the companion coefficient isolates as (boundaryLim - braggLim)/(2 pi i) - 1 - arch, GIVEN the three exhaustion/archimedean limit prim… |
| `RH_corridor_bound` | `RvMBridge3.corridor_bound` | `rvm_bridge/lean/E6Bridge3.lean` | nanoda (36707277853) | AI, not independent | The CORRIDOR BOUND (routes-roadmap E7 = A3 = B5 = D6, the unique four-consumer blocker): for every T >= 2 some height T' in [T, T+1] has a zero-free horizontal segment -1… |
| `RH_dbn_H0_eq_xi` | `dbn_H0_eq_xi` | `dbn/lean/DBNXi.lean` | nanoda (36707277853) | AI, not independent | Route C / C2 representation theorem: H_0(z) = (1/8) xi(1/2 + iz/2) for every complex z -- the heat-flow family at t = 0 is the Riemann xi function (Polymath15 eq. (3), Ti… |
| `RH_dbn_H0_zero_strip` | `dbn_H0_zero_strip` | `dbn/lean/DBNStrip.lean` | nanoda (36707277853) | AI, not independent | Route C, the C2-free zero strip: every zero of H_0 lies in the strip \|Im z\| <= 1. PROVED on the dbn island (DBNStrip) from the absolutely convergent half-plane via the … |
| `RH_dbn_debruijn_parametric` | `dbn_debruijn_parametric` | `dbn/lean/DBNM1Parametric.lean` | nanoda (36707277853) | AI, not independent | Route C M1a, parametric de Bruijn (de Bruijn 1950 Thm 13 / P15 Thm 3.2): if every zero of H_t0 has (Im z)^2 <= Y then for t >= t0 every zero of H_t has (Im z)^2 <= max(Y … |
| `RH_dbn_debruijn_real_zeros` | `dbn_debruijn_real_zeros` | `dbn/lean/DBNHadamardApprox.lean` | nanoda (36707277853) | AI, not independent | Route C / C3, de Bruijn 1950: for every t >= 1/2 every zero of H_t is real (Lambda <= 1/2). PROVED on the dbn island (DBNHadamardApprox: Hadamard factorisation of order <… |
| `RH_dbn_newman` | `dbn_newman` | `dbn/lean/DBNNewman.lean` | nanoda (38062595826) | human (author) | Newman's conjecture (Rodgers-Tao 2018), after Dobner 2020: for every t < 0 the heat-flowed H_t has a NON-REAL zero, i.e. Lambda >= 0 in the island's sInf-free vocabulary.… |
| `RH_dbn_real_zeros_ge_2811857` | `dbn_real_zeros_ge_2811857` | `liu_dbn_bridge/lean/ArdaDBNLiu.lean` | nanoda (38179118143) | human (author) | Rational headline: every zero of H_t is real for t >= 2811857/10^7 = 0.2811857 (> 2(B_new - 1/2)^2 = 0.2811856...), i.e. Lambda <= 0.2811857, kernel-checked, from RH_dbn_… |
| `RH_dbn_real_zeros_nine_thirtyseconds` | `dbn_real_zeros_of_qrh_unconditional` | `oai_qrh_bridge/lean/ArdaDBNUnconditional.lean` | nanoda (37955041118) | human (author) | Every zero of H_t is real for every t >= 9/32 (classically Lambda <= 9/32), UNCONDITIONAL in one environment: the dbn closure ported to OpenAI's pin composed with OpenAI'… |
| `RH_dbn_real_zeros_of_liu_unconditional` | `dbn_real_zeros_of_liu_unconditional` | `liu_dbn_bridge/lean/ArdaDBNLiu.lean` | nanoda (38179118143) | human (author) | Lambda <= 2(B_new - 1/2)^2 = (1867057 - 10888 sqrt 921)/5464818 = 0.2811856... for the de Bruijn-Newman constant, UNCONDITIONAL in one Lean environment at OpenAI's pin: L… |
| `RH_dbn_real_zeros_of_qrh` | `dbn_real_zeros_of_qrh` | `dbn/lean/DBNZeroFreeHalfplane.lean` | nanoda (37955041118) | human (author) | QRH hypothesis (zeta != 0 on Re s > 7/8, OpenAI's statement with the binder closed) => every zero of H_t is real for t >= 9/32 (conditional; not RH). dbn island. conjectu… |
| `RH_dbn_real_zeros_of_zeta_halfplane` | `dbn_real_zeros_of_zeta_halfplane` | `dbn/lean/DBNZeroFreeHalfplane.lean` | nanoda (37955041118) | human (author) | Zero-free half-plane theta for zeta => every zero of H_t is real for t >= 2(theta-1/2)^2 (conditional on the half-plane; not RH). dbn island, Route C. conjecture1_proved … |
| `RH_dbn_real_zeros_upset` | `dbn_real_zeros_upset` | `dbn/lean/DBNM1Parametric.lean` | nanoda (36707277853) | AI, not independent | Route C M1b, up-set property: if every zero of H_t0 is real then every zero of H_t is real for all t >= t0 (the Y = 0 case of M1a). conjecture1_proved = False |
| `RH_dbn_rh_iff_H0_real_zeros` | `dbn_rh_iff_H0_real_zeros` | `dbn/lean/DBNRealZerosIffFinal.lean` | nanoda (36707277853) | AI, not independent | Route C / C4: RH (AND_ladder grammar: every nontrivial zero in the open strip has real part 1/2) iff every zero of H_0 is real. PROVED unconditionally as an EQUIVALENCE (… |
| `RH_dbn_rh_iff_real_zeros_nonneg_t` | `dbn_rh_iff_real_zeros_nonneg_t` | `dbn/lean/DBNM1RHIff.lean` | nanoda (36707277853) | AI, not independent | Route C M1c, the sInf-free statement of the wall clause C10: RH (strip form) iff every zero of H_t is real for every t >= 0 (classically Lambda <= 0). An EQUIVALENCE; pro… |
| `RH_dbn_selberg_newman` | `selberg_newman` | `dbn/lean/DBNSelbergNewman.lean` | nanoda (38133404121) | human (author) | Newman's conjecture for the extended Selberg class (Dobner 2020, Theorem 1 in the form the dbn island states it): for every ExtSelbergData F (coefficients absolutely conv… |
| `RH_dbn_selberg_newman_sharp` | `selberg_newman_sharp` | `dbn/lean/DBNSelbergSharpStrip.lean` | nanoda (38133404121) | human (author) | Newman's conjecture for the extended Selberg class S^# itself (Dobner 2020, Theorem 1): for every SelbergSharp S (Dirichlet series absolutely convergent on Re s > 1 with … |
| `RH_dlvp_region_effective` | - | `li_positivity/lean/DlvpZetaRateEffective.lean` † | not recorded | AI, not independent | The de la Vallee Poussin region at the classical rate, EFFECTIVE constant (multiplicity-hypothesis form) |
| `RH_dlvp_zero_free_region` | - | `zero_free_bridge/lean/DlvpZetaZeroFree.lean` † | not recorded | AI, not independent | The SELF-CONTAINED effective dVP zero-free region (no multiplicity hypothesis; artifact on the v4.32 island) |
| `RH_li_forward_half` | `RvMBridge15.rh_implies_liLimit_re_nonneg` | `rvm_bridge/lean/E6Bridge15.lean` | nanoda (36707277853) | AI, not independent | LI'S CRITERION, FORWARD HALF, on the rvm_bridge island (2026-09-21): under Mathlib's RiemannHypothesis every paired Li coefficient is nonnegative (on the line \|1 - 1/rho… |
| `RH_li_ladder_height` | - | `li_positivity/lean/LiLadderHeight.lean` † | not recorded | AI, not independent | THE LI LADDER (li_positivity island, 2026-09-21): if every nontrivial zero with \|Im\| <= T (T >= 1) lies on the line, then Li rung n is nonnegative for every n + 1 <= 3 … |
| `RH_li_ladder_height_sharp` | - | `li_positivity/lean/LiLadderSharp.lean` † | not recorded | AI, not independent | THE LI LADDER, SHARPENED (li_positivity island, LiLadderSharp, 2026-09-22): zeros on the line up to T >= 1 give rung n for n + 1 <= 2 pi (T - 1/2); window lemma cos b = c… |
| `RH_li_ladder_liLimit` | `RvMBridge28.liLimit_re_nonneg_of_line_below` | `rvm_bridge/lean/E6Bridge28.lean` | nanoda (36707277853) | AI, not independent | THE LI LADDER IN THE B7 VOCABULARY (rvm_bridge island, E6Bridge28, 2026-09-21): if every nontrivial zero with \|Im\| <= T (T >= 1) is on the line then 0 <= Re(liLimit N) … |
| `RH_li_ladder_liLimit_sharp` | `RvMBridge29.liLimit_re_nonneg_of_line_below_sharp` | `rvm_bridge/lean/E6Bridge29.lean` | nanoda (36707277853) | AI, not independent | THE LI LADDER, SHARPENED (rvm_bridge island, E6Bridge29, 2026-09-22): zeros on the line up to T >= 1 give 0 <= Re(liLimit N) for N <= 2 pi (T - 1/2). Window lemma: for 3 … |
| `RH_li_ladder_reduction` | - | `li_positivity/lean/LiLadder.lean` † | not recorded | AI, not independent | The Li ladder as a reduction of RH to its tail: given a certified prefix, RH iff the infinite tail (proves NEITHER side) |
| `RH_li_neg_refutes_rh` | - | `li_positivity/lean/LiPositivity.lean` † | not recorded | AI, not independent | The falsifiability face: a certified NEGATIVE upper bound on any Li rung refutes RH via the upstream equivalence |
| `RH_li_rung0_kernel` | - | `li_positivity/lean/LiLadderHeight.lean` † | not recorded | AI, not independent | Routes-roadmap B2 (the hypothesis-free rung anchor): 0 <= Re(taylorCoeff riemannXi 0) with NO Arb enclosure hypothesis -- the first Li rung evaluated entirely in-kernel o… |
| `RH_li_rung_certificates` | - | `li_positivity/lean/LiPositivity.lean` † | not recorded | AI, not independent | Li ladder rungs 0..19 (20 emitted certificates, each conditional on its Arb enclosure hypothesis); statement = the topmost rung li_rung_19 |
| `RH_li_rungs_lt_five` | - | `li_positivity/lean/LiBoxRungs.lean` † | not recorded | AI, not independent | LI RUNGS 0..4 WITH NO HYPOTHESIS (li_positivity island, 2026-09-21): 0 <= Re(taylorCoeff riemannXi n) for n < 5, i.e. Li's lambda_1..lambda_5 nonnegative in the kernel wi… |
| `RH_li_rungs_of_height_4000` | - | `li_positivity/lean/LiLadderHeight.lean` † | not recorded | AI, not independent | LI RUNGS 0..18848 FROM THE HEIGHT-4000 CERTIFICATES (li_positivity island, 2026-09-21): under the exact conclusion shape of AllZeros_h4000 (all zeros with 0 < Im <= 4000 … |
| `RH_li_rungs_of_height_4000_sharp` | - | `li_positivity/lean/LiLadderSharp.lean` † | not recorded | AI, not independent | LI RUNGS 0..25128 FROM THE HEIGHT-4000 CERTIFICATES, SHARP (li_positivity island, 2026-09-22): under the tiled capstone's conclusion shape (conditional on its Arb bands),… |
| `RH_li_zero_sums_converge` | `RvMBridge15.liZeroSum_tendsto` | `rvm_bridge/lean/E6Bridge15.lean` | nanoda (36707277853) | AI, not independent | B7 CONVERGENCE HALF (2026-09-21, open lemma 2): for every n the SYMMETRIC window sums of Li's kernel over the nontrivial zeros converge as T -> infinity, to the absolutel… |
| `RH_limit_explicit_formula` | `RvMBridge4.limit_explicit_formula` | `rvm_bridge/lean/E6Bridge4.lean` | nanoda (36707277853) | AI, not independent | The LIMIT EXPLICIT FORMULA (routes-roadmap E8 = B6 = D6, the T -> infinity Guinand-Weil identity in diffraction form): for every smooth compactly supported g : R -> C, Su… |
| `RH_livalue` | `RvMBridge27.liValue` | `rvm_bridge/lean/E6Bridge27.lean` | nanoda (36707277853) | AI, not independent | THE BOMBIERI-LAGARIAS VALUE IDENTITY, UNCONDITIONAL (2026-09-21): liLimit n = archSide n + finiteSide n for every n >= 1. conjecture1_proved = False. |
| `RH_livalue_of_partial_fraction` | `RvMBridge19.liValue_of` | `rvm_bridge/lean/E6Bridge19.lean` | nanoda (36707277853) | AI, not independent | THE BOMBIERI-LAGARIAS VALUE IDENTITY, Taylor bookkeeping PROVED (2026-09-21): LiValue n (liLimit n = archSide n + finiteSide n) for every n >= 1, GIVEN the derivative par… |
| `RH_local_count_sum` | `RvMBridge23.local_count_sum` | `rvm_bridge/lean/E6Bridge23.lean` | nanoda (36707277853) | AI, not independent | LOCAL COUNT SUM DISCHARGED (2026-09-21): Sum m(rho)/(1 + (Im rho - a)^2) <= C(1 + log(2 + \|a\|)) for every real a -- finite partial sums regrouped on integer ceilings, e… |
| `RH_no_real_zero_unit_interval` | `RvMBridge25.noRealZeroInUnitInterval` | `rvm_bridge/lean/E6Bridge25.lean` | nanoda (36707277853) | AI, not independent | NO REAL ZERO IN (0,1) DISCHARGED (2026-09-21): Re zeta(sigma) < 0 for 0 < sigma < 1, from the summation-by-parts representation zeta(s) = 1/2 + 1/(s-1) + s J(s) with the … |
| `RH_rvm_unconditional` | `RvMBridge2.rvm_unconditional` | `rvm_bridge/lean/E6Bridge2.lean` | nanoda (36707277853) | AI, not independent | Riemann-von Mangoldt UNCONDITIONAL (routes-roadmap A4/D5, the E6 target): \|N(T) - (T/2pi log(T/2pi) - T/2pi + 7/8)\| <= C log T for all T >= 2, N(T) the multiplicity REC… |
| `RH_strip_deriv_bound` | `RvMBridge24.stripDerivBound` | `rvm_bridge/lean/E6Bridge24.lean` | nanoda (36707277853) | AI, not independent | STRIP DERIVATIVE BOUND DISCHARGED (2026-09-21): Landau's local partial fraction transferred to the derivative of xi'/xi on 1/4 <= Re s <= 9/4, \|Im s\| >= 5 -- divide out… |
| `RH_strip_repr` | - | `li_positivity/lean/StripReprAssembled.lean` † | not recorded | AI, not independent | The UNCONDITIONAL fractional-part strip representation: zeta = stripRHS on all of {0 < Re s} \ {1} |
| `RH_weil_criterion_iff` | `RvMBridge9.zeta_comb_membership_iff_rh` | `rvm_bridge/lean/E6Bridge9.lean` | nanoda (36707277853) | AI, not independent | WEIL'S CRITERION, in-kernel (routes-roadmap section 1, the Positivity face pinned by theorem, 2026-09-21): Weil positivity of the E8 primes-side functional on Hermitian a… |
| `RH_xi_derivative_partial_fraction` | `RvMBridge27.xi_logDeriv_deriv_eq` | `rvm_bridge/lean/E6Bridge27.lean` | nanoda (36707277853) | AI, not independent | THE XI PARTIAL FRACTION, DERIVATIVE FORM, UNCONDITIONAL (2026-09-21): (log xi)''(s) = -Sum m(rho)/(s - rho)^2 for every s that is not a nontrivial zero, proved WITHOUT th… |
| `RH_xi_derivative_partial_fraction_of` | `RvMBridge18.xi_logDeriv_deriv_eq_of` | `rvm_bridge/lean/E6Bridge18.lean` | nanoda (36707277853) | AI, not independent | THE XI PARTIAL FRACTION, DERIVATIVE FORM, WITHOUT HADAMARD (2026-09-21): (log xi)''(s) = -Sum m(rho)/(s - rho)^2 for every s that is not a nontrivial zero, PROVED modulo … |
| `RH_xi_derivative_partial_fraction_of_regular` | `RvMBridge21.xi_logDeriv_deriv_eq_of_regular` | `rvm_bridge/lean/E6Bridge21.lean` | nanoda (36707277853) | AI, not independent | THE XI PARTIAL FRACTION now rests on ONE obligation (2026-09-21): (log xi)'' = -Sum m(rho)/(s-rho)^2 GIVEN XiDiffRegular (equivalently, via E6Bridge20, the log-growth bou… |
| `RH_xi_derivative_partial_fraction_of_strip` | `RvMBridge23.xiLogDerivDerivEq_of_strip` | `rvm_bridge/lean/E6Bridge23.lean` | nanoda (36707277853) | AI, not independent | THE XI PARTIAL FRACTION rests on StripDerivBound ALONE (2026-09-21). conjecture1_proved = False. |
| `RH_xi_derivative_partial_fraction_of_two` | `RvMBridge22.xiLogDerivDerivEq_of_two` | `rvm_bridge/lean/E6Bridge22.lean` | nanoda (36707277853) | AI, not independent | THE XI PARTIAL FRACTION, full chain (2026-09-21): (log xi)'' = -Sum m(rho)/(s-rho)^2 GIVEN only LocalCountSum and StripDerivBound (Liouville with log growth + entire exte… |
| `RH_xi_diff_entire_extension` | `RvMBridge20.xiDiffExt_differentiable` | `rvm_bridge/lean/E6Bridge20.lean` | nanoda (36707277853) | AI, not independent | XI PARTIAL FRACTION, obligation 1 part A (2026-09-21): deriv(logDeriv xi) + Sum m(rho)/(s-rho)^2 extends to an ENTIRE function (order of xi at every point = the E8 multip… |
| `RH_xi_diff_regular_of_growth` | `RvMBridge20.xiDiffRegular_of_right` | `rvm_bridge/lean/E6Bridge20.lean` | nanoda (36707277853) | AI, not independent | XI PARTIAL FRACTION, obligation 1 reduced (2026-09-21): XiDiffRegular follows from a logarithmic growth bound on Re s >= 1/2 (XiDiffExtGrowthRight: Landau + Cauchy + Stir… |
| `RH_xi_growth_of_two` | `RvMBridge22.xiDiffExtGrowthRight_of_two` | `rvm_bridge/lean/E6Bridge22.lean` | nanoda (36707277853) | AI, not independent | XI PARTIAL FRACTION, obligation 1 REDUCED to two classical inequalities (2026-09-21): the log-growth bound on Re s >= 1/2 follows from LocalCountSum (Sum m(rho)/(1+(Im rh… |
| `RH_xi_logDeriv_deriv_decay` | `RvMBridge21.xi_logDeriv_deriv_decay` | `rvm_bridge/lean/E6Bridge21.lean` | nanoda (36707277853) | AI, not independent | XI PARTIAL FRACTION, obligation 2 DISCHARGED (2026-09-21): (log xi)''(sigma) -> 0 along the positive real axis -- termwise differentiation on Re s > 1 (rational terms, th… |
| `RH_xi_right_deriv_bound` | `RvMBridge22.rightDerivBound` | `rvm_bridge/lean/E6Bridge22.lean` | nanoda (36707277853) | AI, not independent | XI PARTIAL FRACTION, region C PROVED (2026-09-21): on Re s >= 2, (log xi)'' is bounded (rational terms, the trigamma series on Re z >= 1, and the L-series of log·Lambda f… |
| `RH_zero_free_gamma5` | - | `li_positivity/lean/ZeroFreeElementary.lean` † | not recorded | AI, not independent | The elementary unconditional zero-free region (Hadamard-free): beta <= 1 - c/gamma^5 |
| `RH_zero_free_polylog` | - | `li_positivity/lean/ZeroFreePolylog.lean` † | not recorded | AI, not independent | The polylog-improved unconditional zero-free region: beta <= 1 - c/(gamma^4 (1 + log 2 gamma)), strictly sharper than gamma^-5 |
| `RH_zeta_log_bound` | - | `li_positivity/lean/ZetaLogBound.lean` † | not recorded | AI, not independent | The sharp near-line growth bound: \|zeta(sigma+it)\| <= 6(1 + log\|t\|) for 1 <= sigma <= 2, \|t\| >= 2 |
| `RH_zeta_repr_R1` | - | `li_positivity/lean/StripReprR1.lean` † | not recorded | AI, not independent | Strip representation seed (R1): zeta = stripRHS on Re s > 1, by Abel summation |
| `RH_zeta_zero_confined` | - | `li_positivity/lean/LowHeightBox.lean` † | not recorded | AI, not independent | LOW-HEIGHT BOX 2 (li_positivity island, 2026-09-21): every nontrivial zero satisfies (Re s - 1/2)^2 <= (Im s)^2 / 3 - 1/4, hypothesis-free (same route as Box 1; informati… |
| `RH_zeta_zero_free_liu` | `liu_zeta_zero_free` | `liu_dbn_bridge/lean/ArdaLiuBridge.lean` | nanoda (38179118143) | human (author) | Liu's zero-free half-plane for zeta (arXiv:2610.12234, 8 Oct 2026): riemannZeta s != 0 for Re s > B_new = (1507 - 2 sqrt 921)/1653 = 0.874957069..., the proved-input opti… |
| `RH_zeta_zero_free_seven_eighths` | `qrh_seven_eighths` | `oai_qrh_bridge/lean/ArdaQRHBridge.lean` | nanoda (37955041118) | human (author) | zeta != 0 on Re s > 7/8. Proof entirely OpenAI's (openai/math adc7f124, family 003, Apache-2.0), re-exported on the oai_qrh_bridge island at OpenAI's pin (Lean v4.34.1, M… |
| `RH_zeta_zero_im_ge` | - | `li_positivity/lean/LowHeightBox.lean` † | not recorded | AI, not independent | LOW-HEIGHT BOX 1 (li_positivity island, 2026-09-21): every nontrivial zero of zeta has \|Im\| >= sqrt 3 / 2. Hypothesis-free, from the fractional-part representation zeta… |

Not proved (draft, open or deprecated):

| node | status | registry title (abridged, verbatim) |
|---|---|---|
| `RH_conjecture` | draft | The Riemann Hypothesis (Mathlib's RiemannHypothesis) -- NOT proved; the campaign goal |
| `RH_weil_window_floor_of_certified_block` | draft | Zhu compact-window reduction (arXiv:2608.24827 Thm 1.1 + Lemma 6.1), RE-SPECIFIED 2026-09-23 from opaque to concrete inputs: the symbol representation (eq. 2) and the dig… |

### MIRRORMERE: Weil positivity, the explicit formula, quasicrystals (`missions/mirrormere`)

51 proved nodes.

| node | judged theorem | artifact (under `telperion/examples/`) | Comparator (kernel, run) | read-back | registry title (abridged, verbatim) |
|---|---|---|---|---|---|
| `MM_bragg_bridge` | - | `li_positivity/lean/RvMBraggBridge.lean` † | not recorded | AI, not independent | W3b DONE, the Bragg bridge: the finite-height explicit formula in diffraction form -- 2 pi i times the box zero-count of zeta over its ACTUAL divisor equals the edge inte… |
| `MM_bragg_defect_witness` | - | `zeta_zero_localization/lean/BraggDefect.lean` † | not recorded | AI, not independent | The certified defect witness pair: the all-on-line configuration has defect functional exactly 0 (defect_witness_online, unconditional) while one synthetic off-line pair … |
| `MM_bragg_defect_witness_sie` | - | `zeta_zero_localization/lean/BraggDefect.lean` † | not recorded | AI, separate session | The certified defect witness pair with NO hypothesis (zeta_zero_localization island, BraggDefect.lean, 2026-10-11): the all-on-line configuration has defect functional ex… |
| `MM_cc_cor_2_3` | `cc_cor_2_3` | `rvm_bridge/lean/ArchRegistry_CCCor23.lean` | nanoda (38278712834) | AI, separate session | CONNES-CONSANI COROLLARY 2.3, KERNEL-CHECKED, ANY SUPPORT (rvm_bridge island, ArchS3_*, 2026-10-11): for EVERY Weil test g (smooth, compact support of any width, no windo… |
| `MM_effective_gaussian_dominance` | `RvMBridge14.effective_gaussian_dominance` | `rvm_bridge/lean/E6Bridge14.lean` | nanoda (36707277853) | AI, not independent | OPEN LEMMA 1 DISCHARGED (2026-09-21): EFFECTIVE Gaussian dominance -- an off-line zero of maximal distance y0 from the line within its height window (radius D >= 1), with… |
| `MM_effective_threshold_unbounded` | `RvMBridge14.effectiveThreshold_unbounded_of_small_spacing` | `rvm_bridge/lean/E6Bridge14.lean` | nanoda (36707277853) | AI, not independent | OPEN LEMMA 1, the load-bearing hypothesis made explicit (2026-09-21): the spacing floor in effective Gaussian dominance cannot be dropped -- for every distance floor 0 < … |
| `MM_euler_factor_section_offline` | - | `quasicrystal/lean/EulerFactorSectionOffline.lean` | not recorded | AI, not independent | Torus-section ladder T2, THE NEGATIVE CONTROL: the p=2 Euler factor 1 - 2^(-s), read on s = 1/2 + ix as the two-frequency section twoFreq(1, -1/sqrt 2; 0, -log 2), is NOT… |
| `MM_gaussian_approx` | `RvMBridge8.gaussian_approx` | `rvm_bridge/lean/E6Bridge8.lean` | nanoda (36707277853) | AI, not independent | Obligation O1' (GaussianApprox): for every centre c and lam > 0 there are Weil tests g_n whose Hermitian transforms converge to the Gaussian-derivative transform G_{c,lam… |
| `MM_gaussian_dominance` | `RvMBridge7.gaussian_dominance` | `rvm_bridge/lean/E6Bridge7.lean` | nanoda (36707277853) | AI, not independent | Obligation O2 (GaussianDominance), the analytic heart of the Weil converse: if rho_0 is a nontrivial zero off the critical line then for some real centre c and some lam >… |
| `MM_gaussian_explicit_formula` | `RvMBridge10.zeroSide_gaussTest_eq` | `rvm_bridge/lean/E6Bridge10.lean` | nanoda (36707277853) | AI, not independent | WALL ASSAULT seam A: the Gaussian explicit formula -- the Gaussian-weighted zero sum equals archSide minus primeSide of the Hermitian autocorrelation of the Gaussian-deri… |
| `MM_gaussian_positivity_envelope` | `RvMBridge11.gaussian_positivity_envelope` | `rvm_bridge/lean/E6Bridge11.lean` | nanoda (36707277853) | AI, not independent | WALL ASSAULT seam B, envelope form (2026-09-21), UNCONDITIONAL: for every width lam > 0 there is an explicit height envelopeC(lam) beyond which the Gaussian-weighted zero… |
| `MM_gaussian_positivity_envelope_sharp` | `RvMBridge16.gaussian_positivity_envelope_sharp` | `rvm_bridge/lean/E6Bridge16.lean` | nanoda (36707277853) | AI, not independent | SEAM B SHARPENED (2026-09-21), UNCONDITIONAL: the sharp c-uniform envelope of the two-parameter Wall -- for every width lam > 0 the Gaussian-weighted zero sum is nonnegat… |
| `MM_gaussian_positivity_of_window` | `RvMBridge12.gaussian_positivity_of_window` | `rvm_bridge/lean/E6Bridge12.lean` | nanoda (36707277853) | AI, not independent | WALL ASSAULT seam C (2026-09-21): the ladder-certified region of the two-parameter Wall as a kernel INSTRUMENT -- if every nontrivial zero within D of the centre c is on … |
| `MM_gaussian_positivity_small_lam` | `RvMBridge13.gaussian_positivity_small_lam` | `rvm_bridge/lean/E6Bridge13.lean` | nanoda (36707277853) | AI, not independent | WALL ASSAULT seam B, zero-side form, UNCONDITIONAL: for every centre and every width <= lam0 the Gaussian-weighted zero sum is nonnegative (seam A's Gaussian explicit for… |
| `MM_gaussian_positivity_small_lam_3e3` | `RvMBridge30.gaussian_positivity_small_lam_3e3` | `rvm_bridge/lean/E6Bridge30.lean` | nanoda (36707277853) | AI, not independent | THE GAUSSIAN PRIME-FREE WINDOW, WIDENED 15000x (rvm_bridge island, E6Bridge30, 2026-09-22): the Wall functional F(c, lam) is nonnegative for EVERY centre c and every 0 < … |
| `MM_gaussian_positivity_small_lam_prime_side` | `RvMBridge11.re_weilForm_gauss_nonneg` | `rvm_bridge/lean/E6Bridge11.lean` | nanoda (36707277853) | AI, not independent | WALL ASSAULT seam B (2026-09-21), UNCONDITIONAL: the small-width region of the two-parameter Wall -- for EVERY real centre c and every width 0 < lam <= lam0 = 1e-7, the a… |
| `MM_gaussian_transfer` | `RvMBridge9.gaussian_transfer` | `rvm_bridge/lean/E6Bridge9.lean` | nanoda (36707277853) | AI, not independent | Obligation O1 (GaussianTransfer): the Gaussian-derivative Hermitian transform G_{c,lam} is a limit of Hermitian transforms of smooth compactly supported Weil tests FOR TH… |
| `MM_hodge1_one_prime_identity` | `re_weilForm_eq_archW_sub_prime` | `rvm_bridge/lean/Hodge1_RegOnePrime.lean` | nanoda (38402969515) | AI, separate session | THE EXACT ONE-PRIME WEIL IDENTITY ON THE POLE-FREE WINDOW (rvm_bridge island, Hodge1_Reduction, HODGE-1 Phase 1, 2026-10-12): for every Weil test g supported in [-L, L] w… |
| `MM_hodge1_rh_reduction` | `rh_iff_poleFree_outside_window5493` | `rvm_bridge/lean/Hodge1_RegRH.lean` | lean-kernel-only (38404699182) | AI, separate session | RH IFF POLE-FREE WEIL POSITIVITY OUTSIDE THE HODGE-1 WINDOW (rvm_bridge, kernel-checked): RiemannHypothesis holds iff 0 <= Re weilForm(autocorr g) for every pole-free Wei… |
| `MM_hodge1_window45` | `weil_positivity_poleFree_window45` | `rvm_bridge/lean/Hodge1_RegWindow45.lean` | lean-kernel-only (38404702485) | AI, separate session | POLE-FREE ONE-PRIME WEIL POSITIVITY, L <= 9/20 (rvm_bridge, HODGE-1 Phase 1, kernel certificate): for every Weil test g with paperFT g (+-i/2) = 0 supported in [-L, L], L… |
| `MM_hodge1_window5493` | `weil_positivity_poleFree_window5493` | `rvm_bridge/lean/Hodge1_RegWindow5493.lean` | lean-kernel-only (38404695545) | AI, separate session | POLE-FREE ONE-PRIME WEIL POSITIVITY, L <= 5493/10000 (rvm_bridge, HODGE-1 Phase 1b-B, kernel certificate): for every Weil test g with paperFT g (+-i/2) = 0 supported in [… |
| `MM_leakage_composite_zero` | - | `quasicrystal/lean/LeakageNode.lean` | not recorded | AI, not independent | A2b, a FORMALIZATION win, not new mathematics: for a completely multiplicative normalized amplitude a, the Dirichlet coefficients b of -F'/F vanish at every non-prime-pow… |
| `MM_nt_brick_conditional` | - | `quasicrystal/lean/BoundaryLemmas.lean` | not recorded | AI, not independent | W2c, R2-honest: the zeta ordinates are not uniformly discrete, GIVEN the named counting hypothesis RvMUnboundedMeanDensity (the Riemann-von Mangoldt mean-density input no… |
| `MM_offline_disjoint_discs` | - | `quasicrystal/lean/OfflineDiscs.lean` | not recorded | AI, not independent | Routes-roadmap E4b (the isolation lemma, QC_RECURRENCE section 4.3): any finite set of points in the open critical strip admits a single positive radius whose closed disc… |
| `MM_offline_pairs_le_defect` | - | `zeta_zero_localization/lean/R2Rigidity.lean` † | not recorded | AI, not independent | W2b, the CONDITIONAL rigidity direction: a p-dimensional negative-definite witness subspace forces p <= defect (offline_pairs_le_defect). The witness is load-bearing and … |
| `MM_polefree_weil_converse` | - | `rvm_bridge/lean/RegRRChain.lean` | not recorded | AI, separate session | POLE-FREE WEIL CONVERSE (rvm_bridge RegRRChain / PFConverseC, kernel-checked): if 0 <= Re weilForm(autocorr g) for every Weil test g with paperFT g (I/2) = 0 and paperFT … |
| `MM_primelog_spectrum_dense` | - | `quasicrystal/lean/BoundaryLemmas.lean` | not recorded | AI, not independent | Spectrum escape (unconditional): the additive subgroup generated by log 2 and log 3 is dense in R -- the zeta frequency spectrum fails Bohr discreteness, so zeta escapes … |
| `MM_rect_trace_reading` | - | `li_positivity/lean/RvMTraceReading.lean` † | not recorded | AI, not independent | Routes-roadmap D1 (spectral trace reading, dictionary-grade): the Bragg bridge rearranged as a finite trace identity -- the box zero-count of zeta over its actual divisor… |
| `MM_recurrence_deficit_eq_excess` | - | `zeta_zero_localization/lean/RecurrenceDeficit.lean` † | not recorded | AI, not independent | Routes-roadmap E4a (Face 4 <-> Face 1 witness bridge): the Bagchi recurrence deficit (e^delta - 1)(1 - e^(-delta)) equals the Bragg amplification excess at the certified … |
| `MM_rh_iff_gaussian_positivity` | `RvMBridge10.rh_iff_gaussian_positivity` | `rvm_bridge/lean/E6Bridge10.lean` | nanoda (36707277853) | AI, not independent | WALL ASSAULT seam A (2026-09-21): the Wall in two real parameters -- Mathlib's RiemannHypothesis is EQUIVALENT to Gaussian positivity: for every centre c and width lam > … |
| `MM_rh_iff_gaussian_prime_le_arch` | `RvMBridge10.rh_iff_gaussian_prime_le_arch` | `rvm_bridge/lean/E6Bridge10.lean` | nanoda (36707277853) | AI, not independent | WALL ASSAULT seam A: RH as a PRIME-SIDE inequality with no zeros in it -- for every centre c and width lam > 0, the prime side of the Gaussian-derivative test does not ex… |
| `MM_rh_iff_theta_positivity` | `RvMBridge17.rh_iff_theta_positivity` | `rvm_bridge/lean/E6Bridge17.lean` | nanoda (36707277853) | AI, not independent | THE THETA FACE (2026-09-21): Mathlib's RiemannHypothesis is EQUIVALENT to positivity of the PLAIN Gaussian face Theta(c, lam) = Re Sum m(rho) e^{-2 lam (gamma_rho - c)^2}… |
| `MM_rh_iff_theta_widths` | `RvMBridge17.rh_iff_thetaWidths_eq` | `rvm_bridge/lean/E6Bridge17.lean` | nanoda (36707277853) | AI, not independent | LAMBDA_THETA (2026-09-21): RH is EQUIVALENT to every positive width being Theta-free, i.e. to the de Bruijn-Newman-type constant of the zero measure being infinite; an of… |
| `MM_rh_implies_weil_positivity` | `RvMBridge5.rh_implies_weil_positivity` | `rvm_bridge/lean/E6Bridge5.lean` | nanoda (36707277853) | AI, not independent | Weil's criterion, forward half, on the E8 vocabulary: Mathlib's RiemannHypothesis implies Weil positivity of weilForm on Hermitian autocorrelations over IsWeilTest -- dis… |
| `MM_rr_square_collapse` | - | `rvm_bridge/lean/RegRRChain.lean` | not recorded | AI, separate session | RR-SQUARE COLLAPSE (rvm_bridge RegRRChain, kernel-checked): with Div = V (iota = id), for symmetric B with B f f > 0, data satisfying the bounded RR axioms EXIST iff the … |
| `MM_rr_square_hodge_index` | - | `rvm_bridge/lean/RegRRChain.lean` | not recorded | AI, separate session | RR-SQUARE HODGE INDEX, DEGREE-BOUND FORM (rvm_bridge RegRRChain, kernel-checked; CONDITIONAL REDUCTION ingredient): for a real form B on V, a degree class f, divisors Div… |
| `MM_rr_square_hodge_index_domain` | - | `rvm_bridge/lean/RegRRChain.lean` | not recorded | AI, separate session | RR-SQUARE HODGE INDEX, NO-ZERO-DIVISOR FORM (rvm_bridge RegRRChain, kernel-checked; CONDITIONAL REDUCTION ingredient): as MM_rr_square_hodge_index with the degree bound r… |
| `MM_rr_windows_imply_rh` | - | `rvm_bridge/lean/RegRRChain.lean` | not recorded | AI, separate session | RR-SQUARE WINDOWS IMPLY RH, CONDITIONAL REDUCTION (rvm_bridge RegRRChain, kernel-checked): a family of windows i, each with V i, Div i, B i, f i, iota i, deg, Prin, h0, h… |
| `MM_rvm_unbounded_mean_density` | `RvMBridge.rvm_unbounded_mean_density` | `rvm_bridge/lean/E6Bridge.lean` | nanoda (36707277853) | AI, not independent | The W2c residual, named: RvMUnboundedMeanDensity -- the zeta-ordinate mean density exceeds every finite bound (Riemann-von Mangoldt growth input). 2026-09-15 SURVEY VERDI… |
| `MM_selfinversive_iff_hardyz_real` | - | `quasicrystal/lean/InvolutionDictionary.lean` | not recorded | AI, not independent | W2a involution dictionary: the self-inversive identity forces the finite Hardy-Z analogue to be real on the circle's preimage (selfInversive_iff_hardyZ_real) -- the finit… |
| `MM_spectral_cooked_control` | - | `li_positivity/lean/RvMSpectralCookedControl.lean` † | not recorded | AI, not independent | Routes-roadmap D4a (the spectral triviality NEGATIVE CONTROL): any finite real multiset is the characteristic-polynomial spectrum of a Hermitian matrix (the diagonal one)… |
| `MM_theta_heat_monotone` | `RvMBridge17.theta_pos_mono` | `rvm_bridge/lean/E6Bridge17.lean` | nanoda (36707277853) | AI, not independent | THE HEAT INSTRUMENT (2026-09-21), UNCONDITIONAL: the plain Gaussian face is heat-monotone in width -- Theta(., lam') = sqrt(lam/lam') P_s Theta(., lam) for lam' < lam (th… |
| `MM_torus_section_n2_rigidity` | - | `quasicrystal/lean/TorusSectionLadder.lean` | not recorded | AI, not independent | Torus-section ladder T1, the N=2 rung: RESTATES its sibling MM_twofreq_realrooted_iff in ladder vocabulary and proves nothing that theorem does not. Statement: for nonzer… |
| `MM_twofreq_realrooted_iff` | - | `quasicrystal/lean/TwoFreqRigidity.lean` | not recorded | AI, not independent | First rigidity theorem, R3(n=2): a two-frequency exponential sum is real-rooted iff its coefficients have equal modulus (twoFreq_realRooted_iff; reality of the support go… |
| `MM_wall_map` | `RvMBridge13.rh_iff_gaussian_positivity_above_lam₀` | `rvm_bridge/lean/E6Bridge13.lean` | nanoda (36707277853) | AI, not independent | THE WALL MAP (2026-09-21): Mathlib's RiemannHypothesis is EQUIVALENT to Gaussian positivity on widths strictly above lam0 = 1e-7 only; below lam0 positivity is a theorem … |
| `MM_weil_positivity_implies_rh` | `RvMBridge9.weil_positivity_implies_rh` | `rvm_bridge/lean/E6Bridge9.lean` | nanoda (36707277853) | AI, not independent | Weil's criterion, converse half (Weil 1952; Bombieri 2000 on C_c^infinity): Weil positivity on Hermitian autocorrelations over IsWeilTest implies Mathlib's RiemannHypothe… |
| `MM_weil_positivity_implies_rh_of_gaussian` | `RvMBridge6.weil_positivity_implies_rh_of` | `rvm_bridge/lean/E6Bridge6.lean` | nanoda (36707277853) | AI, not independent | The Weil converse, REDUCED: Weil positivity implies Mathlib's RiemannHypothesis GIVEN the two named analytic obligations GaussianTransfer (transfer of the zero-side funct… |
| `MM_weil_positivity_prime_free_window` | `weil_positivity_prime_free_window` | `rvm_bridge/lean/KWin_Bridge.lean` | lean-kernel-only (36772578397) | AI, not independent | THE FULL PRIME-FREE WINDOW ON THE GOAL NODE'S OWN TEST CLASS, KERNEL-NATIVE (rvm_bridge island, KWin_*, 2026-09-24): for every Weil test g with tsupport g in [-L, L] and … |
| `MM_weil_positivity_window_two_fifths` | `weil_positivity_window_two_fifths` | `rvm_bridge/lean/KWin2_Bridge.lean` | lean-kernel-only (36772787177) | AI, not independent | THE WEIL WINDOW PAST THE PRIME-FREE BOUNDARY, KERNEL-NATIVE (rvm_bridge island, KWin2_*, 2026-09-24): for every Weil test g with tsupport g in [-L, L] and 2L <= 4/5, Re w… |
| `MM_zeta_comb_membership_iff_rh` | `RvMBridge9.zeta_comb_membership_iff_rh` | `rvm_bridge/lean/E6Bridge9.lean` | nanoda (36707277853) | AI, not independent | The dictionary theorem: the MIRRORMERE goal statement is EQUIVALENT to Mathlib's RiemannHypothesis, in-kernel -- replaces the 2026-09-14 placeholder's by-fiat identificat… |
| `MM_zeta_ordinates_not_uniformly_discrete` | `RvMBridge.zeta_ordinates_not_uniformly_discrete` | `rvm_bridge/lean/W2cAssembly.lean` | nanoda (36707277853) | AI, not independent | W2c target, unconditional form: the zeta ordinates are not uniformly discrete, no hypotheses -- lands when the RvM residual is discharged into the conditional brick |

Not proved (draft, open or deprecated):

| node | status | registry title (abridged, verbatim) |
|---|---|---|
| `MM_satake_degree_two_rejects_delta` | draft | A1b: the REGISTERED content is the elementary identity that a two-term Newton power sum a^m + b^m is geometric in one scalar IFF a*b = 0; every Delta-specific theorem (ta… |
| `MM_speiser_box_probe` | open | Routes-roadmap E9 (Face 7 pilot, W4c): a concrete zeta'-zero-free box left of the critical line -- deriv riemannZeta nonvanishing on [1/4, 3/8] x [6, 10]. NOT the Speiser… |
| `MM_torus_section_dictionary` | deprecated | Torus-section ladder T1, NOTATION ONLY (not a bridge lemma): the island's twoFreq is the same two-term exponential sum as linearTorusForm 2 on torusOrbit 2, written with … |
| `MM_weil_positivity_window_tenth` | draft | THE PRIME-FREE WINDOW AT L <= 1/10 ON THE GOAL NODE'S OWN TEST CLASS (rvm_bridge island, E6Bridge31-34, 2026-09-23): for every smooth compactly supported g with tsupport … |
| `MM_zeta_comb_membership` | draft | The W3c membership goal: defect-0 membership of the Guinand-Weil REGULARIZED TRIPLE (zero comb against h, prime comb against g, archimedean density against h) stated as W… |

### ANDURIL: finite verification and kernel reflection (`missions/anduril`)

12 proved nodes.

| node | judged theorem | artifact (under `telperion/examples/`) | Comparator (kernel, run) | read-back | registry title (abridged, verbatim) |
|---|---|---|---|---|---|
| `AND_checkline_correct` | `ZetaReflection.checkLine_correct` | `zeta_reflection/lean/CheckBand.lean` † | nanoda (36707277853) | AI, not independent | A4 reflection core: checkLine_correct -- the once-proven correctness theorem for the Boolean band checker over dyadic-interval sign boxes (BandData -> Bool; per-band cert… |
| `AND_edge_clear_glue` | `EdgeClearGlue.hnzl_discharged` | `zeta_reflection/lean/EdgeClearGlue.lean` † | nanoda (36707277853) | AI, not independent | Edge-clear glue K1, H2b discharged: riemannZeta(-1 + iy) != 0 for every real y (every band edge), hypothesis-free (zeta_zero_re_mem_strip off the real axis, zeta(-1) = -1… |
| `AND_em_tail3_number` | `ZetaReflection.em_tail3_number` | `zeta_reflection/lean/EMZetaTail.lean` † | nanoda (36707277853) | AI, not independent | Order-K EM tail engine, THE NUMBER: the order-3 Euler-Maclaurin tail remainder is kernel-decided below 10^-3 (em_tail3_number; the shared substrate for Stirling K=4 and t… |
| `AND_em_zeta_strip` | `ZetaReflection.em_zeta_strip` | `zeta_reflection/lean/EMZetaComplex.lean` † | nanoda (36707277853) | AI, not independent | A2 E-track headliner: the verified Euler-Maclaurin representation of zeta continued into the critical strip -- zeta(s) = 1/(s-1) + 1/2 + integral of sawBernoulli-weighted… |
| `AND_first_zero_kernel` | `ForgeFirstZeroKernel.first_zero_kernel` | `zeta_reflection/lean/ForgeFirstZeroKernel.lean` † | nanoda (36707277853) | AI, not independent | REFLECTION CAPSTONE: first_zero_kernel -- an argument-free, hypothesis-free nontrivial zeta zero in (14, 15), verified entirely by kernel computation over rational certif… |
| `AND_g2_reflected_band` | - | `zeta_reflection/lean/ReflectedBand_t14.lean` † | not recorded | AI, not independent | G2: THE FIRST REFLECTED BAND (ReflectedBand_t14) -- a band certificate proved by kernel decide through checkLine rather than emitted norm_num, consumed by the height chai… |
| `AND_g2_reflected_band_kernel` | `ReflectedBand_t14_Kernel.pilot_kernel` | `zeta_reflection/lean/ReflectedBand_t14_Kernel.lean` † | nanoda (36707277853) | AI, not independent | G2 hypothesis-free companion: two zeros of completedRiemannZeta on the critical line with heights in [14, 22], proved entirely in the kernel (wide kernel-proved boxes dK … |
| `AND_height_floor_kernel` | `HeightFloor.height_floor` | `zeta_reflection/lean/HeightFloor.lean` † | nanoda (36707277853) | AI, not independent | Height floor, hypothesis-free: no zero of riemannZeta has 0 < Im rho < 55/16 (for every height bound H). Kernel-proved (order-3 Euler-Maclaurin at N = 2 plus 32 exact int… |
| `AND_ladder_h1000_kernel` | `AllZerosKernel_h1000.all_nontrivial_zeros_up_to_height_1000` | `zeta_reflection/lean/AllZerosKernel_h1000.lean` † | nanoda (36707277853) | AI, not independent | G0-kernel: every nontrivial zeta zero with 0 < Im rho <= 1000 lies on Re = 1/2 -- the FIRST fully hypothesis-free ladder segment, kernel-checked with no Arb or oracle inp… |
| `AND_ladder_h8000_kernel` | `Arb4_Compose_h8000.ladder_h8000_of_bands` | `zeta_reflection/lean/Arb4_h8000.lean` † | lean-kernel-only (36306561345) | AI, not independent | Every nontrivial zeta zero with 0 < Im rho <= 8000 lies on Re = 1/2 -- hypothesis-free, kernel-checked, NO Arb or oracle input (Arb4 compact certificates, 8 segments chai… |
| `AND_stirling_binet_k1` | `ZetaReflection.logDeriv_gammaR_stirling` | `zeta_reflection/lean/StirlingBinet.lean` † | nanoda (36707277853) | AI, not independent | A2 Stirling/Binet K=1: logDeriv_gammaR_stirling -- the Gamma_R logarithmic derivative with explicit Binet remainder on Re z > 0 (serves both the Gamma_R edges and, at K=4… |
| `AND_theta_branch` | `RSDesignTheta.gaussBranch_theta_sub_thetaMain_le` | `zeta_reflection/lean/RSTheta.lean` † | nanoda (36707277853) | AI, not independent | Riemann-Siegel brick B0 (theta): for every t > 0 the Gauss-product branch limit of Im log Gamma(1/4 + it/2) exists and lies within 1/t of the RS main term after the (t/2)… |

Not proved (draft, open or deprecated):

| node | status | registry title (abridged, verbatim) |
|---|---|---|
| `AND_ladder_1e13` | draft | G5: every nontrivial zeta zero with \|Im rho\| <= 10^13 lies on Re = 1/2 -- the campaign goal (finite verification target, NOT RH; charter: native_decide era, flagged sib… |
| `AND_ladder_1e6` | open | G1: every nontrivial zeta zero with \|Im rho\| <= 10^6 lies on Re = 1/2 (~1.8M zeros; roadmap: nothing structural remains on current T5 machinery, wall-clock only) |
| `AND_ladder_1e9` | open | G4: every nontrivial zeta zero with \|Im rho\| <= 10^9 lies on Re = 1/2, kernel-only (3-axiom decide; charter gates this on the A3 Riemann-Siegel era -- theta branch + RS… |
| `AND_ladder_h11000_kernel` | draft | Every nontrivial zeta zero with 0 < Im rho <= 11000 lies on Re = 1/2 -- hypothesis-free, kernel-checked, no Arb or oracle input: the h8000 Arb4 ladder chained (height_cha… |
| `AND_ladder_h280000` | open | Current certified height: every nontrivial zeta zero with \|Im rho\| <= 280000 lies on Re = 1/2 (432,474 zeros, leg 17). REGISTRY-SHAPE MISMATCH, corrected 2026-09-22: th… |

