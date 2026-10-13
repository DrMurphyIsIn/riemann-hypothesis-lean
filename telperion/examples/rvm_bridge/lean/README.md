# rvm_bridge/lean — the E6 bridge island (Lean v4.33.0-rc2)

A self-contained Lean 4 project that discharges four registry nodes from an external,
independently machine-checked formalization: Anthropic's **zeta-23-lean** (Alpöge–Furman,
*More than two thirds of the zeta zeros are simple and on the critical line*,
arXiv:2608.13637). It is the outcome of the routes-roadmap **E6 probe** (2026-09-17,
`telperion/docs/E6_PROBE_2026-09-17.md`) and its follow-up
(`telperion/docs/RVM_CUMULATIVE_BRIDGE_2026-09-17.md`):

1. the MIRRORMERE residual `MM_rvm_unbounded_mean_density` (`E6Bridge.lean`), and
2. the RH critical-path node `RH_rvm_unconditional` — the **cumulative** Riemann–von Mangoldt
   formula `N(T) = (T/2π) log(T/2π) − T/2π + 7/8 + O(log T)` for all `T ≥ 2`, no hypotheses
   (`E6Bridge2.lean`). zeta-23-lean states only the dyadic clause; the cumulative `O(log T)`
   form is re-assembled here from its general-window internals (see below), and
3. the RH four-consumer blocker `RH_corridor_bound` (roadmap milestone E7 = A3 = B5 = D6) — the
   **good-ordinate lemma**: for every `T ≥ 2` some `T' ∈ [T, T+1]` has a zero-free horizontal
   segment `−1 ≤ σ ≤ 2` on which `|ζ'/ζ(σ + iT')| ≤ C log² T` (`E6Bridge3.lean`,
   `telperion/docs/CORRIDOR_BOUND_BRIDGE_2026-09-17.md`). zeta-23-lean's own good-height lemma is
   at integer heights and only on `1/2 ≤ σ ≤ 2`; the real-height selection and the reflected
   half `−1 ≤ σ < 1/2` (functional equation + Γℝ log-derivative bounds) are done here, and
4. the RH node `RH_limit_explicit_formula` (roadmap milestone E8 = B6 = D6) — the unconditional
   **Weil / Guinand explicit formula** for every smooth compactly supported `g : ℝ → ℂ`, stated
   as `Integrable (archIntegrand g) ∧ HasSum (fun ρ : ℂ => zeroMult ρ * weilKernel g ρ)
   (archSide g − primeSide g)` with the registry's divisor multiplicity over **all** `ρ : ℂ`
   (`E6Bridge4.lean`, `telperion/docs/E8_EXPLICIT_FORMULA_BRIDGE_2026-09-18.md`). zeta-23-lean
   proves the literature-form formula (`Zeta23.WeilEF.EF_lit_zetaZeroConfig`, Iwaniec–Kowalski
   5.12 shape, `C_c²` tests, zero sum over the subtype of nontrivial zeros weighted by
   `analyticOrderAt`); the bridge is the transform / index-set / multiplicity / archimedean-term
   normalisation (see below). The E8 registry statement lives on branch `rh/e8-statement`; this
   island carries a verbatim copy of its six definitions and embeds the theorem text in the
   module header so the drift check works before that branch is merged.

**No RH progress is claimed.** All four discharged statements are classical (Selberg-type
density; the von Mangoldt / Backlund zero count, Titchmarsh 9.4; the good-ordinate lemma,
Davenport ch. 15–17 / Titchmarsh 9.6; the explicit formula, Weil 1952 / Guinand 1948 /
Iwaniec–Kowalski Thm 5.12). `conjecture1_proved = False`.

| file | role |
|---|---|
| `lean-toolchain`, `lakefile.toml` | Lean `v4.33.0-rc2`; `Zeta23` pinned to `anthropics/formal-math@fbdc36bbf17d20af3fd0447c6d1a8a02773c9844` (`subDir = zeta23`), which transitively pins Mathlib `51e6992efd06126df61a496bebf8f49482a4e129` (tag `v4.33.0-rc2`) |
| `E6Bridge.lean` | the first bridge: mirrors of the two registry definitions (`MMDefs.lean:48-53`), `eventually_Ncount_ge` (the `T log T` lower bound from the RvM main clause), and the node statement `theorem rvm_unbounded_mean_density : RvMUnboundedMeanDensity zetaOrdinates` verbatim |
| `E6Bridge2.lean` | the second bridge: mirror of `RvMCount.zetaZeroCount` (`RHDefs.lean`), the definitional seam `zetaZeroCount_eq_Ncount` (divisor count = Zeta23's `Ncount 0 T`), integrated Stirling on a general window (`int_mu_cumulative`), the cumulative assembly (`rvm_cumulative_eventually`, `rvm_cumulative`) and the node statement `theorem rvm_unconditional` verbatim |
| `E6Bridge3.lean` | the third bridge: Γℝ log-derivative bounds off the real axis (`logDeriv_Gammaℝ_shift`, `norm_logDeriv_Gammaℝ_le_log_strip`), the functional-equation identity `logDeriv_zeta_reflect`, the real-height good ordinate `good_height_real`, the two ranges `corridor_large` (`T ≥ 7`) / `corridor_small` (`2 ≤ T ≤ 7`, compactness) and the node statement `theorem corridor_bound` verbatim |
| `E6Bridge4.lean` | the fourth bridge: verbatim mirror of the six `WeilExplicit.*` registry definitions (`RHDefs.lean`, branch `rh/e8-statement`), the transform seam `weilKernel_eq_Hfn`, Fourier inversion at the origin `inversion_zero`, the archimedean integrability `integrable_archIntegrand`, the normalisation `archSide_sub_primeSide` (= upstream `literatureRHS`), the divisor/`analyticOrderAt` seam (`zeroMult_eq_of_strip`, `zeroMult_eq_zero_of_not_nontrivial`) and the node statement `theorem limit_explicit_formula` verbatim |
| `W2cAssembly.lean` | the W2c assembly (not a bridge): a VERBATIM re-proof of the v4.32 quasicrystal island's pigeonhole brick (`BoundaryLemmas.lean`, branch `rh/million-turing`, blob `b019e8e9`) — `IsUniformlyDiscrete`, `not_uniformlyDiscrete_of_gaps_to_zero`, `exists_close_of_card_gt`, `RvMWindowedDensity`, `windowedDensity_of_unboundedMeanDensity`, `not_uniformlyDiscrete_of_windowedDensity`, `zeta_ordinates_not_uniformlyDiscrete_of_unbounded_density` — composed with `E6Bridge.rvm_unbounded_mean_density` to give the MIRRORMERE node statement `theorem zeta_ordinates_not_uniformly_discrete : ¬ IsUniformlyDiscrete zetaOrdinates` verbatim |
| `AxiomGuardRvMBridge.lean` | CI guard: `#print axioms` for all four bridges' theorems, the W2c assembly and its ported brick, AND the consumed upstream inputs; CI fails on `sorryAx` |
| `../generate.py --check` | drift check registered in `telperion.toml`: all five node statements (name + binders + body) and the mirrored definitions must still match the registry files verbatim, the toolchain pin must be the zeta-23-lean pin, and every statement ported into `W2cAssembly.lean` must equal the pinned v4.32 `BoundaryLemmas.lean` text (diffed against the live file too, when that island is in the checkout); for the E8 node the theorem is always checked against the copy embedded in the `E6Bridge4.lean` header, and the registry-file halves are skipped with a printed notice when the E8 registry files are absent from the checkout |

Since 2026-09-18 the island also carries a **fifth** artifact, which is an assembly rather than a
bridge: the MIRRORMERE milestone `MM_zeta_ordinates_not_uniformly_discrete` (W2c, unconditional
form) in `W2cAssembly.lean` — see "The W2c assembly" below.

## Why a third toolchain island

zeta-23-lean pins Lean `v4.33.0-rc2` / Mathlib `51e6992e`. The mirrormere statements and
the main Telperion islands are on `v4.32.0` (376 Mathlib commits earlier); `missions/rh` and
`li_positivity` are on `v4.34.0-rc1` (129 commits later). Bumping 118 upstream modules was
judged a day-scale mechanical task; a verbatim-statement island importing the upstream at its
own pin is hours and keeps the upstream unmodified. Cross-island grants are the accepted
precedent (`missions/rh/mission.toml`: one granted node's artifact lives on the v4.32
`zero_free_bridge` island).

## What is consumed from upstream, and why Theorem A rather than RvM alone

* `Zeta23.thmA₀ : ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (2/3 − ε) · Ncount T (2T) ≤ N0star T (2T)` —
  Theorem A in dyadic form; `N0star` is the `ncard` of the **distinct** critical-line zeros.
* `Zeta23.riemannVonMangoldt_zeta.main : ∃ C T₀, ∀ T ≥ T₀, |Ncount T (2T) − T/(2π)·ℓ₁(T)| ≤ C log T`
  — the unconditional dyadic Riemann–von Mangoldt main clause (proved upstream in `Zeta23/RvM/`).
* `Zeta23.zetaSeam.finite_window` — finitely many strip zeros in a window.

The registry predicate needs **distinct ordinates** (a `Finset ℝ`). A multiplicity-weighted
count, however sharp, cannot deliver that: the only bound on the fibre of `Complex.im` over an
ordinate is the local count `O(log T)`, which turns `T log T` into linear growth. Distinct
points on `Re = 1/2` have distinct ordinates, so a positive proportion of critical-line zeros is
exactly the missing input. This is the roadmap correction recorded in the E6 doc.

Bridge shape: window `a := T`, `L := T`; `F := image of Complex.im on {ρ ∈ zerosIn T (2T) | Re ρ = 1/2}`
(injective since `Re` is constant); `thmA₀` at `ε = 1/3` and `Ncount T (2T) ≥ (T/4π) log T`
give `r·T + 1 < F.card` for large `T`.

## The second bridge: cumulative RvM from the general-window internals

The E6 probe (Part B) found that summing the dyadic clause over `T, T/2, T/4, …` only gives an
`O(log² T)` cumulative remainder, so `RH_rvm_unconditional` is **not** a corollary of the stated
upstream theorems. `E6Bridge2.lean` re-runs the upstream's own assembly
(`Zeta23/RvM/MainTerm.lean:rvM_main_param`) on the window `[T₁, T₂]` with `T₁ ∈ [4, 5]` a
zero-free ordinate fixed once and `T₂ ∈ [T, T+1]` a zero-free ordinate near `T`, consuming as
black boxes: `N_eq_halfContour_completedZeta` (folded argument principle),
`halfContour_completedZeta_split`, `gamma_side` (Γ-side = `∫ μ`), `StirlingVert.mu_stirling`
(`|μ(τ) − (1/2π) log(τ/2π)| ≤ C/τ²`), `backlund_horizontal` (top edge), `vertical_two` (right
edge), `zeta_local_zero_count` (`N(0,T₂] → N(0,T]`), `exists_goodHeight`, `Ncount_add`,
`Ncount_mono`. The new analysis is elementary: an FTC lemma for `∫ (1/2π) log(τ/2π)` on a
general interval, the `∫ C/τ²` tail, a Lipschitz bound for the main term on `[T, T+1]`, and the
finite range `2 ≤ T < T₀` absorbed into the constant. The multiplicity seam
(`MeromorphicOn.divisor` vs `analyticOrderAt`) is `MeromorphicOn.AnalyticOnNhd.divisor_apply`
plus `Zeta23.RvM.analyticOnNhd_riemannZeta` on the open strip.

## The third bridge: the corridor bound from Landau's partial fraction + the functional equation

zeta-23-lean proves (for its Weil explicit formula) a good-height lemma
`Zeta23.WeilEF.good_heights_at`: for integer `j ≥ 7` some `R ∈ [j, j+1]` has `ζ ≠ 0` and
`‖ζ'/ζ‖ ≤ C log²(j+3)` on `Im s = ±R`, `1/2 ≤ Re s ≤ 2`. The registry node needs a **real** `T`
(window `[T, T+1]`) and the segment **`−1 ≤ σ ≤ 2`**, so `E6Bridge3.lean` re-runs the selection
at a real height (the upstream pigeonhole gap lemma `exists_far_point` already takes a real
endpoint; the zero count near `±T` is six unit windows of `zeta_local_zero_count`), consuming
`zeta_logDeriv_partial_fraction` (Landau about `2 + it`, `|t| ≥ 6`) as a black box. The left half
`σ < 1/2` is reached through `Λ(s) = Λ(1−s)`:
`ζ'/ζ(s) = −ζ'/ζ(1−s) − Γℝ'/Γℝ(1−s) − Γℝ'/Γℝ(s)` (`logDeriv_completedZeta`,
`logDeriv_completedZeta_one_sub`), with both Γℝ terms `≤ log(|t|+3) + 6` from Stirling for `ψ`
(`digamma_stirling`) and the shift `Γℝ'/Γℝ(u) = Γℝ'/Γℝ(u+2) − 1/u`. The range `2 ≤ T ≤ 7` is
absorbed by compactness: on the closed subset of `[−1,2] × [2,8]` whose ordinate is `δ`-far from
the finitely many zero ordinates there, `ζ'/ζ` is continuous, hence bounded. Three small
`Zeta23.XiPrime.*` lemmas (Γℝ shift and bounds) are re-proved locally because that challenge tree
is not built on this island.

## The fourth bridge: the explicit formula as a normalisation of zeta-23-lean's `EF_lit`

zeta-23-lean's `Zeta23/WeilEF/` (~4,500 lines) proves the Weil explicit formula in the
literature form `[eq:EFstd]` for its canonical zero configuration: for every `k ∈ C_c²(ℝ)`,
`Σ'_{ρ ∈ carrier} m_ρ · h(γ_ρ) = h(i/2) + h(−i/2) − Σ_n Λ(n)/√n (k(log n) + k(−log n))
+ (1/2π) ∫ h(r) [Re ψ(1/4 + ir/2) − log π] dr`, the zero sum `Summable`, with `carrier` the
nontrivial zeros, `m_ρ = (analyticOrderAt ζ ρ).toNat`, `h(z) = ∫ k(u) e^{izu} du`. The E8 node is
the same identity with five bookkeeping differences, each a lemma in `E6Bridge4.lean`:

* **transform** `weilKernel g s = ∫ g(u) e^{(s−1/2)u} du` is the upstream `Hfn g s = h((s−1/2)/i)`
  (`weilKernel_eq_Hfn`; `I · (x / I) = x`), so `weilKernel g 0 = h(i/2)`, `weilKernel g 1 = h(−i/2)`,
  `weilKernel g (1/2 + ir) = h(r)`;
* **archimedean term** the node writes `− g(0) log π + (1/2π) ∫ h(r) Re ψ(1/4 + ir/2) dr`; the
  difference from the upstream bracket is `(log π/2π) ∫ h(r) dr = g(0) log π`, Fourier inversion at
  the origin (`inversion_zero`, from `Zeta23.EF.paper_inversion` +
  `integrable_fourier_of_contDiff_two`);
* **integrability** the node asserts `Integrable (archIntegrand g)` separately
  (`integrable_archIntegrand`: `‖h(r)‖ ≤ C/(1+r²)` from `norm_Hfn_le`, times
  `Γℝ'/Γℝ(1/2 ± ir) = O(log(2+|r|))` through `gammaR_bracket` and the upstream majorant lemma
  `integrable_mul_logDeriv_Gammaℝ_of_decay`);
* **index set and multiplicity** the node sums over all `ρ : ℂ` with weight
  `(MeromorphicOn.divisor ζ {0 < Re < 1} ρ).toNat`; the divisor is supported in the strip
  (`supportWithinDomain`) and equals `analyticOrderAt` there
  (`MeromorphicOn.AnalyticOnNhd.divisor_apply` + `Zeta23.RvM.analyticOnNhd_riemannZeta`), and
  vanishes at strip non-zeros (`analyticOrderAt_eq_zero`), so
  `hasSum_subtype_iff_of_support_subset` transports the upstream `Summable`/`tsum` pair to the
  node's `HasSum` over `ℂ`;
* **test class** `C^∞ ⊆ C²` (`contDiff_infty`).

`E6Bridge2`/`E6Bridge3` (cumulative RvM, corridor bound) are the classical inputs the E8 design
memo planned to consume in a from-scratch contour argument; on this island the upstream's own
good-height lemma and local zero count play those roles inside `EF_lit_zetaZeroConfig`, so the
fourth bridge imports neither. The design memo's "pole-in-box seam" (§8, step 3) does not arise:
the upstream contour runs on the completed zeta `Λ(s)` with the poles at `0, 1` as residues.

## The W2c assembly: a cross-toolchain composition by verbatim re-proof

The MIRRORMERE milestone `MM_zeta_ordinates_not_uniformly_discrete` says, with no hypotheses,
that the ordinates of the nontrivial zeta zeros are **not uniformly discrete**. Both of its
registry dependencies are proved, but on different toolchains:

* `MM_nt_brick_conditional` — the elementary pigeonhole brick
  `zeta_ordinates_not_uniformlyDiscrete_of_unbounded_density`, on the **v4.32.0** quasicrystal
  island (`telperion/examples/quasicrystal/lean/BoundaryLemmas.lean`, branch `rh/million-turing`
  `@0bac3e608`, blob `b019e8e9167d51504a8775e9006ec8fceb9255bd`). Mathlib-only, zeta-free.
* `MM_rvm_unbounded_mean_density` — `RvMBridge.rvm_unbounded_mean_density` on **this** island
  (`E6Bridge.lean`, v4.33.0-rc2), from `Zeta23.thmA₀` + the RvM main clause.

Two Lean toolchains cannot meet in one environment, so the composition happens here by
**re-proving the brick verbatim**: `W2cAssembly.lean` copies the four theorems and two
definitions line-for-line from the v4.32 file (source line ranges cited above each block; only
the namespace and the docstrings differ) and applies the result to the E6 bridge's discharge.

**HONESTY LINE.** The registry dependency `MM_nt_brick_conditional` is therefore satisfied by a
verbatim re-proof on this island, **not** by consuming the v4.32 artifact. The guarantee that the
re-proof says the same thing is mechanical, not editorial: `../generate.py --check` item (7) pins
every ported statement to the v4.32 text (`_BRICK_V432_TEXT`) and fails on any drift — and when
the quasicrystal island is present in the checkout, that pin is itself diffed against the live
file. The load-bearing analytic input remains zeta-23-lean Theorem A, via `E6Bridge`; everything
added here is elementary pigeonhole packing (bin `x ↦ ⌊(x−a)/δ⌋`, more points than bins).

No RH progress is claimed: "the zeta ordinates escape the crystalline class on the space side"
is a classical consequence of `N(T)/T → ∞`. `conjecture1_proved = False`.

## Recorded results at the pin (local build, 2026-09-18, macOS arm64, 32 cores)

`lake update` + `lake exe cache get` + `lake build` (8,825 jobs, Zeta23 compiled from source)
+ `lake env lean AxiomGuardRvMBridge.lean`, verbatim (51 anchors; the last six lines of the
`RvMBridge` block were added by the W2c assembly on 2026-09-18, whose own build reused the
cached Mathlib/Zeta23 oleans):

```
'RvMBridge.rvm_unbounded_mean_density' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge.eventually_Ncount_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge.zeta_ordinates_not_uniformly_discrete' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge.zeta_ordinates_not_uniformlyDiscrete_of_unbounded_density' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RvMBridge.exists_close_of_card_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge.not_uniformlyDiscrete_of_gaps_to_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge.windowedDensity_of_unboundedMeanDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge.not_uniformlyDiscrete_of_windowedDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge2.rvm_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge2.rvm_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge2.rvm_cumulative_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge2.int_mu_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge2.zetaZeroCount_eq_Ncount' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge3.corridor_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge3.corridor_large' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge3.corridor_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge3.good_height_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge3.logDeriv_zeta_reflect' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge3.zeta_ne_zero_of_reflect' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge3.logDeriv_Gammaℝ_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge3.norm_logDeriv_Gammaℝ_le_log_strip' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge4.limit_explicit_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge4.integrable_archIntegrand' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge4.archSide_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge4.archSide_sub_primeSide' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge4.inversion_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge4.weilKernel_eq_Hfn' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge4.zeroMult_eq_of_strip' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge4.zeroMult_eq_zero_of_not_nontrivial' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.RvM.N_eq_halfContour_completedZeta' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.RvM.halfContour_completedZeta_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.RvM.gamma_side' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.RvM.backlund_horizontal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.RvM.vertical_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.StirlingVert.mu_stirling' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.thmA₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.two_thirds_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.riemannVonMangoldt_zeta' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.RvM.zeta_local_zero_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.zetaSeam' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.WeilEF.zeta_logDeriv_partial_fraction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.WeilEF.exists_far_point' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.WeilEF.logDeriv_completedZeta' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.WeilEF.logDeriv_completedZeta_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.StirlingVert.digamma_stirling' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.RvM.riemannZeta_zeros_finite_of_isCompact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.WeilEF.EF_lit_zetaZeroConfig' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.EF.paper_inversion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.WeilEF.gammaR_bracket' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.WeilEF.integrable_mul_logDeriv_Gammaℝ_of_decay' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.EF.integrable_fourier_of_contDiff_two' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Upstream's own `AUDIT.md` at the same commit records the same three axioms for all 27 Comparator
statements (`comparator.json`, `permitted_axioms = [propext, Quot.sound, Classical.choice]`).

## Run locally

```sh
cd telperion/examples/rvm_bridge/lean
lake update            # clones anthropics/formal-math (zeta23/) and Mathlib at the pins
lake exe cache get     # Mathlib oleans for 51e6992e (~2.5 min); Zeta23 itself compiles from source (~2 min on 32 cores)
lake build
lake env lean AxiomGuardRvMBridge.lean
```

## NOTICE — attribution

This island **depends on** (does not copy) `Zeta23`, the Lean development in the `zeta23/`
directory of [anthropics/formal-math](https://github.com/anthropics/formal-math)
(historically `anthropics/zeta-23-lean`, which redirects there).

* Copyright 2026 Anthropic, PBC. Licensed under the **Apache License, Version 2.0**
  (`zeta23/LICENSE`); `zeta23/NOTICE` records that it contains software derived from
  [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
  (Kontorovich–Tao).
* Mathematics: Levent Alpöge and Ralph Furman, arXiv:2608.13637. Per upstream
  `formalization.yaml`, "All Lean code was written by Claude; the trusted statement file was
  read against the paper by a paper author"; responsible maintainer Ralph Furman.
* What this island takes is the **theorem interface** (`Zeta23.thmA₀`,
  `Zeta23.riemannVonMangoldt_zeta`, `Zeta23.zetaSeam`, and for the second bridge the RvM
  internals `Zeta23.RvM.{N_eq_halfContour_completedZeta, halfContour_completedZeta_split,
  gamma_side, backlund_horizontal, vertical_two, zeta_local_zero_count, exists_goodHeight}`
  and `Zeta23.StirlingVert.mu_stirling`; for the third bridge
  `Zeta23.WeilEF.{zeta_logDeriv_partial_fraction, exists_far_point, logDeriv_completedZeta,
  logDeriv_completedZeta_one_sub}`, `Zeta23.RvM.{zeta_local_zero_count,
  riemannZeta_zeros_finite_of_isCompact, logDeriv_Gammaℝ}` and
  `Zeta23.StirlingVert.digamma_stirling`) at commit
  `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844` (2026-09-05). Theorem A, the RvM package and the
  Landau/good-height machinery are **not** this repository's work and must not be attributed to
  it; the bridges (`E6Bridge.lean`, `E6Bridge2.lean`, `E6Bridge3.lean`) are definition-level
  assembly plus elementary real/complex analysis. `E6Bridge3.lean` additionally transcribes the
  proof shape of `Zeta23.WeilEF.good_heights_at` (real height in place of integer) and three
  short lemmas from `Zeta23.XiPrime.Hardy.Basic` / `Zeta23.XiPrime.Hardy.TwoLine` /
  `Zeta23.XiPrime.ZeroCount.Y` (Apache-2.0, attributed in the file header).
