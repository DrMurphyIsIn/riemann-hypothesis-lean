/-
  PFConverseC -- pole-free Weil converse, part C (2026-10-12): assembly, and the RR-square composition.

  * `weil_positivity_poleFree_implies_rh`: Weil positivity of the explicit-formula functional on the
    Hermitian autocorrelations of POLE-FREE tests (paperFT g (+-i/2) = 0, the class Hodge1.PoleFree2)
    implies Mathlib's `RiemannHypothesis`.  Unconditional on this island: PFConverseA (pole-free
    tests and weighted strip approximation), PFConverseB (weighted dominance), Tannery
    (RvMBridgeGauss).  With the forward half (E6Bridge5) this is `rh_iff_poleFree_weil_positivity`.
  * The abstract RR-square core (ported from weil_form_enclosure/lean/RRSquare.lean, which is on a
    different Mathlib pin): RRAxioms + degree bound or no-zero-divisors => Hodge index.
  * `rh_of_rr_windows`: a family of RR-square windows whose test spaces cover every pole-free test,
    each with B(v,v) = -c Re weilForm(autocorr (tau v)) and pole-free => degree 0, implies RH.
    So Conjecture RR-square (all windows) => RH is now fully kernel-checked; the content of
    RR-square is the construction of such windows without reference to the zeros.

  Nothing here is progress on RH: the hypotheses are the open content.  conjecture1_proved = False.
-/
import PFConverseB
import E6Bridge5

open Zeta23 Complex MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace RvMBridgePF
open WeilExplicit RvMBridge6 RvMBridgeGauss

/-! ## A. The pole-free converse. -/

/-- Both pole functionals vanish (definitionally Hodge1.PoleFree2). -/
def PoleFree (g : ℝ → ℂ) : Prop := paperFT g (I / 2) = 0 ∧ paperFT g (-I / 2) = 0

/-- **Weil's criterion, converse half, on pole-free tests.** -/
theorem weil_positivity_poleFree_implies_rh
    (hpos : ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g → PoleFree g →
      0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re) :
    RiemannHypothesis := by
  apply rh_of_all_on_line
  intro ρ₀ h₀
  by_contra hre
  obtain ⟨c, lam, hlam1, hneg⟩ := weighted_dominance ρ₀ h₀ hre
  have hlam : 0 < lam := by linarith
  obtain ⟨htest, hpf, ⟨C, hC⟩, hlim⟩ := weighted_approx (c := c) hlam
  have hT : Tendsto (fun n => zeroSide (hermitianTransform (ptest c lam n))) atTop
      (𝓝 (zeroSide (qG c lam))) := by
    unfold zeroSide
    exact RvMBridgeGauss.tendsto_tsum_zeroMult_of_strip_bound hC hlim
  have hnn : ∀ n, 0 ≤ (zeroSide (hermitianTransform (ptest c lam n))).re := fun n => by
    rw [← weilForm_autocorr_eq_zeroSide (htest n)]
    exact hpos _ (htest n) (hpf n)
  have hlim_nn : 0 ≤ (zeroSide (qG c lam)).re :=
    ge_of_tendsto' ((Complex.continuous_re.tendsto _).comp hT) hnn
  linarith

/-- Both halves: RH iff Weil positivity on pole-free tests. -/
theorem rh_iff_poleFree_weil_positivity :
    RiemannHypothesis ↔ ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g → PoleFree g →
      0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re :=
  ⟨fun h g hg _ => RvMBridge5.rh_implies_weil_positivity h g hg, weil_positivity_poleFree_implies_rh⟩

/-! ## B. The RR-square core (port). -/

namespace RRSquare

variable {V Div : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup Div] [Module ℝ Div]

/-- Dimension-level axioms (a)-(d) of Conjecture RR-square for one window. -/
structure RRAxioms (B : LinearMap.BilinForm ℝ V) (f : V) (ι : V →ₗ[ℝ] Div) where
  deg : Div →ₗ[ℝ] ℝ
  deg_ι : ∀ v, deg (ι v) = B v f
  Prin : Submodule ℝ Div
  deg_prin : ∀ X ∈ Prin, deg X = 0
  Eff : Div → Prop
  h0 : Div → ℝ
  h1 : Div → ℝ
  h0_nonneg : ∀ X, 0 ≤ h0 X
  h1_nonneg : ∀ X, 0 ≤ h1 X
  K : Div
  a : V → ℝ
  χ : ℝ
  /-- Riemann-Roch index identity, with `h2 (nD) = h0 (K - nD)` (Serre duality) substituted. -/
  rr : ∀ (v : V) (n : ℕ), h0 (ι ((n : ℝ) • v)) - h1 (ι ((n : ℝ) • v)) + h0 (K - ι ((n : ℝ) • v))
      = (1 / 2) * (n : ℝ) ^ 2 * B v v - (1 / 2) * (n : ℝ) * a v + χ
  /-- Effectivity (Connes's facts 1-2): sections give an effective representative of positive degree, or a principal one. -/
  eff : ∀ X, 0 < h0 X → ∃ E, Eff E ∧ X - E ∈ Prin ∧ (0 < deg E ∨ E ∈ Prin)
  /-- Compatibility: principal divisors in the graph span are numerically trivial. -/
  compat : ∀ v, ι v ∈ Prin → B v v = 0

/-- Axioms plus "degree bounds dimension". -/
structure RRAxiomsBounded (B : LinearMap.BilinForm ℝ V) (f : V) (ι : V →ₗ[ℝ] Div)
    extends RRAxioms B f ι where
  β : ℝ → ℝ
  bound : ∀ X, h0 X ≤ β (deg X)

/-- The Hodge index from the bounded axioms (Grothendieck's argument). -/
theorem hodge_index {B : LinearMap.BilinForm ℝ V} {f : V} {ι : V →ₗ[ℝ] Div}
    (A : RRAxiomsBounded B f ι) (v : V) (hv : B v f = 0) : B v v ≤ 0 := by
  by_contra hpos
  push Not at hpos
  set c := B v v
  set M := A.β (A.deg A.K)
  set a0 := A.a v
  -- choose n ≥ 1 with n c ≥ |a0| + 2(|χ| + |M|) + 2
  obtain ⟨n, hn⟩ := exists_nat_ge ((|a0| + 2 * (|A.χ| + |M|) + 2) / c)
  set m : ℕ := n + 1
  have hm1 : (1 : ℝ) ≤ m := by simp [m]
  have hmc : |a0| + 2 * (|A.χ| + |M|) + 2 ≤ (m : ℝ) * c := by
    have h1 : (|a0| + 2 * (|A.χ| + |M|) + 2) ≤ (n : ℝ) * c := by
      rwa [div_le_iff₀ hpos] at hn
    have : (n : ℝ) * c ≤ (m : ℝ) * c := by
      apply mul_le_mul_of_nonneg_right _ hpos.le; simp [m]
    linarith
  -- degree of K - m v is deg K
  have hdegK : A.deg (A.K - ι ((m : ℝ) • v)) = A.deg A.K := by
    rw [map_sub, A.deg_ι, LinearMap.BilinForm.smul_left, hv]; ring
  have hKb : A.h0 (A.K - ι ((m : ℝ) • v)) ≤ M := by
    have := A.bound (A.K - ι ((m : ℝ) • v)); rwa [hdegK] at this
  have hrr := A.rr v m
  have hh1 := A.h1_nonneg (ι ((m : ℝ) • v))
  -- lower bound: h0 (m v) > 0
  have key : (1 / 2) * (m : ℝ) ^ 2 * c - (1 / 2) * (m : ℝ) * a0 + A.χ - M ≥ 1 := by
    have ha : -(1 / 2) * (m : ℝ) * a0 ≥ -(1 / 2) * (m : ℝ) * |a0| := by
      have h1 : (m : ℝ) * a0 ≤ (m : ℝ) * |a0| :=
        mul_le_mul_of_nonneg_left (le_abs_self a0) (by positivity)
      linarith
    have hχ : A.χ ≥ -|A.χ| := neg_abs_le _
    have hM : -M ≥ -|M| := by linarith [le_abs_self M]
    have hsq : (1 / 2) * (m : ℝ) ^ 2 * c = (1 / 2) * (m : ℝ) * ((m : ℝ) * c) := by ring
    have : (1 / 2) * (m : ℝ) * ((m : ℝ) * c)
        ≥ (1 / 2) * (m : ℝ) * (|a0| + 2 * (|A.χ| + |M|) + 2) := by
      apply mul_le_mul_of_nonneg_left hmc; positivity
    nlinarith [abs_nonneg A.χ, abs_nonneg M, abs_nonneg a0]
  have hpos0 : 0 < A.h0 (ι ((m : ℝ) • v)) := by linarith
  obtain ⟨E, -, hXE, hE⟩ := A.eff _ hpos0
  have hdegX : A.deg (ι ((m : ℝ) • v)) = 0 := by
    rw [A.deg_ι, LinearMap.BilinForm.smul_left, hv, mul_zero]
  have hdegE : A.deg E = 0 := by
    have h := A.deg_prin _ hXE
    rw [map_sub, hdegX] at h; linarith
  have hEP : E ∈ A.Prin := by
    rcases hE with h | h
    · exact absurd h (by rw [hdegE]; exact lt_irrefl 0)
    · exact h
  have hXP : ι ((m : ℝ) • v) ∈ A.Prin := by
    have := A.Prin.add_mem hXE hEP; simpa using this
  have h0B := A.compat _ hXP
  rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right] at h0B
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have : c = 0 := by
    have : (m : ℝ) * ((m : ℝ) * c) = 0 := h0B
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hm0
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hm0
      · exact h'
  linarith



/-! ## The domain alternative: no zero divisors also suffices

"No zero divisors": a nonzero section `s ∈ H⁰(A)` embeds `H⁰(B)` into `H⁰(A + B)`, so `h0 B ≤ h0 (A + B)`. This holds
automatically in Connes-Consani's characteristic-one setting, where multiplication of sections is addition of
`ℝ_max`-valued functions (an isometric embedding for the sup metric) and `Dim_ℝ` is a normalised topological dimension. -/

/-- Axioms plus "no zero divisors". -/
structure RRAxiomsDomain (B : LinearMap.BilinForm ℝ V) (f : V) (ι : V →ₗ[ℝ] Div)
    extends RRAxioms B f ι where
  domain : ∀ X Y, 0 < h0 X → h0 Y ≤ h0 (X + Y)

/-- If `ι (n • v)` has sections and `B v f = 0`, then `B v v = 0` (effectivity + compatibility). -/
lemma sections_force_null {B : LinearMap.BilinForm ℝ V} {f : V} {ι : V →ₗ[ℝ] Div}
    (A : RRAxioms B f ι) (v : V) (hv : B v f = 0) (m : ℕ) (hm : 1 ≤ m)
    (hpos0 : 0 < A.h0 (ι ((m : ℝ) • v))) : B v v = 0 := by
  obtain ⟨E, -, hXE, hE⟩ := A.eff _ hpos0
  have hdegX : A.deg (ι ((m : ℝ) • v)) = 0 := by
    rw [A.deg_ι, LinearMap.BilinForm.smul_left, hv, mul_zero]
  have hdegE : A.deg E = 0 := by
    have h := A.deg_prin _ hXE
    rw [map_sub, hdegX] at h; linarith
  have hEP : E ∈ A.Prin := by
    rcases hE with h | h
    · exact absurd h (by rw [hdegE]; exact lt_irrefl 0)
    · exact h
  have hXP : ι ((m : ℝ) • v) ∈ A.Prin := by
    have := A.Prin.add_mem hXE hEP; simpa using this
  have h0B := A.compat _ hXP
  rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right] at h0B
  have hm0 : (m : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ m := by exact_mod_cast hm
                               linarith
  have : (m : ℝ) * ((m : ℝ) * B v v) = 0 := h0B
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hm0
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hm0
    · exact h'

/-- Large `n` makes both Riemann-Roch right-hand sides beat any fixed constant. -/
lemma rr_rhs_large (c a1 a2 χ M : ℝ) (hc : 0 < c) :
    ∃ m : ℕ, 1 ≤ m ∧ (1 / 2) * (m : ℝ) ^ 2 * c - (1 / 2) * (m : ℝ) * a1 + χ - M ≥ 1 ∧
      (1 / 2) * (m : ℝ) ^ 2 * c - (1 / 2) * (m : ℝ) * a2 + χ - M ≥ 1 := by
  set a := |a1| + |a2|
  obtain ⟨n, hn⟩ := exists_nat_ge ((a + 2 * (|χ| + |M|) + 2) / c)
  have hm1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by simp
  have hmc : a + 2 * (|χ| + |M|) + 2 ≤ ((n + 1 : ℕ) : ℝ) * c := by
    have h1 : (a + 2 * (|χ| + |M|) + 2) ≤ (n : ℝ) * c := by rwa [div_le_iff₀ hc] at hn
    have : (n : ℝ) * c ≤ ((n + 1 : ℕ) : ℝ) * c := by
      apply mul_le_mul_of_nonneg_right _ hc.le; simp
    linarith
  have hbig : (1 / 2) * ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) * c)
      ≥ (1 / 2) * ((n + 1 : ℕ) : ℝ) * (a + 2 * (|χ| + |M|) + 2) := by
    apply mul_le_mul_of_nonneg_left hmc; positivity
  have ha1 : a1 ≤ a := by have := le_abs_self a1; have := abs_nonneg a2; simp only [a]; linarith
  have ha2 : a2 ≤ a := by have := le_abs_self a2; have := abs_nonneg a1; simp only [a]; linarith
  have hχ := neg_abs_le χ
  have hM := le_abs_self M
  set N : ℝ := ((n + 1 : ℕ) : ℝ)
  have hsq : (1 / 2) * N ^ 2 * c = (1 / 2) * N * (N * c) := by ring
  have hprod : 0 ≤ (N - 1) * (|χ| + |M|) :=
    mul_nonneg (by linarith) (by positivity)
  refine ⟨n + 1, by omega, ?_, ?_⟩
  · have h3 : N * a1 ≤ N * a := mul_le_mul_of_nonneg_left ha1 (by positivity)
    have : (1 / 2) * N ^ 2 * c - (1 / 2) * N * a1 + χ - M ≥ 1 := by
      rw [hsq]; nlinarith
    exact this
  · have h3 : N * a2 ≤ N * a := mul_le_mul_of_nonneg_left ha2 (by positivity)
    have : (1 / 2) * N ^ 2 * c - (1 / 2) * N * a2 + χ - M ≥ 1 := by
      rw [hsq]; nlinarith
    exact this

/-- The Hodge index from the domain axioms (no degree bound needed). -/
theorem hodge_index_of_domain {B : LinearMap.BilinForm ℝ V} {f : V} {ι : V →ₗ[ℝ] Div}
    (A : RRAxiomsDomain B f ι) (v : V) (hv : B v f = 0) : B v v ≤ 0 := by
  by_contra hpos
  push Not at hpos
  set c := B v v
  set M := A.h0 (A.K + A.K)
  have hM0 : 0 ≤ M := A.h0_nonneg _
  obtain ⟨m, hm, hb1, hb2⟩ := rr_rhs_large c (A.a v) (A.a (-v)) A.χ M hpos
  have hvneg : B (-v) f = 0 := by simp [hv]
  have hcneg : B (-v) (-v) = c := by simp [c]
  have hrr := A.rr v m
  have hrr' := A.rr (-v) m
  have hh1 := A.h1_nonneg (ι ((m : ℝ) • v))
  have hh1' := A.h1_nonneg (ι ((m : ℝ) • (-v)))
  have hKeq : A.K - ι ((m : ℝ) • (-v)) = A.K + ι ((m : ℝ) • v) := by
    simp [smul_neg, map_neg, sub_neg_eq_add]
  rw [hKeq, hcneg] at hrr'
  by_cases hK : 0 < A.h0 (A.K - ι ((m : ℝ) • v))
  · have hdom := A.domain _ (A.K + ι ((m : ℝ) • v)) hK
    have hsum : A.K - ι ((m : ℝ) • v) + (A.K + ι ((m : ℝ) • v)) = A.K + A.K := by abel
    rw [hsum] at hdom
    have hp : 0 < A.h0 (ι ((m : ℝ) • (-v))) := by linarith
    have := sections_force_null A.toRRAxioms (-v) hvneg m hm hp
    rw [hcneg] at this; linarith
  · push Not at hK
    have hp : 0 < A.h0 (ι ((m : ℝ) • v)) := by linarith
    exact absurd (sections_force_null A.toRRAxioms v hv m hm hp) (ne_of_gt hpos)


end RRSquare

/-! ## C. Composition: RR-square on every window implies RH. -/

open RRSquare in
/-- One window of an RR-square: a real space of tests with a bilinear form whose diagonal is a
negative multiple of Weil's quadratic form, a degree class killing pole-free tests, and the RR
axioms in either the degree-bound or the no-zero-divisor form. -/
structure RRWindow where
  V : Type
  Div : Type
  [iV : AddCommGroup V]
  [mV : Module ℝ V]
  [iD : AddCommGroup Div]
  [mD : Module ℝ Div]
  B : LinearMap.BilinForm ℝ V
  f : V
  ι : V →ₗ[ℝ] Div
  ax : RRAxiomsBounded B f ι ⊕ RRAxiomsDomain B f ι
  τ : V → (ℝ → ℂ)
  c : ℝ
  hc : 0 < c
  hdiag : ∀ v, B v v = -(c * (WeilExplicit.weilForm (WeilExplicit.autocorr (τ v))).re)
  hpole : ∀ v, PoleFree (τ v) → B v f = 0

attribute [instance] RRWindow.iV RRWindow.mV RRWindow.iD RRWindow.mD

open RRSquare in
/-- Weil positivity on one window. -/
theorem RRWindow.weil_positive (W : RRWindow) (v : W.V) (hv : PoleFree (W.τ v)) :
    0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr (W.τ v))).re := by
  have hf := W.hpole v hv
  have h : W.B v v ≤ 0 := by
    rcases W.ax with A | A
    · exact hodge_index A v hf
    · exact hodge_index_of_domain A v hf
  rw [W.hdiag] at h
  have := W.hc
  by_contra hneg
  push Not at hneg
  nlinarith

/-- **RR-square on every window implies RH.**  If a family of RR-square windows covers every
pole-free Weil test, Mathlib's RiemannHypothesis holds. -/
theorem rh_of_rr_windows {ι' : Type} (W : ι' → RRWindow)
    (hcover : ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g → PoleFree g →
      ∃ i : ι', ∃ v : (W i).V, (W i).τ v = g) :
    RiemannHypothesis := by
  apply weil_positivity_poleFree_implies_rh
  intro g hg hpf
  obtain ⟨i, v, rfl⟩ := hcover g hg hpf
  exact (W i).weil_positive v hpf

end RvMBridgePF
