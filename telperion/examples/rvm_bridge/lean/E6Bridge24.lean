/-
  E6Bridge24 -- StripDerivBound (obligation 2 of the growth bound), 2026-09-21.

  TARGET.  RvMBridge22.StripDerivBound :
      ∃ C, ∀ s, 1/4 ≤ Re s → Re s ≤ 9/4 → 5 ≤ |Im s| → ¬ IsNontrivialZero s →
        ‖deriv (logDeriv xi) s + Sum_{rho ∈ window s} m(rho)/(s - rho)^2‖ ≤ C (1 + log (2 + |Im s|)),
  window s = the nontrivial zeros with |Im rho - Im s| ≤ 2.

  THE ARGUMENT.
    (1) COUNT.  Sum_{rho ∈ window s} m(rho) ≤ 5 A0 log(|Im s| + 6): the window is covered by five
        unit windows and Zeta23.RvM.zeta_local_zero_count bounds each (window_sum_le).
    (2) DIGAMMA.  ‖psi(z)‖ ≤ log(2 + |Im z|) + pi + 7/2 for 0 < Re z ≤ 2, |Im z| ≥ 1
        (Zeta23.StirlingVert.digamma_stirling).
    (3) LANDAU, repackaged (landau_window): for |Im w| ≥ 6, 1/2 ≤ Re w ≤ 7/2, w not a zero, there
        is a finite set Z of nontrivial zeros with |Im rho - Im w| ≤ 1.61, total multiplicity
        ≤ C log(|Im w| + 3), and ‖zeta'/zeta(w) - Sum_Z m/(w - rho)‖ ≤ C log(|Im w| + 3).
    (4) THE FUNCTION.  Fwin s w := logDeriv xi w - Sum_{window s} m/(w - rho), with its punctured
        limits at the zeros (FwinExt), is DIFFERENTIABLE on the disc D(s, 1/2) (the double poles
        are exactly cancelled, as in E6Bridge20), and deriv (FwinExt s) s is the target quantity.
    (5) CAUCHY on a circle of radius r ∈ (1/4, 1/2) avoiding the finitely many zeros in the disc:
        ‖target‖ ≤ 4 sup_{|w - s| = r} ‖Fwin s w‖.
    (6) THE SUP.  For Re w ≥ 1/2: Fwin s w = 1/w + 1/(w - 1) + logDeriv Gamma_R w
        + [zeta'/zeta(w) - Sum_Z] + [Sum_Z - Sum_{window s}]; the last bracket is a sum over the
        symmetric difference, whose zeros are at distance ≥ 1/10 from w, with total multiplicity
        O(log) by (1) and (3).  For Re w < 1/2: Fwin s w = -Fwin (1 - s) (1 - w) (functional
        equation and the reflection symmetry of the divisor) and the same bound at 1 - w.
    (7) LOW HEIGHTS |Im s| ≤ 7 (where Landau's |t| ≥ 6 is not available on the whole circle):
        the target equals xiDiffExt s - Sum_{rho ∉ window s} m/(s - rho)^2, bounded by the compact
        bound of xiDiffExt and E6Bridge22's far-sum comparison; no Landau needed.

  2026-09-22: the closed zero set (isClosed_zeros / eventually_not_zero), the local unit factor
  computation behind logDeriv_xi_local, the punctured-limit extension atom behind
  FwinExt_eventuallyEq_at_zero, the finite-avoidance radius and the rectangle bound are the
  prelude's (RvMBridgeXi); every node theorem here is unchanged, statement verbatim.

  conjecture1_proved = False.  Nothing here bears on RH.
-/
import E6Bridge22
import RvMBridgeXi
import Zeta23.WeilEF.Landau
import Zeta23.GammaFacts.StirlingVert
import Zeta23.RvM.GammaSide

open Zeta23 Complex MeasureTheory Filter Topology Metric
open scoped ComplexConjugate

noncomputable section

namespace RvMBridge24
open WeilExplicit RvMBridge18 RvMBridge20 RvMBridge22 RvMBridgeXi

/-! ## A. The window count from the local zero count. -/

/-- On nontrivial zeros the registry multiplicity is Zeta23's. -/
lemma zeroMult_eq_zeta23 {ρ : ℂ} (h : IsNontrivialZero ρ) :
    WeilExplicit.zeroMult ρ = Zeta23.zeroMult ρ :=
  RvMBridge4.zeroMult_eq_of_strip h.2.1 h.2.2

/-- The zeros in (T₁, T₂] as a finite set. -/
lemma zerosIn_finite (T₁ T₂ : ℝ) : (zerosIn T₁ T₂).Finite := by
  refine (zetaSeam.finite_window T₁ T₂).subset ?_
  rintro ρ ⟨h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

/-- A finite set of nontrivial zeros with ordinates in (T₁, T₂] has total multiplicity ≤ Ncount. -/
lemma sum_le_Ncount (T₁ T₂ : ℝ) (W : Finset ℂ)
    (hW : ∀ ρ ∈ W, IsNontrivialZero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂) :
    (∑ ρ ∈ W, (WeilExplicit.zeroMult ρ : ℝ)) ≤ (Ncount T₁ T₂ : ℝ) := by
  have hfin := zerosIn_finite T₁ T₂
  have hN : Ncount T₁ T₂ = ∑ ρ ∈ hfin.toFinset, Zeta23.zeroMult ρ := by
    unfold Ncount
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  rw [hN]
  push_cast
  have hsub : W ⊆ hfin.toFinset := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset]
    exact hW ρ hρ
  calc (∑ ρ ∈ W, (WeilExplicit.zeroMult ρ : ℝ))
      = ∑ ρ ∈ W, (Zeta23.zeroMult ρ : ℝ) :=
        Finset.sum_congr rfl fun ρ hρ => by rw [zeroMult_eq_zeta23 (hW ρ hρ).1]
    _ ≤ ∑ ρ ∈ hfin.toFinset, (Zeta23.zeroMult ρ : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _

/-- The window is covered by five unit windows. -/
lemma window_sum_le_five (s : ℂ) :
    (∑ ρ ∈ window s, (WeilExplicit.zeroMult ρ : ℝ))
      ≤ ∑ k ∈ Finset.Icc (-3 : ℤ) 1, (Ncount (s.im + k) (s.im + k + 1) : ℝ) := by
  classical
  set a := s.im
  -- each rho lies in at least one unit window
  have hcover : ∀ ρ ∈ window s, (WeilExplicit.zeroMult ρ : ℝ)
      ≤ ∑ k ∈ Finset.Icc (-3 : ℤ) 1,
          (if a + k < ρ.im ∧ ρ.im ≤ a + k + 1 then (WeilExplicit.zeroMult ρ : ℝ) else 0) := by
    intro ρ hρ
    obtain ⟨-, hw⟩ := mem_window.mp hρ
    have hw' := abs_le.mp hw
    -- k := ⌈ρ.im - a⌉ - 1
    set k : ℤ := ⌈ρ.im - a⌉ - 1 with hk
    have hk1 : (k : ℝ) < ρ.im - a := by
      rw [hk]; push_cast
      linarith [Int.ceil_lt_add_one (ρ.im - a)]
    have hk2 : ρ.im - a ≤ (k : ℝ) + 1 := by
      rw [hk]; push_cast
      linarith [Int.le_ceil (ρ.im - a)]
    have hkmem : k ∈ Finset.Icc (-3 : ℤ) 1 := by
      rw [Finset.mem_Icc]
      have h1 : (k : ℝ) < 2 := by linarith [hw'.2]
      have h2 : (-3 : ℝ) ≤ k := by linarith [hw'.1]
      have h1' : k < 2 := by exact_mod_cast h1
      have h2' : (-3 : ℤ) ≤ k := by exact_mod_cast h2
      constructor <;> omega
    have hpos : ∀ j ∈ Finset.Icc (-3 : ℤ) 1, (0 : ℝ) ≤
        (if a + j < ρ.im ∧ ρ.im ≤ a + j + 1 then (WeilExplicit.zeroMult ρ : ℝ) else 0) := by
      intro j _
      split_ifs <;> positivity
    calc (WeilExplicit.zeroMult ρ : ℝ)
        = (if a + k < ρ.im ∧ ρ.im ≤ a + k + 1 then (WeilExplicit.zeroMult ρ : ℝ) else 0) := by
          rw [if_pos ⟨by linarith, by linarith⟩]
      _ ≤ _ := Finset.single_le_sum hpos hkmem
  calc (∑ ρ ∈ window s, (WeilExplicit.zeroMult ρ : ℝ))
      ≤ ∑ ρ ∈ window s, ∑ k ∈ Finset.Icc (-3 : ℤ) 1,
          (if a + k < ρ.im ∧ ρ.im ≤ a + k + 1 then (WeilExplicit.zeroMult ρ : ℝ) else 0) :=
        Finset.sum_le_sum hcover
    _ = ∑ k ∈ Finset.Icc (-3 : ℤ) 1, ∑ ρ ∈ window s,
          (if a + k < ρ.im ∧ ρ.im ≤ a + k + 1 then (WeilExplicit.zeroMult ρ : ℝ) else 0) :=
        Finset.sum_comm
    _ = ∑ k ∈ Finset.Icc (-3 : ℤ) 1, ∑ ρ ∈ (window s).filter (fun ρ => a + k < ρ.im ∧ ρ.im ≤ a + k + 1),
          (WeilExplicit.zeroMult ρ : ℝ) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_filter]
    _ ≤ ∑ k ∈ Finset.Icc (-3 : ℤ) 1, (Ncount (a + k) (a + k + 1) : ℝ) := by
        refine Finset.sum_le_sum fun k _ => ?_
        refine sum_le_Ncount _ _ _ fun ρ hρ => ?_
        rw [Finset.mem_filter] at hρ
        exact ⟨(mem_window.mp hρ.1).1, hρ.2.1, hρ.2.2⟩

/-- **The window count**: ∃ A, ∀ s, Sum_{window s} m ≤ A log(|Im s| + 6). -/
theorem exists_window_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ s : ℂ, (∑ ρ ∈ window s, (WeilExplicit.zeroMult ρ : ℝ)) ≤ A * Real.log (|s.im| + 6) := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zeta_local_zero_count
  refine ⟨5 * A₀, by linarith, fun s => ?_⟩
  refine (window_sum_le_five s).trans ?_
  have hterm : ∀ k ∈ Finset.Icc (-3 : ℤ) 1,
      (Ncount (s.im + k) (s.im + k + 1) : ℝ) ≤ A₀ * Real.log (|s.im| + 6) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    refine (hloc (s.im + k)).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) (by linarith)
    have hk1 : (-3 : ℝ) ≤ k := by exact_mod_cast hk.1
    have hk2 : (k : ℝ) ≤ 1 := by exact_mod_cast hk.2
    have := abs_add_le s.im (k : ℝ)
    have hkabs : |(k : ℝ)| ≤ 3 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  calc ∑ k ∈ Finset.Icc (-3 : ℤ) 1, (Ncount (s.im + k) (s.im + k + 1) : ℝ)
      ≤ ∑ _k ∈ Finset.Icc (-3 : ℤ) 1, A₀ * Real.log (|s.im| + 6) := Finset.sum_le_sum hterm
    _ = 5 * A₀ * Real.log (|s.im| + 6) := by
        rw [Finset.sum_const]
        have hcard : (Finset.Icc (-3 : ℤ) 1).card = 5 := by decide
        rw [hcard]
        simp only [nsmul_eq_mul, Nat.cast_ofNat]
        ring

/-! ## B. The digamma bound and the log bound. -/

lemma norm_log_le (z : ℂ) (hz : 1 ≤ ‖z‖) : ‖Complex.log z‖ ≤ Real.log ‖z‖ + Real.pi := by
  have h := Complex.norm_le_abs_re_add_abs_im (Complex.log z)
  rw [Complex.log_re, Complex.log_im] at h
  have hl : |Real.log ‖z‖| = Real.log ‖z‖ := abs_of_nonneg (Real.log_nonneg hz)
  rw [hl] at h
  linarith [Complex.abs_arg_le_pi z]

/-- ‖psi z‖ ≤ log(2 + |Im z|) + pi + 7/2 for 0 < Re z ≤ 2, |Im z| ≥ 1. -/
theorem norm_digamma_le_log {z : ℂ} (hre : 0 < z.re) (hre' : z.re ≤ 2) (him : 1 ≤ |z.im|) :
    ‖Complex.digamma z‖ ≤ Real.log (2 + |z.im|) + Real.pi + 7 / 2 := by
  have hst := Zeta23.StirlingVert.digamma_stirling hre (by linarith)
  have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hre; exact lt_irrefl _ hre
  have hn1 : 1 ≤ ‖z‖ := him.trans (Complex.abs_im_le_norm z)
  have hn : ‖z‖ ≤ 2 + |z.im| := by
    have := Complex.norm_le_abs_re_add_abs_im z
    have : |z.re| ≤ 2 := abs_le.mpr ⟨by linarith, hre'⟩
    linarith
  have hlog : ‖Complex.log z‖ ≤ Real.log (2 + |z.im|) + Real.pi := by
    refine (norm_log_le z hn1).trans ?_
    linarith [Real.log_le_log (by linarith) hn]
  have hinv : ‖(1 / 2 : ℂ) / z‖ ≤ 1 / 2 := by
    rw [norm_div]
    have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [h12, div_le_iff₀ (by linarith)]
    linarith
  have hrem : 3 / z.im ^ 2 ≤ 3 := by
    have h1 : 1 ≤ z.im ^ 2 := by
      have := sq_abs z.im
      nlinarith [abs_nonneg z.im]
    rw [div_le_iff₀ (by positivity)]
    linarith
  calc ‖Complex.digamma z‖
      = ‖(Complex.digamma z - Complex.log z + (1 / 2 : ℂ) / z) + Complex.log z - (1 / 2 : ℂ) / z‖ := by
        congr 1; ring
    _ ≤ ‖Complex.digamma z - Complex.log z + (1 / 2 : ℂ) / z‖ + ‖Complex.log z‖ + ‖(1 / 2 : ℂ) / z‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ 3 + (Real.log (2 + |z.im|) + Real.pi) + 1 / 2 := by
        gcongr
        exact hst.trans hrem
    _ = Real.log (2 + |z.im|) + Real.pi + 7 / 2 := by ring

/-! ## C. Landau's local partial fraction, repackaged. -/

/-- Landau in the island's vocabulary: at every w with |Im w| ≥ 6, 1/2 ≤ Re w ≤ 7/2, not a zero,
a finite set Z of nontrivial zeros with |Im rho - Im w| ≤ 161/100, total multiplicity
≤ C log(|Im w| + 3), such that ‖zeta'/zeta(w) - Sum_Z m(rho)/(w - rho)‖ ≤ C log(|Im w| + 3);
moreover every nontrivial zero within distance 161/100 ... is NOT claimed: instead, every
nontrivial zero NOT in Z is at distance > 8/5 from 2 + i Im w. -/
theorem landau_window : ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, 6 ≤ |w.im| → 1 / 2 ≤ w.re → w.re ≤ 7 / 2 →
    ¬ IsNontrivialZero w → ∃ Z : Finset ℂ,
      (∀ ρ ∈ Z, IsNontrivialZero ρ ∧ dist ρ (2 + w.im * I) ≤ 161 / 100) ∧
      (∀ ρ : ℂ, IsNontrivialZero ρ → ρ ∉ Z → 8 / 5 < dist ρ (2 + w.im * I)) ∧
      (∑ ρ ∈ Z, (WeilExplicit.zeroMult ρ : ℝ)) ≤ C * Real.log (|w.im| + 3) ∧
      ‖logDeriv riemannZeta w - ∑ ρ ∈ Z, (WeilExplicit.zeroMult ρ : ℂ) / (w - ρ)‖
        ≤ C * Real.log (|w.im| + 3) := by
  obtain ⟨C, hC, hL⟩ := Zeta23.WeilEF.zeta_logDeriv_partial_fraction
  refine ⟨C, hC, fun w him hre hre' hnz => ?_⟩
  obtain ⟨Z, hZ, hcount, hbound⟩ := hL w.im him
  have hmemZ : ∀ ρ, ρ ∈ Z ↔ ρ ∈ closedBall (2 + w.im * I) (22 / 25 * (91 / 50)) ∧ riemannZeta ρ = 0 := by
    intro ρ
    exact Finset.mem_coe.symm.trans (Set.ext_iff.mp hZ ρ)
  -- zeros of zeta in the ball are nontrivial
  have hnt : ∀ ρ ∈ Z, IsNontrivialZero ρ := by
    intro ρ hρ
    obtain ⟨hball, hz⟩ := (hmemZ ρ).mp hρ
    rw [mem_closedBall, dist_eq_norm] at hball
    have hre1 := Complex.abs_re_le_norm (ρ - (2 + w.im * I))
    have hreρ : (ρ - (2 + w.im * I)).re = ρ.re - 2 := by simp
    rw [hreρ] at hre1
    have h0 : 0 < ρ.re := by
      have := abs_le.mp hre1
      linarith [this.1]
    have h1 : ρ.re < 1 := by
      by_contra hge
      push Not at hge
      exact riemannZeta_ne_zero_of_one_le_re hge hz
    exact ⟨hz, h0, h1⟩
  have hζw : riemannZeta w ≠ 0 := by
    intro hz
    rcases lt_or_ge w.re 1 with h1 | h1
    · exact hnz ⟨hz, by linarith, h1⟩
    · exact riemannZeta_ne_zero_of_one_le_re h1 hz
  have hwball : w ∈ closedBall (2 + w.im * I) (3 / 2) := by
    rw [mem_closedBall, dist_eq_norm]
    have : w - (2 + w.im * I) = ((w.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hord : ∀ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ) = (WeilExplicit.zeroMult ρ : ℝ) := by
    intro ρ hρ
    rw [zeroMult_eq_zeta23 (hnt ρ hρ)]
    rfl
  have hordC : ∀ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) = (WeilExplicit.zeroMult ρ : ℂ) := by
    intro ρ hρ
    rw [zeroMult_eq_zeta23 (hnt ρ hρ)]
    rfl
  refine ⟨Z, fun ρ hρ => ⟨hnt ρ hρ, ?_⟩, fun ρ hρnt hρZ => ?_, ?_, ?_⟩
  · have := ((hmemZ ρ).mp hρ).1
    rw [mem_closedBall] at this
    have h : (22 / 25 * (91 / 50) : ℝ) ≤ 161 / 100 := by norm_num
    linarith
  · by_contra hle
    push Not at hle
    apply hρZ
    rw [hmemZ]
    refine ⟨?_, hρnt.1⟩
    rw [mem_closedBall]
    -- need dist ≤ 22/25 * 91/50; we only know ≤ 8/5 = 1.6 > 1.6016?  8/5 = 1.6 < 1.6016 ok
    calc dist ρ (2 + w.im * I) ≤ 8 / 5 := hle
      _ ≤ 22 / 25 * (91 / 50) := by norm_num
  · calc (∑ ρ ∈ Z, (WeilExplicit.zeroMult ρ : ℝ)) = ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ) :=
          Finset.sum_congr rfl fun ρ hρ => (hord ρ hρ).symm
      _ ≤ C * Real.log (|w.im| + 3) := hcount
  · have h := hbound w hwball hζw
    calc ‖logDeriv riemannZeta w - ∑ ρ ∈ Z, (WeilExplicit.zeroMult ρ : ℂ) / (w - ρ)‖
        = ‖logDeriv riemannZeta w - ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (w - ρ)‖ := by
          congr 2
          exact Finset.sum_congr rfl fun ρ hρ => by rw [hordC ρ hρ]
      _ ≤ C * Real.log (|w.im| + 3) := h

/-! ## D. The punctured-window function and its entire-on-the-disc extension. -/

/-- Fwin s w = logDeriv xi w - Sum_{window s} m(rho)/(w - rho). -/
def Fwin (s w : ℂ) : ℂ :=
  logDeriv xi w - ∑ ρ ∈ window s, (WeilExplicit.zeroMult ρ : ℂ) / (w - ρ)

open scoped Classical in
/-- Fwin with its punctured limits at the zeros. -/
def FwinExt (s w : ℂ) : ℂ :=
  if IsNontrivialZero w then limUnder (𝓝[≠] w) (Fwin s) else Fwin s w

lemma FwinExt_eq {s w : ℂ} (hw : ¬ IsNontrivialZero w) : FwinExt s w = Fwin s w := by
  unfold FwinExt
  rw [if_neg hw]

/-! The zero set is closed: isClosed_zeros / eventually_not_zero are the prelude's (RvMBridgeXi). -/

/-- The local form of logDeriv xi at s₀ (E6Bridge20's unit factor, the prelude's computation). -/
lemma logDeriv_xi_local (s₀ : ℂ) : ∃ ε > 0, ∃ u : ℂ → ℂ,
    (∀ z ∈ ball s₀ ε, AnalyticAt ℂ u z ∧ u z ≠ 0) ∧
    ∀ z ∈ ball s₀ ε, z ≠ s₀ →
      logDeriv xi z = (WeilExplicit.zeroMult s₀ : ℂ) * (z - s₀)⁻¹ + logDeriv u z := by
  obtain ⟨u, hu, hu0, hxu⟩ := exists_unit_factor s₀
  have hall : ∀ᶠ z in 𝓝 s₀, xi z = (z - s₀) ^ (WeilExplicit.zeroMult s₀) * u z ∧
      AnalyticAt ℂ u z ∧ u z ≠ 0 :=
    hxu.and (hu.eventually_analyticAt.and (hu.continuousAt.eventually_ne hu0))
  obtain ⟨ε, hε, hεall⟩ := Metric.eventually_nhds_iff.mp hall
  exact ⟨ε, hε, u, fun z hz => (hεall (mem_ball.mp hz)).2, fun z hz hne =>
    logDeriv_of_unit_factor hεall (mem_ball.mp hz) hne⟩

lemma Fwin_differentiableAt {s w₀ : ℂ} (hw₀ : ¬ IsNontrivialZero w₀) :
    DifferentiableAt ℂ (Fwin s) w₀ := by
  unfold Fwin
  refine DifferentiableAt.sub ?_ ?_
  · exact (analyticAt_logDeriv (xi_differentiable.analyticAt _)
      (xi_ne_zero_of_not_nontrivial hw₀)).differentiableAt
  · have hfun : (fun w : ℂ => ∑ ρ ∈ window s, (WeilExplicit.zeroMult ρ : ℂ) / (w - ρ))
        = ∑ ρ ∈ window s, (fun w : ℂ => (WeilExplicit.zeroMult ρ : ℂ) / (w - ρ)) := by
      funext w
      simp [Finset.sum_apply]
    rw [hfun]
    refine DifferentiableAt.sum (𝕜 := ℂ) (u := window s)
      (A := fun ρ w => (WeilExplicit.zeroMult ρ : ℂ) / (w - ρ)) fun ρ hρ => ?_
    have hne : w₀ - ρ ≠ 0 := sub_ne_zero.mpr fun h => hw₀ (by rw [h]; exact (mem_window.mp hρ).1)
    exact (differentiableAt_const _).div (differentiableAt_id.sub_const ρ) hne

/-- Around a zero w₀ in the disc, FwinExt agrees with an analytic function (the double pole of
logDeriv xi is cancelled by the w₀ term of the window sum). -/
lemma FwinExt_eventuallyEq_at_zero {s w₀ : ℂ} (hw₀ : IsNontrivialZero w₀) (hdist : dist w₀ s < 1 / 2) :
    ∃ H : ℂ → ℂ, DifferentiableAt ℂ H w₀ ∧ FwinExt s =ᶠ[𝓝 w₀] H := by
  classical
  obtain ⟨ε, hε, u, hu, hloc⟩ := logDeriv_xi_local w₀
  obtain ⟨ε₂, hε₂, hε₂1, hfar⟩ := exists_ball_avoid w₀
  have himw : |w₀.im - s.im| ≤ dist w₀ s := by
    rw [dist_eq_norm]
    have := Complex.abs_im_le_norm (w₀ - s)
    rwa [Complex.sub_im] at this
  have hw₀win : w₀ ∈ window s := mem_window.mpr ⟨hw₀, by linarith⟩
  set r := min ε (min ε₂ 1) with hr
  have hr0 : 0 < r := by positivity
  have hrε : r ≤ ε := min_le_left _ _
  have hrε₂ : r ≤ ε₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  -- other window zeros are at distance ≥ r from w₀
  have hsep : ∀ ρ ∈ window s, ρ ≠ w₀ → r ≤ dist ρ w₀ := by
    intro ρ hρ hne
    have hnt := (mem_window.mp hρ).1
    by_cases hnear : |ρ.im - w₀.im| < 2
    · exact hrε₂.trans (hfar ρ ⟨⟨hnt, hnear⟩, hne⟩)
    · push Not at hnear
      have := Complex.abs_im_le_norm (ρ - w₀)
      rw [Complex.sub_im] at this
      rw [dist_eq_norm]
      linarith
  set H : ℂ → ℂ := fun z => logDeriv u z - ∑ ρ ∈ (window s).erase w₀, (WeilExplicit.zeroMult ρ : ℂ) / (z - ρ)
    with hH
  have hHdiff : DifferentiableAt ℂ H w₀ := by
    refine DifferentiableAt.sub ?_ ?_
    · exact (analyticAt_logDeriv (hu w₀ (Metric.mem_ball_self hε)).1 (hu w₀ (Metric.mem_ball_self hε)).2).differentiableAt
    · have hfun : (fun z : ℂ => ∑ ρ ∈ (window s).erase w₀, (WeilExplicit.zeroMult ρ : ℂ) / (z - ρ))
          = ∑ ρ ∈ (window s).erase w₀, (fun z : ℂ => (WeilExplicit.zeroMult ρ : ℂ) / (z - ρ)) := by
        funext z
        simp [Finset.sum_apply]
      rw [hfun]
      refine DifferentiableAt.sum (𝕜 := ℂ) (u := (window s).erase w₀)
        (A := fun ρ z => (WeilExplicit.zeroMult ρ : ℂ) / (z - ρ)) fun ρ hρ => ?_
      have hρne : ρ ≠ w₀ := (Finset.mem_erase.mp hρ).1
      exact (differentiableAt_const _).div (differentiableAt_id.sub_const ρ) (sub_ne_zero.mpr hρne.symm)
  -- on the punctured ball: no zeros, and Fwin = H
  have hball : ∀ z ∈ ball w₀ r, z ≠ w₀ → ¬ IsNontrivialZero z ∧ Fwin s z = H z := by
    intro z hz hne
    have hzr : dist z w₀ < r := mem_ball.mp hz
    have hnz : ¬ IsNontrivialZero z := by
      intro hzz
      have hzim : |z.im - s.im| ≤ 2 := by
        have h1 := Complex.abs_im_le_norm (z - w₀)
        rw [Complex.sub_im] at h1
        rw [dist_eq_norm] at hzr
        have : |z.im - s.im| ≤ |z.im - w₀.im| + |w₀.im - s.im| := by
          have := abs_sub_le z.im w₀.im s.im
          linarith
        linarith
      have hzwin : z ∈ window s := mem_window.mpr ⟨hzz, hzim⟩
      have := hsep z hzwin hne
      linarith
    refine ⟨hnz, ?_⟩
    unfold Fwin
    rw [hloc z (mem_ball.mpr (lt_of_lt_of_le hzr hrε)) hne, hH]
    rw [← Finset.add_sum_erase (window s) _ hw₀win]
    have : (WeilExplicit.zeroMult w₀ : ℂ) * (z - w₀)⁻¹ = (WeilExplicit.zeroMult w₀ : ℂ) / (z - w₀) :=
      (div_eq_mul_inv _ _).symm
    rw [this]
    ring
  exact ⟨H, hHdiff, ext_eventuallyEq_of_punctured (P := IsNontrivialZero) (f := Fwin s) hr0
    (fun _ hw => FwinExt_eq hw) (fun w hw => by unfold FwinExt; rw [if_pos hw])
    hHdiff.continuousAt hball (fun h => absurd hw₀ h)⟩

/-- FwinExt s is differentiable on the disc D(s, 1/2). -/
theorem FwinExt_differentiableOn (s : ℂ) : DifferentiableOn ℂ (FwinExt s) (ball s (1 / 2)) := by
  intro w₀ hw₀
  refine DifferentiableAt.differentiableWithinAt ?_
  by_cases hz : IsNontrivialZero w₀
  · obtain ⟨H, hH, hev⟩ := FwinExt_eventuallyEq_at_zero hz (mem_ball.mp hw₀)
    exact hev.differentiableAt_iff.mpr hH
  · have hev : FwinExt s =ᶠ[𝓝 w₀] Fwin s := by
      filter_upwards [eventually_not_zero hz] with z hz'
      exact FwinExt_eq hz'
    exact hev.differentiableAt_iff.mpr (Fwin_differentiableAt hz)

/-- The derivative of FwinExt s at s is the target quantity. -/
theorem deriv_FwinExt {s : ℂ} (hs : ¬ IsNontrivialZero s) :
    deriv (FwinExt s) s
      = deriv (logDeriv xi) s + ∑ ρ ∈ window s, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2 := by
  have hev : FwinExt s =ᶠ[𝓝 s] Fwin s := by
    filter_upwards [eventually_not_zero hs] with z hz'
    exact FwinExt_eq hz'
  rw [hev.deriv_eq]
  have h1 : HasDerivAt (logDeriv xi) (deriv (logDeriv xi) s) s :=
    (analyticAt_logDeriv (xi_differentiable.analyticAt _)
      (xi_ne_zero_of_not_nontrivial hs)).differentiableAt.hasDerivAt
  have hterm : ∀ ρ ∈ window s, HasDerivAt (fun w : ℂ => (WeilExplicit.zeroMult ρ : ℂ) / (w - ρ))
      (-(WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2) s := by
    intro ρ hρ
    have hne : s - ρ ≠ 0 := sub_ne_zero.mpr fun h => hs (by rw [h]; exact (mem_window.mp hρ).1)
    have := (hasDerivAt_const s (WeilExplicit.zeroMult ρ : ℂ)).div ((hasDerivAt_id' s).sub_const ρ) hne
    refine this.congr_deriv ?_
    ring
  have h2 : HasDerivAt (fun w : ℂ => ∑ ρ ∈ window s, (WeilExplicit.zeroMult ρ : ℂ) / (w - ρ))
      (∑ ρ ∈ window s, -(WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2) s := by
    have hfun : (fun w : ℂ => ∑ ρ ∈ window s, (WeilExplicit.zeroMult ρ : ℂ) / (w - ρ))
        = ∑ ρ ∈ window s, (fun w : ℂ => (WeilExplicit.zeroMult ρ : ℂ) / (w - ρ)) := by
      funext w
      simp [Finset.sum_apply]
    rw [hfun]
    exact HasDerivAt.sum hterm
  have hd : HasDerivAt (Fwin s)
      (deriv (logDeriv xi) s - ∑ ρ ∈ window s, -(WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2) s :=
    h1.sub h2
  rw [hd.deriv]
  simp only [neg_div, Finset.sum_neg_distrib, sub_neg_eq_add]

/-- A radius in (1/4, 1/2) whose circle about s carries no zero. -/
lemma exists_radius (s : ℂ) :
    ∃ r : ℝ, 1 / 4 < r ∧ r < 1 / 2 ∧ ∀ w ∈ sphere s r, ¬ IsNontrivialZero w := by
  classical
  set D : Finset ℝ := (window s).image (fun ρ => dist ρ s) with hD
  obtain ⟨r, hr, hrD⟩ := exists_mem_Ioo_notMem_finset (by norm_num : (1 / 4 : ℝ) < 1 / 2) D
  refine ⟨r, hr.1, hr.2, fun w hw hz => ?_⟩
  rw [mem_sphere] at hw
  have himw : |w.im - s.im| ≤ 2 := by
    rw [dist_eq_norm] at hw
    have := Complex.abs_im_le_norm (w - s)
    rw [Complex.sub_im] at this
    linarith [hr.2]
  have hwin : w ∈ window s := mem_window.mpr ⟨hz, himw⟩
  exact hrD (Finset.mem_image.mpr ⟨w, hwin, hw⟩)

/-- Cauchy's estimate for FwinExt s on the circle of radius r. -/
theorem norm_deriv_FwinExt_le {s : ℂ} {r : ℝ} (hr : 0 < r) (hr2 : r < 1 / 2) {B : ℝ}
    (hB : ∀ w ∈ sphere s r, ‖FwinExt s w‖ ≤ B) : ‖deriv (FwinExt s) s‖ ≤ B / r := by
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr ?_ hB
  refine DifferentiableOn.diffContOnCl ?_
  rw [closure_ball s hr.ne']
  exact (FwinExt_differentiableOn s).mono (closedBall_subset_ball hr2)

/-! ## E. The reflection identity Fwin (1 - s) (1 - w) = -Fwin s w. -/

lemma window_one_sub (s : ℂ) : window (1 - s) = (window s).image (fun ρ => 1 - ρ) := by
  ext ρ
  rw [mem_window, Finset.mem_image]
  have him : (1 - s).im = -s.im := by simp
  constructor
  · rintro ⟨hnt, hw⟩
    refine ⟨1 - ρ, mem_window.mpr ⟨(isNontrivialZero_one_sub_iff ρ).mpr hnt, ?_⟩, by ring⟩
    have h1 : (1 - ρ).im = -ρ.im := by simp
    rw [h1]
    rw [him] at hw
    have : -ρ.im - s.im = -(ρ.im - -s.im) := by ring
    rw [this, abs_neg]
    exact hw
  · rintro ⟨ρ', hρ', rfl⟩
    obtain ⟨hnt, hw⟩ := mem_window.mp hρ'
    refine ⟨(isNontrivialZero_one_sub_iff ρ').mpr hnt, ?_⟩
    have h1 : (1 - ρ').im = -ρ'.im := by simp
    rw [h1, him]
    have : -ρ'.im - -s.im = -(ρ'.im - s.im) := by ring
    rw [this, abs_neg]
    exact hw

lemma Fwin_one_sub (s w : ℂ) : Fwin (1 - s) (1 - w) = -Fwin s w := by
  unfold Fwin
  rw [logDeriv_xi_one_sub, window_one_sub,
    Finset.sum_image (fun x _ y _ h => by linear_combination -h)]
  have hterm : ∀ ρ ∈ window s,
      (WeilExplicit.zeroMult (1 - ρ) : ℂ) / ((1 - w) - (1 - ρ))
        = -((WeilExplicit.zeroMult ρ : ℂ) / (w - ρ)) := by
    intro ρ _
    rw [zeroMult_one_sub, show (1 - w) - (1 - ρ) = -(w - ρ) by ring, div_neg]
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
  ring

/-! ## F. The bound on the right half of the circle (Landau). -/

lemma le_mul_one_add {a b L : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hL : 0 ≤ L) :
    a + b * L ≤ (a + b) * (1 + L) := by nlinarith

/-- The core estimate at a point w with 1/2 ≤ Re w ≤ 7/2, |Im w| ≥ 6, within 1/2 of s. -/
theorem Fwin_bound_core : ∃ K : ℝ, 0 ≤ K ∧ ∀ s w : ℂ, dist w s ≤ 1 / 2 → 1 / 2 ≤ w.re → w.re ≤ 7 / 2 →
    6 ≤ |w.im| → ¬ IsNontrivialZero w → ‖Fwin s w‖ ≤ K * (1 + Real.log (2 + |s.im|)) := by
  classical
  obtain ⟨A, hA1, hwin⟩ := exists_window_bound
  obtain ⟨C, hC, hL⟩ := landau_window
  have hlogπ : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  set K : ℝ := (1 / 3 + Real.log Real.pi / 2 + (Real.pi + 7 / 2) / 2 + 1 / 2)
    + (C * Real.log 2 + C) + (2 / 3 * C * Real.log 2 + 2 / 3 * C) + (10 * A * Real.log 3 + 10 * A) with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    have := Real.pi_pos
    positivity
  refine ⟨K, hK0, fun s w hdist hre hre' him hnz => ?_⟩
  set L := Real.log (2 + |s.im|) with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith [abs_nonneg s.im])
  -- relations between Im w and Im s
  have himws : |w.im - s.im| ≤ 1 / 2 := by
    rw [dist_eq_norm] at hdist
    have := Complex.abs_im_le_norm (w - s)
    rw [Complex.sub_im] at this
    linarith
  have hims : 11 / 2 ≤ |s.im| := by
    have := abs_sub_abs_le_abs_sub w.im s.im
    linarith
  -- the pieces
  obtain ⟨Z, hZnt, hZout, hZcount, hZbound⟩ := hL w him hre hre' hnz
  have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_im, abs_zero] at him; linarith
  have hw1 : w ≠ 1 := fun h => by rw [h, Complex.one_im, abs_zero] at him; linarith
  have hwre : 0 < w.re := by linarith
  have hζw : riemannZeta w ≠ 0 := by
    intro hz
    rcases lt_or_ge w.re 1 with h1 | h1
    · exact hnz ⟨hz, hwre, h1⟩
    · exact riemannZeta_ne_zero_of_one_le_re h1 hz
  have hΛw : completedRiemannZeta w ≠ 0 := by
    rw [(Zeta23.WeilEF.completedZeta_eventuallyEq_mul hwre).eq_of_nhds]
    exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hwre) hζw
  set f : ℂ → ℂ := fun ρ => (WeilExplicit.zeroMult ρ : ℂ) / (w - ρ) with hf
  -- the symmetric-difference split
  have hsplit : (∑ ρ ∈ Z, f ρ) - ∑ ρ ∈ window s, f ρ
      = (∑ ρ ∈ Z \ window s, f ρ) - ∑ ρ ∈ window s \ Z, f ρ := by
    have h1 := Finset.sum_sdiff (f := f) (Finset.inter_subset_left (s₁ := Z) (s₂ := window s))
    have h2 := Finset.sum_sdiff (f := f) (Finset.inter_subset_left (s₁ := window s) (s₂ := Z))
    rw [Finset.sdiff_inter_self_left] at h1 h2
    rw [Finset.inter_comm] at h2
    linear_combination h2 - h1
  have hFwin : Fwin s w = (1 / w + 1 / (w - 1))
      + (-(Real.log Real.pi : ℂ) / 2 + (1 / 2 : ℂ) * Complex.digamma (w / 2))
      + (logDeriv riemannZeta w - ∑ ρ ∈ Z, f ρ)
      + (∑ ρ ∈ Z \ window s, f ρ) + (-∑ ρ ∈ window s \ Z, f ρ) := by
    unfold Fwin
    rw [logDeriv_xi_eq hw0 hw1 hΛw, Zeta23.WeilEF.logDeriv_completedZeta w hw1 hζw hwre,
      Zeta23.RvM.logDeriv_Gammaℝ hwre]
    have := hsplit
    linear_combination this
  -- piece bounds
  have hnw : 6 ≤ ‖w‖ := him.trans (Complex.abs_im_le_norm w)
  have hnw1 : 6 ≤ ‖w - 1‖ := by
    have := Complex.abs_im_le_norm (w - 1)
    rw [Complex.sub_im, Complex.one_im, sub_zero] at this
    linarith
  have e1 : ‖1 / w + 1 / (w - 1)‖ ≤ 1 / 3 := by
    calc ‖1 / w + 1 / (w - 1)‖ ≤ ‖1 / w‖ + ‖1 / (w - 1)‖ := norm_add_le _ _
      _ ≤ 1 / 6 + 1 / 6 := by
          gcongr
          · rw [norm_div, norm_one, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
          · rw [norm_div, norm_one, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      _ = 1 / 3 := by norm_num
  have e2 : ‖-(Real.log Real.pi : ℂ) / 2 + (1 / 2 : ℂ) * Complex.digamma (w / 2)‖
      ≤ Real.log Real.pi / 2 + (Real.pi + 7 / 2) / 2 + 1 / 2 * L := by
    have h2 : w / 2 = ((1 / 2 : ℝ) : ℂ) * w := by push_cast; ring
    have hre2 : (w / 2).re = 1 / 2 * w.re := by rw [h2, Complex.re_ofReal_mul]
    have him2 : |(w / 2).im| = |w.im| / 2 := by
      rw [h2, Complex.im_ofReal_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      ring
    have hz : ‖Complex.digamma (w / 2)‖ ≤ Real.log (2 + |(w / 2).im|) + Real.pi + 7 / 2 := by
      refine norm_digamma_le_log ?_ ?_ ?_
      · rw [hre2]; linarith
      · rw [hre2]; linarith
      · rw [him2]; linarith
    have hhalf : |(w / 2).im| ≤ |s.im| := by
      rw [him2]
      have := abs_sub_abs_le_abs_sub w.im s.im
      linarith
    have hlogle : Real.log (2 + |(w / 2).im|) ≤ L :=
      Real.log_le_log (by linarith [abs_nonneg (w / 2).im]) (by linarith)
    calc ‖-(Real.log Real.pi : ℂ) / 2 + (1 / 2 : ℂ) * Complex.digamma (w / 2)‖
        ≤ ‖-(Real.log Real.pi : ℂ) / 2‖ + ‖(1 / 2 : ℂ) * Complex.digamma (w / 2)‖ := norm_add_le _ _
      _ = Real.log Real.pi / 2 + 1 / 2 * ‖Complex.digamma (w / 2)‖ := by
          rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogπ,
            norm_mul]
          have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
          rw [this]
          norm_num
      _ ≤ Real.log Real.pi / 2 + 1 / 2 * (L + Real.pi + 7 / 2) := by
          gcongr
          linarith
      _ = Real.log Real.pi / 2 + (Real.pi + 7 / 2) / 2 + 1 / 2 * L := by ring
  have hlogw : Real.log (|w.im| + 3) ≤ L + Real.log 2 := by
    rw [← Real.log_mul (by linarith [abs_nonneg s.im]) (by norm_num)]
    refine Real.log_le_log (by linarith [abs_nonneg w.im]) ?_
    have := abs_sub_abs_le_abs_sub w.im s.im
    linarith
  have e3 : ‖logDeriv riemannZeta w - ∑ ρ ∈ Z, f ρ‖ ≤ C * Real.log 2 + C * L := by
    refine hZbound.trans ?_
    calc C * Real.log (|w.im| + 3) ≤ C * (L + Real.log 2) := mul_le_mul_of_nonneg_left hlogw hC.le
      _ = C * Real.log 2 + C * L := by ring
  have e4 : ‖∑ ρ ∈ Z \ window s, f ρ‖ ≤ 2 / 3 * C * Real.log 2 + 2 / 3 * C * L := by
    have hterm : ∀ ρ ∈ Z \ window s, ‖f ρ‖ ≤ 2 / 3 * (WeilExplicit.zeroMult ρ : ℝ) := by
      intro ρ hρ
      rw [Finset.mem_sdiff] at hρ
      have hnt := (hZnt ρ hρ.1).1
      have hfar : 2 < |ρ.im - s.im| := by
        by_contra hle
        exact hρ.2 (mem_window.mpr ⟨hnt, not_lt.mp hle⟩)
      have hd : 3 / 2 ≤ ‖w - ρ‖ := by
        have := Complex.abs_im_le_norm (w - ρ)
        rw [Complex.sub_im] at this
        have h2 := abs_sub_abs_le_abs_sub (ρ.im - s.im) (w.im - s.im)
        have h3 : ρ.im - s.im - (w.im - s.im) = -(w.im - ρ.im) := by ring
        rw [h3, abs_neg] at h2
        linarith
      rw [hf]
      simp only
      rw [norm_div, Complex.norm_natCast, div_le_iff₀ (by linarith)]
      nlinarith [Nat.cast_nonneg (α := ℝ) (WeilExplicit.zeroMult ρ)]
    calc ‖∑ ρ ∈ Z \ window s, f ρ‖ ≤ ∑ ρ ∈ Z \ window s, ‖f ρ‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z \ window s, 2 / 3 * (WeilExplicit.zeroMult ρ : ℝ) := Finset.sum_le_sum hterm
      _ ≤ ∑ ρ ∈ Z, 2 / 3 * (WeilExplicit.zeroMult ρ : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ => by positivity
      _ = 2 / 3 * ∑ ρ ∈ Z, (WeilExplicit.zeroMult ρ : ℝ) := by rw [Finset.mul_sum]
      _ ≤ 2 / 3 * (C * Real.log (|w.im| + 3)) := by gcongr
      _ ≤ 2 / 3 * (C * (L + Real.log 2)) := by gcongr
      _ = 2 / 3 * C * Real.log 2 + 2 / 3 * C * L := by ring
  have hlogs : Real.log (|s.im| + 6) ≤ L + Real.log 3 := by
    rw [← Real.log_mul (by linarith [abs_nonneg s.im]) (by norm_num)]
    refine Real.log_le_log (by linarith [abs_nonneg s.im]) ?_
    linarith [abs_nonneg s.im]
  have e5 : ‖-∑ ρ ∈ window s \ Z, f ρ‖ ≤ 10 * A * Real.log 3 + 10 * A * L := by
    rw [norm_neg]
    have hterm : ∀ ρ ∈ window s \ Z, ‖f ρ‖ ≤ 10 * (WeilExplicit.zeroMult ρ : ℝ) := by
      intro ρ hρ
      rw [Finset.mem_sdiff] at hρ
      have hnt := (mem_window.mp hρ.1).1
      have hout := hZout ρ hnt hρ.2
      have hwc : dist w (2 + w.im * I) ≤ 3 / 2 := by
        rw [dist_eq_norm]
        have : w - (2 + w.im * I) = ((w.re - 2 : ℝ) : ℂ) := by
          apply Complex.ext <;> simp
        rw [this, Complex.norm_real, Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      have hd : 1 / 10 ≤ ‖w - ρ‖ := by
        have := dist_triangle ρ w (2 + w.im * I)
        rw [← dist_eq_norm, dist_comm]
        linarith
      rw [hf]
      simp only
      rw [norm_div, Complex.norm_natCast, div_le_iff₀ (by linarith)]
      nlinarith [Nat.cast_nonneg (α := ℝ) (WeilExplicit.zeroMult ρ)]
    calc ‖∑ ρ ∈ window s \ Z, f ρ‖ ≤ ∑ ρ ∈ window s \ Z, ‖f ρ‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ window s \ Z, 10 * (WeilExplicit.zeroMult ρ : ℝ) := Finset.sum_le_sum hterm
      _ ≤ ∑ ρ ∈ window s, 10 * (WeilExplicit.zeroMult ρ : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ => by positivity
      _ = 10 * ∑ ρ ∈ window s, (WeilExplicit.zeroMult ρ : ℝ) := by rw [Finset.mul_sum]
      _ ≤ 10 * (A * Real.log (|s.im| + 6)) := by gcongr; exact hwin s
      _ ≤ 10 * (A * (L + Real.log 3)) := by gcongr
      _ = 10 * A * Real.log 3 + 10 * A * L := by ring
  -- assemble
  rw [hFwin]
  have htri : ‖(1 / w + 1 / (w - 1))
      + (-(Real.log Real.pi : ℂ) / 2 + (1 / 2 : ℂ) * Complex.digamma (w / 2))
      + (logDeriv riemannZeta w - ∑ ρ ∈ Z, f ρ)
      + (∑ ρ ∈ Z \ window s, f ρ) + (-∑ ρ ∈ window s \ Z, f ρ)‖
      ≤ ‖1 / w + 1 / (w - 1)‖
        + ‖-(Real.log Real.pi : ℂ) / 2 + (1 / 2 : ℂ) * Complex.digamma (w / 2)‖
        + ‖logDeriv riemannZeta w - ∑ ρ ∈ Z, f ρ‖
        + ‖∑ ρ ∈ Z \ window s, f ρ‖ + ‖-∑ ρ ∈ window s \ Z, f ρ‖ := by
    refine (norm_add_le _ _).trans ?_
    gcongr
    refine (norm_add_le _ _).trans ?_
    gcongr
    refine (norm_add_le _ _).trans ?_
    gcongr
    exact norm_add_le _ _
  refine htri.trans ?_
  set a : ℝ := 1 / 3 + Real.log Real.pi / 2 + (Real.pi + 7 / 2) / 2 + C * Real.log 2
    + 2 / 3 * C * Real.log 2 + 10 * A * Real.log 3 with ha
  set b : ℝ := 1 / 2 + C + 2 / 3 * C + 10 * A with hb
  have ha0 : 0 ≤ a := by
    rw [ha]
    have := Real.pi_pos
    positivity
  have hb0 : 0 ≤ b := by
    rw [hb]
    positivity
  have hKab : K = a + b := by
    rw [hK, ha, hb]
    ring
  rw [hKab]
  refine le_trans ?_ (le_mul_one_add ha0 hb0 hL0)
  rw [ha, hb]
  linarith [e1, e2, e3, e4, e5]

/-! ## G. The sphere bound (both halves) and the high-height target bound. -/

theorem sphere_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ s w : ℂ, dist w s ≤ 1 / 2 → 1 / 4 ≤ s.re → s.re ≤ 9 / 4 →
    13 / 2 ≤ |s.im| → ¬ IsNontrivialZero w → ‖Fwin s w‖ ≤ K * (1 + Real.log (2 + |s.im|)) := by
  obtain ⟨K, hK0, hcore⟩ := Fwin_bound_core
  refine ⟨K, hK0, fun s w hdist hre hre' him hnz => ?_⟩
  have hwre : |w.re - s.re| ≤ 1 / 2 := by
    rw [dist_eq_norm] at hdist
    have := Complex.abs_re_le_norm (w - s)
    rw [Complex.sub_re] at this
    linarith
  have hwim : |w.im - s.im| ≤ 1 / 2 := by
    rw [dist_eq_norm] at hdist
    have := Complex.abs_im_le_norm (w - s)
    rw [Complex.sub_im] at this
    linarith
  have hwre' := abs_le.mp hwre
  have hwim' := abs_le.mp hwim
  have him6 : 6 ≤ |w.im| := by
    have := abs_sub_abs_le_abs_sub s.im w.im
    have h2 : |s.im - w.im| = |w.im - s.im| := abs_sub_comm _ _
    linarith
  rcases le_or_gt (1 / 2) w.re with hhalf | hhalf
  · exact hcore s w hdist hhalf (by linarith) him6 hnz
  · have hdist' : dist (1 - w) (1 - s) ≤ 1 / 2 := by
      rw [dist_eq_norm, show (1 - w) - (1 - s) = -(w - s) by ring, norm_neg, ← dist_eq_norm]
      exact hdist
    have hre1 : 1 / 2 ≤ (1 - w).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    have hre1' : (1 - w).re ≤ 7 / 2 := by rw [Complex.sub_re, Complex.one_re]; linarith
    have him1 : 6 ≤ |(1 - w).im| := by
      rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]; exact him6
    have hnz1 : ¬ IsNontrivialZero (1 - w) := fun h => hnz ((isNontrivialZero_one_sub_iff w).mp h)
    have h := hcore (1 - s) (1 - w) hdist' hre1 hre1' him1 hnz1
    rw [Fwin_one_sub, norm_neg] at h
    have hsim : |(1 - s).im| = |s.im| := by
      rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
    rwa [hsim] at h

/-- The target bound at heights |Im s| ≥ 13/2 (Cauchy on a circle of radius r ∈ (1/4, 1/2)). -/
theorem target_bound_high : ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 9 / 4 → 13 / 2 ≤ |s.im| →
    ¬ IsNontrivialZero s →
    ‖deriv (logDeriv xi) s + ∑ ρ ∈ window s, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2‖
      ≤ K * (1 + Real.log (2 + |s.im|)) := by
  obtain ⟨K, hK0, hsph⟩ := sphere_bound
  refine ⟨4 * K, by positivity, fun s hre hre' him hnz => ?_⟩
  obtain ⟨r, hr1, hr2, hrz⟩ := exists_radius s
  have hL0 : 0 ≤ 1 + Real.log (2 + |s.im|) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + |s.im| by linarith [abs_nonneg s.im])
    linarith
  have hB : ∀ w ∈ sphere s r, ‖FwinExt s w‖ ≤ K * (1 + Real.log (2 + |s.im|)) := by
    intro w hw
    have hwz := hrz w hw
    rw [FwinExt_eq hwz]
    have hd : dist w s ≤ 1 / 2 := by
      rw [mem_sphere] at hw
      linarith
    exact hsph s w hd hre hre' him hwz
  have hC := norm_deriv_FwinExt_le (by linarith : 0 < r) hr2 hB
  rw [deriv_FwinExt hnz] at hC
  refine hC.trans ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg hK0 hL0]

/-! ## H. Low heights via the entire extension (no Landau). -/

/-- The local-count sum at height a is at most (13/4 + 2 a^2) times a fixed constant. -/
lemma tsum_lcTerm_le (a : ℝ) :
    ∑' ρ : ℂ, lcTerm a ρ
      ≤ (13 / 4 + 2 * a ^ 2) * ∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℝ) * (1 / (1 + Complex.normSq (gammaOf ρ))) := by
  rw [← tsum_mul_left]
  refine (summable_lcTerm a).tsum_le_tsum (fun ρ => ?_) ((RvMBridgeGauss.summable_mult_div_one_add_normSq 1).mul_left _)
  refine (lcTerm_le_majorant a ρ).trans (le_of_eq ?_)
  ring

theorem target_bound_low : ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 9 / 4 → |s.im| ≤ 7 →
    ¬ IsNontrivialZero s →
    ‖deriv (logDeriv xi) s + ∑ ρ ∈ window s, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2‖ ≤ K := by
  classical
  obtain ⟨M, hM0, hM⟩ :=
    exists_bound_on_reProdIm xiDiffExt_differentiable.continuous (1 / 4) (9 / 4) (-7) 7
  set B₁ : ℝ := ∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℝ) * (1 / (1 + Complex.normSq (gammaOf ρ))) with hB₁
  have hB₁0 : 0 ≤ B₁ := tsum_nonneg fun ρ => by
    have := Complex.normSq_nonneg (gammaOf ρ); positivity
  refine ⟨M + 2 * ((13 / 4 + 2 * 49) * B₁), by positivity, fun s hre hre' him hnz => ?_⟩
  have hsplit := (summable_polTerm s).sum_add_tsum_compl (s := window s)
  have hxi : xiDiffExt s = deriv (logDeriv xi) s + ∑' ρ : ℂ, polTerm s ρ := by
    rw [xiDiffExt_eq hnz]; rfl
  have heq : deriv (logDeriv xi) s + ∑ ρ ∈ window s, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2
      = xiDiffExt s - ∑' ρ : ↥(((window s : Finset ℂ) : Set ℂ)ᶜ), polTerm s ρ := by
    rw [hxi, ← hsplit]
    change deriv (logDeriv xi) s + ∑ ρ ∈ window s, polTerm s ρ = _
    ring
  rw [heq]
  have hMs : ‖xiDiffExt s‖ ≤ M := hM s hre hre' (abs_le.mp him).1 (abs_le.mp him).2
  have hfar := norm_tsum_far_le s
  have hlc : ∑' ρ : ℂ, lcTerm s.im ρ ≤ (13 / 4 + 2 * 49) * B₁ := by
    refine (tsum_lcTerm_le s.im).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hB₁0
    have h := abs_le.mp him
    nlinarith [sq_abs s.im, abs_nonneg s.im]
  calc ‖xiDiffExt s - ∑' ρ : ↥(((window s : Finset ℂ) : Set ℂ)ᶜ), polTerm s ρ‖
      ≤ ‖xiDiffExt s‖ + ‖∑' ρ : ↥(((window s : Finset ℂ) : Set ℂ)ᶜ), polTerm s ρ‖ := norm_sub_le _ _
    _ ≤ M + 2 * ((13 / 4 + 2 * 49) * B₁) := by
        gcongr
        exact hfar.trans (by gcongr)

/-! ## I. Assembly: StripDerivBound. -/

/-- **StripDerivBound, DISCHARGED.** -/
theorem stripDerivBound : StripDerivBound := by
  obtain ⟨K₁, hK₁, hlow⟩ := target_bound_low
  obtain ⟨K₂, hK₂, hhigh⟩ := target_bound_high
  refine ⟨K₁ + K₂, fun s hre hre' him hnz => ?_⟩
  have hL0 : 0 ≤ Real.log (2 + |s.im|) := Real.log_nonneg (by linarith [abs_nonneg s.im])
  rcases le_or_gt |s.im| 7 with h7 | h7
  · refine (hlow s hre hre' h7 hnz).trans ?_
    nlinarith
  · refine (hhigh s hre hre' (by linarith) hnz).trans ?_
    nlinarith

/-- With E6Bridge22: the growth bound modulo LocalCountSum only. -/
theorem xiDiffExtGrowthRight_of_localCount (h1 : LocalCountSum) : XiDiffExtGrowthRight :=
  xiDiffExtGrowthRight_of_two h1 stripDerivBound

/-- With E6Bridge18/20/21/22: the derivative partial fraction modulo LocalCountSum only. -/
theorem xiLogDerivDerivEq_of_localCount (h1 : LocalCountSum) : RvMBridge18.XiLogDerivDerivEq :=
  xiLogDerivDerivEq_of_two h1 stripDerivBound

end RvMBridge24
