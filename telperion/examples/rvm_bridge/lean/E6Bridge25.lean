/-
  E6Bridge25 -- NoRealZeroInUnitInterval PROVED, and the B7 value half on two inequalities
  (2026-09-21; rh campaign node RH_bl_explicit_formula).

  E6Bridge19 carried `NoRealZeroInUnitInterval : ∀ σ : ℝ, 0 < σ → σ < 1 → riemannZeta σ ≠ 0` as a
  named Prop (used only to integrate deriv (logDeriv xi) along the real segment [0, 1]).  It is
  discharged here, kernel-clean, by the summation-by-parts representation already on the island
  (Zeta23's PrimeNumberTheoremAnd port, `Zeta0EqZeta` with N = 1, valid for Re s > 0, s ≠ 1):

      zeta(s) = 1/2 + 1/(s - 1) + s * J(s),   J(s) = ∫_1^∞ (⌊x⌋ + 1/2 - x) x^{-s-1} dx,

  and the sharp bound |J(σ)| ≤ (1/2) ∫_1^∞ x^{-σ-1} dx = 1/(2σ) for real σ > 0, so that

      Re zeta(σ) ≤ 1/2 - 1/(1 - σ) + 1/2 = 1 - 1/(1 - σ) < 0       (0 < σ < 1).

  (Zeta23's own `norm_riemannZeta_le_of_re_pos` uses the cruder |J| ≤ 1/σ, which only gives the
  sign for σ > 1/3; the factor 1/2 from |⌊x⌋ + 1/2 - x| ≤ 1/2 is what closes the whole interval.)
  The Dirichlet-eta route of the brief is not needed: no alternating series, no continuation.

  CONSEQUENCE: with E6Bridge22's reduction of the xi partial fraction to two named inequalities,
      liValue_of_two (h1 : RvMBridge22.LocalCountSum) (h2 : RvMBridge22.StripDerivBound) (n) (hn) :
        LiValue n,
      bl_explicit_formula_of_two h1 h2 n hn : Tendsto (liZeroSum n) atTop (nhds (archSide n + finiteSide n)),
  the node RH_bl_explicit_formula rests on exactly those two inequalities.

  conjecture1_proved = False.  Nothing here says anything about whether RH holds.
-/
import E6Bridge19
import E6Bridge22
import Zeta23.FromPNTPlus.ZetaBounds

open Zeta23 Complex MeasureTheory Filter Topology Set

noncomputable section

namespace RvMBridge25

/-- The tail integral of the summation-by-parts formula at N = 1, real exponent, sharp bound:
‖∫_1^∞ (⌊x⌋ + 1/2 - x) x^{-σ-1} dx‖ ≤ 1/(2σ). -/
lemma norm_tail_integral_le {σ : ℝ} (hσ : 0 < σ) :
    ‖∫ x in Ioi (1 : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - x) / (x : ℂ) ^ ((σ : ℂ) + 1)‖ ≤ 1 / (2 * σ) := by
  have hint : Integrable (fun x : ℝ => (1 / 2 : ℝ) * x ^ (-σ - 1)) (volume.restrict (Ioi (1 : ℝ))) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
  refine (norm_integral_le_of_norm_le hint ?_).trans ?_
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    have hx0 : 0 < x := lt_trans one_pos hx
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re]
    have h3 : ‖(⌊x⌋ : ℂ) + 1 / 2 - x‖ ≤ 1 / 2 := by
      have := ZetaSum_aux1_3 x
      rw [show ((⌊x⌋ : ℂ) + 1 / 2 - x) = (((⌊x⌋ : ℝ) + 1 / 2 - x : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real]
      exact this
    rw [div_eq_mul_inv, ← Real.rpow_neg hx0.le]
    calc ‖(⌊x⌋ : ℂ) + 1 / 2 - x‖ * x ^ (-(σ + 1)) ≤ (1 / 2) * x ^ (-(σ + 1)) := by
          gcongr
      _ = (1 / 2 : ℝ) * x ^ (-σ - 1) := by ring_nf
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow,
      show (-σ - 1 + 1) = -σ by ring]
    apply le_of_eq
    rw [neg_div_neg_eq, one_div_mul_one_div]

/-- For real 0 < σ < 1, Re zeta(σ) < 0. -/
theorem re_riemannZeta_neg_of_unit_interval {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    (riemannZeta (σ : ℂ)).re < 0 := by
  have hσ : 0 < (σ : ℂ).re := by simpa using h0
  have hs : (σ : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hs0 : (σ : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [← Zeta0EqZeta (N := 1) one_pos hσ hs]
  simp only [riemannZeta0, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Complex.zero_cpow hs0, Nat.cast_one, Complex.one_cpow, div_one, div_zero, zero_add]
  set J := ∫ x in Ioi (1 : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - x) / (x : ℂ) ^ ((σ : ℂ) + 1) with hJ
  have hJle : ‖J‖ ≤ 1 / (2 * σ) := norm_tail_integral_le h0
  have h1σ : 0 < 1 - σ := by linarith
  have hre : ((1 : ℂ) + -1 / (1 - (σ : ℂ)) + -1 / 2 + (σ : ℂ) * J).re
      = 1 / 2 - 1 / (1 - σ) + σ * J.re := by
    have e : ((1 : ℂ) + -1 / (1 - (σ : ℂ)) + -1 / 2) = (((1 : ℝ) + -1 / (1 - σ) + -1 / 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
    ring
  rw [hre]
  have hJre : J.re ≤ ‖J‖ := Complex.re_le_norm J
  have hprod : σ * J.re ≤ 1 / 2 := by
    calc σ * J.re ≤ σ * ‖J‖ := by gcongr
      _ ≤ σ * (1 / (2 * σ)) := by gcongr
      _ = 1 / 2 := by field_simp
  have hdiv : 1 < 1 / (1 - σ) := by
    rw [lt_div_iff₀ h1σ]; linarith
  linarith

/-- For real 0 < σ < 1, zeta(σ) ≠ 0. -/
theorem riemannZeta_ne_zero_of_unit_interval {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta (σ : ℂ) ≠ 0 := by
  intro h
  have := re_riemannZeta_neg_of_unit_interval h0 h1
  rw [h, Complex.zero_re] at this
  exact lt_irrefl _ this

/-- **E6Bridge19's segment Prop, discharged.** -/
theorem noRealZeroInUnitInterval : RvMBridge19.NoRealZeroInUnitInterval :=
  fun _ h0 h1 => riemannZeta_ne_zero_of_unit_interval h0 h1

/-! ## The B7 value half on the two inequalities of E6Bridge22. -/

/-- LiValue n from the xi partial fraction alone (the segment Prop is gone). -/
theorem liValue_of_partialFraction (hP : RvMBridge18.XiLogDerivDerivEq) (n : ℕ) (hn : 0 < n) :
    RvMBridge15.LiValue n :=
  RvMBridge19.liValue_of hP noRealZeroInUnitInterval n hn

/-- LiValue n from the ONE growth obligation of E6Bridge20. -/
theorem liValue_of_growth (h : RvMBridge20.XiDiffExtGrowthRight) (n : ℕ) (hn : 0 < n) :
    RvMBridge15.LiValue n :=
  RvMBridge19.liValue_of_growth h noRealZeroInUnitInterval n hn

/-- **LiValue n from the two inequalities** LocalCountSum and StripDerivBound (E6Bridge22). -/
theorem liValue_of_two (h1 : RvMBridge22.LocalCountSum) (h2 : RvMBridge22.StripDerivBound) (n : ℕ)
    (hn : 0 < n) : RvMBridge15.LiValue n :=
  RvMBridge19.liValue_of (RvMBridge22.xiLogDerivDerivEq_of_two h1 h2) noRealZeroInUnitInterval n hn

/-- **The node RH_bl_explicit_formula, verbatim, from the two inequalities.** -/
theorem bl_explicit_formula_of_two (h1 : RvMBridge22.LocalCountSum) (h2 : RvMBridge22.StripDerivBound)
    (n : ℕ) (hn : 0 < n) :
    Tendsto (RvMBridge15.BombieriLagarias.liZeroSum n) atTop
      (𝓝 (RvMBridge15.BombieriLagarias.archSide n + RvMBridge15.BombieriLagarias.finiteSide n)) :=
  RvMBridge15.bl_explicit_formula_of hn (liValue_of_two h1 h2 n hn)

end RvMBridge25
