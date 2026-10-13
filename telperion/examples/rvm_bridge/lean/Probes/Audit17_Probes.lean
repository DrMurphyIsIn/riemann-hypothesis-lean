/- Audit probes for E6Bridge17. -/
import E6Bridge17
open Zeta23 Complex MeasureTheory Filter Topology RvMBridge6 RvMBridge7 RvMBridge12 RvMBridge14 RvMBridge17 WeilExplicit

/- 1. ThetaFree is not closable by automation (expected FAIL). -/
example (lam : ℝ) : ThetaFree lam := by unfold ThetaFree Theta; simp
example (lam : ℝ) : ThetaFree lam := by unfold ThetaFree; aesop

/- 2. At x = 0 (centre at the ordinate) the plain summand is +m e^{2 lam y^2} ≥ 0, so the E6Bridge14
   centre-at-ordinate trick does not transfer (expected SUCCESS). -/
theorem audit_re_plainGauss_axis (c lam y : ℝ) :
    (plainGauss c lam ((c : ℂ) + (y : ℂ) * I)).re = Real.exp (2 * lam * y ^ 2) := by
  rw [re_plainGauss]
  simp
#print axioms audit_re_plainGauss_axis

/- 3. Consumption: the equivalences, monotonicity, and the off-line bound (expected SUCCESS). -/
example : RiemannHypothesis ↔ ∀ c lam : ℝ, 0 < lam → 0 ≤ Theta c lam := rh_iff_theta_positivity
example {lam' lam : ℝ} (h0 : 0 < lam') (hlt : lam' < lam) (h : ThetaFree lam) : ThetaFree lam' :=
  theta_pos_mono h0 hlt h
example {ρ₀ : ℂ} (h₀ : IsNontrivialZero ρ₀) (hre₀ : ρ₀.re ≠ 1 / 2) : BddAbove ThetaWidths :=
  thetaWidths_bddAbove_of_offline h₀ hre₀

/- 4. Monotonicity cannot be reversed: positivity at a SMALLER width does not yield it at a larger
   one by the same identity (expected FAIL: the heat identity only expresses the smaller width). -/
example {lam' lam : ℝ} (h0 : 0 < lam') (hlt : lam' < lam) (hpos : ∀ c : ℝ, 0 ≤ Theta c lam') (c : ℝ) :
    0 ≤ Theta c lam := by
  first
  | exact theta_pos_mono h0 hlt hpos c
  | (rw [theta_heat h0 hlt c]; positivity)

/- 5. theta_pos_mono needs hpos on the WHOLE line: a band-restricted hypothesis does not suffice
   (expected FAIL). -/
example {lam' lam : ℝ} (h0 : 0 < lam') (hlt : lam' < lam) (T : ℝ)
    (hpos : ∀ c : ℝ, |c| ≤ T → 0 ≤ Theta c lam) (c : ℝ) : 0 ≤ Theta c lam' := by
  rw [theta_heat h0 hlt c]
  refine mul_nonneg (Real.sqrt_nonneg _) (integral_nonneg fun c' => ?_)
  exact mul_nonneg (heatKernel_nonneg (heatVar_pos h0 hlt) _) (hpos c' (by positivity))

/- 6. The heat identity on the real line, consistent direction: ∫ K G_lam = √(lam'/lam) G_lam'
   (expected SUCCESS, consumption of real_gauss_heat). -/
example {lam' lam : ℝ} (h0 : 0 < lam') (hlt : lam' < lam) (c x : ℝ) :
    ∫ c' : ℝ, heatKernel (heatVar lam' lam) (c - c') * Real.exp (-(2 * lam) * (x - c') ^ 2)
      = Real.sqrt (lam' / lam) * Real.exp (-(2 * lam') * (x - c) ^ 2) := real_gauss_heat h0 hlt c x

/- 7. Countability of the zero set and its use as an index (expected SUCCESS). -/
example : ({ρ : ℂ | IsNontrivialZero ρ}).Countable := RvMBridgeXi.nontrivialZeros_countable
example : Countable NZ := inferInstance
