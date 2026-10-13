/- Audit probes for E6Bridge23 / E6Bridge25 / E6Bridge26. -/
import E6Bridge26
open Zeta23 Complex Filter Topology RvMBridge22 RvMBridge23 RvMBridge25 RvMBridge26

/- 1. Consumption of the two discharged facts and the assembly (expected SUCCESS). -/
example : LocalCountSum := local_count_sum
example : RvMBridge19.NoRealZeroInUnitInterval := noRealZeroInUnitInterval
example (h2 : StripDerivBound) (n : ℕ) (hn : 0 < n) : RvMBridge15.LiValue n := liValue_of_strip h2 n hn
example (h2 : StripDerivBound) : RvMBridge18.XiLogDerivDerivEq := xiLogDerivDerivEq_of_strip h2
/- The assembly is exactly the composition of the named inputs (expected SUCCESS). -/
example (h2 : StripDerivBound) (n : ℕ) (hn : 0 < n) : RvMBridge15.LiValue n :=
  RvMBridge25.liValue_of_two RvMBridge23.local_count_sum h2 n hn

/- 2. The fiber weight, re-proved independently for the two cases (expected SUCCESS). -/
theorem audit_fiber_pos {x k : ℝ} (hk1 : 1 ≤ k) (hx : k - 1 < x) : 1 + k ^ 2 ≤ 4 * (1 + x ^ 2) := by
  have hx0 : 0 ≤ k - 1 := by linarith
  have : (k - 1) ^ 2 ≤ x ^ 2 := by nlinarith
  nlinarith [sq_nonneg (3 * k - 4)]
theorem audit_fiber_nonpos {x k : ℝ} (hk : k ≤ 0) (hx : x ≤ k) : 1 + k ^ 2 ≤ 4 * (1 + x ^ 2) := by
  have : k ^ 2 ≤ x ^ 2 := by nlinarith
  nlinarith [sq_nonneg x]
#print axioms audit_fiber_pos

/- 3. The log inequality, re-proved (expected SUCCESS). -/
theorem audit_log_add_four {y : ℝ} (hy : 1 ≤ y) : Real.log (y + 4) ≤ 6 * Real.sqrt y := log_add_four_le hy
theorem audit_log_split (a k : ℝ) :
    Real.log (|a| + |k| + 4) ≤ Real.log (2 + |a|) + Real.log (|k| + 4) := by
  rw [← Real.log_mul (by positivity) (by positivity)]
  refine Real.log_le_log (by positivity) ?_
  nlinarith [abs_nonneg a, abs_nonneg k]
#print axioms audit_log_split

/- 4. Re zeta(1/2) < 0 is exercised, against Mathlib's positivity at 2 (expected SUCCESS). -/
example : (riemannZeta ((1 / 2 : ℝ) : ℂ)).re < 0 :=
  re_riemannZeta_neg_of_unit_interval (by norm_num) (by norm_num)
example : riemannZeta ((1 / 2 : ℝ) : ℂ) ≠ 0 := riemannZeta_ne_zero_of_unit_interval (by norm_num) (by norm_num)
example : riemannZeta 2 ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)

/- 5. The sign step, abstractly: for 0 < σ < 1, 1 - 1/(1 - σ) < 0 (expected SUCCESS). -/
theorem audit_sign {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) : 1 - 1 / (1 - σ) < 0 := by
  have : 1 < 1 / (1 - σ) := by rw [lt_div_iff₀ (by linarith)]; linarith
  linarith
#print axioms audit_sign

/- 6. The exponent condition of the tail integral: -σ - 1 < -1 iff σ > 0 (expected SUCCESS). -/
example {σ : ℝ} (h : 0 < σ) : -σ - 1 < -1 := by linarith

/- 7. The theorem does not apply outside (0, 1) (expected FAIL at σ = 2). -/
example : (riemannZeta ((2 : ℝ) : ℂ)).re < 0 :=
  re_riemannZeta_neg_of_unit_interval (by norm_num) (by norm_num)
