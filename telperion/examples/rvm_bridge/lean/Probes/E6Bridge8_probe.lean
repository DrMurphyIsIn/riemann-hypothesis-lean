/-
  Probes for E6Bridge8 (2026-09-21): axiom audit of the O1' discharge (RvMBridge8.gaussian_approx :
  RvMBridge6.GaussianApprox) and of every stage, plus two non-vacuity probes (the witness tests
  are not the zero function; the closed obligation composes with E6Bridge6's Tannery transfer to
  give GaussianTransfer unconditionally).
  Run: cd telperion/examples/rvm_bridge/lean && lake env lean Probes/E6Bridge8_probe.lean
  Expected: every #print axioms line is exactly [propext, Classical.choice, Quot.sound].
-/
import E6Bridge8

open Zeta23 Complex RvMBridge8

/-! ### The delivered theorem, verbatim type. -/
example : RvMBridge6.GaussianApprox := RvMBridge8.gaussian_approx

#print axioms RvMBridge8.gaussian_approx

/-! ### Stages. -/
#print axioms RvMBridgeGauss.integral_mul_cexp_gaussian_fourier
#print axioms RvMBridge8.paperFT_gaussPhi
#print axioms RvMBridge8.gaussTest_eq_half_mul_conj
#print axioms RvMBridge8.isWeilTest_gaussTests
#print axioms RvMBridge8.paperFT_gaussTests_tendsto
#print axioms RvMBridge8.I_mul_paperFT_eq
#print axioms RvMBridge8.norm_mul_paperFT_gaussTests_le
#print axioms RvMBridge8.norm_paperFT_gaussTests_le
#print axioms RvMBridge8.exists_paperFT_gaussTests_bound
#print axioms RvMBridgeGauss.integrable_mul_cexp_quadratic
#print axioms RvMBridgeGauss.integrable_abs_pow_mul_exp_quadratic_abs

/-! ### Composition with E6Bridge6: GaussianTransfer (O1) is now unconditional. -/
theorem probe_gaussianTransfer : RvMBridge6.GaussianTransfer :=
  RvMBridge6.gaussianTransfer_of_approx RvMBridge8.gaussian_approx

#print axioms probe_gaussianTransfer

/-! ### Non-vacuity: the witness tests are not the zero function (g_0 (1) = K exp (-b - i c) != 0),
so the closed statement is not satisfied by a degenerate family. -/
theorem probe_gaussTests_ne_zero (c lam : ℝ) (hlam : 0 < lam) :
    RvMBridge8.gaussTests c lam 0 1 ≠ 0 := by
  have h1 : RvMBridge8.cutoff 0 1 = 1 :=
    RvMBridge8.cutoff_eq_one (n := 0) (u := 1) (by rw [abs_one]; norm_num)
  have h2 : RvMBridge8.gaussPhi c lam 1 ≠ 0 := by
    unfold RvMBridge8.gaussPhi
    exact mul_ne_zero (mul_ne_zero (RvMBridge8.gaussK_ne_zero hlam) (by norm_num))
      (Complex.exp_ne_zero _)
  show RvMBridge8.gaussPhi c lam 1 * ((RvMBridge8.cutoff 0 1 : ℝ) : ℂ) ≠ 0
  rw [h1, Complex.ofReal_one, mul_one]
  exact h2

#print axioms probe_gaussTests_ne_zero
