/- Audit probe: gaussTest c lam IS a Hermitian-transform shape h(z) conj(h(conj z)) with
   h(z) = (z - c) exp(-lam (z - c)^2), and it is real nonnegative on the real axis.
   Both EXPECTED TO SUCCEED. -/
import E6Bridge6
open Zeta23 Complex RvMBridge6
open scoped ComplexConjugate

theorem audit_gaussTest_shape (c lam : ℝ) (z : ℂ) :
    gaussTest c lam z
      = ((z - c) * Complex.exp (-(lam : ℂ) * (z - c) ^ 2))
        * conj ((conj z - c) * Complex.exp (-(lam : ℂ) * (conj z - c) ^ 2)) := by
  unfold gaussTest
  simp only [map_mul, map_sub, map_neg, map_pow, Complex.conj_conj, Complex.conj_ofReal,
    ← Complex.exp_conj]
  have h : (-(2 * (lam : ℂ)) * (z - c) ^ 2)
      = (-(lam : ℂ) * (z - c) ^ 2) + (-(lam : ℂ) * (z - c) ^ 2) := by ring
  rw [h, Complex.exp_add]
  ring

theorem audit_gaussTest_real_axis_nonneg (c lam r : ℝ) :
    0 ≤ (gaussTest c lam (r : ℂ)).re ∧ (gaussTest c lam (r : ℂ)).im = 0 := by
  unfold gaussTest
  have h : ((r : ℂ) - c) ^ 2 * Complex.exp (-(2 * (lam : ℂ)) * ((r : ℂ) - c) ^ 2)
      = (((r - c) ^ 2 * Real.exp (-(2 * lam) * (r - c) ^ 2) : ℝ) : ℂ) := by
    simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_exp,
      Complex.ofReal_neg, Complex.ofReal_ofNat]
  rw [h, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨by positivity, rfl⟩

#print axioms audit_gaussTest_shape
#print axioms audit_gaussTest_real_axis_nonneg
