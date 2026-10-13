/- Audit probe for E6Bridge8/9: the witness family is nonzero, the bound constant does not
   depend on n, and the assembly consumes exactly the named inputs. -/
import E6Bridge9
open Zeta23 Complex MeasureTheory Filter Topology RvMBridge8 WeilExplicit

/- 1. gaussTests c lam n is not the zero function: at u = 1 the cutoff is 1 and phi(1) ≠ 0
   (expected SUCCESS). -/
theorem audit_gaussTests_ne_zero {c lam : ℝ} (hlam : 0 < lam) (n : ℕ) : gaussTests c lam n ≠ 0 := by
  intro h
  have h1 : gaussTests c lam n 1 = 0 := congrFun h 1
  unfold gaussTests gaussPhi at h1
  rw [cutoff_eq_one (n := n) (u := 1) (by
    rw [abs_one]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])] at h1
  simp only [Complex.ofReal_one, mul_one, mul_eq_zero, Complex.exp_ne_zero, or_false] at h1
  exact gaussK_ne_zero hlam h1
#print axioms audit_gaussTests_ne_zero

/- 2. Every member of the family is a Weil test and nonzero (expected SUCCESS). -/
example {c lam : ℝ} (hlam : 0 < lam) (n : ℕ) : IsWeilTest (gaussTests c lam n) ∧ gaussTests c lam n ≠ 0 :=
  ⟨isWeilTest_gaussTests c lam n, audit_gaussTests_ne_zero hlam n⟩

/- 3. The uniform constant: ∃ M is OUTSIDE ∀ n (expected SUCCESS by unification). -/
example {c lam : ℝ} (hlam : 0 < lam) :
    ∃ M : ℝ, ∀ n : ℕ, ∀ z : ℂ, |z.im| ≤ 1 / 2 →
      ‖paperFT (gaussTests c lam n) z‖ ≤ 2 * M / (1 + ‖z‖) :=
  let ⟨M, _, h⟩ := exists_paperFT_gaussTests_bound (c := c) hlam; ⟨M, h⟩

/- 4. Shape consumption and the assembly's inputs (expected SUCCESS). -/
example : RvMBridge6.GaussianApprox := RvMBridge8.gaussian_approx
example : RvMBridge6.GaussianTransfer := RvMBridge6.gaussianTransfer_of_approx RvMBridge8.gaussian_approx
example : (∀ g : ℝ → ℂ, IsWeilTest g → 0 ≤ (weilForm (autocorr g)).re) ↔ RiemannHypothesis :=
  ⟨RvMBridge7.weil_positivity_implies_rh_of_approx RvMBridge8.gaussian_approx,
   RvMBridge5.rh_implies_weil_positivity⟩

/- 5. The strip majorant really dominates ‖e^{izu}‖ by e^{|u|/2} only on |Im z| ≤ 1/2:
   off the strip the bound is false at some u (expected FAIL). -/
example (z : ℂ) (u : ℝ) : ‖cexp (I * z * u)‖ ≤ Real.exp ((1 / 2) * |u|) := by
  exact norm_cexp_I_mul_le (by norm_num) u
