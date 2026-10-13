/- Audit probe: the E8 test class is inhabited by a NONZERO function (so the theorem is not vacuous). -/
import E6Bridge5
open Zeta23 Complex MeasureTheory

/-- A real smooth bump, coerced to ℂ, is a Weil test function and is nonzero. -/
theorem audit_isWeilTest_inhabited_nonzero : ∃ g : ℝ → ℂ, WeilExplicit.IsWeilTest g ∧ g ≠ 0 := by
  let f : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨fun x => ((f x : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp f.contDiff
  · exact f.hasCompactSupport.comp_left Complex.ofReal_zero
  · intro h
    have h0 : ((f 0 : ℝ) : ℂ) = 0 := congrFun h 0
    rw [f.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num))] at h0
    norm_num at h0

#print axioms audit_isWeilTest_inhabited_nonzero

/-- The autocorrelation of that bump is nonzero at 0 (so `autocorr g` is not the zero function). -/
theorem audit_autocorr_ne_zero : ∃ g : ℝ → ℂ, WeilExplicit.IsWeilTest g ∧ WeilExplicit.autocorr g ≠ 0 := by
  let f : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨fun x => ((f x : ℝ) : ℂ), ⟨Complex.ofRealCLM.contDiff.comp f.contDiff,
    f.hasCompactSupport.comp_left Complex.ofReal_zero⟩, ?_⟩
  intro h
  have h0 : WeilExplicit.autocorr (fun x => ((f x : ℝ) : ℂ)) 0 = 0 := congrFun h 0
  unfold WeilExplicit.autocorr at h0
  simp only [sub_zero, Complex.conj_ofReal, ← Complex.ofReal_mul] at h0
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at h0
  have hpos : 0 < ∫ v : ℝ, f v * f v := by
    have hc : Continuous fun v : ℝ => f v * f v := f.continuous.mul f.continuous
    have hi : Integrable fun v : ℝ => f v * f v :=
      hc.integrable_of_hasCompactSupport (f.hasCompactSupport.mul_left)
    refine (integral_pos_iff_support_of_nonneg (fun v => mul_self_nonneg (f v)) hi).mpr ?_
    have hsupp : Function.support (fun v : ℝ => f v * f v) = Function.support f := by
      ext v; simp [Function.mem_support, mul_self_eq_zero]
    rw [hsupp, f.support_eq]
    exact Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr (by norm_num))
  exact (ne_of_gt hpos) h0

#print axioms audit_autocorr_ne_zero
