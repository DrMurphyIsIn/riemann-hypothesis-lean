/- Probes for E6Bridge5 (not a delivered artifact). Run: lake env lean Probes/E6Bridge5_probe.lean -/
import E6Bridge5

open Zeta23 Complex MeasureTheory

#print axioms RvMBridge5.rh_implies_weil_positivity
#print axioms RvMBridge5.autocorr_eq_weilTest
#print axioms RvMBridge5.isWeilTest_autocorr
#print axioms RvMBridge5.eq_half_add_im_of_rh
#print axioms RvMBridge5.weilKernel_autocorr_line
#print axioms RvMBridge5.term_re_nonneg

/-! Trivial-close probes on the HYPOTHESIS-FREE sentence: each must FAIL. -/

example : ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g →
    0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re := by
  simp [WeilExplicit.weilForm, WeilExplicit.autocorr, WeilExplicit.archSide, WeilExplicit.primeSide]

example : ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g →
    0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re := by
  aesop

example : ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g →
    0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re := by
  intro g hg
  positivity

/-! autocorr does not collapse: must FAIL. -/
example (g : ℝ → ℂ) : WeilExplicit.autocorr g = 0 := by simp [WeilExplicit.autocorr]
