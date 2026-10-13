/-
  Probes for E6Bridge22 (2026-09-21): axiom audit of the growth-bound framework (regions,
  sum comparisons, continuity across zeros, assembly), of the DISCHARGED right half-plane bound,
  and of the full chain to the derivative partial fraction modulo the two remaining inequalities.
  Run: cd telperion/examples/rvm_bridge/lean && lake env lean Probes/E6Bridge22_probe.lean
  Expected: every #print axioms line is exactly [propext, Classical.choice, Quot.sound]; no errors.
  (Automation attempts on the two obligations: E6Bridge22_obligation_probe.lean, expected FAIL.)
-/
import E6Bridge22

open Zeta23 Complex Filter Topology RvMBridge18 RvMBridge20 RvMBridge22

#print axioms RvMBridge22.rightDerivBound
#print axioms RvMBridge22.xiDiffExtGrowthRight_of_two
#print axioms RvMBridge22.xiLogDerivDerivEq_of_two
#print axioms RvMBridge22.xiDiffExtGrowthRight_of
#print axioms RvMBridge22.growth_compact
#print axioms RvMBridge22.growth_right
#print axioms RvMBridge22.growth_strip
#print axioms RvMBridge22.bound_of_bound_off_zeros
#print axioms RvMBridge22.norm_tsum_far_le
#print axioms RvMBridge22.norm_tsum_polTerm_le_right
#print axioms RvMBridge22.summable_lcTerm
#print axioms RvMBridge21.deriv_logDeriv_xi_of_one_lt_re
#print axioms RvMBridge22.norm_deriv_digamma_le
#print axioms RvMBridge22.norm_deriv_logDeriv_zeta_le

/-! ### The delivered shapes. -/
example (h1 : LocalCountSum) (h2 : StripDerivBound) : RvMBridge20.XiDiffExtGrowthRight :=
  xiDiffExtGrowthRight_of_two h1 h2

example (h1 : LocalCountSum) (h2 : StripDerivBound) : RvMBridge18.XiDiffRegular :=
  xiDiffRegular_of_three h1 h2 rightDerivBound

example (h1 : LocalCountSum) (h2 : StripDerivBound) (s : ℂ) (hs : ¬ IsNontrivialZero s) :
    deriv (logDeriv xi) s = -∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2 :=
  xiLogDerivDerivEq_of_two h1 h2 s hs

/-! ### Non-vacuity of the right half-plane bound: its constant is a genuine finite number and the
bound applies at the point 2 (not a zero), where deriv (logDeriv xi) 2 is a definite value. -/
example : ∃ C : ℝ, ‖deriv (logDeriv xi) 2‖ ≤ C := by
  obtain ⟨C, hC⟩ := rightDerivBound
  exact ⟨C, hC 2 (by norm_num)⟩
