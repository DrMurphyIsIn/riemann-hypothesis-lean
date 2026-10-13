/-
  Probes for E6Bridge24 (2026-09-21): axiom audit of StripDerivBound (DISCHARGED) and its stages,
  and of the resulting reductions: the growth bound and the derivative partial fraction of xi'/xi
  now rest on LocalCountSum alone.
  Run: cd telperion/examples/rvm_bridge/lean && lake env lean Probes/E6Bridge24_probe.lean
  Expected: every #print axioms line is exactly [propext, Classical.choice, Quot.sound]; no errors.
-/
import E6Bridge24

open Zeta23 Complex Filter Topology RvMBridge18 RvMBridge20 RvMBridge22 RvMBridge24

#print axioms RvMBridge24.stripDerivBound
#print axioms RvMBridge24.xiDiffExtGrowthRight_of_localCount
#print axioms RvMBridge24.xiLogDerivDerivEq_of_localCount
#print axioms RvMBridge24.exists_window_bound
#print axioms RvMBridge24.norm_digamma_le_log
#print axioms RvMBridge24.landau_window
#print axioms RvMBridge24.FwinExt_differentiableOn
#print axioms RvMBridge24.deriv_FwinExt
#print axioms RvMBridge24.exists_radius
#print axioms RvMBridge24.norm_deriv_FwinExt_le
#print axioms RvMBridge24.Fwin_one_sub
#print axioms RvMBridge24.Fwin_bound_core
#print axioms RvMBridge24.sphere_bound
#print axioms RvMBridge24.target_bound_high
#print axioms RvMBridge24.target_bound_low

/-! ### The delivered shape, verbatim. -/
example : RvMBridge22.StripDerivBound := stripDerivBound

example (h1 : LocalCountSum) : RvMBridge20.XiDiffExtGrowthRight := xiDiffExtGrowthRight_of_localCount h1

example (h1 : LocalCountSum) (s : ℂ) (hs : ¬ IsNontrivialZero s) :
    deriv (logDeriv xi) s = -∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2 :=
  xiLogDerivDerivEq_of_localCount h1 s hs
