/-
  Probes for E6Bridge7 (2026-09-20): axiom audit of the O2 discharge and its lemmas, and the
  remaining obligation's non-triviality.
  Run: cd telperion/examples/rvm_bridge/lean && lake env lean Probes/E6Bridge7_probe.lean
-/
import E6Bridge7

open RvMBridge7

/-! ### Axiom audit. -/
#print axioms RvMBridge7.gaussian_dominance
#print axioms RvMBridge7.weil_positivity_implies_rh_of_approx
#print axioms RvMBridge7.norm_gaussTest
#print axioms RvMBridge7.norm_term
#print axioms RvMBridge7.re_gaussTest
#print axioms RvMBridge7.exists_lam_trig
#print axioms RvMBridge7.exists_lam_re_gaussTest
#print axioms RvMBridge7.windowSet_finite
#print axioms RvMBridge7.eq_badOf_of_phi_eq
#print axioms RvMBridge7.exists_generic_centre
#print axioms RvMBridge7.eq_or_eq_reflect_of_phi_eq
#print axioms RvMBridge7.exists_maximiser_gap
#print axioms RvMBridge7.phi_neg_of_not_mem_window
#print axioms RvMBridge7.norm_term_le_majorant
#print axioms RvMBridge7.tsum_majorant
#print axioms RvMBridge7.tail_bound
#print axioms RvMBridge7.re_zeroSide_le

/-! ### The discharged obligation is exactly E6Bridge6's def. -/
example : RvMBridge6.GaussianDominance := RvMBridge7.gaussian_dominance
#check @RvMBridge7.weil_positivity_implies_rh_of_approx

/-! ### The remaining obligation GaussianApprox is neither closed nor refuted by simp/aesop. -/
/-- error: `simp` made no progress -/
#guard_msgs in
example : RvMBridge6.GaussianApprox := by simp

/-- error: `simp` made no progress -/
#guard_msgs in
example : ¬ RvMBridge6.GaussianApprox := by simp

/--
error: Tactic `aesop` failed, made no progress
Initial goal:
  ⊢ RvMBridge6.GaussianApprox
-/
#guard_msgs in
example : RvMBridge6.GaussianApprox := by aesop

/--
warning: aesop: failed to prove the goal after exhaustive search.
---
error: unsolved goals
a : RvMBridge6.GaussianApprox
⊢ False
-/
#guard_msgs in
example : ¬ RvMBridge6.GaussianApprox := by aesop
