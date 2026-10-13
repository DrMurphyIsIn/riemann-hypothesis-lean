/-
  Probes for E6Bridge6 (2026-09-20): axiom audit of every delivered theorem, and non-triviality
  probes for the two named obligations (neither is closed nor refuted by simp/aesop).
  Run: cd telperion/examples/rvm_bridge/lean && lake env lean Probes/E6Bridge6_probe.lean
-/
import E6Bridge6

open RvMBridge6

/-! ### Axiom audit: every delivered theorem prints [propext, Classical.choice, Quot.sound]. -/
#print axioms RvMBridge6.weilForm_autocorr_eq_zeroSide
#print axioms RvMBridge6.hasSum_weilForm_autocorr
#print axioms RvMBridge6.zeroSide_conj
#print axioms RvMBridge6.weilForm_autocorr_real
#print axioms RvMBridge6.gammaOf_reflect
#print axioms RvMBridge6.zeroMult_reflect
#print axioms RvMBridge6.strip_of_zero
#print axioms RvMBridge6.rh_of_all_on_line
#print axioms RvMBridge6.weil_positivity_implies_rh_of
#print axioms RvMBridge6.rh_iff_weil_positivity_of
#print axioms RvMBridge6.zeroSide_pair_split
#print axioms RvMBridge6.gaussTest_axis
#print axioms RvMBridge6.gaussTest_axis_re_neg
#print axioms RvMBridge6.norm_gaussTest_mul_le
#print axioms RvMBridgeGauss.summable_mult_div_one_add_normSq
#print axioms RvMBridge6.summable_gauss_zeroSide
#print axioms RvMBridge6.gauss_zeroSide_real
#print axioms RvMBridge6.gauss_zeroSide_pair_split
#print axioms RvMBridge6.gaussianTransfer_of_approx
#print axioms RvMBridge6.weil_positivity_implies_rh_of'

/-! ### The obligations are not closed by simp or aesop. -/
/-- error: `simp` made no progress -/
#guard_msgs in
example : GaussianTransfer := by simp

/-- error: `simp` made no progress -/
#guard_msgs in
example : GaussianDominance := by simp

/-- error: `simp` made no progress -/
#guard_msgs in
example : GaussianApprox := by simp

/-- error: `simp` made no progress -/
#guard_msgs in
example : ¬ GaussianApprox := by simp

/--
error: Tactic `aesop` failed, made no progress
Initial goal:
  ⊢ GaussianApprox
-/
#guard_msgs in
example : GaussianApprox := by aesop

/--
warning: aesop: failed to prove the goal after exhaustive search.
---
error: unsolved goals
a : GaussianApprox
⊢ False
-/
#guard_msgs in
example : ¬ GaussianApprox := by aesop

/-! ### The obligations are not refuted by simp or aesop. -/
/-- error: `simp` made no progress -/
#guard_msgs in
example : ¬ GaussianTransfer := by simp

/-- error: `simp` made no progress -/
#guard_msgs in
example : ¬ GaussianDominance := by simp

/--
error: Tactic `aesop` failed, made no progress
Initial goal:
  ⊢ GaussianTransfer
-/
#guard_msgs in
example : GaussianTransfer := by aesop

/--
error: Tactic `aesop` failed, made no progress
Initial goal:
  ⊢ GaussianDominance
-/
#guard_msgs in
example : GaussianDominance := by aesop

/--
warning: aesop: failed to prove the goal after exhaustive search.
---
error: unsolved goals
a : GaussianTransfer
⊢ False
-/
#guard_msgs in
example : ¬ GaussianTransfer := by aesop

/--
warning: aesop: failed to prove the goal after exhaustive search.
---
error: unsolved goals
a : GaussianDominance
⊢ False
-/
#guard_msgs in
example : ¬ GaussianDominance := by aesop

/-! ### The obligations are consumed only as hypotheses (no instance, no axiom): the delivered
theorem's type mentions them explicitly. -/
#check @RvMBridge6.weil_positivity_implies_rh_of
#check @RvMBridge6.weil_positivity_implies_rh_of'
