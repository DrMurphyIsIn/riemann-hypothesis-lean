/-
  Probes for E6Bridge17 (2026-09-21): axiom audit of the plain Gaussian face, the heat identity and
  the ThetaFree constant; non-triviality of ThetaFree.
  Run: cd telperion/examples/rvm_bridge/lean && lake env lean Probes/E6Bridge17_probe.lean
-/
import E6Bridge17

open RvMBridge17

/-! ### Axiom audit. -/
#print axioms RvMBridge17.rh_iff_theta_positivity
#print axioms RvMBridge17.theta_nonneg_of_rh
#print axioms RvMBridge17.exists_theta_neg_of_offline
#print axioms RvMBridge17.summable_plain_zeroSide
#print axioms RvMBridge17.plainGauss_heat
#print axioms RvMBridge17.real_gauss_heat
#print axioms RvMBridge17.theta_heat
#print axioms RvMBridge17.theta_pos_mono
#print axioms RvMBridge17.thetaFree_mono
#print axioms RvMBridge17.rh_iff_thetaFree_all
#print axioms RvMBridge17.rh_iff_thetaWidths_eq
#print axioms RvMBridge17.not_thetaFree_of_offline
#print axioms RvMBridge17.rh_or_thetaWidths_bddAbove
#print axioms RvMBridgeXi.nontrivialZeros_countable

#check @RvMBridge17.rh_iff_theta_positivity
#check @RvMBridge17.theta_heat
#check @RvMBridge17.not_thetaFree_of_offline

/-! ### ThetaFree is neither closed nor refuted by simp/aesop (it is RH-strength as lam -> infinity). -/
/-- error: `simp` made no progress -/
#guard_msgs in
example (lam : ℝ) : ThetaFree lam := by simp

/-- error: `simp` made no progress -/
#guard_msgs in
example (lam : ℝ) : ¬ ThetaFree lam := by simp

/--
error: Tactic `aesop` failed, made no progress
Initial goal:
  lam : ℝ
  ⊢ ThetaFree lam
-/
#guard_msgs in
example (lam : ℝ) : ThetaFree lam := by aesop

/-! ### The heat variance is positive and the kernel nonnegative on the stated range. -/
example : 0 < heatVar 1 2 := heatVar_pos one_pos (by norm_num)
example (u : ℝ) : 0 ≤ heatKernel (heatVar 1 2) u := heatKernel_nonneg (heatVar_pos one_pos (by norm_num)) u

/-! ### The normalisation: sigma^2 = 1/(4 lam') - 1/(4 lam). -/
example : heatVar 1 2 = 1 / 8 := by unfold heatVar; norm_num
