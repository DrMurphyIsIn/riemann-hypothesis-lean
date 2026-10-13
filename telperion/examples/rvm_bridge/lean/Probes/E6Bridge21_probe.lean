/- Audit probe for E6Bridge21 (Obligation 2 of E6Bridge18: real-axis decay of (log xi)'').
   Run: cd telperion/examples/rvm_bridge/lean && lake env lean Probes/E6Bridge21_probe.lean
   Expected: every #print axioms lists exactly [propext, Classical.choice, Quot.sound]; the
   automation attempts on the target are EXPECTED TO FAIL (the target is not simp/aesop-closable). -/
import E6Bridge21
open Zeta23 Complex Filter Topology RvMBridge18 RvMBridge21

/- 1. Axioms of the delivered theorem and its stage lemmas. -/
#print axioms RvMBridge21.xi_logDeriv_deriv_decay
#print axioms RvMBridge21.deriv_logDeriv_xi_real
#print axioms RvMBridge21.digamma_deriv_tendsto_zero
#print axioms RvMBridge21.zeta_logDeriv_deriv_tendsto_zero
#print axioms RvMBridge21.hasSum_trigamma_of_re_pos
#print axioms RvMBridge21.norm_deriv_digamma_real_le
#print axioms RvMBridge21.deriv_logDeriv_zeta_eq
#print axioms RvMBridge21.xi_logDeriv_deriv_eq_of_regular

/- 2. The delivered statement is literally the E6Bridge18 obligation. -/
example : RvMBridge18.XiLogDerivDerivDecay := RvMBridge21.xi_logDeriv_deriv_decay
#check @RvMBridge21.xi_logDeriv_deriv_decay
#check @RvMBridge21.deriv_logDeriv_xi_real
#check @RvMBridge21.hasSum_trigamma_of_re_pos
#check @RvMBridge21.norm_deriv_digamma_real_le

/- 3. Non-vacuity: the trigamma bound is not vacuous on the ray (x = 2 is admissible), and the
   real-ray identity has a nonzero right-hand side in general (only sanity-typechecks). -/
example : ‖deriv Complex.digamma ((2 : ℝ) : ℂ)‖ ≤ 1 / ((2 : ℝ) - 1 / 2) :=
  RvMBridge21.norm_deriv_digamma_real_le (by norm_num)

/- 4. Automation on the target (expected FAIL). -/
example : RvMBridge18.XiLogDerivDerivDecay := by
  unfold RvMBridge18.XiLogDerivDerivDecay RvMBridge18.xi
  simp

example : RvMBridge18.XiLogDerivDerivDecay := by
  unfold RvMBridge18.XiLogDerivDerivDecay
  aesop
