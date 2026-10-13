/- Audit probe for the two obligations of E6Bridge18.  Automation attempts are EXPECTED TO FAIL
   in both directions: neither XiDiffRegular nor XiLogDerivDerivDecay is proved or refuted by
   simp / aesop after unfolding, and the interface identity does not follow from summability alone.
   Run: cd telperion/examples/rvm_bridge/lean && lake env lean Probes/E6Bridge18_obligation_probe.lean -/
import E6Bridge18
open Zeta23 Complex Filter Topology RvMBridge18

/- 1. XiDiffRegular by a constant witness (expected FAIL: G must agree with xiDiffReg off zeros). -/
example : XiDiffRegular := by
  refine ⟨fun _ => 0, differentiable_const _, ?_, 0, ?_⟩
  · intro s hs; simp [xiDiffReg]
  · intro s; simp

/- 2. XiDiffRegular by aesop (expected FAIL). -/
example : XiDiffRegular := by
  unfold XiDiffRegular xiDiffReg
  aesop

/- 3. XiLogDerivDerivDecay by simp (expected FAIL). -/
example : XiLogDerivDerivDecay := by
  unfold XiLogDerivDerivDecay xi
  simp

/- 4. Refutations (expected FAIL). -/
example : ¬ XiDiffRegular := by
  unfold XiDiffRegular xiDiffReg
  simp

example : ¬ XiLogDerivDerivDecay := by
  unfold XiLogDerivDerivDecay
  simp

/- 5. The identity from summability alone (expected FAIL). -/
example (s : ℂ) (hs : ¬ IsNontrivialZero s) :
    deriv (logDeriv xi) s = -∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2 := by
  have := summable_inv_sub_sq s hs
  simp [xi]
