/- Audit probe for the ONE obligation of E6Bridge15, LiValue n (the value half of B7).
   Automation attempts are EXPECTED TO FAIL in both directions: LiValue n is neither proved nor
   refuted by simp / aesop / norm_num after unfolding.  (At n = 0 it IS refutable; that case is
   in E6Bridge15_probe.lean and is exactly why the node carries 0 < n.)
   Run: cd telperion/examples/rvm_bridge/lean && lake env lean Probes/E6Bridge15_obligation_probe.lean -/
import E6Bridge15
open Zeta23 Complex Filter Topology RvMBridge15 RvMBridge15.BombieriLagarias

/- 1. LiValue 1 by simp (expected FAIL). -/
example : LiValue 1 := by
  unfold LiValue liLimit liPaired liKernel BombieriLagarias.archSide BombieriLagarias.finiteSide
    BombieriLagarias.eta BombieriLagarias.zetaLogDerivReg
  simp

/- 2. LiValue n, n >= 1, by aesop (expected FAIL). -/
example (n : ℕ) (hn : 0 < n) : LiValue n := by
  unfold LiValue liLimit liPaired liKernel BombieriLagarias.archSide BombieriLagarias.finiteSide
  aesop

/- 3. Refutation of LiValue 1 by simp / norm_num (expected FAIL). -/
example : ¬ LiValue 1 := by
  unfold LiValue liLimit liPaired liKernel BombieriLagarias.archSide BombieriLagarias.finiteSide
    BombieriLagarias.eta BombieriLagarias.zetaLogDerivReg
  simp

example : ¬ LiValue 1 := by
  unfold LiValue liLimit liPaired liKernel BombieriLagarias.archSide BombieriLagarias.finiteSide
  norm_num

/- 4. The convergence theorem does NOT by itself give the value (expected FAIL): the limit is
   liLimit n, an unevaluated tsum. -/
example (n : ℕ) (hn : 0 < n) :
    Tendsto (liZeroSum n) atTop (𝓝 (BombieriLagarias.archSide n + BombieriLagarias.finiteSide n)) := by
  have := liZeroSum_tendsto n
  simpa [LiValue] using this
