/- Audit probe for the growth obligation of E6Bridge20 (XiDiffExtGrowth / XiDiffExtGrowthRight).
   Automation attempts are EXPECTED TO FAIL in both directions.
   Run: cd telperion/examples/rvm_bridge/lean && lake env lean Probes/E6Bridge20_obligation_probe.lean -/
import E6Bridge20
open Zeta23 Complex Filter Topology RvMBridge18 RvMBridge20

/- 1. Growth by simp after unfolding (expected FAIL). -/
example : XiDiffExtGrowth := by
  unfold XiDiffExtGrowth xiDiffExt xiDiffReg
  refine ⟨1, fun s => ?_⟩
  simp

/- 2. Growth by aesop (expected FAIL). -/
example : XiDiffExtGrowthRight := by
  unfold XiDiffExtGrowthRight
  aesop

/- 3. Refutation (expected FAIL). -/
example : ¬ XiDiffExtGrowth := by
  unfold XiDiffExtGrowth
  simp

/- 4. The entire extension alone does not give XiDiffRegular (expected FAIL: the growth clause). -/
example : RvMBridge18.XiDiffRegular := by
  refine ⟨xiDiffExt, xiDiffExt_differentiable, fun _ hs => xiDiffExt_eq hs, ?_⟩
  simp [xiDiffExt, xiDiffReg]
