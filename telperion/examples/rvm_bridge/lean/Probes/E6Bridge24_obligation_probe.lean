/- Audit probe (2026-09-21): after E6Bridge24 the ONE remaining input of the growth bound is
   LocalCountSum (E6Bridge22; owned by xi-decay's E6Bridge23).  Automation attempts are EXPECTED
   TO FAIL: StripDerivBound alone does not give the growth, and LocalCountSum is neither proved nor
   refuted by simp / aesop.
   Run: cd telperion/examples/rvm_bridge/lean && lake env lean Probes/E6Bridge24_obligation_probe.lean -/
import E6Bridge24
open Zeta23 Complex Filter Topology RvMBridge18 RvMBridge20 RvMBridge22 RvMBridge24

/- 1. Growth from StripDerivBound alone (expected FAIL). -/
example : XiDiffExtGrowthRight := by
  have := stripDerivBound
  unfold XiDiffExtGrowthRight
  simp [xiDiffExt, xiDiffReg]

/- 2. LocalCountSum by simp / aesop (expected FAIL). -/
example : LocalCountSum := by
  unfold LocalCountSum lcTerm
  refine ⟨1, fun a => ?_⟩
  simp

example : LocalCountSum := by
  unfold LocalCountSum
  aesop

/- 3. Refutation (expected FAIL). -/
example : ¬ LocalCountSum := by
  unfold LocalCountSum lcTerm
  simp
