/- Audit probe for the two remaining obligations of E6Bridge22 (LocalCountSum, StripDerivBound).
   Automation attempts are EXPECTED TO FAIL in both directions.
   Run: cd telperion/examples/rvm_bridge/lean && lake env lean Probes/E6Bridge22_obligation_probe.lean -/
import E6Bridge22
open Zeta23 Complex Filter Topology RvMBridge18 RvMBridge20 RvMBridge22

/- 1. LocalCountSum by a constant and simp (expected FAIL). -/
example : LocalCountSum := by
  unfold LocalCountSum lcTerm
  refine ⟨1, fun a => ?_⟩
  simp

/- 2. LocalCountSum by aesop (expected FAIL). -/
example : LocalCountSum := by
  unfold LocalCountSum
  aesop

/- 3. StripDerivBound by simp (expected FAIL). -/
example : StripDerivBound := by
  unfold StripDerivBound
  refine ⟨1, fun s h1 h2 h3 h4 => ?_⟩
  simp

/- 4. Refutations (expected FAIL). -/
example : ¬ LocalCountSum := by
  unfold LocalCountSum lcTerm
  simp

example : ¬ StripDerivBound := by
  unfold StripDerivBound
  simp

/- 5. The growth from the right half-plane bound alone (expected FAIL). -/
example : XiDiffExtGrowthRight := by
  have := rightDerivBound
  unfold XiDiffExtGrowthRight
  simp [xiDiffExt, xiDiffReg]
