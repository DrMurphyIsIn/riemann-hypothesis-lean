/- Audit probe for E6Bridge23 (LocalCountSum of E6Bridge22 discharged).
   Run: cd telperion/examples/rvm_bridge/lean && lake env lean Probes/E6Bridge23_probe.lean
   Expected: every #print axioms lists exactly [propext, Classical.choice, Quot.sound]; the
   automation attempts on the target are EXPECTED TO FAIL (not simp/aesop-closable). -/
import E6Bridge23
open Zeta23 Complex Filter Topology RvMBridge22 RvMBridge23

/- 1. Axioms of the delivered theorem and its stage lemmas. -/
#print axioms RvMBridge23.local_count_sum
#print axioms RvMBridge23.sum_lcTerm_le
#print axioms RvMBridge23.sum_zeroMult_fiber_le
#print axioms RvMBridge23.summable_wt
#print axioms RvMBridge23.summable_wlog
#print axioms RvMBridge23.log_div_le_rpow
#print axioms RvMBridge23.xiDiffExtGrowthRight_of_strip
#print axioms RvMBridge23.xiLogDerivDerivEq_of_strip

/- 2. The delivered statement is literally the E6Bridge22 obligation. -/
example : RvMBridge22.LocalCountSum := RvMBridge23.local_count_sum
#check @RvMBridge23.local_count_sum
#check @RvMBridge23.sum_lcTerm_le
#check @RvMBridge23.sum_zeroMult_fiber_le
#check @RvMBridge23.xiLogDerivDerivEq_of_strip

/- 3. Automation on the target (expected FAIL). -/
example : RvMBridge22.LocalCountSum := by
  unfold RvMBridge22.LocalCountSum RvMBridge22.lcTerm
  simp

example : RvMBridge22.LocalCountSum := by
  unfold RvMBridge22.LocalCountSum
  aesop

/- 4. Refutation (expected FAIL). -/
example : ¬ RvMBridge22.LocalCountSum := by
  unfold RvMBridge22.LocalCountSum
  simp
