/-
  Hodge1_Cert5493N -- NEGATIVE CONTROL: the even head matrix at lam = 631/1000000, above the even head eigenvalue 6.3071e-4,
  is NOT certified
  (HODGE-1 Phase 1b-B, 2026-10-12).

  STAGED kernel evaluation (Hodge1_KPenM, Hodge1_KPenW), so that no single declaration needs more than
  about 10 GB (macOS RSS, about 6 GB of which is the import baseline):
    * the moment rows are the kernel-checked ones of Hodge1_Rows5493E;
    * the moment-transform matrix is the kernel-checked WBE5493 of Hodge1_Cert5493E (wbE5493);
    * four `decide +kernel` row blocks check the rounded, shifted, strip-free head matrix on that WB against the
      literal BN5493 (Hodge1_B5493);
    * Hodge1_Ldl5493N then runs KWin's exact LDL^T checker `psdCert` on the literal BN5493;
  The kernel enforces maxHeartbeats on `decide +kernel` (200000 x 1000); the evaluation declarations carry
  `set_option maxHeartbeats 0`, which lifts that resource limit only: the kernel still checks every step.
  conjecture1_proved = False.  No `sorry`.
-/
import Hodge1_Cert5493E
import Hodge1_B5493
import Hodge1_WB5493
import Hodge1_KPenW

namespace Hodge1
open KWin KWin2

set_option maxHeartbeats 0 in
theorem blkN5493_0 : (List.range 8).map (fun i => (roundShift (headMatW H5493 0 NE5493 (631 / 10 ^ 6) WBE5493) NE5493 R5493).getD (0 + i) [])
    = (List.range 8).map (fun i => BN5493.getD (0 + i) []) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem blkN5493_1 : (List.range 8).map (fun i => (roundShift (headMatW H5493 0 NE5493 (631 / 10 ^ 6) WBE5493) NE5493 R5493).getD (8 + i) [])
    = (List.range 8).map (fun i => BN5493.getD (8 + i) []) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem blkN5493_2 : (List.range 8).map (fun i => (roundShift (headMatW H5493 0 NE5493 (631 / 10 ^ 6) WBE5493) NE5493 R5493).getD (16 + i) [])
    = (List.range 8).map (fun i => BN5493.getD (16 + i) []) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem blkN5493_3 : (List.range 8).map (fun i => (roundShift (headMatW H5493 0 NE5493 (631 / 10 ^ 6) WBE5493) NE5493 R5493).getD (24 + i) [])
    = (List.range 8).map (fun i => BN5493.getD (24 + i) []) := by
  decide +kernel

theorem matN5493 : roundShift (headMatW H5493 0 NE5493 (631 / 10 ^ 6) WBE5493) NE5493 R5493 = BN5493 :=
  list_eq_of_getD [] (roundShift_length _ _ _) (by decide +kernel)
    (rows_of_four_blocks (f := fun j => (roundShift (headMatW H5493 0 NE5493 (631 / 10 ^ 6) WBE5493) NE5493 R5493).getD j [])
      (g := fun j => BN5493.getD j []) blkN5493_0 blkN5493_1 blkN5493_2 blkN5493_3)

end Hodge1
