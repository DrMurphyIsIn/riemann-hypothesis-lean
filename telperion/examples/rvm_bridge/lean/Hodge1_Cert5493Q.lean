/-
  Hodge1_Cert5493Q -- NEGATIVE CONTROL: with the prime location moved to q = 2.1 (comb weight 2 log 2.1/sqrt 2.1 at lag
  log 2.1; beta0 kept, which is optimistic for the fake) the even head matrix is NOT certified (even head
  eigenvalue -0.0716; B's truth on the pole-free hyperplane at L = 0.549: -0.0695)
  (HODGE-1 Phase 1b-B, 2026-10-12).

  STAGED kernel evaluation (Hodge1_KPenM, Hodge1_KPenW), so that no single declaration needs more than
  about 10 GB (macOS RSS, about 6 GB of which is the import baseline):
    * the moment rows are the kernel-checked ones of Hodge1_Rows5493E;
    * five `decide +kernel` blocks (8, 8, 8, 8, 5 rows) check the moment-transform matrix WBmatM against the literal WBQ5493 (Hodge1_WB5493);
    * four `decide +kernel` row blocks check the rounded, shifted, strip-free head matrix on that WB against the
      literal BQ5493 (Hodge1_B5493);
    * Hodge1_Ldl5493Q then runs KWin's exact LDL^T checker `psdCert` on the literal BQ5493;
  The kernel enforces maxHeartbeats on `decide +kernel` (200000 x 1000); the evaluation declarations carry
  `set_option maxHeartbeats 0`, which lifts that resource limit only: the kernel still checks every step.
  conjecture1_proved = False.  No `sorry`.
-/
import Hodge1_Rows5493E
import Hodge1_B5493
import Hodge1_WB5493
import Hodge1_KPenW

namespace Hodge1
open KWin KWin2

set_option maxHeartbeats 0 in
theorem wbblkQ5493_0 : (List.range 8).map (fun i =>
      (WBmatM H5493q21.K 0 NE5493 (momListLit H5493q21.K 0 rowsE5493)).getD (0 + i) [])
    = (List.range 8).map (fun i => WBQ5493.getD (0 + i) []) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem wbblkQ5493_1 : (List.range 8).map (fun i =>
      (WBmatM H5493q21.K 0 NE5493 (momListLit H5493q21.K 0 rowsE5493)).getD (8 + i) [])
    = (List.range 8).map (fun i => WBQ5493.getD (8 + i) []) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem wbblkQ5493_2 : (List.range 8).map (fun i =>
      (WBmatM H5493q21.K 0 NE5493 (momListLit H5493q21.K 0 rowsE5493)).getD (16 + i) [])
    = (List.range 8).map (fun i => WBQ5493.getD (16 + i) []) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem wbblkQ5493_3 : (List.range 8).map (fun i =>
      (WBmatM H5493q21.K 0 NE5493 (momListLit H5493q21.K 0 rowsE5493)).getD (24 + i) [])
    = (List.range 8).map (fun i => WBQ5493.getD (24 + i) []) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem wbblkQ5493_4 : (List.range 5).map (fun i =>
      (WBmatM H5493q21.K 0 NE5493 (momListLit H5493q21.K 0 rowsE5493)).getD (32 + i) [])
    = (List.range 5).map (fun i => WBQ5493.getD (32 + i) []) := by
  decide +kernel

theorem wbQ5493 : WBmatM H5493q21.K 0 NE5493 (momListLit H5493q21.K 0 rowsE5493) = WBQ5493 :=
  list_eq_of_getD [] (WBmatM_length _ _ _ _) (by decide +kernel)
    (rows_of_five_blocks (f := fun j => (WBmatM H5493q21.K 0 NE5493 (momListLit H5493q21.K 0 rowsE5493)).getD j [])
      (g := fun j => WBQ5493.getD j []) wbblkQ5493_0 wbblkQ5493_1 wbblkQ5493_2 wbblkQ5493_3 wbblkQ5493_4)

set_option maxHeartbeats 0 in
theorem blkQ5493_0 : (List.range 8).map (fun i => (roundShift (headMatW H5493q21 0 NE5493 lamE5493 WBQ5493) NE5493 R5493).getD (0 + i) [])
    = (List.range 8).map (fun i => BQ5493.getD (0 + i) []) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem blkQ5493_1 : (List.range 8).map (fun i => (roundShift (headMatW H5493q21 0 NE5493 lamE5493 WBQ5493) NE5493 R5493).getD (8 + i) [])
    = (List.range 8).map (fun i => BQ5493.getD (8 + i) []) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem blkQ5493_2 : (List.range 8).map (fun i => (roundShift (headMatW H5493q21 0 NE5493 lamE5493 WBQ5493) NE5493 R5493).getD (16 + i) [])
    = (List.range 8).map (fun i => BQ5493.getD (16 + i) []) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem blkQ5493_3 : (List.range 8).map (fun i => (roundShift (headMatW H5493q21 0 NE5493 lamE5493 WBQ5493) NE5493 R5493).getD (24 + i) [])
    = (List.range 8).map (fun i => BQ5493.getD (24 + i) []) := by
  decide +kernel

theorem matQ5493 : roundShift (headMatW H5493q21 0 NE5493 lamE5493 WBQ5493) NE5493 R5493 = BQ5493 :=
  list_eq_of_getD [] (roundShift_length _ _ _) (by decide +kernel)
    (rows_of_four_blocks (f := fun j => (roundShift (headMatW H5493q21 0 NE5493 lamE5493 WBQ5493) NE5493 R5493).getD j [])
      (g := fun j => BQ5493.getD j []) blkQ5493_0 blkQ5493_1 blkQ5493_2 blkQ5493_3)

end Hodge1
