/-
  Hodge1_Cert5493W -- NEGATIVE CONTROL: with the comb weight 1.05 c2 at the true lag log 2 the even head matrix is NOT
  certified (even head eigenvalue -0.00684; B's truth: -0.0066)
  (HODGE-1 Phase 1b-B, 2026-10-12).

  STAGED kernel evaluation (Hodge1_KPenM, Hodge1_KPenW), so that no single declaration needs more than
  about 10 GB (macOS RSS, about 6 GB of which is the import baseline):
    * the moment rows are the kernel-checked ones of Hodge1_Rows5493E;
    * five `decide +kernel` blocks (8, 8, 8, 8, 5 rows) check the moment-transform matrix WBmatM against the literal WBW5493 (Hodge1_WB5493);
    * four `decide +kernel` row blocks check the rounded, shifted, strip-free head matrix on that WB against the
      literal BW5493 (Hodge1_B5493);
    * Hodge1_Ldl5493W then runs KWin's exact LDL^T checker `psdCert` on the literal BW5493;
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
theorem wbblkW5493_0 : (List.range 8).map (fun i =>
      (WBmatM H5493w105.K 0 NE5493 (momListLit H5493w105.K 0 rowsE5493)).getD (0 + i) [])
    = (List.range 8).map (fun i => WBW5493.getD (0 + i) []) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem wbblkW5493_1 : (List.range 8).map (fun i =>
      (WBmatM H5493w105.K 0 NE5493 (momListLit H5493w105.K 0 rowsE5493)).getD (8 + i) [])
    = (List.range 8).map (fun i => WBW5493.getD (8 + i) []) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem wbblkW5493_2 : (List.range 8).map (fun i =>
      (WBmatM H5493w105.K 0 NE5493 (momListLit H5493w105.K 0 rowsE5493)).getD (16 + i) [])
    = (List.range 8).map (fun i => WBW5493.getD (16 + i) []) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem wbblkW5493_3 : (List.range 8).map (fun i =>
      (WBmatM H5493w105.K 0 NE5493 (momListLit H5493w105.K 0 rowsE5493)).getD (24 + i) [])
    = (List.range 8).map (fun i => WBW5493.getD (24 + i) []) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem wbblkW5493_4 : (List.range 5).map (fun i =>
      (WBmatM H5493w105.K 0 NE5493 (momListLit H5493w105.K 0 rowsE5493)).getD (32 + i) [])
    = (List.range 5).map (fun i => WBW5493.getD (32 + i) []) := by
  decide +kernel

theorem wbW5493 : WBmatM H5493w105.K 0 NE5493 (momListLit H5493w105.K 0 rowsE5493) = WBW5493 :=
  list_eq_of_getD [] (WBmatM_length _ _ _ _) (by decide +kernel)
    (rows_of_five_blocks (f := fun j => (WBmatM H5493w105.K 0 NE5493 (momListLit H5493w105.K 0 rowsE5493)).getD j [])
      (g := fun j => WBW5493.getD j []) wbblkW5493_0 wbblkW5493_1 wbblkW5493_2 wbblkW5493_3 wbblkW5493_4)

set_option maxHeartbeats 0 in
theorem blkW5493_0 : (List.range 8).map (fun i => (roundShift (headMatW H5493w105 0 NE5493 lamE5493 WBW5493) NE5493 R5493).getD (0 + i) [])
    = (List.range 8).map (fun i => BW5493.getD (0 + i) []) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem blkW5493_1 : (List.range 8).map (fun i => (roundShift (headMatW H5493w105 0 NE5493 lamE5493 WBW5493) NE5493 R5493).getD (8 + i) [])
    = (List.range 8).map (fun i => BW5493.getD (8 + i) []) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem blkW5493_2 : (List.range 8).map (fun i => (roundShift (headMatW H5493w105 0 NE5493 lamE5493 WBW5493) NE5493 R5493).getD (16 + i) [])
    = (List.range 8).map (fun i => BW5493.getD (16 + i) []) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem blkW5493_3 : (List.range 8).map (fun i => (roundShift (headMatW H5493w105 0 NE5493 lamE5493 WBW5493) NE5493 R5493).getD (24 + i) [])
    = (List.range 8).map (fun i => BW5493.getD (24 + i) []) := by
  decide +kernel

theorem matW5493 : roundShift (headMatW H5493w105 0 NE5493 lamE5493 WBW5493) NE5493 R5493 = BW5493 :=
  list_eq_of_getD [] (roundShift_length _ _ _) (by decide +kernel)
    (rows_of_four_blocks (f := fun j => (roundShift (headMatW H5493w105 0 NE5493 lamE5493 WBW5493) NE5493 R5493).getD j [])
      (g := fun j => BW5493.getD j []) blkW5493_0 blkW5493_1 blkW5493_2 blkW5493_3)

end Hodge1
