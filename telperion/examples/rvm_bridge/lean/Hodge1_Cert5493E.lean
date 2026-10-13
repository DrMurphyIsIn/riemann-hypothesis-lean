/-
  Hodge1_Cert5493E -- the EVEN-sector head certificate of the direct pole-free certificate at l = 5493/10000 (N = 32,
  lam = 55/100000)
  (HODGE-1 Phase 1b-B, 2026-10-12).

  STAGED kernel evaluation (Hodge1_KPenM, Hodge1_KPenW), so that no single declaration needs more than
  about 10 GB (macOS RSS, about 6 GB of which is the import baseline):
    * the moment rows are the kernel-checked ones of Hodge1_Rows5493E;
    * five `decide +kernel` blocks (8, 8, 8, 8, 5 rows) check the moment-transform matrix WBmatM against the literal WBE5493 (Hodge1_WB5493);
    * four `decide +kernel` row blocks check the rounded, shifted, strip-free head matrix on that WB against the
      literal BE5493 (Hodge1_B5493);
    * Hodge1_Ldl5493E then runs KWin's exact LDL^T checker `psdCert` on the literal BE5493;
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
theorem wbblkE5493_0 : (List.range 8).map (fun i =>
      (WBmatM P5493 0 NE5493 (momListLit P5493 0 rowsE5493)).getD (0 + i) [])
    = (List.range 8).map (fun i => WBE5493.getD (0 + i) []) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem wbblkE5493_1 : (List.range 8).map (fun i =>
      (WBmatM P5493 0 NE5493 (momListLit P5493 0 rowsE5493)).getD (8 + i) [])
    = (List.range 8).map (fun i => WBE5493.getD (8 + i) []) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem wbblkE5493_2 : (List.range 8).map (fun i =>
      (WBmatM P5493 0 NE5493 (momListLit P5493 0 rowsE5493)).getD (16 + i) [])
    = (List.range 8).map (fun i => WBE5493.getD (16 + i) []) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem wbblkE5493_3 : (List.range 8).map (fun i =>
      (WBmatM P5493 0 NE5493 (momListLit P5493 0 rowsE5493)).getD (24 + i) [])
    = (List.range 8).map (fun i => WBE5493.getD (24 + i) []) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem wbblkE5493_4 : (List.range 5).map (fun i =>
      (WBmatM P5493 0 NE5493 (momListLit P5493 0 rowsE5493)).getD (32 + i) [])
    = (List.range 5).map (fun i => WBE5493.getD (32 + i) []) := by
  decide +kernel

theorem wbE5493 : WBmatM P5493 0 NE5493 (momListLit P5493 0 rowsE5493) = WBE5493 :=
  list_eq_of_getD [] (WBmatM_length _ _ _ _) (by decide +kernel)
    (rows_of_five_blocks (f := fun j => (WBmatM P5493 0 NE5493 (momListLit P5493 0 rowsE5493)).getD j [])
      (g := fun j => WBE5493.getD j []) wbblkE5493_0 wbblkE5493_1 wbblkE5493_2 wbblkE5493_3 wbblkE5493_4)

set_option maxHeartbeats 0 in
theorem blkE5493_0 : (List.range 8).map (fun i => (roundShift (headMatW H5493 0 NE5493 lamE5493 WBE5493) NE5493 R5493).getD (0 + i) [])
    = (List.range 8).map (fun i => BE5493.getD (0 + i) []) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem blkE5493_1 : (List.range 8).map (fun i => (roundShift (headMatW H5493 0 NE5493 lamE5493 WBE5493) NE5493 R5493).getD (8 + i) [])
    = (List.range 8).map (fun i => BE5493.getD (8 + i) []) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem blkE5493_2 : (List.range 8).map (fun i => (roundShift (headMatW H5493 0 NE5493 lamE5493 WBE5493) NE5493 R5493).getD (16 + i) [])
    = (List.range 8).map (fun i => BE5493.getD (16 + i) []) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem blkE5493_3 : (List.range 8).map (fun i => (roundShift (headMatW H5493 0 NE5493 lamE5493 WBE5493) NE5493 R5493).getD (24 + i) [])
    = (List.range 8).map (fun i => BE5493.getD (24 + i) []) := by
  decide +kernel

theorem matE5493 : roundShift (headMatW H5493 0 NE5493 lamE5493 WBE5493) NE5493 R5493 = BE5493 :=
  list_eq_of_getD [] (roundShift_length _ _ _) (by decide +kernel)
    (rows_of_four_blocks (f := fun j => (roundShift (headMatW H5493 0 NE5493 lamE5493 WBE5493) NE5493 R5493).getD j [])
      (g := fun j => BE5493.getD j []) blkE5493_0 blkE5493_1 blkE5493_2 blkE5493_3)

end Hodge1
