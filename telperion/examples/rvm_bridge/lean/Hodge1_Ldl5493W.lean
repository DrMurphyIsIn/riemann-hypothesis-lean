/-
  Hodge1_Ldl5493W -- the exact LDL^T step of Hodge1_Cert5493W (HODGE-1 Phase 1b-B): KWin's checker
  `psdCert` on the literal rounded matrix, in its own module (its kernel evaluation is the largest single
  step, about 10 GB macOS RSS including the import baseline), and `psdCertR_headMatP_eq` (proved) turns
  the result into the statement about the monolithic checker on `headMatP`.
  conjecture1_proved = False.  No `sorry`.
-/
import Hodge1_Cert5493W

namespace Hodge1
open KWin KWin2

theorem ldlW5493 : psdCert BW5493 NE5493 = false := by decide +kernel

/-- NEGATIVE CONTROL on the monolithic pipeline: `psdCertR (headMatP ...) = false`. -/
theorem certE5493_negative_control_w105 :
    psdCertR (headMatP H5493w105 0 NE5493 lamE5493 eta5493 D5493) NE5493 R5493 = false :=
  (psdCertR_headMatP_eq H5493w105 rfl 0 NE5493 lamE5493 eta5493 D5493 R5493 rowsE5493 (fun i hi => rowsE5493_ok i hi)
    WBW5493 wbW5493 BW5493 matW5493).trans ldlW5493

end Hodge1
