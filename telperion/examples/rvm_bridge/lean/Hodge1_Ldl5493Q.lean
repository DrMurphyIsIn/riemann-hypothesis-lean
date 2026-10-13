/-
  Hodge1_Ldl5493Q -- the exact LDL^T step of Hodge1_Cert5493Q (HODGE-1 Phase 1b-B): KWin's checker
  `psdCert` on the literal rounded matrix, in its own module (its kernel evaluation is the largest single
  step, about 10 GB macOS RSS including the import baseline), and `psdCertR_headMatP_eq` (proved) turns
  the result into the statement about the monolithic checker on `headMatP`.
  conjecture1_proved = False.  No `sorry`.
-/
import Hodge1_Cert5493Q

namespace Hodge1
open KWin KWin2

theorem ldlQ5493 : psdCert BQ5493 NE5493 = false := by decide +kernel

/-- NEGATIVE CONTROL on the monolithic pipeline: `psdCertR (headMatP ...) = false`. -/
theorem certE5493_negative_control_q21 :
    psdCertR (headMatP H5493q21 0 NE5493 lamE5493 eta5493 D5493) NE5493 R5493 = false :=
  (psdCertR_headMatP_eq H5493q21 rfl 0 NE5493 lamE5493 eta5493 D5493 R5493 rowsE5493 (fun i hi => rowsE5493_ok i hi)
    WBQ5493 wbQ5493 BQ5493 matQ5493).trans ldlQ5493

end Hodge1
