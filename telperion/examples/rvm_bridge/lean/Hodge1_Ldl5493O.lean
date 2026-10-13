/-
  Hodge1_Ldl5493O -- the exact LDL^T step of Hodge1_Cert5493O (HODGE-1 Phase 1b-B): KWin's checker
  `psdCert` on the literal rounded matrix, in its own module (its kernel evaluation is the largest single
  step, about 10 GB macOS RSS including the import baseline), and `psdCertR_headMatP_eq` (proved) turns
  the result into the statement about the monolithic checker on `headMatP`.
  conjecture1_proved = False.  No `sorry`.
-/
import Hodge1_Cert5493O

namespace Hodge1
open KWin KWin2

theorem ldlO5493 : psdCert BO5493 NO5493 = true := by decide +kernel

/-- The odd head matrix of the direct pole-free certificate is PSD. -/
theorem certO5493 : HeadPSD (headMatP H5493 1 NO5493 lamO5493 eta5493 D5493) NO5493 :=
  headPSD_of_psdCertR ((psdCertR_headMatP_eq H5493 rfl 1 NO5493 lamO5493 eta5493 D5493 R5493 rowsO5493 rowsO5493_ok
    WBO5493 wbO5493 BO5493 matO5493).trans ldlO5493)

end Hodge1
