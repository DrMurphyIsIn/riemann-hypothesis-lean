/-
  Hodge1_Ldl5493E -- the exact LDL^T step of Hodge1_Cert5493E (HODGE-1 Phase 1b-B): KWin's checker
  `psdCert` on the literal rounded matrix, in its own module (its kernel evaluation is the largest single
  step, about 10 GB macOS RSS including the import baseline), and `psdCertR_headMatP_eq` (proved) turns
  the result into the statement about the monolithic checker on `headMatP`.
  conjecture1_proved = False.  No `sorry`.
-/
import Hodge1_Cert5493E

namespace Hodge1
open KWin KWin2

theorem ldlE5493 : psdCert BE5493 NE5493 = true := by decide +kernel

/-- The even head matrix of the direct pole-free certificate is PSD. -/
theorem certE5493 : HeadPSD (headMatP H5493 0 NE5493 lamE5493 eta5493 D5493) NE5493 :=
  headPSD_of_psdCertR ((psdCertR_headMatP_eq H5493 rfl 0 NE5493 lamE5493 eta5493 D5493 R5493 rowsE5493 rowsE5493_ok
    WBE5493 wbE5493 BE5493 matE5493).trans ldlE5493)

end Hodge1
