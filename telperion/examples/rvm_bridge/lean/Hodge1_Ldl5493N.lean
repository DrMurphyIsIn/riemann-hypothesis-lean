/-
  Hodge1_Ldl5493N -- the exact LDL^T step of Hodge1_Cert5493N (HODGE-1 Phase 1b-B): KWin's checker
  `psdCert` on the literal rounded matrix, in its own module (its kernel evaluation is the largest single
  step, about 10 GB macOS RSS including the import baseline), and `psdCertR_headMatP_eq` (proved) turns
  the result into the statement about the monolithic checker on `headMatP`.
  conjecture1_proved = False.  No `sorry`.
-/
import Hodge1_Cert5493N

namespace Hodge1
open KWin KWin2

theorem ldlN5493 : psdCert BN5493 NE5493 = false := by decide +kernel

/-- NEGATIVE CONTROL on the monolithic pipeline: `psdCertR (headMatP ...) = false`. -/
theorem certE5493_negative_control_lam :
    psdCertR (headMatP H5493 0 NE5493 (631 / 10 ^ 6) eta5493 D5493) NE5493 R5493 = false :=
  (psdCertR_headMatP_eq H5493 rfl 0 NE5493 (631 / 10 ^ 6) eta5493 D5493 R5493 rowsE5493 rowsE5493_ok
    WBE5493 wbE5493 BN5493 matN5493).trans ldlN5493

end Hodge1
