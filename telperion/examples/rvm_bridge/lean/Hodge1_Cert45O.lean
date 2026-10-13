/-
  Hodge1_Cert45O -- kernel evaluations of the HODGE-1 checkers at l = 9/20: the ODD sector
  (2026-10-12).  Same pipeline as Hodge1_Cert45E: psdCertR at R = 40 of the strip head matrix
  (penalty pc = 1000, strip block with the leakage term at eta = 3/2).
  NEGATIVE CONTROL: the same pipeline returns `false` at lam = 3547/10000, above the odd head
  eigenvalue 0.35451.
  conjecture1_proved = False.  No `sorry`.
-/
import Hodge1_Par45

namespace Hodge1
open KWin KWin2

theorem tailO45 : tailCondP H45 1 NO45 lamO45 etaO45 = true := by decide +kernel
theorem ginvO45 : ginvCheck P45 1 NO45 = true := by decide +kernel

/-- The odd-sector head certificate (N = 15, lam = 31/100, eta = 3/2). -/
theorem certO45 : psdCertR (headMatP H45 1 NO45 lamO45 etaO45 DO45) NO45 R45 = true := by
  decide +kernel

/-- NEGATIVE CONTROL: above the head eigenvalue 0.35451 the odd certificate fails. -/
theorem certO45_negative_control_lam :
    psdCertR (headMatP H45 1 NO45 (3547 / 10000) etaO45 DO45) NO45 R45 = false := by
  decide +kernel

end Hodge1
