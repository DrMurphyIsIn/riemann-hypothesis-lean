/-
  Hodge1_Cert45E -- kernel evaluations of the HODGE-1 checkers at l = 9/20: the structural checks and
  the EVEN sector (2026-10-12).

  Every theorem is `decide +kernel`: the Lean kernel reduces the Boolean checker in exact rational
  arithmetic; no compiled evaluation is trusted.  Each check is its own declaration (peak memory is set
  by the largest single one).  The head certificate is the rounded LDL^T certificate psdCertR at
  R = 40 (KWin2_Round) of the strip head matrix (Psi minorant, penalty pc = 1000, strip block with the
  leakage term at eta = 2).
  NEGATIVE CONTROLS: the same pipeline returns `false` at lam = 19/500 (above the even head eigenvalue
  0.037848) and with the strip weight w2up * 13/10 (head eigenvalue -0.0366).
  conjecture1_proved = False.  No `sorry`.
-/
import Hodge1_Par45

namespace Hodge1
open KWin KWin2

theorem par45 : parCheck P45 = true := by decide +kernel
theorem brk45 : brkCheck P45 = true := by decide +kernel
theorem piece45 : pieceCheck P45 = true := by decide +kernel
theorem min45 : minCheck P45 = true := by decide +kernel
theorem comb45 : combCheck P45 = true := by decide +kernel

theorem tailE45 : tailCondP H45 0 NE45 lamE45 etaE45 = true := by decide +kernel
theorem ginvE45 : ginvCheck P45 0 NE45 = true := by decide +kernel

/-- The even-sector head certificate (N = 16, lam = 33/1000, eta = 2). -/
theorem certE45 : psdCertR (headMatP H45 0 NE45 lamE45 etaE45 DE45) NE45 R45 = true := by
  decide +kernel

/-- NEGATIVE CONTROL: above the head eigenvalue 0.037848 the even certificate fails. -/
theorem certE45_negative_control_lam :
    psdCertR (headMatP H45 0 NE45 (19 / 500) etaE45 DE45) NE45 R45 = false := by
  decide +kernel

/-- NEGATIVE CONTROL: with the strip weight 1.3 w2 (above the even reach c*/w2 = 1.25) it fails. -/
theorem certE45_negative_control_w2 :
    psdCertR (headMatP H45x13 0 NE45 lamE45 etaE45 DE45) NE45 R45 = false := by
  decide +kernel

end Hodge1
