/-
  KWin_Cert -- the kernel evaluations of the KWin_Data checkers (rvm_bridge island, 2026-09-24).

  Every theorem below is `decide +kernel`: the Lean kernel itself reduces the Boolean checker
  (exact rational arithmetic, GMP-accelerated `Nat`); no compiled-code evaluation is trusted.
  The two head certificates are the expensive ones (tens of seconds each): they rebuild the
  symbol minorant, its moments, the head matrix and its exact LDL^T factorisation, and verify
  A = sum_s d_s v_s v_s^T entrywise.  The NEGATIVE CONTROL at the end shows the checker is not
  vacuous: at lam = 1/1000 (above the even head eigenvalue 9.24e-4) the same pipeline returns
  `false`, which the kernel also proves.  conjecture1_proved = False.  No `sorry`.
-/
import KWin_Data

namespace KWin

/-- The even-sector head certificate (N = 12, lam = 915e-6). -/
theorem cert_even : psdCert (headMat 0 12 lamE) 12 = true := by decide +kernel

/-- The odd-sector head certificate (N = 10, lam = 1/100). -/
theorem cert_odd : psdCert (headMat 1 10 lamO) 10 = true := by decide +kernel

theorem ginv_even : ginvCheck 0 12 = true := by decide +kernel

theorem ginv_odd : ginvCheck 1 10 = true := by decide +kernel

theorem piece_ok : pieceCheck = true := by decide +kernel

theorem tail_even : tailCond 0 12 lamE = true := by decide +kernel

theorem tail_odd : tailCond 1 10 lamO = true := by decide +kernel

/-- NEGATIVE CONTROL: the even-sector head matrix at `lam = 1/1000` is NOT certified (a pivot of its
exact LDL^T is negative), so `cert_even` is a statement about the actual margin 9.24e-4. -/
theorem cert_even_negative_control : psdCert (headMat 0 12 (1 / 1000)) 12 = false := by decide +kernel

end KWin
