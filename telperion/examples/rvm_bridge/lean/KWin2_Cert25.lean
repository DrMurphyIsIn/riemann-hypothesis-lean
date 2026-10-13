/-
  KWin2_Cert25 -- the kernel evaluations of the KWin2 checkers at L = 2/5 (rvm_bridge island,
  2026-09-24).

  Every theorem below is `decide +kernel`: the Lean kernel itself reduces the Boolean checker
  (exact rational arithmetic, GMP-accelerated `Nat`); no compiled-code evaluation is trusted.  The
  two head certificates are the expensive ones (about 40 s each): the kernel rebuilds the symbol
  minorant WITH the prime comb (the n = 2 term, degree-62 upper polynomial), its moments, the head
  matrix and its exact LDL^T factorisation, and verifies A = sum_s d_s v_s v_s^T entrywise.
  NEGATIVE CONTROL: at lam = 5e-5, above the even head eigenvalue 4.70e-5, the same pipeline
  returns `false` (a pivot of the exact LDL^T is negative), which the kernel also proves.  The
  rational halves of the real side conditions (log 2 series, sqrt 2 squares, exp Taylor bounds)
  are in KWin2_Window25.  conjecture1_proved = False.  No `sorry`.
-/
import KWin2_Par25

open Finset

namespace KWin2
open KWin

/-! ## A. Structural checks. -/

theorem par25 : parCheck P25 = true := by decide +kernel
theorem brk25 : brkCheck P25 = true := by decide +kernel
theorem piece25 : pieceCheck P25 = true := by decide +kernel
theorem min25 : minCheck P25 = true := by decide +kernel
theorem comb25 : combCheck P25 = true := by decide +kernel
theorem tailE25 : tailCond P25 0 16 lamE25 = true := by decide +kernel
theorem tailO25 : tailCond P25 1 14 lamO25 = true := by decide +kernel
theorem ginvE25 : ginvCheck P25 0 16 = true := by decide +kernel
theorem ginvO25 : ginvCheck P25 1 14 = true := by decide +kernel

/-! ## B. The head certificates. -/

/-- The even-sector head certificate (N = 16, lam = 45e-6). -/
theorem certE25 : psdCert (headMat P25 0 16 lamE25) 16 = true := by decide +kernel

/-- The odd-sector head certificate (N = 14, lam = 1e-3). -/
theorem certO25 : psdCert (headMat P25 1 14 lamO25) 14 = true := by decide +kernel

/-- NEGATIVE CONTROL: the even head matrix at `lam = 5e-5` is NOT certified, so `certE25` is a
statement about the actual margin 4.70e-5 of the comb-bearing form. -/
theorem certE25_negative_control : psdCert (headMat P25 0 16 (5 / 10 ^ 5)) 16 = false := by
  decide +kernel

end KWin2
