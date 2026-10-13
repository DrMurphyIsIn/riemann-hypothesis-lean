/-
  KWin2_Cert920N -- NEGATIVE CONTROL at L = 9/20 (kernel evaluation; rvm_bridge island,
  2026-09-24): at lam = 5.2e-6, above the even head eigenvalue 5.18e-6, the same pipeline returns
  `false` (a pivot of the exact LDL^T is negative), so certE920 is a statement about the actual
  margin of the comb-bearing form, not a vacuous checker.  conjecture1_proved = False.  No `sorry`.
-/
import KWin2_Par920

namespace KWin2
open KWin

theorem certE920_negative_control : psdCert (headMat P920 0 22 (52 / 10 ^ 7)) 22 = false := by
  decide +kernel

end KWin2
