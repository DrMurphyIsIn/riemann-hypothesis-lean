/-
  KWin2_Cert12N -- NEGATIVE CONTROL at L = 1/2 (kernel evaluation; rvm_bridge island, 2026-09-24):
  at lam = 4.6e-7, above the even head eigenvalue 4.50e-7, the same pipeline (rounded checker at
  10^-70) returns `false` (a pivot of the LDL^T is negative).  conjecture1_proved = False.
  No `sorry`.
-/
import KWin2_Par12
import KWin2_Round

namespace KWin2
open KWin

theorem certE12_negative_control : psdCertR (headMat P12 0 31 (46 / 10 ^ 8)) 31 70 = false := by
  decide +kernel

end KWin2
