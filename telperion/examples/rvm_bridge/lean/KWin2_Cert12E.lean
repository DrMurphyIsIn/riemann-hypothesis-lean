/-
  KWin2_Cert12E -- the even-sector head certificate at L = 1/2 (kernel evaluation; rvm_bridge
  island, 2026-09-24).  `decide +kernel`: the kernel rebuilds the comb-bearing symbol minorant on
  [0, 40], its moments and the exact 31 x 31 head matrix, floors it at 10^-70, shifts the diagonal
  by 31e-70 and runs the exact LDL^T checker (KWin2_Round.psdCertR).  conjecture1_proved = False.
  No `sorry`.
-/
import KWin2_Par12
import KWin2_Round

namespace KWin2
open KWin

/-- The even-sector head certificate at L = 1/2 (N = 31, lam = 4.2e-7, rounding 10^-70). -/
theorem certE12 : psdCertR (headMat P12 0 31 lamE12) 31 70 = true := by decide +kernel

end KWin2
