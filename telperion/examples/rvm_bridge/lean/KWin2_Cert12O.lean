/-
  KWin2_Cert12O -- the odd-sector head certificate at L = 1/2 (kernel evaluation, rounded checker
  psdCertR at 10^-70; rvm_bridge island, 2026-09-24).  conjecture1_proved = False.  No `sorry`.
-/
import KWin2_Par12
import KWin2_Round

namespace KWin2
open KWin

/-- The odd-sector head certificate at L = 1/2 (N = 29, lam = 1e-4, rounding 10^-70). -/
theorem certO12 : psdCertR (headMat P12 1 29 lamO12) 29 70 = true := by decide +kernel

end KWin2
