/-
  KWin2_Cert920O -- the odd-sector head certificate at L = 9/20 (kernel evaluation; rvm_bridge
  island, 2026-09-24).  conjecture1_proved = False.  No `sorry`.
-/
import KWin2_Par920

namespace KWin2
open KWin

/-- The odd-sector head certificate at L = 9/20 (N = 19, lam = 1e-3). -/
theorem certO920 : psdCert (headMat P920 1 19 lamO920) 19 = true := by decide +kernel

end KWin2
