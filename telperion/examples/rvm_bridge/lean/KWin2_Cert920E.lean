/-
  KWin2_Cert920E -- the even-sector head certificate at L = 9/20 (kernel evaluation; rvm_bridge
  island, 2026-09-24).  `decide +kernel`: the kernel rebuilds the comb-bearing symbol minorant, its
  moments, the 22 x 22 head matrix and its exact LDL^T factorisation.  conjecture1_proved = False.
  No `sorry`.
-/
import KWin2_Par920

namespace KWin2
open KWin

/-- The even-sector head certificate at L = 9/20 (N = 22, lam = 5e-6). -/
theorem certE920 : psdCert (headMat P920 0 22 lamE920) 22 = true := by decide +kernel

end KWin2
