/-
  ArchS11_Cert -- kernel evaluation of S11 certificate checkers (rounding of chiPoly, Legendre orthogonality, test vectors).
  `decide +kernel` only: the Lean kernel reduces each Boolean checker in exact rational arithmetic.
  conjecture1_proved = False.  No `sorry`.
-/
import ArchS11_Data

namespace ArchS11.Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem roundA_ok : roundOK EA aA dRA = true := by decide +kernel
theorem roundH_ok : roundOK EH aH dRH = true := by decide +kernel
theorem roundL_ok : roundOK EL aL dRL = true := by decide +kernel
theorem ortho_ok : orthoOK = true := by decide +kernel
theorem okT1lo_ok : okT1lo = true := by decide +kernel
theorem okToplo_ok : okToplo = true := by decide +kernel

end ArchS11.Data
