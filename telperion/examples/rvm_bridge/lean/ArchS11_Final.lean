/-
  ArchS11_Final -- the clean rational bounds of stage S11, kernel-checked against the certificate
  constants (`decide +kernel`).  Each bound adds the S10 enclosure deltaChi and the rounding dR
  (times the interval length) to the certified Galerkin value.  conjecture1_proved = False.
-/
import ArchS11_Data

namespace ArchS11.Data

set_option maxHeartbeats 0

/-- The clean bounds.  `T1`: |I| = 1/2.  `Top`, `Gam`, `Lam2`, `Ovl`: |I| = log 2 (via H ≥ log 2,
the lower bound via lo ≤ log 2). -/
def finalOK : Bool :=
  decide (aA * lamT1 + (ArchS10.Data.deltaChi + dRA) * aA ≤ 95921 / 100000) &&
  decide (95920 / 100000 ≤ aA * lamT1lo - (ArchS10.Data.deltaChi + dRA) * aA) &&
  decide (aH * lamTop + (ArchS10.Data.deltaChi + dRH) * aH ≤ 10516 / 10000) &&
  decide (105156 / 100000 ≤ aL * lamToplo - (ArchS10.Data.deltaChi + dRL) * aL) &&
  decide (aH * lamGam + (ArchS10.Data.deltaChi + dRH) * aH ≤ 9995 / 10000) &&
  decide (aH * lamLam2 + (ArchS10.Data.deltaChi + dRH) * aH ≤ 6866 / 10000) &&
  decide (aH * lamOvl + (ArchS10.Data.deltaChi + dRH) * aH ≤ 103354 / 100000) &&
  decide (c0T1 = 0) && decide (c0Top = 0) && decide (c0Gam = -(58 / 1000) / aH) &&
  decide (c0Lam2 = -1 / aH) && decide (c0Ovl = -(2 / 100) / aH) &&
  decide (aA = 1 / 2) && decide (aH = 6931471808 / 10 ^ 10) && decide (aL = 6931471803 / 10 ^ 10) &&
  decide (0 ≤ dRA) && decide (0 ≤ dRH) && decide (0 ≤ dRL) && decide (0 ≤ ArchS10.Data.deltaChi) &&
  decide (EA.length ≤ 47) && decide (EH.length ≤ 47) && decide (EL.length ≤ 47)

theorem final_ok : finalOK = true := by decide +kernel

end ArchS11.Data
