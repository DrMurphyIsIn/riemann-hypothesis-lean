/-
  ArchS9_CertRes -- residual certificate for the completeness theorem of stage S9 (2026-10-11).
  rhoQ (from telperion/research/arch_rung/s9/gen_s9_res.py) bounds sup_[0,1] |T psi_n - theta_n psi_n|
  through  gamma * Σ_m |theta_m| Σ_k |Bq m k| + zeta1 (1 + gamma);  and rhoQ² < w0q n² (1 - gamma)
  for every window n ≤ 12.  `decide +kernel`.  conjecture1_proved = False.  No `sorry`.
-/
import ArchS9_Data

namespace ArchS9.Data

set_option maxRecDepth 100000

def rhoQ : ℚ := 21 / 31250000000000000000000000000000000000000000
def Psi1Q (m : ℕ) : ℚ := ∑ k ∈ Finset.range Jd, |Bq m k|
def resOK : Bool :=
  decide (gamQ * (∑ m ∈ Finset.range Jd, |thq m| * Psi1Q m) + zeta1Q * (1 + gamQ) ≤ rhoQ) &&
  ((List.range (NCw + 1)).all fun n => decide (rhoQ ^ 2 < w0q n ^ 2 * (1 - gamQ)))

theorem res_ok : resOK = true := by decide +kernel

end ArchS9.Data
