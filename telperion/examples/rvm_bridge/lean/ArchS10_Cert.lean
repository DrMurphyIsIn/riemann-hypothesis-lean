/-
  ArchS10_Cert -- the kernel checks of stage S10 (certified kernel χ, 2026-10-11).
  Every Boolean check of ArchS10_Data, by `decide +kernel` (about 30 s of kernel time in total):
    round_ok   : |θ_n²/(1-θ_n²) hh_{n,l} - Dq n l| ≤ 1e-60 for n ≤ 12, l < 40 (hh exact, from S9's ψ_n)
    epsHead_ok : |Σ_{n≤12} θ_n²/(1-θ_n²) ψ_n(1)² - EQ| ≤ 1e-40
    head_ok    : the per-n perturbation constants errHq, errEq
    tail_ok    : the Bessel tail constants AQ, AdQ, A1Q, tauQ, tauE
    poly_ok    : the Taylor remainder deltaP of the polynomial and its size Pmax
    total_ok   : the totals dQtot, deltaE, deltaChi.
  conjecture1_proved = False.  No `sorry`.
-/
import ArchS10_Data

namespace ArchS10.Data

set_option maxRecDepth 100000

theorem round_ok : (List.range NH).all roundRowOK = true := by decide +kernel
theorem epsHead_ok : epsHeadOK = true := by decide +kernel
theorem head_ok : headOK = true := by decide +kernel
theorem tail_ok : tailOK = true := by decide +kernel
theorem poly_ok : polyOK = true := by decide +kernel
theorem total_ok : totalOK = true := by decide +kernel

end ArchS10.Data
