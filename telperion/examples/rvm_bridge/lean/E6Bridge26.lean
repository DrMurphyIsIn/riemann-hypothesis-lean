/-  E6Bridge26 -- ASSEMBLY (2026-09-21): the Bombieri-Lagarias explicit formula on Li's test class
    (the rh node RH_bl_explicit_formula, B7) modulo the SINGLE remaining obligation StripDerivBound.

    Inputs, all kernel-checked on this island:
      * RvMBridge23.local_count_sum          (LocalCountSum, E6Bridge23)
      * RvMBridge25.noRealZeroInUnitInterval  (no real zero of zeta in (0,1), E6Bridge25)
      * RvMBridge25.liValue_of_two / bl_explicit_formula_of_two  (E6Bridge25, on top of the
        E6Bridge19 Taylor bookkeeping and the E6Bridge18/20/21/22 partial-fraction chain)

    NOT a proof of anything about RH.  conjecture1_proved = False. -/
import E6Bridge23
import E6Bridge25

open Filter Topology

namespace RvMBridge26

/-- The Bombieri-Lagarias value identity, modulo the strip derivative bound alone. -/
theorem liValue_of_strip (h2 : RvMBridge22.StripDerivBound) (n : ℕ) (hn : 0 < n) :
    RvMBridge15.LiValue n :=
  RvMBridge25.liValue_of_two RvMBridge23.local_count_sum h2 n hn

/-- The rh node RH_bl_explicit_formula (B7), modulo the strip derivative bound alone. -/
theorem bl_explicit_formula_of_strip (h2 : RvMBridge22.StripDerivBound) (n : ℕ) (hn : 0 < n) :
    Tendsto (RvMBridge15.BombieriLagarias.liZeroSum n) atTop
      (𝓝 (RvMBridge15.BombieriLagarias.archSide n + RvMBridge15.BombieriLagarias.finiteSide n)) :=
  RvMBridge25.bl_explicit_formula_of_two RvMBridge23.local_count_sum h2 n hn

end RvMBridge26
