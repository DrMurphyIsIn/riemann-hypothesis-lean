/-  E6Bridge27 -- THE UNCONDITIONAL ASSEMBLY (2026-09-21).

    Every named obligation of the constant-free partial-fraction route is now a theorem on this
    island: LocalCountSum (E6Bridge23), StripDerivBound (E6Bridge24), NoRealZeroInUnitInterval
    (E6Bridge25).  Hence, unconditionally:
      * xi_logDeriv_deriv_eq : the derivative partial fraction of xi'/xi,
          (log xi)''(s) = -Sum_rho m(rho)/(s - rho)^2 for every s that is not a nontrivial zero,
        obtained WITHOUT the Hadamard product;
      * liValue : the Bombieri-Lagarias value identity for every n >= 1;
      * bl_explicit_formula : the rh registry node RH_bl_explicit_formula (B7), statement VERBATIM.

    NOT a proof of anything about RH: these are identities about the zeros and the primes,
    valid whether or not RH holds.  conjecture1_proved = False. -/
import E6Bridge23
import E6Bridge24
import E6Bridge25

open Filter Topology RvMBridge15

namespace RvMBridge27

/-- The derivative partial fraction of xi'/xi, unconditional. -/
theorem xi_logDeriv_deriv_eq : RvMBridge18.XiLogDerivDerivEq :=
  RvMBridge24.xiLogDerivDerivEq_of_localCount RvMBridge23.local_count_sum

/-- The Bombieri-Lagarias value identity, unconditional. -/
theorem liValue (n : ℕ) (hn : 0 < n) : LiValue n :=
  RvMBridge25.liValue_of_two RvMBridge23.local_count_sum RvMBridge24.stripDerivBound n hn

/-- The rh node RH_bl_explicit_formula (B7), statement verbatim, unconditional. -/
theorem bl_explicit_formula (n : ℕ) (hn : 0 < n) :
    Tendsto (BombieriLagarias.liZeroSum n) atTop
      (𝓝 (BombieriLagarias.archSide n + BombieriLagarias.finiteSide n)) :=
  RvMBridge25.bl_explicit_formula_of_two RvMBridge23.local_count_sum RvMBridge24.stripDerivBound n hn

end RvMBridge27
