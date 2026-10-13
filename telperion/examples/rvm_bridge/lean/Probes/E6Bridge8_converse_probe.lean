/-
  Composition probe (2026-09-21): E6Bridge8.gaussian_approx (O1') plugged into E6Bridge7's capstone
  weil_positivity_implies_rh_of_approx (which carries O2 discharged).  Reports ONLY what the kernel
  prints; the statement is an implication (Weil positivity -> RiemannHypothesis), not RH.
  Run: cd telperion/examples/rvm_bridge/lean && lake env lean Probes/E6Bridge8_converse_probe.lean
-/
import E6Bridge7
import E6Bridge8

theorem probe_weil_positivity_implies_rh
    (hpos : ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g →
      0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re) :
    RiemannHypothesis :=
  RvMBridge7.weil_positivity_implies_rh_of_approx RvMBridge8.gaussian_approx hpos

#print axioms probe_weil_positivity_implies_rh
#print axioms RvMBridge7.weil_positivity_implies_rh_of_approx
