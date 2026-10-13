/-  E6Bridge9 -- the ASSEMBLY (2026-09-21): the Weil converse, unconditional, and the
    MIRRORMERE dictionary theorem.

    Inputs, all kernel-checked on this island:
      * RvMBridge5.rh_implies_weil_positivity      (forward half, E6Bridge5)
      * RvMBridge6.gaussianTransfer_of_approx       (O1 from O1', E6Bridge6)
      * RvMBridge7.weil_positivity_implies_rh_of_approx  (converse modulo O1', E6Bridge7; O2
        discharged there by RvMBridge7.gaussian_dominance)
      * RvMBridge8.gaussian_approx                  (O1' discharged, E6Bridge8)

    The three theorems below are the registry statements of MM_gaussian_transfer,
    MM_weil_positivity_implies_rh and MM_zeta_comb_membership_iff_rh, VERBATIM (the grant gate
    matches by normalized text containment).

    What this is NOT: a proof of RH.  zeta_comb_membership_iff_rh says the MIRRORMERE goal
    statement (Weil positivity of the E8 primes-side functional on Hermitian autocorrelations)
    is EQUIVALENT to Mathlib's RiemannHypothesis; it says nothing about whether either side
    holds.  The goal node stays draft and RH-hard, now for a proved reason.
    conjecture1_proved = False. -/
import E6Bridge5
import E6Bridge6
import E6Bridge7
import E6Bridge8

open WeilExplicit

namespace RvMBridge9

/-- O1 (GaussianTransfer), unconditional: O1' discharged in E6Bridge8, transferred by Tannery. -/
theorem gaussian_transfer : RvMBridge6.GaussianTransfer :=
  RvMBridge6.gaussianTransfer_of_approx RvMBridge8.gaussian_approx

/-- Weil's criterion, converse half, UNCONDITIONAL on this island: Weil positivity on Hermitian
autocorrelations over the E8 test class implies Mathlib's RiemannHypothesis. -/
theorem weil_positivity_implies_rh (hpos : ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g → 0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re) : RiemannHypothesis :=
  RvMBridge7.weil_positivity_implies_rh_of_approx RvMBridge8.gaussian_approx hpos

/-- The dictionary theorem: the MIRRORMERE goal statement is equivalent to RH. -/
theorem zeta_comb_membership_iff_rh : (∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g → 0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re) ↔ RiemannHypothesis :=
  ⟨weil_positivity_implies_rh, RvMBridge5.rh_implies_weil_positivity⟩

/-- The falsifiability face, now HYPOTHESIS-FREE: a certified strictly negative Weil pairing of
some Hermitian autocorrelation refutes RH outright.  The weil_form_enclosure emitter's
`weil_negative_refutes_rh` carries the forward half as an undischarged hypothesis `hpos`
(different toolchain island); here it is consumed as the theorem RvMBridge5.rh_implies_weil_positivity.
Not expected to fire; recorded so the ladder is falsifiable rather than confirmation-only. -/
theorem weil_negative_refutes_rh (g : ℝ → ℂ) (hg : WeilExplicit.IsWeilTest g)
    (hneg : (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re < 0) : ¬ RiemannHypothesis :=
  fun h => absurd (RvMBridge5.rh_implies_weil_positivity h g hg) (not_le.mpr hneg)

end RvMBridge9
