/-  AxiomGuardLeakage.lean -- PROGRAM MIRRORMERE, ROUTE A item A2b kernel-axiom guard.

    NOT a `lean_lib`; run explicitly with

        lake env lean AxiomGuardLeakage.lean

    HAND-WRITTEN (not emitted): the guard must be an independent statement of what
    the island claims, so that a drifting emitter cannot silently drop a theorem
    from its own guard list.

    Prints the axiom set of every theorem of the hand-written `LeakageDictionary.lean`,
    of the emitted `LeakageInstances.lean`, and of both node declarations in
    `LeakageNode.lean` (48 declarations in all).  Expected on ALL of them:
    {propext, Classical.choice, Quot.sound} -- no sorryAx, no ofReduceBool, no
    Lean.ofReduceNat.

    conjecture1_proved = False (NOT a proof of RH).
-/
import LeakageDictionary
import LeakageInstances
import LeakageNode

open Quasicrystal

/-! ### THE REGISTRY NODE (MM_leakage_composite_zero) -/
#print axioms Quasicrystal.leakage_composite_zero

/-! ### The registry GATE MIRROR of the node (2026-09-22): the statement module's
    four inlined definitions and its theorem, restated CHARACTER FOR CHARACTER in
    `namespace MMLeakageStatement` (LeakageNode.lean) and discharged by the island
    theorem above through delta-definitional unfolding.  This is the declaration
    whose text the grant gate matches; same expected axiom set. -/
#print axioms MMLeakageStatement.leakage_composite_zero

/-! ### The trivial direction, quarantined

    `vonMangoldt_support_is_definitional` is the `rfl`-grade half the roadmap
    flagged as a trap (`ArithmeticFunction.vonMangoldt_eq_zero_iff` unfolds the
    defining `if IsPrimePow n then ... else 0`).  It is guarded here so the axiom
    list is complete, NOT because it carries content. -/
#print axioms Quasicrystal.vonMangoldt_support_is_definitional

/-! ### The content: the log-derivative coefficient functional -/
#print axioms Quasicrystal.logDerivCoeff_peel
#print axioms Quasicrystal.logDerivCoeff_unique
#print axioms Quasicrystal.logDerivCoeffOf_spec
#print axioms Quasicrystal.exists_logDerivCoeff
#print axioms Quasicrystal.vonMangoldt_mul_isLogDerivCoeff
#print axioms Quasicrystal.logDerivCoeff_eq_vonMangoldt_mul

/-! ### The dictionary and its contrapositive instrument -/
#print axioms Quasicrystal.composite_bragg_amplitude_zero
#print axioms Quasicrystal.composite_braggAmplitude_zero
#print axioms Quasicrystal.not_completelyMultiplicative_of_composite_leak

/-! ### Positive control: the completely-multiplicative (zeta) fiber -/
#print axioms Quasicrystal.zetaAmp_completelyMultiplicative
#print axioms Quasicrystal.zetaAmp_logDerivCoeff
#print axioms Quasicrystal.zeta_composite_amplitude_zero
#print axioms Quasicrystal.zeta_prime_amplitude_ne_zero
#print axioms Quasicrystal.exists_nondegenerate_cm_logDerivCoeff

/-! ### Constants consumed by the certified instances -/
#print axioms Quasicrystal.sqrt_five_bounds
#print axioms Quasicrystal.sqrt_inner_bounds
#print axioms Quasicrystal.dhKappa_gt
#print axioms Quasicrystal.dhKappa_lt
#print axioms Quasicrystal.dhKappa_bounds
#print axioms Quasicrystal.log_three_halves_bounds
#print axioms Quasicrystal.log_two_bounds
#print axioms Quasicrystal.log_three_bounds
#print axioms Quasicrystal.log_six_bounds

/-! ### Emitted instance: chi_5 mod 5 -- the COMPLETELY MULTIPLICATIVE positive
    control.  The re-derived coefficient row cancels, certifying `b 6 = 0`. -/
#print axioms LeakageInstances.leak_chi5_amp_1
#print axioms LeakageInstances.leak_chi5_amp_2
#print axioms LeakageInstances.leak_chi5_amp_3
#print axioms LeakageInstances.leak_chi5_amp_6
#print axioms LeakageInstances.leak_chi5_b_1
#print axioms LeakageInstances.leak_chi5_b_2
#print axioms LeakageInstances.leak_chi5_b_3
#print axioms LeakageInstances.leak_chi5_b_6
#print axioms LeakageInstances.leak_chi5_composite_vanishes

/-! ### Emitted instance: Davenport-Heilbronn -- the NEGATIVE control.  The
    re-derived row LEAKS at the composite frequency `log 6`, DH is refused
    complete multiplicativity, and the hypothesis-free dictionary is refuted. -/
#print axioms LeakageInstances.leak_dh_amp_1
#print axioms LeakageInstances.leak_dh_amp_2
#print axioms LeakageInstances.leak_dh_amp_3
#print axioms LeakageInstances.leak_dh_amp_6
#print axioms LeakageInstances.leak_dh_b_1
#print axioms LeakageInstances.leak_dh_b_2
#print axioms LeakageInstances.leak_dh_b_3
#print axioms LeakageInstances.leak_dh_b_6
#print axioms LeakageInstances.leak_dh_composite_leak_pos
#print axioms LeakageInstances.leak_dh_not_completelyMultiplicative
#print axioms LeakageInstances.leak_dh_enclosure
#print axioms LeakageInstances.leak_dh_leak_exists
#print axioms LeakageInstances.leak_dh_multiplicativity_is_necessary
