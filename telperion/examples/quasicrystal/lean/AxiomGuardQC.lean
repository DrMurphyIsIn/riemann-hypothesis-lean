/-  AxiomGuardQC.lean -- PROGRAM MIRRORMERE QC-1 kernel-axiom guard.

    NOT a `lean_lib`; run explicitly with

        lake env lean AxiomGuardQC.lean

    Prints the axiom sets of every completed QC-1 headline theorem.  Expected on
    all: {propext, Classical.choice, Quot.sound} -- no sorryAx, no ofReduceBool.

    conjecture1_proved = False (NOT a proof of RH).
-/
import LeeYangCore
import KSConstruction
import BoundaryLemmas
import TwoFreqRigidity
import RationalFreqReduction
import InvolutionDictionary
import TorusSectionLadder
import OfflineDiscs
import OfflineDiscsInstances
import EulerFactorOffline
import SelfInversiveOfflineInstances
import EulerFactorSectionOffline
import SatakeDegreeTwo
import DedekindQuadratic
import LemmaO
import LemmaOWitnesses

open Quasicrystal

/-! ### increment (i) -- LeeYangCore exponential-sum bridge -/
#print axioms Quasicrystal.norm_exp_arg
#print axioms Quasicrystal.exp_arg_ne_zero
#print axioms Quasicrystal.expPoly_root_iff_eval_zero
#print axioms Quasicrystal.expPoly_root_on_circle
#print axioms Quasicrystal.leeYang_root_norm_one

/-! ### increment (ii) -- KSConstruction crystalline structure + Poisson -/
#print axioms Quasicrystal.preimage_eq_latticeAP
#print axioms Quasicrystal.mem_zeroSet_iff
#print axioms Quasicrystal.latticeAP_mem
#print axioms Quasicrystal.poisson_shifted_lattice

/-! ### increment (iv) -- BoundaryLemmas "where zeta escapes" -/
#print axioms Quasicrystal.not_uniformlyDiscrete_of_dense
#print axioms Quasicrystal.two_pow_ne_three_pow
#print axioms Quasicrystal.log_two_three_incommensurable
#print axioms Quasicrystal.log_two_three_incommensurable_int
#print axioms Quasicrystal.primeLogSpectrum_dense
#print axioms Quasicrystal.primeLogSpectrum_not_uniformlyDiscrete
#print axioms Quasicrystal.not_uniformlyDiscrete_of_gaps_to_zero
#print axioms Quasicrystal.exists_close_of_card_gt
#print axioms Quasicrystal.zeta_ordinates_not_uniformlyDiscrete

/-! ### increment (iv) W2c -- the N(T) brick: discharging the counting hypothesis -/
#print axioms Quasicrystal.exists_close_of_gap_lt
#print axioms Quasicrystal.exists_gap_le_of_window
#print axioms Quasicrystal.windowedDensity_of_unboundedMeanDensity
#print axioms Quasicrystal.not_uniformlyDiscrete_of_windowedDensity
#print axioms Quasicrystal.zeta_ordinates_not_uniformlyDiscrete_of_unbounded_density

/-! ### handoff K1 -- TwoFreqRigidity (Theorem A) -/
#print axioms Quasicrystal.twoFreq_eq_zero_iff
#print axioms Quasicrystal.twoFreq_zero_norm
#print axioms Quasicrystal.twoFreq_realRooted_iff

/-! ### handoff K2 -- RationalFreqReduction (Theorem B bridge) -/
#print axioms Quasicrystal.norm_exp_omega
#print axioms Quasicrystal.im_zero_iff_norm_one
#print axioms Quasicrystal.ratFreq_eq_zero_iff
#print axioms Quasicrystal.ratFreq_realRooted_of_leeYangCircle
#print axioms Quasicrystal.leeYangCircle_reached_of_realRooted

/-! ### Wave-2 handoff W2a -- InvolutionDictionary (functional equation ⟺
    self-inversive symmetry) -/
#print axioms Quasicrystal.intertwiner
#print axioms Quasicrystal.fixed_locus_correspondence
#print axioms Quasicrystal.selfInversive_zeros_symmetric
#print axioms Quasicrystal.inv_conj_exp_real
#print axioms Quasicrystal.selfInversive_circle_identity
#print axioms Quasicrystal.selfInversive_iff_hardyZ_real
#print axioms Quasicrystal.binomialPoly_eval
#print axioms Quasicrystal.binomialPoly_natDegree
#print axioms Quasicrystal.twoFreq_dictionary
#print axioms Quasicrystal.selfInversive_binomial_realRooted
#print axioms Quasicrystal.fixed_locus_dichotomy

/-! ### MIRRORMERE torus-section ladder T1 -- TorusSectionLadder (2026-09-18):
    registry nodes MM_torus_section_dictionary + MM_torus_section_n2_rigidity.
    Vocabulary bridges over TwoFreqRigidity (simp-grade; recorded, not counted). -/
#print axioms Quasicrystal.expSum_eq_linearTorusForm_torusOrbit
#print axioms Quasicrystal.torus_section_dictionary
#print axioms Quasicrystal.torus_section_n2_rigidity
/-! ### MIRRORMERE E4b -- OfflineDiscs (registry node MM_offline_disjoint_discs,
    QC_RECURRENCE section 4.3 isolation lemma) -/
#print axioms Quasicrystal.exists_pos_lower_bound_of_finset
#print axioms Quasicrystal.abs_re_sub_le_dist
#print axioms Quasicrystal.offline_disjoint_discs

/-! ### MIRRORMERE E4b instances -- OfflineDiscsInstances (emitted by the Telperion
    `disjoint_discs` kind; the points are INPUT, not a claim about zeta) -/
#print axioms OfflineDiscsInstances.offline_discs_online_pair
#print axioms OfflineDiscsInstances.offline_discs_offline_bank
/-! ### torus-section ladder T2 -- TorusSectionLadder, THE NEGATIVE CONTROL
    (registry node MM_euler_factor_section_offline + explicit off-line witness) -/
#print axioms TorusSectionLadder.euler_factor_coeff_ne_zero
#print axioms TorusSectionLadder.euler_factor_freq_ne
#print axioms TorusSectionLadder.euler_factor_section_offline
#print axioms TorusSectionLadder.euler_factor_section_witness
#print axioms TorusSectionLadder.euler_factor_section_witness_im
#print axioms TorusSectionLadder.euler_factor_section_offline_of_witness

/-! ### torus-section ladder T2 -- the emitter dogfood (selfinversive_rigidity mode="offline"):
    the p = 2, 3, 5 Euler-factor sections, refuted from the exact normSq inequality -/
#print axioms SelfInversiveOfflineInstances.euler_factor_p2_offline
#print axioms SelfInversiveOfflineInstances.euler_factor_p2_offline_witness
#print axioms SelfInversiveOfflineInstances.euler_factor_p2_offline_of_witness
#print axioms SelfInversiveOfflineInstances.euler_factor_p2_offline_node
#print axioms SelfInversiveOfflineInstances.euler_factor_p3_offline
#print axioms SelfInversiveOfflineInstances.euler_factor_p3_offline_witness
#print axioms SelfInversiveOfflineInstances.euler_factor_p3_offline_of_witness
#print axioms SelfInversiveOfflineInstances.euler_factor_p3_offline_node
#print axioms SelfInversiveOfflineInstances.euler_factor_p5_offline
#print axioms SelfInversiveOfflineInstances.euler_factor_p5_offline_witness
#print axioms SelfInversiveOfflineInstances.euler_factor_p5_offline_of_witness
#print axioms SelfInversiveOfflineInstances.euler_factor_p5_offline_node

/-! ### increment (iii) -- CharacterizationStatements

    DELIBERATELY NOT GUARDED HERE.  `CharacterizationStatements.lean` contains only
    `def ... : Prop` STATEMENTS of the published 1-D FQ characterization
    (Kurasov-Sarnak / Olevskii-Ulanovskii / Alon-Cohen-Vinzant Cor 1.4 /
    Lev-Olevskii / AKKV) and the OPEN program conjectures.  Nothing there is a
    theorem, so there are no axioms to print.  It builds green (no sorry) and is
    a defaultTarget; listing its `def`s under `#print axioms` would be a category
    error (they are Props, not proofs). -/

-- MM_euler_factor_section_offline's proof-link artifact (emitter-generated,
-- drift-gated by examples/twofreq_offline/generate.py --check).
#print axioms EulerFactorSectionOffline.euler_factor_section_offline
#print axioms EulerFactorSectionOffline.euler_factor_section_offline_offline_zero
#print axioms EulerFactorSectionOffline.euler_factor_section_offline_displacement
#print axioms EulerFactorSectionOffline.euler_factor_section_offline_p3
#print axioms EulerFactorSectionOffline.euler_factor_section_offline_p3_offline_zero
#print axioms EulerFactorSectionOffline.euler_factor_section_offline_p3_displacement
#print axioms EulerFactorSectionOffline.euler_factor_section_offline_p5
#print axioms EulerFactorSectionOffline.euler_factor_section_offline_p5_offline_zero

/-! ### ROUTE A milestone A1b (2026-09-19) -- SatakeDegreeTwo, THE FALSIFICATION.

    Registry node MM_satake_degree_two_rejects_delta.  These theorems PROVE THE
    ISLAND'S OWN CLAUSE (B-mult-twisted) FALSE: it rejects `L(s, Delta)`, a
    degree-2 Selberg element tempered by Deligne's theorem.  The rejection is
    unconditional; Ramanujan-Petersson is a NAMED input used only to certify that
    the rejected object belongs to the class, and no theorem here consumes it.

    `tau` is re-derived in-kernel from Delta = q * prod (1-q^n)^24; the Hecke and
    multiplicativity cross-checks below are the anti-phantom refusal.

    conjecture1_proved = False. -/
#print axioms SatakeDegreeTwo.scalarGenerated_powerSum_iff
#print axioms SatakeDegreeTwo.deg1_scalarGenerated
#print axioms SatakeDegreeTwo.zeta_layer_scalarGenerated
#print axioms SatakeDegreeTwo.lchi_layer_scalarGenerated
#print axioms SatakeDegreeTwo.unitary_deg2_not_scalarGenerated
#print axioms SatakeDegreeTwo.satake_pair_exists
#print axioms SatakeDegreeTwo.deg2_amplitude_defect
#print axioms SatakeDegreeTwo.tau_one
#print axioms SatakeDegreeTwo.tau_two
#print axioms SatakeDegreeTwo.tau_three
#print axioms SatakeDegreeTwo.tau_four
#print axioms SatakeDegreeTwo.tau_six
#print axioms SatakeDegreeTwo.tau_hecke_p2
#print axioms SatakeDegreeTwo.tau_mult_six
#print axioms SatakeDegreeTwo.delta_satakeDet_two
#print axioms SatakeDegreeTwo.delta_twist_not_unimodular
#print axioms SatakeDegreeTwo.delta_amplitude_defect_two
#print axioms SatakeDegreeTwo.delta_rejected_by_B_mult_twisted
#print axioms SatakeDegreeTwo.delta_rejected_nonvacuous

/-! ### Dedekind product-closure control (2026-09-23) -- DedekindQuadratic.
zeta_K = zeta * L(chi_-20) is rejected by (B-mult-twisted) while both factors pass.
Expected: every line prints exactly [propext, Classical.choice, Quot.sound] (the two
`norm_num` Jacobi-symbol evaluations may print a subset).  conjecture1_proved = False. -/
#print axioms SatakeDegreeTwo.dedekind_split_rejected
#print axioms SatakeDegreeTwo.dedekind_inert_rejected
#print axioms SatakeDegreeTwo.dedekind_ramified_admitted
#print axioms SatakeDegreeTwo.dedekind_inert_layer_odd
#print axioms SatakeDegreeTwo.dedekind_inert_layer_even
#print axioms SatakeDegreeTwo.scalarGenerated_congr
#print axioms SatakeDegreeTwo.layer_of_product
#print axioms SatakeDegreeTwo.scalarGenerated_not_closed_under_product
#print axioms SatakeDegreeTwo.chi_m20_three
#print axioms SatakeDegreeTwo.chi_m20_eleven
#print axioms SatakeDegreeTwo.dedekind_at_three_rejected
#print axioms SatakeDegreeTwo.dedekind_at_eleven_rejected

/-! ### LEMMA O (2026-09-25) -- LemmaO + LemmaOWitnesses.
The log-derivative coefficient functional `b` of an amplitude `a` (Mathlib
`ArithmeticFunction`, abstract completely additive weight) is supported on prime powers
IFF `a` is multiplicative; among multiplicative `a`, the prime-layer generation law
`b (p^k) = l p * a p ^ k` holds IFF `a` is completely multiplicative.  Instances at
`Real.log` over `ℝ` and `ℂ`.  Witnesses at `n = 6`: zeta (`b 6 = 0`), Davenport-Heilbronn
(`b 6 = (1 + κ²) log 6 > 0`, NOT multiplicative), Epstein `x² + 5y²` (`b 6 = 2 log 6`,
NOT multiplicative; representation numbers counted by `decide` on a box proved complete).
Kernel justification of zoo.py `check_multiplicativity`.  Expected: every line prints
exactly [propext, Classical.choice, Quot.sound] (the `decide`-proved lattice counts and
divisor sets may print a subset).  conjecture1_proved = False. -/
#print axioms LemmaO.IsCompletelyAdditive.map_one
#print axioms LemmaO.IsCompletelyAdditive.map_pow
#print axioms LemmaO.mul_apply_divisors
#print axioms LemmaO.IsLogDerivCoeff.sum
#print axioms LemmaO.IsLogDerivCoeff.peel
#print axioms LemmaO.IsLogDerivCoeff.one
#print axioms LemmaO.logDerivCoeff_unique
#print axioms LemmaO.logDerivCoeffOf_spec
#print axioms LemmaO.exists_logDerivCoeff
#print axioms LemmaO.sum_divisors_coprime_split
#print axioms LemmaO.exists_coprime_factorization
#print axioms LemmaO.primePow_support_of_isMultiplicative
#print axioms LemmaO.not_isPrimePow_mul_of_coprime
#print axioms LemmaO.isMultiplicative_of_primePow_support
#print axioms LemmaO.lemmaO
#print axioms LemmaO.not_isMultiplicative_of_composite_leak
#print axioms LemmaO.IsCompletelyMultiplicative.isMultiplicative
#print axioms LemmaO.IsCompletelyMultiplicative.map_pow
#print axioms LemmaO.IsLogDerivCoeff.primePow_sum
#print axioms LemmaO.generation_law_of_completelyMultiplicative
#print axioms LemmaO.completelyMultiplicative_of_generation_law
#print axioms LemmaO.generation_law_iff_completelyMultiplicative
#print axioms LemmaO.not_completelyMultiplicative_of_generation_law_fails
#print axioms LemmaO.logWeight_completelyAdditive
#print axioms LemmaO.logWeight_ne_zero
#print axioms LemmaO.logWeightC_completelyAdditive
#print axioms LemmaO.logWeightC_ne_zero
#print axioms LemmaO.lemmaO_real
#print axioms LemmaO.lemmaO_complex
#print axioms LemmaO.generation_law_iff_completelyMultiplicative_real
#print axioms LemmaO.generation_law_iff_completelyMultiplicative_complex
-- the n = 6 witnesses
#print axioms LemmaO.divisors_two
#print axioms LemmaO.divisors_three
#print axioms LemmaO.divisors_six
#print axioms LemmaO.six_not_isPrimePow
#print axioms LemmaO.b_two
#print axioms LemmaO.b_three
#print axioms LemmaO.b_six
#print axioms LemmaO.zeta_completelyMultiplicative
#print axioms LemmaO.zeta_logDerivCoeff
#print axioms LemmaO.zeta_b_six
#print axioms LemmaO.zeta_functional_eq_vonMangoldt
#print axioms LemmaO.zeta_generation_law
#print axioms LemmaO.dhAmp_one
#print axioms LemmaO.dhAmp_two
#print axioms LemmaO.dhAmp_three
#print axioms LemmaO.dhAmp_six
#print axioms LemmaO.dh_b_six
#print axioms LemmaO.dh_b_six_pos
#print axioms LemmaO.dhAmp_not_isMultiplicative
#print axioms LemmaO.dhAmp_not_isMultiplicative_uncond
#print axioms LemmaO.boxShift_injective
#print axioms LemmaO.rep5_eq_card
#print axioms LemmaO.rep5Set_sound
#print axioms LemmaO.rep5_box_complete
#print axioms LemmaO.rep5_one
#print axioms LemmaO.rep5_two
#print axioms LemmaO.rep5_three
#print axioms LemmaO.rep5_six
#print axioms LemmaO.epsteinAmp_one
#print axioms LemmaO.epsteinAmp_two
#print axioms LemmaO.epsteinAmp_three
#print axioms LemmaO.epsteinAmp_six
#print axioms LemmaO.epstein_b_six
#print axioms LemmaO.epstein_b_six_ne_zero
#print axioms LemmaO.epsteinAmp_not_isMultiplicative
#print axioms LemmaO.epsteinAmp_not_isMultiplicative_uncond
#print axioms LemmaO.epsteinAmp_not_isMultiplicative_direct
