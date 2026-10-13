/-
  ArchS8_Guard -- axiom guard for stage S8 (archimedean conceptual blueprint, 2026-10-11).
  Every top-level theorem of ArchS8_Volterra, ArchS8_ProlateData, ArchS8_Kernel.
  Required output for each: [propext, Classical.choice, Quot.sound].
  Check with:  lake build ArchS8_Kernel && lake env lean ArchS8_Guard.lean
  conjecture1_proved = False.
-/
import ArchS8_Kernel

-- ArchS8_Volterra.lean
#print axioms ArchS8.volt_comm
#print axioms ArchS8.volt_zero
#print axioms ArchS8.continuous_volt
#print axioms ArchS8.abs_volt_le
#print axioms ArchS8.hasDerivAt_volt
#print axioms ArchS8.hasDerivAt_volt_left
#print axioms ArchS8.hasDerivAt_volt_left'
#print axioms ArchS8.volt_deriv_swap
#print axioms ArchS8.lemma52_additive
#print axioms ArchS8.aOf_zero
#print axioms ArchS8.bOf_zero
#print axioms ArchS8.aOf_Du
#print axioms ArchS8.bOf_Du
#print axioms ArchS8.hasDerivAt_aOf
#print axioms ArchS8.hasDerivAt_bOf
#print axioms ArchS8.continuous_aOf
#print axioms ArchS8.continuous_bOf
#print axioms ArchS8.continuous_aOf'
#print axioms ArchS8.continuous_bOf'
#print axioms ArchS8.volt_aOf_bOf
#print axioms ArchS8.lemma52
#print axioms ArchS8.lemma51_scaling

-- ArchS8_ProlateData.lean
#print axioms ArchS8.prod_bound_gen
#print axioms ArchS8.aOf_bounds_gen
#print axioms ArchS8.bOf_eq_aOf
#print axioms ArchS8.bOf'_eq_aOf'
#print axioms ArchS8.ProlateData.w_nonneg
#print axioms ArchS8.ProlateData.cont_phi
#print axioms ArchS8.ProlateData.cont_dphi
#print axioms ArchS8.ProlateData.diff_phi
#print axioms ArchS8.ProlateData.hasDerivAt_kn
#print axioms ArchS8.ProlateData.hasDerivAt_kn1
#print axioms ArchS8.ProlateData.continuous_kn2
#print axioms ArchS8.ProlateData.kn_zero
#print axioms ArchS8.ProlateData.kn1_zero
#print axioms ArchS8.ProlateData.kn2_zero
#print axioms ArchS8.ProlateData.Qkn_eq_Cn
#print axioms ArchS8.ProlateData.M_nonneg
#print axioms ArchS8.ProlateData.N_nonneg
#print axioms ArchS8.ProlateData.bdd_aOf
#print axioms ArchS8.ProlateData.alpha_beta_nonneg
#print axioms ArchS8.ProlateData.summable_wB
#print axioms ArchS8.ProlateData.abs_kn_le
#print axioms ArchS8.ProlateData.norm_w_le
#print axioms ArchS8.ProlateData.zero_mem_Ioo
#print axioms ArchS8.ProlateData.hasDerivAt_eps
#print axioms ArchS8.ProlateData.hasDerivAt_eps1
#print axioms ArchS8.ProlateData.continuousOn_eps
#print axioms ArchS8.ProlateData.continuousOn_eps1
#print axioms ArchS8.ProlateData.continuousOn_eps2
#print axioms ArchS8.ProlateData.continuousOn_Qeps
#print axioms ArchS8.ProlateData.prop53
#print axioms ArchS8.ProlateData.eps_zero
#print axioms ArchS8.ProlateData.eps1_zero
#print axioms ArchS8.ProlateData.lemma54
#print axioms ArchS8.ProlateData.summable_w_phi_one
#print axioms ArchS8.ProlateData.eps1_zero_nonneg
#print axioms ArchS8.ProlateData.eps1_zero_pos
#print axioms ArchS8.ProlateData.Qeps_zero
#print axioms ArchS8.ProlateData.epsMul_inv
#print axioms ArchS8.ProlateData.epsMul_eq
#print axioms ArchS8.ProlateData.epsMul_hasDerivWithinAt
#print axioms ArchS8.ProlateData.cc84_term
#print axioms ArchS8.cosPhi_bound
#print axioms ArchS8.outer_of_cosPhi

-- ArchS8_Kernel.lean
#print axioms ArchS8.corr_self_eq_autocorr
#print axioms ArchS8.integrable_corr_integrand
#print axioms ArchS8.hasDerivAt_corr
#print axioms ArchS8.corr_eq_zero
#print axioms ArchS8.smoothOn_of_contDiff
#print axioms ArchS8.deriv_corr
#print axioms ArchS8.lemma51_corr
#print axioms ArchS8.ProlateData.chi_zero
#print axioms ArchS8.ProlateData.mem_Ioo_of_le
#print axioms ArchS8.ProlateData.halfline
#print axioms ArchS8.ProlateData.integral_eq_halfline
#print axioms ArchS8.ProlateData.eq102
#print axioms ArchS8.ProlateData.continuous_Qeps_clamp
#print axioms ArchS8.integral_corr_mul
#print axioms ArchS8.ProlateData.prop55
#print axioms ArchS8.ProlateData.prop55_KI
#print axioms ArchS8.ProlateData.prop55_autocorr
#print axioms ArchS8.corr_lift
#print axioms ArchS8.ProlateData.prop55_lift
