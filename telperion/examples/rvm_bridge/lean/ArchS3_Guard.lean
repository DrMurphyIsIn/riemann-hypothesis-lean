/-
  ArchS3_Guard -- axiom guard for stage S3 (structural positivity L = W_inf + D >= 0, CC Cor 2.3).
  Required output for every line: [propext, Classical.choice, Quot.sound].
  Run:  lake build ArchS3_Limits && lake env lean ArchS3_Guard.lean
-/
import ArchS3_Limits

-- M1: the kernel delta (CC (48)/(49)) and its properties
#print axioms ArchS3.integral_cos_mul_neg_log
#print axioms ArchS3.ccDelta_eq
#print axioms ArchS3.deltaK_eq_ccDelta
#print axioms ArchS3.deltaK_zero
#print axioms ArchS3.continuous_deltaK
#print axioms ArchS3.abs_Si_le
#print axioms ArchS3.abs_deltaK_le
#print axioms ArchS3.integrable_deltaK
#print axioms ArchS3.continuous_deltaHat
#print axioms ArchS3.pairing_deltaK
-- M1: the functional L = W_inf + D
#print axioms ArchS3.Lfun_eq_integral_ell
#print axioms ArchS3.archW_eq_dirichlet
#print axioms ArchS3.Lfun_eq_dirichlet
#print axioms ArchS3.re_archSide_eq_poles_add_archW
#print axioms ArchS3.re_weilForm_eq_archW
#print axioms ArchS3.Lfun_nonneg_of_ell_nonneg
-- M2a: the Mellin transform of cos on the critical strip
#print axioms ArchS3.gInt_eq
#print axioms ArchS3.integral_log_gInt
#print axioms ArchS3.integral_cosD
#print axioms ArchS3.integral_log_cosD
#print axioms ArchS3.tendsto_PsiE
#print axioms ArchS3.tendsto_dPsiE
#print axioms ArchS3.hasDerivAt_PsiE
#print axioms ArchS3.Psi_eq_Gammaℂ
#print axioms ArchS3.Psi_eq_Gammaℝ
#print axioms ArchS3.norm_Psi_zt
#print axioms ArchS3.re_dPsi_mul_conj_Psi
-- M2b: Phi_t(a) = 2∫_a^∞ s^{-1/2+it} cos(2 pi s) ds, bounds, square-integrability
#print axioms ArchS3.norm_Gpart_le
#print axioms ArchS3.PhiE_add_Gpart
#print axioms ArchS3.norm_PhiE_le
#print axioms ArchS3.tendsto_PhiE
#print axioms ArchS3.norm_Phi_le
#print axioms ArchS3.tendsto_integral_Psi
#print axioms ArchS3.tendsto_integral_Phi
#print axioms ArchS3.integrableOn_normSq_Phi
#print axioms ArchS3.Nnorm_nonneg
-- M2c part 1: the exact damped identity
#print axioms ArchS3.stepA
#print axioms ArchS3.kernel_eq
#print axioms ArchS3.subst_swap
#print axioms ArchS3.stepC1
#print axioms ArchS3.stepC2
#print axioms ArchS3.stepB
#print axioms ArchS3.damped_identity
-- M2c part 2: the limit eps -> 0
#print axioms ArchS3.integral_cos_exp
#print axioms ArchS3.Jd_eq
#print axioms ArchS3.log_mul_jfun_le
#print axioms ArchS3.tendsto_R
#print axioms ArchS3.logcos_bound
#print axioms ArchS3.norm_Id_le
#print axioms ArchS3.tendsto_D
#print axioms ArchS3.Dlimit_value
#print axioms ArchS3.tendsto_N
#print axioms ArchS3.tendsto_A
-- THE MANIFEST-POSITIVITY IDENTITY and M3 (CC Corollary 2.3)
#print axioms ArchS3.ell_eq_Nnorm
#print axioms ArchS3.ell_nonneg
#print axioms ArchS3.Lfun_eq_integral_Nnorm
#print axioms ArchS3.cc_cor_2_3
#print axioms ArchS3.cc_cor_2_3_dirichlet
#print axioms ArchS3.weilForm_add_Dfun_nonneg
