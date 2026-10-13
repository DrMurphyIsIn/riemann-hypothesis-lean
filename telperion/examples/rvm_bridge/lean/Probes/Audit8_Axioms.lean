import E6Bridge9
#print axioms RvMBridgeGauss.integrable_exp_quadratic
#print axioms RvMBridgeGauss.integrable_exp_quadratic_abs
#print axioms RvMBridgeGauss.abs_pow_le_exp
#print axioms RvMBridgeGauss.integrable_abs_pow_mul_exp_quadratic_abs
#print axioms RvMBridgeGauss.integrable_mul_cexp_quadratic
#print axioms RvMBridgeGauss.integral_mul_cexp_gaussian_fourier
#print axioms RvMBridge8.gaussB
#print axioms RvMBridge8.gaussB_pos
#print axioms RvMBridge8.gaussK
#print axioms RvMBridge8.gaussPhi
#print axioms RvMBridge8.gaussHalf
#print axioms RvMBridge8.gaussTest_eq_half_mul_conj
#print axioms RvMBridge8.gaussK_ne_zero
#print axioms RvMBridge8.paperFT_gaussPhi
#print axioms RvMBridge8.bump
#print axioms RvMBridge8.cutoff
#print axioms RvMBridge8.gaussTests
#print axioms RvMBridge8.cutoff_nonneg
#print axioms RvMBridge8.cutoff_le_one
#print axioms RvMBridge8.abs_cutoff_le_one
#print axioms RvMBridge8.cutoff_eq_one
#print axioms RvMBridge8.cutoff_eq_zero
#print axioms RvMBridge8.contDiff_cutoff
#print axioms RvMBridge8.hasCompactSupport_cutoff
#print axioms RvMBridge8.contDiff_gaussPhi
#print axioms RvMBridge8.isWeilTest_gaussTests
#print axioms RvMBridge8.norm_gaussPhi
#print axioms RvMBridge8.norm_cexp_I_mul_le
#print axioms RvMBridge8.norm_gaussTests_mul_le
#print axioms RvMBridge8.norm_gaussPhi_mul_le
#print axioms RvMBridge8.integrable_majorant
#print axioms RvMBridge8.paperFT_gaussTests_tendsto
#print axioms RvMBridge8.gaussPhi'
#print axioms RvMBridge8.hasDerivAt_gaussPhi
#print axioms RvMBridge8.norm_gaussPhi'_le
#print axioms RvMBridge8.exists_deriv_bump_bound
#print axioms RvMBridge8.hasDerivAt_cutoff
#print axioms RvMBridge8.hasDerivAt_gaussTests
#print axioms RvMBridge8.derivMajorant
#print axioms RvMBridge8.integrable_derivMajorant
#print axioms RvMBridge8.norm_deriv_gaussTests_mul_le
#print axioms RvMBridge8.I_mul_paperFT_eq
#print axioms RvMBridge8.norm_mul_paperFT_gaussTests_le
#print axioms RvMBridge8.norm_paperFT_gaussTests_le
#print axioms RvMBridge8.exists_paperFT_gaussTests_bound
#print axioms RvMBridge8.norm_hermitianTransform_eq
#print axioms RvMBridge8.gaussian_approx
#print axioms RvMBridge9.gaussian_transfer
#print axioms RvMBridge9.weil_positivity_implies_rh
#print axioms RvMBridge9.zeta_comb_membership_iff_rh
#check @RvMBridge8.gaussian_approx
#check @RvMBridge8.exists_paperFT_gaussTests_bound
#check @RvMBridge9.zeta_comb_membership_iff_rh
example : RvMBridge6.GaussianApprox := RvMBridge8.gaussian_approx
