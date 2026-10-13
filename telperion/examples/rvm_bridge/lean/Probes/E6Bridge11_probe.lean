/-  E6Bridge11_probe -- kernel-axiom probe for seam B of the Wall (2026-09-21).

    Run AFTER `lake build` (E6Bridge11 is not in defaultTargets; build it explicitly):

        lake env lean E6Bridge11.lean && lake env lean Probes/E6Bridge11_probe.lean

    Expected: every `#print axioms` line lists exactly [propext, Classical.choice, Quot.sound]
    and no sorryAx.  The obligation GaussianExplicitFormula is a `def : Prop` (no axioms of its
    own); gaussian_positivity_small_lam_of consumes it as a hypothesis. -/
import E6Bridge11

open RvMBridge11

-- the delivered theorems (UNCONDITIONAL: the explicit formula is E6Bridge10.zeroSide_gaussTest_eq)
#print axioms RvMBridge11.re_weilForm_gauss_nonneg
#print axioms RvMBridge11.gaussianExplicitFormula
#print axioms RvMBridge11.gaussian_positivity_small_lam
#print axioms RvMBridge11.gaussian_positivity_small_lam_explicit
#print axioms RvMBridge11.re_weilForm_gauss_nonneg_of_large_c
#print axioms RvMBridge11.gaussian_positivity_envelope
#print axioms RvMBridge11.gaussian_positivity_envelope'
-- the same modulo the (now discharged) named hypothesis
#print axioms RvMBridge11.gaussian_positivity_small_lam_of
#print axioms RvMBridge11.gaussian_positivity_small_lam_explicit_of
-- envelope stages
#print axioms RvMBridge11.norm_primeSide_le_uniform
#print axioms RvMBridge11.re_digamma_quarter_ge_log
#print axioms RvMBridge11.integral_indicator_bumpR_tail_le
#print axioms RvMBridge11.integral_bumpR_mul_psiR_ge_envelope
#print axioms RvMBridge11.gaussA_half
-- the stages
#print axioms RvMBridge11.autocorr_gaussPhi
#print axioms RvMBridge11.norm_autocorrGauss_le
#print axioms RvMBridge11.norm_primeSide_le
#print axioms RvMBridge11.norm_weilKernel_zero_le
#print axioms RvMBridge11.norm_weilKernel_one_le
#print axioms RvMBridgeGauss.integral_sq_mul_cexp_gaussian_fourier
#print axioms RvMBridge11.weilKernel_autocorrGauss_line
#print axioms RvMBridge11.re_digamma_quarter_ge
#print axioms RvMBridge11.re_digamma_quarter_ge_two
#print axioms RvMBridge11.integrable_bumpR_mul_psiR
#print axioms RvMBridge11.integral_bumpR
#print axioms RvMBridge11.integral_bumpR_mul_psiR_ge
#print axioms RvMBridge11.re_archSide_ge
#print axioms RvMBridge11.integral_sq_mul_exp_neg_mul_sq
-- the obligation, verbatim
#print RvMBridge11.GaussianExplicitFormula
-- the theorem statements, verbatim
#check @RvMBridge11.re_weilForm_gauss_nonneg
#check @RvMBridge11.gaussian_positivity_small_lam_of
#check @RvMBridge11.gaussian_positivity_small_lam
#check @RvMBridge11.re_weilForm_gauss_nonneg_of_large_c
#check @RvMBridge11.gaussian_positivity_envelope
#check @RvMBridge11.gaussian_positivity_envelope'
#print RvMBridge11.lam₀
#print RvMBridge11.R₀
#print RvMBridge11.envelopeX
#print RvMBridge11.envelopeC
