/-  E6Bridge16_probe -- kernel-axiom probe for the sharp envelope (2026-09-21).

        lake env lean -o .lake/build/lib/lean/E6Bridge16.olean -i .lake/build/lib/lean/E6Bridge16.ilean E6Bridge16.lean
        lake env lean Probes/E6Bridge16_probe.lean

    Expected: every #print axioms line is exactly [propext, Classical.choice, Quot.sound]. -/
import E6Bridge16

open RvMBridge16

-- delivered (UNCONDITIONAL)
#print axioms RvMBridge16.gaussian_positivity_envelope_sharp
#print axioms RvMBridge16.band_upper_edge
#print axioms RvMBridge16.re_weilForm_gauss_nonneg_sharp
#print axioms RvMBridge16.envelopeCsharp_le_crude
#print axioms RvMBridge16.gaussian_positivity_above_height
#print axioms RvMBridge16.gaussian_positivity_above_height_log
-- stages
#print axioms RvMBridgeGauss.integral_sq_mul_cexp_gaussian_fourier
#print axioms RvMBridge16.fourier_autocorrGauss
#print axioms RvMBridge16.weilKernel_zero_eq_gaussTest
#print axioms RvMBridge16.weilKernel_one_eq_gaussTest
#print axioms RvMBridge16.norm_gaussTest_half
#print axioms RvMBridge16.norm_poles_le
#print axioms RvMBridge16.norm_primeSide_le_primeAbs
#print axioms RvMBridge16.summable_primeAbsTerm
#print axioms RvMBridge16.primeAbs_le_crude
#print axioms RvMBridge16.re_digamma_quarter_ge_log'
#print axioms RvMBridge16.integral_indicator_bumpR_tail_le'
#print axioms RvMBridge16.integral_bumpR_mul_psiR_ge_capped
-- statements, verbatim
#check @RvMBridge16.gaussian_positivity_envelope_sharp
#check @RvMBridge16.band_upper_edge
#check @RvMBridge16.gaussian_positivity_above_height
#check @RvMBridge16.gaussian_positivity_above_height_log
#check @RvMBridge16.fourier_autocorrGauss
#print RvMBridge16.primeAbsTerm
#print RvMBridge16.primeAbs
#print RvMBridge16.tailRadius
#print RvMBridge16.envelopeCsharp
