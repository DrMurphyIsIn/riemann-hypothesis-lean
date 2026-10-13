/-  AxiomGuardRvMBridge -- CI kernel-axiom guard for the E6 RvM bridge island.

    Declared as a `lean_lib` in defaultTargets, so `lake build` compiles this file and thus
    transitively every module it imports. CI then runs

        lake env lean AxiomGuardRvMBridge.lean

    AFTER `lake build`, and FAILS if any `#print axioms` output mentions `sorryAx`.

    Guarded anchors:
      * RvMBridge.rvm_unbounded_mean_density -- the MIRRORMERE node statement, verbatim.
      * RvMBridge.eventually_Ncount_ge       -- the T log T lower bound from the RvM main clause.
      * RvMBridge2.rvm_unconditional         -- the RH node RH_rvm_unconditional, verbatim
        (cumulative RvM, O(log T)); plus its seam (zetaZeroCount_eq_Ncount), the integrated
        Stirling window lemma (int_mu_cumulative) and the two assembly stages.
      * Zeta23.RvM.{N_eq_halfContour_completedZeta, halfContour_completedZeta_split, gamma_side,
        backlund_horizontal, vertical_two} / Zeta23.StirlingVert.mu_stirling -- the upstream
        general-window internals the second bridge consumes as black boxes.
      * RvMBridge3.corridor_bound            -- the RH node RH_corridor_bound, verbatim (the
        good-ordinate lemma: zero-free segment -1 <= sigma <= 2 at a height in [T, T+1] with
        |zeta'/zeta| <= C log^2 T); plus its stages good_height_real (real-height good ordinate),
        corridor_large (T >= 7, both halves), corridor_small (2 <= T <= 7, compactness), the
        functional-equation identity logDeriv_zeta_reflect and the Gamma_R bounds.
      * Zeta23.WeilEF.{zeta_logDeriv_partial_fraction, exists_far_point, logDeriv_completedZeta,
        logDeriv_completedZeta_one_sub} / Zeta23.StirlingVert.digamma_stirling -- the upstream
        inputs the third bridge consumes as black boxes.
      * RvMBridge4.limit_explicit_formula    -- the RH node RH_limit_explicit_formula, verbatim
        (the Weil/Guinand explicit formula: Integrable archimedean integrand + HasSum of the
        divisor-weighted zero side over all rho : C to archSide - primeSide, for every smooth
        compactly supported g); plus its stages integrable_archIntegrand, archSide_eq,
        archSide_sub_primeSide, inversion_zero (Fourier inversion at 0), weilKernel_eq_Hfn
        (transform seam) and zeroMult_eq_of_strip / zeroMult_eq_zero_of_not_nontrivial
        (divisor vs analyticOrderAt seam).
      * Zeta23.WeilEF.EF_lit_zetaZeroConfig / Zeta23.EF.paper_inversion /
        Zeta23.WeilEF.gammaR_bracket / Zeta23.WeilEF.integrable_mul_logDeriv_Gammaℝ_of_decay --
        the upstream inputs the fourth bridge consumes as black boxes (the literature-form
        explicit formula itself, Fourier inversion, the Gamma_R bracket, the majorant lemma).
      * RvMBridge5.rh_implies_weil_positivity -- the MIRRORMERE dictionary node
        MM_rh_implies_weil_positivity, verbatim (Weil's criterion, forward half: Mathlib's
        RiemannHypothesis implies 0 <= Re weilForm (autocorr g) for every IsWeilTest g); plus its
        stages autocorr_eq_weilTest (autocorr = Zeta23's weilTest g g), isWeilTest_autocorr,
        eq_half_add_im_of_rh, weilKernel_autocorr_line (the |h(r)|^2 factorisation on the line)
        and term_re_nonneg.  Proves nothing about RH; discharges the hpos hypothesis of
        weil_negative_refutes_rh.  conjecture1_proved = False.
      * RvMBridgeGauss.{integrable_exp_quadratic, integrable_abs_pow_mul_exp_quadratic_abs,
        integrable_mul_cexp_quadratic, integral_mul_cexp_gaussian_fourier,
        integral_sq_mul_cexp_gaussian_fourier, norm_tsum_subtype_le_tsum, exp_two_mul_le_of_le,
        summable_mult_div_one_add_normSq, tendsto_tsum_zeroMult_of_strip_bound,
        zeroWindowSet_finite, mem_zeroWindow, ...} -- the Gaussian / Wall PRELUDE (2026-09-22): ONE
        copy of the helper vocabulary that E6Bridge6, 7, 8, 10, 11, 12 and 16 (parallel agents) had
        each re-proved (SHAPES_AUDIT_48H section 4, proposal P2; SHAPES_AUDIT_B N1, N5, D1, D5):
        the Gaussian integrability calculus and the two Gaussian moments at a complex frequency,
        the tsum tail envelope with its rate-splitting companion, the shared local-count majorant
        over all rho : C with the Tannery transfer, and the certified ordinate window; imported by
        E6Bridge6 and everything above it.  Helpers only: no registry node statement lives there,
        and every node theorem stays verbatim in its own artifact file.  conjecture1_proved = False.
      * RvMBridge6.weil_positivity_implies_rh_of / weil_positivity_implies_rh_of' /
        rh_iff_weil_positivity_of -- the Weil converse ATTACK (2026-09-20): Weil positivity implies
        Mathlib's RiemannHypothesis MODULO the named obligations GaussianTransfer (or the zero-free
        GaussianApprox) and GaussianDominance, carried as explicit hypotheses; plus every
        unconditional stage (explicit formula with the zero side isolated, zeroSide real,
        reflection symmetry gammaOf_reflect / zeroMult_reflect, strip_of_zero, pair split,
        Gaussian summability, gaussianTransfer_of_approx).  Proves nothing about RH.
      * RvMBridge7.gaussian_dominance -- the MIRRORMERE node MM_gaussian_dominance, verbatim
        (O2 DISCHARGED, 2026-09-21: every off-line nontrivial zero admits a centre c and width
        lam > 0 with Re zeroSide (gaussTest c lam) < 0); plus its stages (window finiteness,
        generic centre, maximiser with gap, phase choice exists_lam_re_gaussTest, tail_bound,
        re_zeroSide_le) and weil_positivity_implies_rh_of_approx (the converse modulo the single
        remaining Fourier obligation GaussianApprox).  Proves nothing about RH.
      * RvMBridge8.gaussian_approx -- the MIRRORMERE node MM_gaussian_approx, verbatim (O1'
        DISCHARGED, 2026-09-21: truncated Gaussian-derivative Weil tests approximate gaussTest on
        the strip with an n-uniform C/(1+|z|^2) bound); plus its stages (the Gaussian Fourier
        integral integral_mul_cexp_gaussian_fourier, since 2026-09-22 in the prelude RvMBridgeGauss;
        paperFT_gaussPhi, the generic integration by parts
        I_mul_paperFT_eq, the DCT limit and the uniform bound).
      * RvMBridge9.gaussian_transfer / weil_positivity_implies_rh / zeta_comb_membership_iff_rh
        -- the MIRRORMERE nodes MM_gaussian_transfer, MM_weil_positivity_implies_rh and
        MM_zeta_comb_membership_iff_rh, verbatim: the Weil converse unconditional on this island
        and the dictionary theorem (goal statement <-> Mathlib RiemannHypothesis).  NOT a proof
        of RH.  conjecture1_proved = False.
      * RvMBridge10.{rh_iff_gaussian_positivity, zeroSide_gaussTest_eq, rh_iff_gaussian_prime_le_arch}
        -- WALL ASSAULT seam A (2026-09-21): the Wall in two real parameters (RH <-> Gaussian
        positivity <-> prime side <= archimedean side for every centre and width), plus the
        limit stages of the Gaussian explicit formula.  Equivalences only; NOT a proof of RH.
      * RvMBridge12.{gaussian_positivity_of_window, gaussian_positivity_of_window_two,
        gaussian_positivity_of_all_on_line} -- WALL ASSAULT seam C (2026-09-21): the
        ladder-certified region instrument (WindowOnLine hypothesis + one certified near zero +
        lam above an explicit threshold => Gaussian positivity at that centre); plus stages
        (zeroSide_split, tail_bound_window, near_term_ge, tail_le_near_of_threshold).
        NOT a proof of RH; the on-line hypothesis is load-bearing.
      * RvMBridge11.re_weilForm_gauss_nonneg -- WALL ASSAULT seam B (2026-09-21): the small-width
        region lam <= lam0 = 1e-7 is UNCONDITIONAL (archimedean dominance), plus its stages.
      * RvMBridge13.{gaussianExplicitFormula, gaussian_positivity_small_lam,
        rh_iff_gaussian_positivity_above_lam0} -- THE WALL MAP: RH <-> Gaussian positivity on
        widths above lam0 only.  Equivalence; NOT a proof of RH.  conjecture1_proved = False.
      * RvMBridge14.{effective_gaussian_dominance, offline_zeros_small_or_margin,
        effectiveThreshold_unbounded_of_small_spacing} -- open lemma 1 (2026-09-21): effective
        Gaussian dominance with the explicit threshold and the localisation instrument; the
        spacing floor is load-bearing.  NOT a proof of RH.  conjecture1_proved = False.
      * RvMBridge15.{liZeroSum_tendsto, bl_explicit_formula_of, rh_implies_liLimit_re_nonneg}
        -- open lemma 2 (2026-09-21): the Weil-to-Li dictionary; B7 convergence half proved, the
        node modulo the named LiValue obligation; Li's criterion forward half.  NOT a proof of RH.
      * RvMBridge16.{gaussian_positivity_envelope_sharp, band_upper_edge} -- seam B sharpened
        (2026-09-21): the sharp c-uniform envelope with the exact prime-side constant primeAbs;
        plus stages (fourier_autocorrGauss, norm_primeSide_le_primeAbs, primeAbs_le_crude).
        NOT a proof of RH.  conjecture1_proved = False.
      * RvMBridge18.{xi_logDeriv_deriv_eq_of, eq_const_of_log_growth, summable_inv_sub_sq,
        tsum_inv_sub_sq_tendsto, logDeriv_xi_eq} -- the xi derivative partial fraction skeleton
        (2026-09-21), modulo the named obligations XiDiffRegular / XiLogDerivDerivDecay.
      * RvMBridgeXi.{xi_one_sub, xi_eq_zero_iff, isClosed_zeros, analyticAt_logDeriv,
        logDeriv_xi_one_sub, deriv_logDeriv_xi_one_sub, zeroMult_one_sub, tsum_reindex_zeroMult,
        tsum_zero_series_one_sub, logDeriv_of_unit_factor, inv_im_sq_le_majorant,
        summable_of_zeroBoundAt, nontrivialZeros_countable, eq_of_continuousAt_of_eventually_ne,
        ext_eventuallyEq_of_punctured, exists_mem_Ioo_notMem_finset, exists_bound_on_reProdIm, ...}
        -- the xi / partial-fraction PRELUDE (2026-09-22): ONE copy of the helper vocabulary that
        E6Bridge19 and E6Bridge20 (parallel agents) had each re-proved and E6Bridge17 / E6Bridge24
        duplicated (SHAPES_AUDIT_48H section 4, proposal P1), imported by E6Bridge17, 19, 20, 21, 22
        and 24; the complex-argument forms of rows 9-10 are consolidated in RvMBridge21 instead.
        Helpers only: no registry node statement lives there, and every node theorem stays verbatim
        in its own artifact file.  conjecture1_proved = False.
      * RvMBridge17.{rh_iff_theta_positivity, theta_heat, theta_pos_mono, rh_iff_thetaWidths_eq,
        not_thetaFree_of_offline, rh_or_thetaWidths_bddAbove} -- the THETA FACE (2026-09-21): the
        plain Gaussian face is heat-monotone in width; RH <-> every width free.  NOT a proof of RH.
      * RvMBridge20.{xiDiffExt_differentiable, xiDiffExt_eq, xiDiffExt_one_sub, exists_local_form,
        analyticOrderAt_xi_eq, xiDiffRegular_of} -- obligation 1 part A (2026-09-21): the entire
        extension across the zeros; growth remains the named obligation XiDiffExtGrowthRight.
      * RvMBridge21.{xi_logDeriv_deriv_decay, xi_logDeriv_deriv_eq_of_regular,
        digamma_deriv_tendsto_zero, zeta_logDeriv_deriv_tendsto_zero, hasSum_trigamma_of_re_pos}
        -- obligation 2 DISCHARGED (2026-09-21): real-axis decay of (log xi)''; since 2026-09-22
        also the complex-argument forms deriv_logDeriv_xi_of_one_lt_re / norm_term_le_of_two_le_re
        (formerly re-proved in E6Bridge22), of which the real-axis forms are corollaries.
      * RvMBridge22.{xiLogDerivDerivEq_of_two, xiDiffExtGrowthRight_of_two, rightDerivBound,
        growth_compact, growth_right, growth_strip, norm_tsum_far_le} -- obligation 1 reduced to
        LocalCountSum + StripDerivBound (2026-09-21).
      * RvMBridge19.{liValue_of, bl_explicit_formula_of_partialFraction, powerSum_eq_taylor,
        pairedPowerSum_one_eq, iteratedDeriv_psiHalf, taylorOne_eq, liLimit_eq_taylorOne,
        xiDerivPartialFraction_iff} -- the LiValue Taylor bookkeeping (2026-09-21), modulo
        XiDerivPartialFraction + NoRealZeroInUnitInterval.
      * RvMBridge23.{local_count_sum, xiLogDerivDerivEq_of_strip} -- LocalCountSum DISCHARGED
        (2026-09-21).  RvMBridge25.{noRealZeroInUnitInterval, liValue_of_two,
        bl_explicit_formula_of_two} -- no real zero in (0,1) DISCHARGED; B7 modulo StripDerivBound.
      * RvMBridge24.{stripDerivBound, xiLogDerivDerivEq_of_localCount, Fwin_bound_core,
        FwinExt_differentiableOn, exists_window_bound} -- StripDerivBound DISCHARGED (2026-09-21).
      * RvMBridge27.{xi_logDeriv_deriv_eq, liValue, bl_explicit_formula} -- THE UNCONDITIONAL
        ASSEMBLY: the derivative partial fraction of xi'/xi (no Hadamard), the Bombieri-Lagarias
        value identity, and the rh node RH_bl_explicit_formula verbatim.  NOT about RH.
      * RvMBridge28.{liLimit_re_nonneg_of_line_below, archSide_add_finiteSide_re_nonneg_of_line_below,
        liLimit_one_re_nonneg, ..., liLimit_five_re_nonneg, box_one, box_two,
        norm_integral_fract_cpow_le} -- THE LI LADDER (2026-09-21): zeros on the line up to
        height T >= 1 give 0 <= Re (liLimit N) for N <= 3 pi T / 2 (pair identity, Lemmas A/B,
        Theorems C/D); the low-height box |Im rho| >= sqrt 3 / 2 and (Re rho - 1/2)^2 <=
        Im^2/3 - 1/4 from the sharp sawtooth bound; rungs N = 1..5 hypothesis-free.  Consumes
        zero localisation, proves nothing about RH.
      * RvMBridge29.{pair_re_nonneg_of_far_sharp, liLimit_re_nonneg_of_line_below_sharp,
        archSide_add_finiteSide_re_nonneg_of_line_below_sharp} -- the SHARPENED exchange rate
        (2026-09-21): N <= 2 pi (T - 1/2) (Lemma A'' window, Lemma B'' combined bound).
        Consumes zero localisation, proves nothing about RH.
      * RvMBridge30.{gaussian_positivity_small_lam_1e3, re_weilForm_gauss_nonneg_1e3, pole_floor,
        psiR_mono, psiR_ge_rational, integral_bumpR_mul_psiR_ge_bands, cake_step} -- THE GAUSSIAN
        WINDOW (2026-09-22): the hypothesis-free small-width region of the Wall raised from
        lam0 = 1e-7 to lam0 = 1/1000 (eight-band layer cake on the archimedean side, evaluated pole
        floor, rational series floors on Re psi(1/4 + i r/2)); the twelve-band stretch
        gaussian_positivity_small_lam_3e3 certifies lam0 = 3/2000.  An unconditional statement
        about one explicit test function's prime-side functional; involves no zeros.
      * RvMBridge.zeta_ordinates_not_uniformly_discrete -- the MIRRORMERE milestone
        MM_zeta_ordinates_not_uniformly_discrete, verbatim (W2c, unconditional form: the zeta
        ordinates are not uniformly discrete); plus the verbatim re-proof of the v4.32
        quasicrystal pigeonhole brick it composes with rvm_unbounded_mean_density
        (zeta_ordinates_not_uniformlyDiscrete_of_unbounded_density and its stages
        exists_close_of_card_gt, not_uniformlyDiscrete_of_gaps_to_zero,
        windowedDensity_of_unboundedMeanDensity, not_uniformlyDiscrete_of_windowedDensity).
      * Zeta23.thmA₀ / Zeta23.two_thirds_on_critical_line -- Theorem A (Alpoege--Furman), the
        UPSTREAM input (anthropics/formal-math zeta23/, pinned in lakefile.toml); guarding it here
        re-verifies the dependency's axiom hygiene at our pin.
      * Zeta23.riemannVonMangoldt_zeta / Zeta23.RvM.zeta_local_zero_count -- the upstream
        unconditional Riemann--von Mangoldt package (dyadic main clause + local count).
      * Zeta23.zetaSeam -- the seam facts (finite windows, reflection symmetry) the bridge uses.
      * DogfoodComplexReImSplit.{e6b7_*, e6b28_re_pow_*, e6b5_hcast, e6b7_pair_*,
        e6b11_arch_hcast, e6b14_centre_hcast} -- the Telperion `complex_re_im_split` dogfood
        (2026-09-22, Probes/Dogfood_complex_re_im_split.lean): emitter-regenerated real/imaginary
        splits and cast identities of E6Bridge5, 7, 11, 14, 28, each gated against the hand
        content (tie gates to RvMBridge28.re_pow_*, consumer re-proofs of
        RvMBridge7.norm_gaussTest / re_gaussTest, verbatim instantiation gates for the cast
        `have`s).  Finite polynomial bookkeeping, nothing about RH.

      * FamilyWeil.{weilFormF_zeta, primeSideF_autocorr_eq_fin, re_weilFormF_autocorr_mono_logq,
        isFundDisc_iff, kronSym_three, kronSym_five, weightQ_prime_pow, weilFormQ_autocorr_eq,
        re_weilFormQ_mono, cell_reduction, reduction_of_entry, table4_check, table7_check,
        family4_of_dmins, family7_of_dmins, ...} -- the QUADRATIC FAMILY, Stage 0 (2026-09-25,
        FamilyWeilForm/Disc/Quad/Table): the parametric degree-<= 2 Weil form (= the zeta
        weilForm at the zeta data), zeta_K's instance, monotonicity in log|d| within a
        (pattern, sign) cell, the kernel-checked d_min tables of the cells cut at N = 4 (18 cells)
        and N = 7 (primes {2, 3, 5}, 54 cells), and the reduction "W(X) for every fundamental d"
        <- W(X) at the cells' d_min, at any real cutoff 0 < X <= N (WindowPosX; e.g. X = 6.5 for
        N = 7; integer corollaries *_nat).  weilFormQ is a frequency-side DEFINITION: no explicit
        formula for zeta_K is proved.  NO positivity unit is proved.  conjecture1_proved = False.

    Expected: every line reads `[propext, Classical.choice, Quot.sound]`.
    conjecture1_proved = False. -/
import E6Bridge
import E6Bridge2
import E6Bridge3
import E6Bridge4
import E6Bridge5
import RvMBridgeGauss
import E6Bridge6
import E6Bridge7
import E6Bridge8
import E6Bridge9
import E6Bridge10
import E6Bridge11
import E6Bridge12
import E6Bridge13
import E6Bridge14
import E6Bridge15
import E6Bridge16
import E6Bridge18
import RvMBridgeXi
import E6Bridge17
import E6Bridge20
import E6Bridge21
import E6Bridge22
import E6Bridge19
import E6Bridge23
import E6Bridge25
import E6Bridge26
import E6Bridge24
import E6Bridge27
import E6Bridge28
import E6Bridge29
import E6Bridge30
import ZhuEnvelope
import ZhuSymbol
import ZhuLegendre
import ZhuParity
import ZhuSplit
import ZhuOrtho
import ZhuTail
import ZhuInstance
import W2cAssembly
import Probes.Dogfood_complex_re_im_split
import Probes.Dogfood_zero_sum_majorant
import KWin_Window
import E6Bridge31
import E6Bridge32
import E6Bridge33
import E6Bridge34
import KWin_Bridge
import KWin2_Window25
import KWin2_Window
import KWin2_Bridge
import FamilyWeilForm
import FamilyWeilDisc
import FamilyWeilQuad
import FamilyWeilTable
import ArchS1_Identity
import ArchS2_QTrick
import ArchS7_LogMap
import ArchS7_Kappa
import ArchS7_PFP
import ArchS7_Density
import ArchS7_H85
import ArchS7_Final
import ArchS6_Enum
import ArchS6_Sobolev
import ArchS6_Bounds
import ArchS6_ProlateData
import ArchS6_Trace
import ArchS6_L1
import ArchS7_Term
import ArchS7_HS
import ArchS7_Abstract
import ArchS7_Concrete
import ArchS7_Dilation
import ArchS7_Theta
import ArchS7_Lemma41
import ArchS7b_Lemma41
import ArchS6_Abstract
import ArchS6_Fourier
import ArchS6_Proj
import ArchS6_Kernel
import ArchS6_Eigen
import ArchS6_Even
import ArchS6_Strict
import ArchS6_Prolate
import ArchS6_Real
import ArchS6_Bridge
import ArchS6_Functions
import ArchS3_Limits
import ArchRegistry_CCCor23
import ArchS4_Bridge
import ArchS5_Spectral
import ArchS5_HSRank
import ArchS8_Kernel
import ArchPipeline_Rung80
import PFConverseC
import Hodge1_RegOnePrime

#print axioms RvMBridge.rvm_unbounded_mean_density
#print axioms RvMBridge.eventually_Ncount_ge
#print axioms RvMBridge.zeta_ordinates_not_uniformly_discrete
#print axioms RvMBridge.zeta_ordinates_not_uniformlyDiscrete_of_unbounded_density
#print axioms RvMBridge.exists_close_of_card_gt
#print axioms RvMBridge.not_uniformlyDiscrete_of_gaps_to_zero
#print axioms RvMBridge.windowedDensity_of_unboundedMeanDensity
#print axioms RvMBridge.not_uniformlyDiscrete_of_windowedDensity
#print axioms RvMBridge2.rvm_unconditional
#print axioms RvMBridge2.rvm_cumulative
#print axioms RvMBridge2.rvm_cumulative_eventually
#print axioms RvMBridge2.int_mu_cumulative
#print axioms RvMBridge2.zetaZeroCount_eq_Ncount
#print axioms RvMBridge3.corridor_bound
#print axioms RvMBridge3.corridor_large
#print axioms RvMBridge3.corridor_small
#print axioms RvMBridge3.good_height_real
#print axioms RvMBridge3.logDeriv_zeta_reflect
#print axioms RvMBridge3.zeta_ne_zero_of_reflect
#print axioms RvMBridge3.logDeriv_Gammaℝ_shift
#print axioms RvMBridge3.norm_logDeriv_Gammaℝ_le_log_strip
#print axioms RvMBridge4.limit_explicit_formula
#print axioms RvMBridge4.integrable_archIntegrand
#print axioms RvMBridge4.archSide_eq
#print axioms RvMBridge4.archSide_sub_primeSide
#print axioms RvMBridge4.inversion_zero
#print axioms RvMBridge4.weilKernel_eq_Hfn
#print axioms RvMBridge4.zeroMult_eq_of_strip
#print axioms RvMBridge4.zeroMult_eq_zero_of_not_nontrivial
#print axioms RvMBridge5.rh_implies_weil_positivity
#print axioms RvMBridge5.autocorr_eq_weilTest
#print axioms RvMBridge5.isWeilTest_autocorr
#print axioms RvMBridge5.eq_half_add_im_of_rh
#print axioms RvMBridge5.weilKernel_autocorr_line
#print axioms RvMBridge5.term_re_nonneg
#print axioms RvMBridgeGauss.integrable_exp_quadratic
#print axioms RvMBridgeGauss.integrable_exp_quadratic_abs
#print axioms RvMBridgeGauss.abs_pow_le_exp
#print axioms RvMBridgeGauss.integrable_abs_pow_mul_exp_quadratic_abs
#print axioms RvMBridgeGauss.integrable_mul_cexp_quadratic
#print axioms RvMBridgeGauss.integral_mul_cexp_gaussian_fourier
#print axioms RvMBridgeGauss.integral_sq_mul_cexp_gaussian_fourier
#print axioms RvMBridgeGauss.norm_tsum_subtype_le_tsum
#print axioms RvMBridgeGauss.norm_tsum_subtype_le_mul_tsum
#print axioms RvMBridgeGauss.exp_two_mul_le_of_le
#print axioms RvMBridgeGauss.summable_mult_div_one_add_normSq
#print axioms RvMBridgeGauss.tendsto_tsum_zeroMult_of_strip_bound
#print axioms RvMBridgeGauss.zeroWindowSet_finite
#print axioms RvMBridgeGauss.mem_zeroWindow
#print axioms RvMBridge6.weilKernel_autocorr
#print axioms RvMBridge6.hasSum_weilForm_autocorr
#print axioms RvMBridge6.weilForm_autocorr_eq_zeroSide
#print axioms RvMBridge6.summable_hermitian_zeroSide
#print axioms RvMBridge6.reflect_reflect
#print axioms RvMBridge6.gammaOf_reflect
#print axioms RvMBridge6.zeroMult_reflect
#print axioms RvMBridge6.zeroSide_conj
#print axioms RvMBridge6.hermitianTransform_conj
#print axioms RvMBridge6.gaussTest_conj
#print axioms RvMBridge6.weilForm_autocorr_real
#print axioms RvMBridge6.strip_of_zero
#print axioms RvMBridge6.rh_of_all_on_line
#print axioms RvMBridge6.weil_positivity_implies_rh_of
#print axioms RvMBridge6.rh_iff_weil_positivity_of
#print axioms RvMBridge6.reflect_ne_self
#print axioms RvMBridge6.zeroSide_pair_split
#print axioms RvMBridge6.gaussTest_axis
#print axioms RvMBridge6.gaussTest_axis_re_neg
#print axioms RvMBridge6.norm_gaussTest_mul_le
#print axioms RvMBridge6.summable_gauss_zeroSide
#print axioms RvMBridge6.gauss_zeroSide_real
#print axioms RvMBridge6.gauss_zeroSide_pair_split
#print axioms RvMBridge6.gaussianTransfer_of_approx
#print axioms RvMBridge6.weil_positivity_implies_rh_of'
#print axioms RvMBridge7.zeroSide_gauss_eq
#print axioms RvMBridge7.norm_gaussTest
#print axioms RvMBridge7.norm_term
#print axioms RvMBridge7.re_gaussTest
#print axioms RvMBridge7.exists_lam_trig
#print axioms RvMBridge7.exists_lam_re_gaussTest
#print axioms RvMBridge7.windowSet_finite
#print axioms RvMBridge7.mem_window
#print axioms RvMBridge7.self_mem_window
#print axioms RvMBridge7.eq_badOf_of_phi_eq
#print axioms RvMBridge7.badOf_mem_badSet
#print axioms RvMBridge7.exists_generic_centre
#print axioms RvMBridge7.eq_or_eq_reflect_of_phi_eq
#print axioms RvMBridge7.exists_maximiser_gap
#print axioms RvMBridge7.phi_neg_of_not_mem_window
#print axioms RvMBridge7.majorant_nonneg
#print axioms RvMBridge7.summable_majorant
#print axioms RvMBridge7.norm_term_le_majorant
#print axioms RvMBridge7.constA_nonneg
#print axioms RvMBridge7.constB_nonneg
#print axioms RvMBridge7.tsum_majorant
#print axioms RvMBridge7.tail_bound
#print axioms RvMBridge7.re_zeroSide_le
#print axioms RvMBridge7.gaussian_dominance
#print axioms RvMBridge7.weil_positivity_implies_rh_of_approx
#print axioms RvMBridge8.gaussB_pos
#print axioms RvMBridge8.gaussTest_eq_half_mul_conj
#print axioms RvMBridge8.gaussK_ne_zero
#print axioms RvMBridge8.paperFT_gaussPhi
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
#print axioms RvMBridge8.hasDerivAt_gaussPhi
#print axioms RvMBridge8.norm_gaussPhi'_le
#print axioms RvMBridge8.exists_deriv_bump_bound
#print axioms RvMBridge8.hasDerivAt_cutoff
#print axioms RvMBridge8.hasDerivAt_gaussTests
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
#print axioms RvMBridge9.weil_negative_refutes_rh
#print axioms RvMBridge10.gaussTest_ofReal
#print axioms RvMBridge10.gaussTest_ofReal_re_nonneg
#print axioms RvMBridge10.gammaOf_eq_im_of_rh
#print axioms RvMBridge10.gauss_term_re_nonneg
#print axioms RvMBridge10.rh_implies_gaussian_positivity
#print axioms RvMBridge10.gaussian_positivity_implies_rh
#print axioms RvMBridge10.rh_iff_gaussian_positivity
#print axioms RvMBridge10.gaussian_positivity_iff_weil_positivity
#print axioms RvMBridge10.exists_hermitian_gaussTests_bound
#print axioms RvMBridge10.hermitianTransform_gaussTests_tendsto
#print axioms RvMBridge10.zeroSide_gaussTests_tendsto
#print axioms RvMBridge10.continuous_gaussPhi
#print axioms RvMBridge10.norm_gaussTests_le
#print axioms RvMBridge10.norm_phi_mul_phi_le
#print axioms RvMBridge10.integrable_sq_add_mul_gauss
#print axioms RvMBridge10.integrable_vMaj
#print axioms RvMBridge10.gaussI0_nonneg
#print axioms RvMBridge10.gaussI2_nonneg
#print axioms RvMBridge10.autocorrMaj_nonneg
#print axioms RvMBridge10.autocorrMaj_neg
#print axioms RvMBridge10.integral_vMaj
#print axioms RvMBridge10.norm_gaussTests_mul_conj_le
#print axioms RvMBridge10.norm_autocorr_gaussTests_le
#print axioms RvMBridge10.autocorr_gaussTests_tendsto
#print axioms RvMBridge10.primeBound_nonneg
#print axioms RvMBridge10.norm_primeTerm_le
#print axioms RvMBridge10.summable_primeBound
#print axioms RvMBridge10.primeSide_gaussTests_tendsto
#print axioms RvMBridge10.continuous_autocorr_gaussTests
#print axioms RvMBridge10.integrable_kernelMaj
#print axioms RvMBridge10.norm_kernel_term_le
#print axioms RvMBridge10.weilKernel_gaussTests_tendsto
#print axioms RvMBridge10.gammaOf_half_add
#print axioms RvMBridge10.exists_paperFT_autocorr_gaussTests_bound
#print axioms RvMBridge10.integrable_archBound
#print axioms RvMBridge10.norm_archIntegrand_le
#print axioms RvMBridge10.archIntegral_gaussTests_tendsto
#print axioms RvMBridge10.archSide_gaussTests_tendsto
#print axioms RvMBridge10.zeroSide_gaussTest_eq
#print axioms RvMBridge10.gaussian_positivity_iff_prime_le_arch
#print axioms RvMBridge10.rh_iff_gaussian_prime_le_arch
#print axioms RvMBridge12.windowOnLine_of_all_on_line
#print axioms RvMBridge12.tailWeight_nonneg
#print axioms RvMBridge12.summable_tailWeight
#print axioms RvMBridge12.tsum_tailWeight
#print axioms RvMBridge12.one_le_lamThreshold
#print axioms RvMBridge12.re_term_of_on_line
#print axioms RvMBridge12.re_term_nonneg_of_on_line
#print axioms RvMBridge12.term_eq_zero_of_not_nontrivial
#print axioms RvMBridge12.re_term_nonneg
#print axioms RvMBridge12.near_term_ge
#print axioms RvMBridge12.gaussian_positivity_of_all_on_line
#print axioms RvMBridge12.summable_term_subtype
#print axioms RvMBridge12.zeroSide_split
#print axioms RvMBridge12.re_window_ge_term
#print axioms RvMBridge12.phi_le_of_far
#print axioms RvMBridge12.norm_term_le_tail
#print axioms RvMBridge12.tail_bound_window
#print axioms RvMBridge12.tail_le_near_of_threshold
#print axioms RvMBridge12.gaussian_positivity_of_window
#print axioms RvMBridge12.gaussian_positivity_of_window_two
#print axioms RvMBridge12.windowSum_nonneg
#print axioms RvMBridge12.tailEnvelope_nonneg
#print axioms RvMBridge12.re_window_eq_windowSum
#print axioms RvMBridge12.gaussian_positivity_of_window_dominance
#print axioms RvMBridge12.re_zeroSide_ge_windowSum_sub
#print axioms RvMBridge12.near_term_le_windowSum
#print axioms RvMBridge11.gaussA_pos
#print axioms RvMBridge11.integral_sq_mul_exp_neg_mul_sq
#print axioms RvMBridge11.integral_sq_mul_cexp_neg_mul_sq
#print axioms RvMBridge11.re_digamma_quarter_ge
#print axioms RvMBridge11.re_digamma_quarter_ge_two
#print axioms RvMBridge11.gaussPhi_mul_conj
#print axioms RvMBridge11.autocorr_gaussPhi_eq_integral
#print axioms RvMBridge11.integral_sq_sub_mul_cexp
#print axioms RvMBridge11.gaussK_mul_conj
#print axioms RvMBridge11.autocorr_gaussPhi
#print axioms RvMBridge11.autocorrGauss_zero
#print axioms RvMBridge11.abs_one_sub_two_mul_exp_le
#print axioms RvMBridge11.norm_autocorrGauss_le
#print axioms RvMBridge11.autocorr_gaussPhi_funext
#print axioms RvMBridge11.prime_term_bound
#print axioms RvMBridge11.norm_primeSide_le
#print axioms RvMBridge11.norm_integral_autocorrGauss_mul_exp_le
#print axioms RvMBridge11.weilKernel_zero_eq
#print axioms RvMBridge11.weilKernel_one_eq
#print axioms RvMBridge11.norm_weilKernel_zero_le
#print axioms RvMBridge11.norm_weilKernel_one_le
#print axioms RvMBridge11.weilKernel_line_eq
#print axioms RvMBridge11.cpow_pi_div_a
#print axioms RvMBridge11.weilKernel_autocorrGauss_line
#print axioms RvMBridge11.psiR_eq
#print axioms RvMBridge11.psiR_ge
#print axioms RvMBridge11.psiR_ge_two
#print axioms RvMBridge11.continuous_psiR
#print axioms RvMBridge11.bumpR_nonneg
#print axioms RvMBridge11.continuous_bumpR
#print axioms RvMBridge11.integrable_bumpR
#print axioms RvMBridge11.integrable_bumpR_mul_psiR
#print axioms RvMBridge11.bumpR_le
#print axioms RvMBridge11.integral_bumpR
#print axioms RvMBridge11.R₀_pos
#print axioms RvMBridge11.setIntegral_bumpR_le
#print axioms RvMBridge11.integral_bumpR_mul_psiR_ge
#print axioms RvMBridge11.integral_archIntegrand_eq
#print axioms RvMBridge11.re_archSide_ge
#print axioms RvMBridge11.re_weilForm_gauss_nonneg
#print axioms RvMBridge11.gaussian_positivity_small_lam_of
#print axioms RvMBridge11.gaussian_positivity_small_lam_explicit_of
#print axioms RvMBridge11.gaussianExplicitFormula
#print axioms RvMBridge11.gaussian_positivity_small_lam
#print axioms RvMBridge11.gaussian_positivity_small_lam_explicit
#print axioms RvMBridge11.prime_term_bound_uniform
#print axioms RvMBridge11.norm_primeSide_le_uniform
#print axioms RvMBridge11.re_digamma_quarter_ge_log
#print axioms RvMBridge11.psiR_ge_log
#print axioms RvMBridge11.gaussA_half
#print axioms RvMBridge11.bumpR_half
#print axioms RvMBridge11.integral_indicator_bumpR_tail_le
#print axioms RvMBridge11.integral_bumpR_mul_psiR_ge_envelope
#print axioms RvMBridge11.envelopeX_nonneg
#print axioms RvMBridge11.re_weilForm_gauss_nonneg_of_large_c
#print axioms RvMBridge11.gaussian_positivity_envelope
#print axioms RvMBridge11.gaussian_positivity_envelope'
#print axioms RvMBridge13.gaussianExplicitFormula
#print axioms RvMBridge13.gaussian_positivity_small_lam
#print axioms RvMBridge13.rh_iff_gaussian_positivity_above_lam₀
#print axioms RvMBridge14.one_le_effectiveThreshold
#print axioms RvMBridge14.effectiveThreshold_pos
#print axioms RvMBridge14.le_exp_of_log_le
#print axioms RvMBridge14.effectiveThreshold_mono_B
#print axioms RvMBridge14.effectiveThreshold_unbounded_of_small_spacing
#print axioms RvMBridge14.tsum_winSet_eq_sum
#print axioms RvMBridge14.re_term_centre
#print axioms RvMBridge14.re_term_centre_nonpos
#print axioms RvMBridge14.norm_term_le_competitor
#print axioms RvMBridge14.re_window_sum_le
#print axioms RvMBridge14.effective_gaussian_dominance
#print axioms RvMBridge14.band_finite
#print axioms RvMBridge14.offline_zeros_small_or_margin
#print axioms RvMBridge14.windowCount_le_Ncount
#print axioms RvMBridge15.isNontrivialZero_conj
#print axioms RvMBridge15.isNontrivialZero_conj_iff
#print axioms RvMBridge15.zeroMult_conj
#print axioms RvMBridge15.mem_windowSet
#print axioms RvMBridge15.conj_mem_windowSet
#print axioms RvMBridge15.finite_zeros_window
#print axioms RvMBridge15.liKernel_conj
#print axioms RvMBridge15.liTerm_eq_zero_of_not_nontrivial
#print axioms RvMBridge15.liPaired_eq_zero_of_not_nontrivial
#print axioms RvMBridge15.liTerm_conj
#print axioms RvMBridge15.windowSupport_finite
#print axioms RvMBridge15.liZeroSum_eq_tsum_indicator
#print axioms RvMBridge15.indicator_liTerm_conj
#print axioms RvMBridge15.summable_indicator_liTerm
#print axioms RvMBridge15.liZeroSum_eq_tsum_paired
#print axioms RvMBridge15.liZeroSum_im
#print axioms RvMBridge15.liKernel_eq_sum
#print axioms RvMBridge15.sum_choose_succ_le
#print axioms RvMBridge15.abs_re_liKernel_le
#print axioms RvMBridge15.liPaired_re
#print axioms RvMBridge15.liPaired_im
#print axioms RvMBridge15.norm_liPaired
#print axioms RvMBridge15.norm_liPaired_le_majorant
#print axioms RvMBridge15.finite_zeros_small
#print axioms RvMBridge15.summable_liBound
#print axioms RvMBridge15.norm_liPaired_le
#print axioms RvMBridge15.summable_liPaired
#print axioms RvMBridge15.liZeroSum_tendsto
#print axioms RvMBridge15.bl_explicit_formula_of
#print axioms RvMBridge15.norm_one_sub_inv_of_on_line
#print axioms RvMBridge15.liPaired_re_nonneg_of_rh
#print axioms RvMBridge15.rh_implies_liZeroSum_re_nonneg
#print axioms RvMBridge15.rh_implies_liLimit_re_nonneg
#print axioms RvMBridge16.gaussA_mul_sqrt
#print axioms RvMBridge16.fourier_autocorrGauss
#print axioms RvMBridge16.weilKernel_zero_eq_gaussTest
#print axioms RvMBridge16.weilKernel_one_eq_gaussTest
#print axioms RvMBridge16.norm_gaussTest_half
#print axioms RvMBridge16.norm_poles_le
#print axioms RvMBridge16.primeAbsTerm_nonneg
#print axioms RvMBridge16.primeAbsTerm_le
#print axioms RvMBridge16.summable_primeAbsTerm
#print axioms RvMBridge16.primeAbs_nonneg
#print axioms RvMBridge16.primeAbs_le_crude
#print axioms RvMBridge16.norm_autocorrGauss_add_neg_le
#print axioms RvMBridge16.norm_primeSide_le_primeAbs
#print axioms RvMBridge16.re_digamma_quarter_ge_log'
#print axioms RvMBridge16.psiR_ge_log'
#print axioms RvMBridge16.integral_indicator_bumpR_tail_le'
#print axioms RvMBridge16.integral_bumpR_mul_psiR_ge_capped
#print axioms RvMBridge16.tailRadius_sq
#print axioms RvMBridge16.tailRadius_nonneg
#print axioms RvMBridge16.re_weilForm_gauss_nonneg_sharp
#print axioms RvMBridge16.gaussian_positivity_envelope_sharp
#print axioms RvMBridge16.band_upper_edge
#print axioms RvMBridge16.envelopeCsharp_le_crude
#print axioms RvMBridge16.gaussian_positivity_above_height
#print axioms RvMBridge16.gaussian_positivity_above_height_log
#print axioms RvMBridge18.xi_differentiable
#print axioms RvMBridge18.xi_eq
#print axioms RvMBridge18.xi_eventuallyEq
#print axioms RvMBridge18.logDeriv_xi_eq
#print axioms RvMBridge18.normSq_gammaOf_le
#print axioms RvMBridge18.polTerm_eq_zero_of_not_nontrivial
#print axioms RvMBridge18.norm_polTerm
#print axioms RvMBridge18.norm_polTerm_le_majorant
#print axioms RvMBridge18.finite_zeros_near
#print axioms RvMBridge18.summable_polBound
#print axioms RvMBridge18.norm_polTerm_le
#print axioms RvMBridge18.summable_inv_sub_sq
#print axioms RvMBridge18.summable_polTerm
#print axioms RvMBridge18.norm_polTerm_le_real
#print axioms RvMBridge18.polTerm_tendsto_zero
#print axioms RvMBridge18.tsum_inv_sub_sq_tendsto
#print axioms RvMBridge18.eq_const_of_log_growth
#print axioms RvMBridge18.not_nontrivialZero_of_one_le_re
#print axioms RvMBridge18.xi_logDeriv_deriv_eq_of
#print axioms RvMBridgeXi.xi_one_sub
#print axioms RvMBridgeXi.xi_zero
#print axioms RvMBridgeXi.xi_one
#print axioms RvMBridgeXi.xi_analyticAt
#print axioms RvMBridgeXi.xi_eq_zero_iff
#print axioms RvMBridgeXi.xi_ne_zero_of_not_nontrivial
#print axioms RvMBridgeXi.isClosed_zeros
#print axioms RvMBridgeXi.eventually_not_zero
#print axioms RvMBridgeXi.analyticAt_logDeriv
#print axioms RvMBridgeXi.logDeriv_xi_analyticAt
#print axioms RvMBridgeXi.hasDerivAt_logDeriv_xi
#print axioms RvMBridgeXi.logDeriv_xi_one_sub
#print axioms RvMBridgeXi.deriv_logDeriv_xi_one_sub
#print axioms RvMBridgeXi.zeroMult_one_sub
#print axioms RvMBridgeXi.tsum_reindex_zeroMult
#print axioms RvMBridgeXi.tsum_zero_series_one_sub
#print axioms RvMBridgeXi.tsum_polTerm_one_sub
#print axioms RvMBridgeXi.logDeriv_of_unit_factor
#print axioms RvMBridgeXi.inv_im_sq_le_majorant
#print axioms RvMBridgeXi.inv_normSq_le_majorant
#print axioms RvMBridgeXi.windowZeros_finite
#print axioms RvMBridgeXi.summable_zeroBoundAt
#print axioms RvMBridgeXi.norm_le_zeroBoundAt
#print axioms RvMBridgeXi.summable_of_zeroBoundAt
#print axioms RvMBridgeXi.smallZeros_finite
#print axioms RvMBridgeXi.smallZeros_eq
#print axioms RvMBridgeXi.zeroBound_eq
#print axioms RvMBridgeXi.summable_zeroBound
#print axioms RvMBridgeXi.norm_le_zeroBound
#print axioms RvMBridgeXi.summable_of_zeroBound
#print axioms RvMBridgeXi.nontrivialZeros_countable
#print axioms RvMBridgeXi.eq_of_continuousAt_of_eventually_ne
#print axioms RvMBridgeXi.ext_eventuallyEq_of_punctured
#print axioms RvMBridgeXi.differentiableAt_of_punctured
#print axioms RvMBridgeXi.exists_mem_Ioo_notMem_finset
#print axioms RvMBridgeXi.exists_bound_on_reProdIm
#print axioms RvMBridge17.zeroSide_plain_eq
#print axioms RvMBridge17.theta_eq
#print axioms RvMBridge17.plainGauss_re_exponent
#print axioms RvMBridge17.plainGauss_im_exponent
#print axioms RvMBridge17.norm_plainGauss
#print axioms RvMBridge17.norm_pterm
#print axioms RvMBridge17.re_plainGauss
#print axioms RvMBridge17.plainGauss_conj
#print axioms RvMBridge17.plainGauss_ofReal
#print axioms RvMBridge17.pterm_eq_zero_of_not_nontrivial
#print axioms RvMBridge17.norm_plainGauss_mul_le
#print axioms RvMBridge17.plainC_nonneg
#print axioms RvMBridge17.norm_pterm_le
#print axioms RvMBridge17.summable_plain_zeroSide
#print axioms RvMBridge17.zeroSide_plain_im
#print axioms RvMBridge17.pterm_re_nonneg_of_rh
#print axioms RvMBridge17.theta_nonneg_of_rh
#print axioms RvMBridge17.exists_lam_cos_neg_one
#print axioms RvMBridge17.exists_generic_centre'
#print axioms RvMBridge17.pmajorant_nonneg
#print axioms RvMBridge17.summable_pmajorant
#print axioms RvMBridge17.norm_pterm_le_pmajorant
#print axioms RvMBridge17.pconstA_nonneg
#print axioms RvMBridge17.pconstB_nonneg
#print axioms RvMBridge17.tsum_pmajorant
#print axioms RvMBridge17.ptail_bound
#print axioms RvMBridge17.theta_le_pair_add_tail
#print axioms RvMBridge17.exists_theta_neg_of_offline
#print axioms RvMBridge17.rh_iff_theta_positivity
#print axioms RvMBridge17.heatVar_pos
#print axioms RvMBridge17.heatKernel_nonneg
#print axioms RvMBridge17.continuous_heatKernel
#print axioms RvMBridge17.heat_A_eq
#print axioms RvMBridge17.heat_integrand_eq
#print axioms RvMBridge17.plainGauss_heat
#print axioms RvMBridge17.real_gauss_heat
#print axioms RvMBridge17.integrable_heatF
#print axioms RvMBridge17.integral_norm_heatF_le
#print axioms RvMBridge17.summable_integral_norm_heatF
#print axioms RvMBridge17.tsum_pterm_NZ
#print axioms RvMBridge17.tsum_pterm_re_NZ
#print axioms RvMBridge17.theta_heat
#print axioms RvMBridge17.theta_pos_mono
#print axioms RvMBridge17.thetaFree_mono
#print axioms RvMBridge17.thetaWidths_Ioc_subset
#print axioms RvMBridge17.rh_iff_thetaFree_all
#print axioms RvMBridge17.rh_iff_thetaWidths_eq
#print axioms RvMBridge17.not_thetaFree_of_offline
#print axioms RvMBridge17.thetaWidths_bddAbove_of_offline
#print axioms RvMBridge17.rh_or_thetaWidths_bddAbove
#print axioms RvMBridge20.xi_ne_zero_of_one_le_re
#print axioms RvMBridge20.analyticOrderAt_xi_ne_top
#print axioms RvMBridge20.analyticAt_completedZeta
#print axioms RvMBridge20.analyticOrderAt_xi_eq_of_zero
#print axioms RvMBridge20.analyticOrderAt_xi_eq
#print axioms RvMBridge20.tsum_polTerm_eq
#print axioms RvMBridge20.nearZeros_finite
#print axioms RvMBridge20.exists_ball_avoid
#print axioms RvMBridge20.polTerm_differentiableAt
#print axioms RvMBridge20.exists_ball_rest
#print axioms RvMBridge20.exists_unit_factor
#print axioms RvMBridge20.deriv_logDeriv_xi_local
#print axioms RvMBridge20.exists_local_form
#print axioms RvMBridge20.xiDiffExt_eq
#print axioms RvMBridge20.xiDiffExt_eventuallyEq
#print axioms RvMBridge20.xiDiffExt_differentiable
#print axioms RvMBridge20.isNontrivialZero_one_sub_iff
#print axioms RvMBridge20.xiDiffReg_one_sub
#print axioms RvMBridge20.xiDiffExt_one_sub
#print axioms RvMBridge20.xiDiffExtGrowth_of_right
#print axioms RvMBridge20.xiDiffRegular_of
#print axioms RvMBridge20.xiDiffRegular_of_right
#print axioms RvMBridge21.ne_neg_nat_of_re_pos
#print axioms RvMBridge21.isOpen_re_pos
#print axioms RvMBridge21.analyticAt_Gamma_of_re_pos
#print axioms RvMBridge21.analyticAt_digamma_of_re_pos
#print axioms RvMBridge21.continuousAt_deriv_digamma
#print axioms RvMBridge21.norm_trigTerm_le
#print axioms RvMBridge21.summable_trigBound
#print axioms RvMBridge21.continuousOn_trigSum
#print axioms RvMBridge21.summable_trigTerm
#print axioms RvMBridge21.eq_of_intCast_near
#print axioms RvMBridge21.hasSum_trigamma_of_re_pos
#print axioms RvMBridge21.sum_range_inv_sq_le
#print axioms RvMBridge21.summable_inv_sq_real
#print axioms RvMBridge21.tsum_inv_sq_real_le
#print axioms RvMBridge21.norm_trigTerm_real
#print axioms RvMBridge21.norm_deriv_digamma_real_le
#print axioms RvMBridge21.digamma_deriv_tendsto_zero
#print axioms RvMBridge21.abscissa_vonMangoldt_le_one
#print axioms RvMBridge21.abscissa_vonMangoldt_lt
#print axioms RvMBridge21.isOpen_one_lt_re
#print axioms RvMBridge21.logDeriv_zeta_eq
#print axioms RvMBridge21.deriv_logDeriv_zeta_eq
#print axioms RvMBridge21.term_logMul_one
#print axioms RvMBridge21.term_tendsto_zero
#print axioms RvMBridge21.norm_term_le_of_two_le_re
#print axioms RvMBridge21.norm_term_le_of_two_le
#print axioms RvMBridge21.zeta_logDeriv_deriv_tendsto_zero
#print axioms RvMBridge21.logDeriv_xi_eq_of_one_lt_re
#print axioms RvMBridge21.deriv_logDeriv_xi_of_one_lt_re
#print axioms RvMBridge21.deriv_logDeriv_xi_real
#print axioms RvMBridge21.tendsto_neg_inv_sq
#print axioms RvMBridge21.tendsto_inv_sub_one_sq
#print axioms RvMBridge21.xi_logDeriv_deriv_decay
#print axioms RvMBridge21.xi_logDeriv_deriv_eq_of_regular
#print axioms RvMBridge22.lcTerm_nonneg
#print axioms RvMBridge22.lcTerm_le_majorant
#print axioms RvMBridge22.summable_lcTerm
#print axioms RvMBridge22.windowSet_finite
#print axioms RvMBridge22.mem_window
#print axioms RvMBridge22.norm_polTerm_le_lcTerm_right
#print axioms RvMBridge22.norm_polTerm_le_lcTerm_far
#print axioms RvMBridge22.norm_tsum_polTerm_le_right
#print axioms RvMBridge22.norm_tsum_far_le
#print axioms RvMBridge22.bound_of_bound_off_zeros
#print axioms RvMBridge22.growth_compact
#print axioms RvMBridge22.growth_right
#print axioms RvMBridge22.isOpen_stripOpen
#print axioms RvMBridge22.growth_strip_off_zeros
#print axioms RvMBridge22.growth_strip
#print axioms RvMBridge22.abs_im_le_norm'
#print axioms RvMBridge22.xiDiffExtGrowthRight_of
#print axioms RvMBridge22.xiDiffRegular_of_three
#print axioms RvMBridge22.xiLogDerivDerivEq_of_three
#print axioms RvMBridge22.norm_deriv_digamma_le
#print axioms RvMBridge22.summable_dirTerms
#print axioms RvMBridge22.norm_deriv_logDeriv_zeta_le
#print axioms RvMBridge22.rightDerivBound
#print axioms RvMBridge22.xiDiffExtGrowthRight_of_two
#print axioms RvMBridge22.xiLogDerivDerivEq_of_two
#print axioms RvMBridge19.xiLogDerivDerivEq_def
#print axioms RvMBridge19.one_le_norm_of_nontrivial
#print axioms RvMBridge19.norm_pos_of_nontrivial
#print axioms RvMBridge19.iteratedDeriv_tsum_ball
#print axioms RvMBridge19.analyticAt_tsum_ball
#print axioms RvMBridge19.exists_zero_radius
#print axioms RvMBridge19.zeroRadius_pos
#print axioms RvMBridge19.zeroRadius_le_one
#print axioms RvMBridge19.zeroRadius_le
#print axioms RvMBridge19.not_nontrivialZero_of_mem_ball
#print axioms RvMBridge19.norm_sub_ge_half
#print axioms RvMBridge19.coef_succ
#print axioms RvMBridge19.coef_zero
#print axioms RvMBridge19.norm_coef
#print axioms RvMBridge19.zterm_zero_eq
#print axioms RvMBridge19.zterm_eq_zero_of_not_nontrivial
#print axioms RvMBridge19.hasDerivAt_zterm
#print axioms RvMBridge19.norm_zterm_le
#print axioms RvMBridge19.summable_zbound
#print axioms RvMBridge19.norm_zterm_le_zbound
#print axioms RvMBridge19.powerSum_term_eq_zero_of_not_nontrivial
#print axioms RvMBridge19.summable_powerSum
#print axioms RvMBridge19.powerSum_conj
#print axioms RvMBridge19.powerSum_re
#print axioms RvMBridge19.zterm_at_zero
#print axioms RvMBridge19.tsum_zterm_zero
#print axioms RvMBridge19.deriv_logDeriv_xi_eventuallyEq
#print axioms RvMBridge19.iteratedDeriv_tsum_zterm
#print axioms RvMBridge19.powerSum_eq_taylor
#print axioms RvMBridge19.powerSum_eq_neg_taylor
#print axioms RvMBridge19.pairedPowerSum_term_eq_zero_of_not_nontrivial
#print axioms RvMBridge19.abs_re_inv_pow_le
#print axioms RvMBridge19.summable_pairedPowerSum
#print axioms RvMBridge19.pairedPowerSum_eq_powerSum
#print axioms RvMBridge19.xi_ne_zero_on_segment
#print axioms RvMBridge19.im_ne_zero_of_nontrivial
#print axioms RvMBridge19.ofReal_ne_of_im_ne_zero
#print axioms RvMBridge19.abs_im_le_norm_ofReal_sub
#print axioms RvMBridge19.norm_zterm_zero_ofReal_le
#print axioms RvMBridge19.norm_zterm_zero_ofReal_le_segBound
#print axioms RvMBridge19.continuous_zterm_zero_ofReal
#print axioms RvMBridge19.integral_zterm_zero
#print axioms RvMBridge19.support_zterm_subset
#print axioms RvMBridge19.hasSum_integral_zterm
#print axioms RvMBridge19.tsum_inv_add_inv_one_sub
#print axioms RvMBridge19.refTerm_reflect
#print axioms RvMBridge19.refTerm_eq_zero_of_not_nontrivial
#print axioms RvMBridge19.summable_refTerm
#print axioms RvMBridge19.tsum_refTerm
#print axioms RvMBridge19.pairedPowerSum_one_eq
#print axioms RvMBridge19.logDeriv_zeta_eq_near_one
#print axioms RvMBridge19.zetaLogDerivReg_eventuallyEq
#print axioms RvMBridge19.logDeriv_zeta₁_analyticAt
#print axioms RvMBridge19.eta_eq
#print axioms RvMBridge19.dcoef_succ
#print axioms RvMBridge19.norm_dcoef
#print axioms RvMBridge19.re_pos_of_mem_ball
#print axioms RvMBridge19.norm_le_of_mem_ball
#print axioms RvMBridge19.norm_shift_ge
#print axioms RvMBridge19.shift_ne_zero
#print axioms RvMBridge19.hasDerivAt_dterm
#print axioms RvMBridge19.summable_dbound
#print axioms RvMBridge19.norm_dterm_le
#print axioms RvMBridge19.iteratedDeriv_dtail
#print axioms RvMBridge19.dtail_analyticAt
#print axioms RvMBridge19.half_mem_integerComplement
#print axioms RvMBridge19.psiHalf_eq
#print axioms RvMBridge19.psiHalf_eventuallyEq
#print axioms RvMBridge19.psiHalf_analyticAt
#print axioms RvMBridge19.summable_inv_nat_pow
#print axioms RvMBridge19.summable_even_inv_pow
#print axioms RvMBridge19.summable_odd_inv_pow'
#print axioms RvMBridge19.summable_odd_inv_pow
#print axioms RvMBridge19.tsum_odd_inv_pow
#print axioms RvMBridge19.iteratedDeriv_psiHalf
#print axioms RvMBridge19.archFn_analyticAt
#print axioms RvMBridge19.archCoeff_zero
#print axioms RvMBridge19.archCoeff_succ
#print axioms RvMBridge19.logDeriv_xi_eq_closed
#print axioms RvMBridge19.closedFn_analyticAt
#print axioms RvMBridge19.logDeriv_xi_eventuallyEq_one
#print axioms RvMBridge19.iteratedDeriv_one_div
#print axioms RvMBridge19.taylorOne_eq
#print axioms RvMBridge19.iter_deriv_comp_add_const
#print axioms RvMBridge19.taylorZero_eq
#print axioms RvMBridge19.pairedPowerSum_succ_eq
#print axioms RvMBridge19.liKernel_re
#print axioms RvMBridge19.liPaired_eq_sum
#print axioms RvMBridge19.liLimit_eq_sum
#print axioms RvMBridge19.liLimit_eq_taylorOne
#print axioms RvMBridge19.sum_choose_alt
#print axioms RvMBridge19.sum_choose_eta
#print axioms RvMBridge19.sum_choose_archCoeff
#print axioms RvMBridge19.liValue_of
#print axioms RvMBridge19.bl_explicit_formula_of_partialFraction
#print axioms RvMBridge19.logDeriv_xi_eq_lambda
#print axioms RvMBridge19.logDeriv_xi_eventuallyEq_lambda
#print axioms RvMBridge19.logDeriv_lambda_analyticAt
#print axioms RvMBridge19.deriv_logDeriv_lambda_eq
#print axioms RvMBridge19.lambdaDerivPartialFraction_of_xi
#print axioms RvMBridge19.xiDerivPartialFraction_of_lambda
#print axioms RvMBridge19.xiDerivPartialFraction_iff
#print axioms RvMBridge19.liValue_of_lambda
#print axioms RvMBridge19.liValue_of_growth
#print axioms RvMBridge19.bl_explicit_formula_of_growth
#print axioms RvMBridge23.one_add_sq_le_of_ceil
#print axioms RvMBridge23.lcTerm_le_fiber_weight
#print axioms RvMBridge23.lcTerm_eq_zero_of_not_nontrivial
#print axioms RvMBridge23.zeroMult_cast_eq
#print axioms RvMBridge23.sum_zeroMult_fiber_le
#print axioms RvMBridge23.wt_nonneg
#print axioms RvMBridge23.wlog_nonneg
#print axioms RvMBridge23.summable_wt
#print axioms RvMBridge23.log_add_four_le
#print axioms RvMBridge23.log_div_le_rpow
#print axioms RvMBridge23.summable_wlog
#print axioms RvMBridge23.wcount_le
#print axioms RvMBridge23.wcount_nonneg
#print axioms RvMBridge23.summable_wbound
#print axioms RvMBridge23.summable_wcount
#print axioms RvMBridge23.sum_lcTerm_le
#print axioms RvMBridge23.S1_nonneg
#print axioms RvMBridge23.S2_nonneg
#print axioms RvMBridge23.tsum_wcount_le
#print axioms RvMBridge23.local_count_sum
#print axioms RvMBridge23.xiDiffExtGrowthRight_of_strip
#print axioms RvMBridge23.xiLogDerivDerivEq_of_strip
#print axioms RvMBridge25.norm_tail_integral_le
#print axioms RvMBridge25.re_riemannZeta_neg_of_unit_interval
#print axioms RvMBridge25.riemannZeta_ne_zero_of_unit_interval
#print axioms RvMBridge25.noRealZeroInUnitInterval
#print axioms RvMBridge25.liValue_of_partialFraction
#print axioms RvMBridge25.liValue_of_growth
#print axioms RvMBridge25.liValue_of_two
#print axioms RvMBridge25.bl_explicit_formula_of_two
#print axioms RvMBridge26.liValue_of_strip
#print axioms RvMBridge26.bl_explicit_formula_of_strip
#print axioms RvMBridge24.zeroMult_eq_zeta23
#print axioms RvMBridge24.zerosIn_finite
#print axioms RvMBridge24.sum_le_Ncount
#print axioms RvMBridge24.window_sum_le_five
#print axioms RvMBridge24.exists_window_bound
#print axioms RvMBridge24.norm_log_le
#print axioms RvMBridge24.norm_digamma_le_log
#print axioms RvMBridge24.landau_window
#print axioms RvMBridge24.FwinExt_eq
#print axioms RvMBridge24.logDeriv_xi_local
#print axioms RvMBridge24.Fwin_differentiableAt
#print axioms RvMBridge24.FwinExt_eventuallyEq_at_zero
#print axioms RvMBridge24.FwinExt_differentiableOn
#print axioms RvMBridge24.deriv_FwinExt
#print axioms RvMBridge24.exists_radius
#print axioms RvMBridge24.norm_deriv_FwinExt_le
#print axioms RvMBridge24.window_one_sub
#print axioms RvMBridge24.Fwin_one_sub
#print axioms RvMBridge24.le_mul_one_add
#print axioms RvMBridge24.Fwin_bound_core
#print axioms RvMBridge24.sphere_bound
#print axioms RvMBridge24.target_bound_high
#print axioms RvMBridge24.tsum_lcTerm_le
#print axioms RvMBridge24.target_bound_low
#print axioms RvMBridge24.stripDerivBound
#print axioms RvMBridge24.xiDiffExtGrowthRight_of_localCount
#print axioms RvMBridge24.xiLogDerivDerivEq_of_localCount
#print axioms RvMBridge27.xi_logDeriv_deriv_eq
#print axioms RvMBridge27.liValue
#print axioms RvMBridge27.bl_explicit_formula
#print axioms RvMBridge28.zeroMult_one_sub_conj
#print axioms RvMBridge28.isNontrivialZero_one_sub_conj
#print axioms RvMBridge28.wOf
#print axioms RvMBridge28.wOf_ne_zero
#print axioms RvMBridge28.one_sub_inv_eq_inv_wOf
#print axioms RvMBridge28.one_sub_inv_one_sub_conj
#print axioms RvMBridge28.liKernel_eq_inv_wOf
#print axioms RvMBridge28.liKernel_one_sub_conj
#print axioms RvMBridge28.re_pow_eq
#print axioms RvMBridge28.re_inv_pow_eq
#print axioms RvMBridge28.pair_re_eq
#print axioms RvMBridge28.pow_add_inv_pow_eq_cosh
#print axioms RvMBridge28.sinh_mul_cos_sub_cosh_mul_sin_nonpos
#print axioms RvMBridge28.cosh_mul_cos_le_one
#print axioms RvMBridge28.cosh_mul_cos_le_one_of_abs_le
#print axioms RvMBridge28.arctan_le_self
#print axioms RvMBridge28.half_le_arctan
#print axioms RvMBridge28.abs_arctan
#print axioms RvMBridge28.wOf_re
#print axioms RvMBridge28.wOf_im
#print axioms RvMBridge28.normSq_sub_one
#print axioms RvMBridge28.normSq_eq_sq_add_sq
#print axioms RvMBridge28.wOf_re_pos
#print axioms RvMBridge28.abs_arg_wOf_eq
#print axioms RvMBridge28.abs_arg_wOf_le
#print axioms RvMBridge28.le_abs_arg_wOf
#print axioms RvMBridge28.abs_log_norm_wOf_le
#print axioms RvMBridge28.pair_re_nonneg_of_far
#print axioms RvMBridge28.pair_re_nonneg_of_on_line
#print axioms RvMBridge28.pair_re_nonneg_of_line_below
#print axioms RvMBridge28.liRe
#print axioms RvMBridge28.liRe_eq
#print axioms RvMBridge28.liRe_add_one_sub_conj
#print axioms RvMBridge28.hasSum_liRe
#print axioms RvMBridge28.liLimit_re_nonneg_of_pairs
#print axioms RvMBridge28.liLimit_re_nonneg_of_line_below
#print axioms RvMBridge28.archSide_add_finiteSide_re_nonneg_of_line_below
#print axioms RvMBridge28.liKernel_one
#print axioms RvMBridge28.liRe_one_nonneg
#print axioms RvMBridge28.liLimit_one_re_nonneg
#print axioms RvMBridge28.archSide_add_finiteSide_one_re_nonneg
#print axioms RvMBridge28.integral_shifted_mul_rpow_nonpos
#print axioms RvMBridge28.integral_fract_eq_shifted
#print axioms RvMBridge28.integrableOn_sawtooth
#print axioms RvMBridge28.integral_sawtooth_nonpos
#print axioms RvMBridge28.integral_fract_mul_rpow_le
#print axioms RvMBridge28.norm_integral_fract_cpow_le
#print axioms RvMBridge28.integral_fract_cpow_eq_of_zero
#print axioms RvMBridge28.zero_constraint
#print axioms RvMBridge28.zero_constraint_reflect
#print axioms RvMBridge28.box_one_sq
#print axioms RvMBridge28.box_one
#print axioms RvMBridge28.box_two
#print axioms RvMBridge28.one_sub_inv_eq_div_normSq
#print axioms RvMBridge28.liKernel_re_eq
#print axioms RvMBridge28.liLimit_re_nonneg_of_termwise
#print axioms RvMBridge28.re_pow_two
#print axioms RvMBridge28.re_pow_three
#print axioms RvMBridge28.re_pow_four
#print axioms RvMBridge28.re_pow_five
#print axioms RvMBridge28.ne_zero_of_nontrivial
#print axioms RvMBridge28.liKernel_two_re_nonneg
#print axioms RvMBridge28.liKernel_three_re_nonneg
#print axioms RvMBridge28.liKernel_four_re_nonneg
#print axioms RvMBridge28.liLimit_two_re_nonneg
#print axioms RvMBridge28.liLimit_three_re_nonneg
#print axioms RvMBridge28.liLimit_four_re_nonneg
#print axioms RvMBridge28.archSide_add_finiteSide_two_re_nonneg
#print axioms RvMBridge28.archSide_add_finiteSide_three_re_nonneg
#print axioms RvMBridge28.archSide_add_finiteSide_four_re_nonneg
#print axioms RvMBridge28.li5c0
#print axioms RvMBridge28.li5c1
#print axioms RvMBridge28.li5c2
#print axioms RvMBridge28.li5c3
#print axioms RvMBridge28.li5c4
#print axioms RvMBridge28.li5c4_nonneg
#print axioms RvMBridge28.li5c3_nonneg
#print axioms RvMBridge28.li5c2_nonneg
#print axioms RvMBridge28.li5c1_nonneg
#print axioms RvMBridge28.li5c0_nonneg
#print axioms RvMBridge28.rung5_identity
#print axioms RvMBridge28.liKernel_five_re_nonneg
#print axioms RvMBridge28.liLimit_five_re_nonneg
#print axioms RvMBridge28.archSide_add_finiteSide_five_re_nonneg
#print axioms RvMBridge29.cosh_mul_cos_le_one_window
#print axioms RvMBridge29.inv_add_inv_two_sq_le
#print axioms RvMBridge29.abs_arg_add_abs_log_le
#print axioms RvMBridge29.abs_arg_add_abs_log_le_sharp
#print axioms RvMBridge29.pair_re_nonneg_of_far_sharp
#print axioms RvMBridge29.pair_re_nonneg_of_line_below_sharp
#print axioms RvMBridge29.liLimit_re_nonneg_of_line_below_sharp
#print axioms RvMBridge29.archSide_add_finiteSide_re_nonneg_of_line_below_sharp
#print axioms RvMBridge30.re_gaussTest_I_half
#print axioms RvMBridge30.pole_floor
#print axioms RvMBridge30.bumpR_le'
#print axioms RvMBridge30.setIntegral_bumpR_le'
#print axioms RvMBridge30.psiR_mono
#print axioms RvMBridge30.serF_antitoneOn
#print axioms RvMBridge30.sum_serF_ge
#print axioms RvMBridge30.psiR_ge_series
#print axioms RvMBridge30.psiR_ge_rational
#print axioms RvMBridge30.eulerMascheroni_le
#print axioms RvMBridge30.psiR_floor_0
#print axioms RvMBridge30.psiR_floor_8
#print axioms RvMBridge30.cake_step
#print axioms RvMBridge30.cake_integral
#print axioms RvMBridge30.integral_bumpR_mul_psiR_ge_bands
#print axioms RvMBridge30.re_weilForm_gauss_nonneg_1e3
#print axioms RvMBridge30.gaussian_positivity_small_lam_1e3
#print axioms RvMBridge30.gaussian_positivity_small_lam_explicit_1e3
#print axioms RvMBridge30.gaussian_positivity_small_lam'
#print axioms RvMBridge30.integral_bumpR_mul_psiR_ge_bands12
#print axioms RvMBridge30.re_weilForm_gauss_nonneg_3e3
#print axioms RvMBridge30.gaussian_positivity_small_lam_3e3
#print axioms RvMBridge30.gaussian_positivity_small_lam_explicit_3e3
#print axioms Zeta23.RvM.N_eq_halfContour_completedZeta
#print axioms Zeta23.RvM.halfContour_completedZeta_split
#print axioms Zeta23.RvM.gamma_side
#print axioms Zeta23.RvM.backlund_horizontal
#print axioms Zeta23.RvM.vertical_two
#print axioms Zeta23.StirlingVert.mu_stirling
#print axioms Zeta23.thmA₀
#print axioms Zeta23.two_thirds_on_critical_line
#print axioms Zeta23.riemannVonMangoldt_zeta
#print axioms Zeta23.RvM.zeta_local_zero_count
#print axioms Zeta23.zetaSeam
#print axioms Zeta23.WeilEF.zeta_logDeriv_partial_fraction
#print axioms Zeta23.WeilEF.exists_far_point
#print axioms Zeta23.WeilEF.logDeriv_completedZeta
#print axioms Zeta23.WeilEF.logDeriv_completedZeta_one_sub
#print axioms Zeta23.StirlingVert.digamma_stirling
#print axioms Zeta23.RvM.riemannZeta_zeros_finite_of_isCompact
#print axioms Zeta23.WeilEF.EF_lit_zetaZeroConfig
#print axioms Zeta23.EF.paper_inversion
#print axioms Zeta23.WeilEF.gammaR_bracket
#print axioms Zeta23.WeilEF.integrable_mul_logDeriv_Gammaℝ_of_decay
#print axioms Zeta23.EF.integrable_fourier_of_contDiff_two
#print axioms DogfoodComplexReImSplit.e6b7_hre
#print axioms DogfoodComplexReImSplit.e6b7_hsq
#print axioms DogfoodComplexReImSplit.e6b7_hexp
#print axioms DogfoodComplexReImSplit.e6b7_hw2re
#print axioms DogfoodComplexReImSplit.e6b7_hw2im
#print axioms DogfoodComplexReImSplit.e6b7_heim
#print axioms DogfoodComplexReImSplit.e6b28_re_pow_two
#print axioms DogfoodComplexReImSplit.e6b28_re_pow_three
#print axioms DogfoodComplexReImSplit.e6b28_re_pow_four
#print axioms DogfoodComplexReImSplit.e6b28_re_pow_five
#print axioms DogfoodComplexReImSplit.e6b5_hcast
#print axioms DogfoodComplexReImSplit.e6b7_pair_hcast
#print axioms DogfoodComplexReImSplit.e6b7_pair_hre
#print axioms DogfoodComplexReImSplit.e6b11_arch_hcast
#print axioms DogfoodComplexReImSplit.e6b14_centre_hcast

#print axioms DogfoodZeroSumMajorant.zbound_regen_strip
#print axioms DogfoodZeroSumMajorant.zbound_regen_le
#print axioms DogfoodZeroSumMajorant.zbound_regen_summable
#print axioms DogfoodZeroSumMajorant.polBound_regen_strip
#print axioms DogfoodZeroSumMajorant.polBound_regen_le
#print axioms DogfoodZeroSumMajorant.polBound_regen_summable
#print axioms DogfoodZeroSumMajorant.liBound_regen_strip
#print axioms DogfoodZeroSumMajorant.liBound_regen_le
#print axioms DogfoodZeroSumMajorant.liBound_regen_summable
#print axioms DogfoodZeroSumMajorant.tail_regen_envelope
#print axioms DogfoodZeroSumMajorant.tail_regen_rate

-- ZhuEnvelope (2026-09-23): Zhu Lemma 3.1, the digamma envelope, PROVED.  conjecture1_proved = False.
#print axioms RvMBridgeZhu.psiR_ge_stirling
#print axioms RvMBridgeZhu.psiR_ge_envelope
#print axioms RvMBridgeZhu.envelopeBound

-- ZhuSymbol (2026-09-23): Zhu eq. (2), the symbol representation, PROVED.  conjecture1_proved = False.
#print axioms RvMBridgeZhu.autocorr_eq_zero_of_two_mul_le
#print axioms RvMBridgeZhu.symbol_representation_ofReal
#print axioms RvMBridgeZhu.symbolRepresentation
#print axioms RvMBridgeZhu.symbolRepresentationOdd

-- ZhuLegendre (2026-09-23): Zhu eqs. (6) and (12), PROVED.  conjecture1_proved = False.
#print axioms RvMBridgeZhu.integral_one_sub_sq_pow
#print axioms RvMBridgeZhu.sphericalBessel_abs_le
#print axioms RvMBridgeZhu.integral_legendreP_mul_cos
#print axioms RvMBridgeZhu.legendreModeFT_eq
#print axioms RvMBridgeZhu.legendreModeFT_abs_le
#print axioms RvMBridgeZhu.integral_legendreP_mul_sin
#print axioms RvMBridgeZhu.legendreModeFTs_eq
#print axioms RvMBridgeZhu.legendreModeFTs_abs_le

-- ZhuParity (2026-09-23): Zhu Lemma 6.1, parity decoupling, PROVED.  conjecture1_proved = False.
#print axioms RvMBridgeZhu.weilForm_eq_zero_of_odd
#print axioms RvMBridgeZhu.Q_add_of_cross_odd
#print axioms RvMBridgeZhu.Q_add_I_mul
#print axioms RvMBridgeZhu.Q_evenPart_add_oddPart
#print axioms RvMBridgeZhu.windowFloor_of_sectors

-- ZhuSplit (2026-09-23): the envelope step of eq. (4), PROVED.  conjecture1_proved = False.
#print axioms RvMBridgeZhu.comb_le_combMass
#print axioms RvMBridgeZhu.weilSymbol_ge_betaStar

-- ZhuOrtho (2026-09-23): Legendre orthonormality, uniform bounds, pole vectors.  conjecture1_proved = False.
#print axioms RvMBridgeZhu.integral_legendreP_sq
#print axioms RvMBridgeZhu.integral_legendreMode_sq
#print axioms RvMBridgeZhu.legendreModeFT_abs_le_uniform
#print axioms RvMBridgeZhu.poleVec_abs_le
#print axioms RvMBridgeZhu.poleVecOdd_abs_le

-- ZhuTail (2026-09-23): the eq. (13) tail data PROVED with closed-form constants.  conjecture1_proved = False.
#print axioms RvMBridgeZhu.abs_weilSymbol_sub_betaStar_le
#print axioms RvMBridgeZhu.tail_tsum_le
#print axioms RvMBridgeZhu.localization_of_bounds
#print axioms RvMBridgeZhu.legendreLocalization_of_cut
#print axioms RvMBridgeZhu.legendreLocalizationOdd_of_cut

-- ZhuInstance (2026-09-23): the instance L = 4/5, T# = 200, N = 200.  conjecture1_proved = False.
#print axioms RvMBridgeZhu.combMass_L08_le
#print axioms RvMBridgeZhu.betaStar_L08_T200_ge_half
#print axioms RvMBridgeZhu.legendreLocalization_L08_T200
#print axioms RvMBridgeZhu.legendreLocalizationOdd_L08_T200
#print axioms RvMBridgeZhu.eps_sum_lt_betaStar_L08_T200

-- KWin (2026-09-24): the prime-free window at 2L = log 2 on the goal node's FULL class (pole terms
-- kept), certified with no Arb seam: exact-rational symbol minorant and head certificate evaluated
-- by the kernel (decide +kernel), projection tail, Zhu split.  WindowFloor(log 2 / 2, 9/10000).
-- A finite-window statement, NOT RH; PR #604: the 1.3e-3 margin is zero content; not
-- Connes-Consani (pole-free class).  conjecture1_proved = False.
#print axioms KWin.gamma_le
#print axioms KWin.log_pi_le
#print axioms KWin.beta0_le_betaStar
#print axioms KWin.combMass_L0
#print axioms KWin.weilSymbol_L0
#print axioms KWin.abs_Psi_sub_beta0_le
#print axioms KWin.psdCert_sound
#print axioms KWin.cert_even
#print axioms KWin.cert_odd
#print axioms KWin.cert_even_negative_control
#print axioms KWin.ginv_even
#print axioms KWin.ginv_odd
#print axioms KWin.piece_ok
#print axioms KWin.tail_even
#print axioms KWin.tail_odd
#print axioms KWin.Tr_sub_le
#print axioms KWin.Pl_sub_le
#print axioms KWin.A1_sq_le
#print axioms KWin.lor_taylor
#print axioms KWin.wpoly_le_Psi
#print axioms KWin.head_floor
#print axioms KWin.Rb_floor
#print axioms KWin.Q_ge_Rb
#print axioms KWin.evenSectorFloor
#print axioms KWin.oddSectorFloor
#print axioms KWin.windowFloor_L0
#print axioms KWin.kwin_primeFreeWindow
#print axioms KWin.kwin_primeFreeWindowArch

-- E6Bridge31: the prime-free window (2026-09-23). conjecture1_proved = False.
#print axioms RvMBridge31.primeSide_autocorr_eq_zero
#print axioms RvMBridge31.weilForm_autocorr_eq_archSide
#print axioms RvMBridge31.norm_autocorr_le
#print axioms RvMBridge31.integral_hsq
#print axioms RvMBridge31.sq_l1_le
#print axioms RvMBridge31.hsq_le
#print axioms RvMBridge31.re_poles_ge
#print axioms RvMBridge31.re_poles_ge_of_le
#print axioms RvMBridge31.integral_mul_psiR_ge_bands
#print axioms RvMBridge31.re_archSide_autocorr_ge
#print axioms RvMBridge31.weil_positivity_narrow_support_of_nonneg
#print axioms RvMBridge31.weil_positivity_narrow_support
#print axioms RvMBridge31.primeFreeWindow_iff_arch
#print axioms RvMBridge31.primeFreeWindow_imp_poleFree
#print axioms RvMBridge31.poles_vanish
#print axioms RvMBridge31.archSide_autocorr_poleFree

-- E6Bridge32: u-space part 1 (2026-09-23). conjecture1_proved = False.
#print axioms RvMBridge32.integral_expK_mul_cexp
#print axioms RvMBridge32.pairing
#print axioms RvMBridge32.integral_hsq_mul_lor
#print axioms RvMBridge32.psiR_ge_finite
#print axioms RvMBridge32.re_arch_integral_ge

-- E6Bridge33: u-space part 2 (2026-09-23). conjecture1_proved = False.
#print axioms RvMBridge33.integral_compl_Icc_expK_ge
#print axioms RvMBridge33.integral_autocorr_mul_expK
#print axioms RvMBridge33.Eb_eq_half
#print axioms RvMBridge33.Rfun_ge
#print axioms RvMBridge33.Eb_ge

-- E6Bridge34: the window at L <= 1/10 (2026-09-23). conjecture1_proved = False.
#print axioms RvMBridge34.re_poles_ge_sq
#print axioms RvMBridge34.arch_ge_series
#print axioms RvMBridge34.FN_tenth_ge
#print axioms RvMBridge34.re_archSide_autocorr_ge_tenth
#print axioms RvMBridge34.weil_positivity_window_tenth_of_nonneg
#print axioms RvMBridge34.weil_positivity_window_tenth

-- Mirrormere prime-free window (kernel-native, KWin)
#print axioms kwin_primeFreeWindowPositivity
#print axioms kwin_primeFreeWindowArchPositivity
#print axioms weil_positivity_prime_free_window
#print axioms weil_positivity_window_tenth_of_prime_free

-- KWin2: the window certificate PAST the prime-free boundary (2026-09-24), parametric in the window;
-- first instance L = 2/5 (2L = 0.8 > log 2: the prime comb term n = 2 is present).  Kernel-native,
-- no Arb seam.  A finite-window statement, NOT RH; not Connes-Consani (pole terms kept); cf. PR #604.
-- conjecture1_proved = False.
#print axioms KWin2.sym_minorant
#print axioms KWin2.comb_le_combPoly
#print axioms KWin2.wpoly_le_Psi
#print axioms KWin2.head_floor
#print axioms KWin2.Rb_floor
#print axioms KWin2.weilSymbol_eq_two
#print axioms KWin2.Q_ge_Rb
#print axioms KWin2.certE25
#print axioms KWin2.certO25
#print axioms KWin2.certE25_negative_control
#print axioms KWin2.log2_near25
#print axioms KWin2.c2_near25
#print axioms KWin2.beta0_le_betaStar25
#print axioms KWin2.symHyp25
#print axioms KWin2.evenSectorFloor25
#print axioms KWin2.oddSectorFloor25
#print axioms KWin2.windowFloor25
#print axioms KWin2.weil_positivity_window_two_fifths
#print axioms KWin2.weil_positivity_prime_free_window_of_two_fifths
-- KWin2 generic assembly (any window with log 2 < 2L <= log 3) and the rounded PSD checker.
#print axioms KWin2.windowFloor_of_cert
#print axioms KWin2.weil_positivity_of_windowFloor
#print axioms KWin2.headPSD_of_psdCertR
#print axioms KWin2.gamma_le32
-- KWin2 registry-shape bridge at L = 2/5 (explicit binders, 2L <= 4/5).
#print axioms weil_positivity_window_two_fifths
#print axioms weil_window_floor_two_fifths

-- ZhuEnvelope (2026-09-23): Zhu Lemma 3.1, the digamma envelope, PROVED.  conjecture1_proved = False.

-- ZhuSymbol (2026-09-23): Zhu eq. (2), the symbol representation, PROVED.  conjecture1_proved = False.

-- ZhuLegendre (2026-09-23): Zhu eqs. (6) and (12), PROVED.  conjecture1_proved = False.

-- ZhuParity (2026-09-23): Zhu Lemma 6.1, parity decoupling, PROVED.  conjecture1_proved = False.

-- ZhuSplit (2026-09-23): the envelope step of eq. (4), PROVED.  conjecture1_proved = False.

-- ZhuOrtho (2026-09-23): Legendre orthonormality, uniform bounds, pole vectors.  conjecture1_proved = False.

-- ZhuTail (2026-09-23): the eq. (13) tail data PROVED with closed-form constants.  conjecture1_proved = False.

-- ZhuInstance (2026-09-23): the instance L = 4/5, T# = 200, N = 200.  conjecture1_proved = False.
-- FamilyWeilForm: the parametric degree-<= 2 Weil form (2026-09-25). conjecture1_proved = False.
#print axioms FamilyWeil.psiShift_zero
#print axioms FamilyWeil.psiShift_one
#print axioms FamilyWeil.symbolArch_zeta
#print axioms FamilyWeil.weilFormF_zeta
#print axioms FamilyWeil.autocorr_pair_eq_zero
#print axioms FamilyWeil.primeSideF_autocorr_eq_fin
#print axioms FamilyWeil.primeSideF_congr_window
#print axioms FamilyWeil.archSideF_congr
#print axioms FamilyWeil.weilFormF_eq_zero_logq_add
#print axioms FamilyWeil.re_weilFormF_autocorr_eq
#print axioms FamilyWeil.re_weilFormF_autocorr_mono_logq

-- FamilyWeilDisc: fundamental discriminants, Kronecker symbols (2026-09-25). conjecture1_proved = False.
#print axioms FamilyWeil.sqfreeChk_iff
#print axioms FamilyWeil.isFundDisc_iff
#print axioms FamilyWeil.IsFundDisc.ne_zero
#print axioms FamilyWeil.IsFundDisc.natAbs_pos
#print axioms FamilyWeil.kron2_eq_χ₈
#print axioms FamilyWeil.kronSym_two
#print axioms FamilyWeil.kronSym_three
#print axioms FamilyWeil.kronSym_five
#print axioms FamilyWeil.kron2_mem
#print axioms FamilyWeil.kron3_mem
#print axioms FamilyWeil.kron5_mem
#print axioms FamilyWeil.Tri.toInt_ofInt
#print axioms FamilyWeil.mem_triList
#print axioms FamilyWeil.signed_natAbs

-- FamilyWeilQuad: zeta_K's form, log|d| monotonicity, the d_min reduction (2026-09-25). conjecture1_proved = False.
#print axioms FamilyWeil.weightQ_prime_pow
#print axioms FamilyWeil.weightQ_eq_cellWeight
#print axioms FamilyWeil.cellWeight_congr
#print axioms FamilyWeil.symbolArch_quad
#print axioms FamilyWeil.cellForm_congr
#print axioms FamilyWeil.weilFormQ_autocorr_eq
#print axioms FamilyWeil.re_weilFormQ_autocorr_eq
#print axioms FamilyWeil.cellForm_eq_of_inCell
#print axioms FamilyWeil.re_weilFormQ_mono
#print axioms FamilyWeil.windowPos_iff
#print axioms FamilyWeil.WindowPosX.mono
#print axioms FamilyWeil.cell_reduction
#print axioms FamilyWeil.cell_reduction_nat
#print axioms FamilyWeil.reduction_of_entry

-- FamilyWeilTable: the kernel-checked d_min tables at N = 4 and N = 7 (2026-09-25). conjecture1_proved = False.
#print axioms FamilyWeil.inCell4_iff
#print axioms FamilyWeil.isCellMin_of_B4
#print axioms FamilyWeil.table4_check
#print axioms FamilyWeil.table4_spec
#print axioms FamilyWeil.family4_of_table
#print axioms FamilyWeil.table4_mem
#print axioms FamilyWeil.family4_of_dmins
#print axioms FamilyWeil.family4_of_dmins_nat
#print axioms FamilyWeil.family4_of_cells
#print axioms FamilyWeil.inCell7_iff
#print axioms FamilyWeil.isCellMin_of_B7
#print axioms FamilyWeil.table7_check
#print axioms FamilyWeil.table7_spec
#print axioms FamilyWeil.family7_of_table
#print axioms FamilyWeil.table7_mem
#print axioms FamilyWeil.family7_of_dmins
#print axioms FamilyWeil.family7_of_dmins_nat
#print axioms FamilyWeil.family7_of_cells

-- Archimedean conceptual programme (Connes-Consani route), stages S1 and S2 (2026-10-11).
#print axioms ArchS1.hasSum_archK
#print axioms ArchS1.tsum_expK_kb
#print axioms ArchS1.tendsto_kTrunc
#print axioms ArchS1.archK_eq_tau
#print axioms ArchS1.tendsto_phiN
#print axioms ArchS1.tendsto_cN
#print axioms ArchS1.truncated_identity
#print axioms ArchS1.integrable_dirichlet
#print axioms ArchS1.arch_integral_dirichlet
#print axioms ArchS1.archSide_autocorr_dirichlet_identity
#print axioms ArchS1.archSide_autocorr_dirichlet_identity'
#print axioms ArchS1.archSide_autocorr_dirichlet_identity_poleFree
#print axioms ArchS1.weilForm_autocorr_dirichlet_identity
#print axioms ArchS2.paperFT_I_half
#print axioms ArchS2.paperFT_zero
#print axioms ArchS2.contDiff_expHalf
#print axioms ArchS2.contDiff_expNegHalf
#print axioms ArchS2.contDiff_tilt
#print axioms ArchS2.continuous_tilt
#print axioms ArchS2.hasDerivAt_expHalf
#print axioms ArchS2.expHalf_mul_expNegHalf
#print axioms ArchS2.hasDerivAt_tiltPrim
#print axioms ArchS2.deriv_tiltPrim
#print axioms ArchS2.contDiff_tiltPrim
#print axioms ArchS2.hasDerivAt_qLift
#print axioms ArchS2.qLift_rel
#print axioms ArchS2.tilt_eq_zero_of_not_mem
#print axioms ArchS2.qLift_eq_zero_left
#print axioms ArchS2.tiltPrim_eq_right
#print axioms ArchS2.qLift_eq_zero_right
#print axioms ArchS2.tsupport_qLift
#print axioms ArchS2.isWeilTest_qLift
#print axioms ArchS2.integrable_mul_phase
#print axioms ArchS2.hasDerivAt_phase
#print axioms ArchS2.differentiable_of_test
#print axioms ArchS2.contDiff_deriv_of_test
#print axioms ArchS2.paperFT_deriv
#print axioms ArchS2.paperFT_lift
#print axioms ArchS2.poleFree_of_lift
#print axioms ArchS2.tsupport_lift_subset
#print axioms ArchS2.isWeilTest_of_lift
#print axioms ArchS2.tsupport_of_lift
#print axioms ArchS2.poleFree_iff_exists_lift
#print axioms ArchS2.hasDerivAt_expNegHalf
#print axioms ArchS2.lift_unique
#print axioms ArchS2.hsq_lift
#print axioms ArchS2.integral_lift
#print axioms ArchS2.paperFT_zero_lift_iff
#print axioms ArchS2.poles_vanish_of_lift
#print axioms ArchS2.archSide_autocorr_lift
#print axioms ArchS2.poleFree_window_lift

-- Archimedean conceptual programme, stages S3, S4, S5, S8, S9 and the S3+S4 pipeline rung (2026-10-11).
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
#print axioms ArchS3.Lfun_eq_integral_ell
#print axioms ArchS3.archW_eq_dirichlet
#print axioms ArchS3.Lfun_eq_dirichlet
#print axioms ArchS3.re_archSide_eq_poles_add_archW
#print axioms ArchS3.re_weilForm_eq_archW
#print axioms ArchS3.Lfun_nonneg_of_ell_nonneg
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
#print axioms ArchS3.norm_Gpart_le
#print axioms ArchS3.PhiE_add_Gpart
#print axioms ArchS3.norm_PhiE_le
#print axioms ArchS3.tendsto_PhiE
#print axioms ArchS3.norm_Phi_le
#print axioms ArchS3.tendsto_integral_Psi
#print axioms ArchS3.tendsto_integral_Phi
#print axioms ArchS3.integrableOn_normSq_Phi
#print axioms ArchS3.Nnorm_nonneg
#print axioms ArchS3.stepA
#print axioms ArchS3.kernel_eq
#print axioms ArchS3.subst_swap
#print axioms ArchS3.stepC1
#print axioms ArchS3.stepC2
#print axioms ArchS3.stepB
#print axioms ArchS3.damped_identity
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
#print axioms ArchS3.ell_eq_Nnorm
#print axioms ArchS3.ell_nonneg
#print axioms ArchS3.Lfun_eq_integral_Nnorm
#print axioms ArchS3.cc_cor_2_3
#print axioms ArchS3.cc_cor_2_3_dirichlet
#print axioms cc_cor_2_3
#print axioms ArchS3.weilForm_add_Dfun_nonneg
#print axioms ArchS4.integral_sq_pow
#print axioms ArchS4.abs_mom_le
#print axioms ArchS4.abs_Sm_one
#print axioms ArchS4.abs_Cm_two
#print axioms ArchS4.hasDerivAt_alphaE
#print axioms ArchS4.hasDerivAt_betaE
#print axioms ArchS4.hasDerivAt_FE
#print axioms ArchS4.hasDerivAt_FE1
#print axioms ArchS4.deltaE_eq_FE
#print axioms ArchS4.hasDerivAt_expHalfR
#print axioms ArchS4.deriv_deltaE_eq
#print axioms ArchS4.deriv_deriv_deltaE
#print axioms ArchS4.kappaD_eq
#print axioms ArchS4.exp_le_of_small
#print axioms ArchS4.abs_kappaD_le
#print axioms ArchS4.integrable_normSq_test
#print axioms ArchS4.norm_autocorr_le
#print axioms ArchS4.autocorr_eq_zero_of_far
#print axioms ArchS4.DQ_nonpos
#print axioms ArchS4.DQ_nonpos_poleFree
#print axioms ArchS4.weil_nonneg_of_CC_cor23
#print axioms ArchS4.ae_sq
#print axioms ArchS4.continuous_momIntegrand
#print axioms ArchS4.norm_momIntegrand_le
#print axioms ArchS4.integrable_momIntegrand
#print axioms ArchS4.hasDerivAt_mom
#print axioms ArchS4.mom_neg
#print axioms ArchS4.hasDerivAt_Cm
#print axioms ArchS4.hasDerivAt_Sm
#print axioms ArchS4.deriv_Cm
#print axioms ArchS4.deriv_Sm
#print axioms ArchS4.contDiff_moments
#print axioms ArchS4.contDiff_Cm
#print axioms ArchS4.contDiff_ccS
#print axioms ArchS4.hasDerivAt_ccS
#print axioms ArchS4.sq_univ
#print axioms ArchS4.ccS_zero
#print axioms ArchS4.Sm_one_zero
#print axioms ArchS4.inner_ftc
#print axioms ArchS4.ccS_add_mul_deriv
#print axioms ArchS4.integral_cos_mul_eq_sinc
#print axioms ArchS4.integral_cos_four_pi
#print axioms ArchS4.contDiff_deltaE
#print axioms ArchS4.deltaE_zero
#print axioms ArchS4.hasDerivAt_deltaE
#print axioms ArchS4.deriv_deltaE_zero
#print axioms ArchS4.contDiff_one_of_test
#print axioms ArchS4.isWeilTest_deriv
#print axioms ArchS4.hasCompactSupport_conj
#print axioms ArchS4.integrable_shift_conj
#print axioms ArchS4.autocorr_eq_shift
#print axioms ArchS4.hasDerivAt_shift
#print axioms ArchS4.hasDerivAt_conj
#print axioms ArchS4.integral_shift_mul_conj_deriv
#print axioms ArchS4.autocorr_fun_eq
#print axioms ArchS4.integrable_conj_test
#print axioms ArchS4.deriv_autocorr
#print axioms ArchS4.deriv_deriv_autocorr
#print axioms ArchS4.autocorr_lift
#print axioms ArchS4.autocorr_zero
#print axioms ArchS4.mass_lift
#print axioms ArchS4.exists_far
#print axioms ArchS4.integral_eq_interval
#print axioms ArchS4.interval_fold
#print axioms ArchS4.contDiff_two_parts
#print axioms ArchS4.jump_ibp
#print axioms ArchS4.contDiff_two_deltaE
#print axioms ArchS4.jump_lemma_general
#print axioms ArchS4.jump_lemma
#print axioms ArchS4.continuous_kappaD
#print axioms ArchS4.kappaD_neg
#print axioms ArchS4.KdeltaI_symm
#print axioms ArchS4.continuous_KdeltaI
#print axioms ArchS4.memLp_KdeltaI
#print axioms ArchS4.integrable_sq_KdeltaI
#print axioms ArchS4.zero_of_not_mem
#print axioms ArchS4.autocorr_pairing_eq_box
#print axioms ArchS4.jump_lemma_window
#print axioms ArchS4.jump_lemma_poleFree
#print axioms ArchS4.ccS_eq_sincInt
#print axioms ArchS4.deltaK_eq_deltaE
#print axioms ArchS4.S3_Dfun_eq
#print axioms ArchS4.S3_Dfun_nonpos_poleFree
#print axioms ArchS4.weil_nonneg_of_Lfun_nonneg
#print axioms ArchS4.weil_nonneg_of_ell_nonneg
#print axioms ArchS5.eLpNorm_two_sq
#print axioms ArchS5.kernelApply_congr_right
#print axioms ArchS5.kernelApply_congr_left_of_ae_ae
#print axioms ArchS5.kernelApply_congr_left
#print axioms ArchS5.enorm_kernelApply_le
#print axioms ArchS5.lintegral_eLpNorm_section_sq
#print axioms ArchS5.eLpNorm_kernelApply_le
#print axioms ArchS5.stronglyMeasurable_kernelApply
#print axioms ArchS5.memLp_kernelApply
#print axioms ArchS5.ae_memLp_section
#print axioms ArchS5.ae_integrable_section_mul
#print axioms ArchS5.kernelApply_add_right
#print axioms ArchS5.kernelApply_smul_right
#print axioms ArchS5.kernelApply_add_left
#print axioms ArchS5.kernelApply_smul_left
#print axioms ArchS5.memLp_kernelApply_Lp
#print axioms ArchS5.intOpAux_ae_eq
#print axioms ArchS5.norm_intOpAux_le
#print axioms ArchS5.intOpAux_add_right
#print axioms ArchS5.intOpAux_smul_right
#print axioms ArchS5.intOpAux_add_left
#print axioms ArchS5.intOpAux_smul_left
#print axioms ArchS5.intOp_apply
#print axioms ArchS5.intOp_ae_eq
#print axioms ArchS5.intOp_apply_eq_iff
#print axioms ArchS5.norm_intOp_apply_le
#print axioms ArchS5.norm_intOp_le
#print axioms ArchS5.norm_intOpL_le
#print axioms ArchS5.intOp_add
#print axioms ArchS5.intOp_sub
#print axioms ArchS5.intOp_neg
#print axioms ArchS5.intOp_smul
#print axioms ArchS5.norm_intOp_sub_le
#print axioms ArchS5.lipschitzWith_intOp
#print axioms ArchS5.continuous_intOp
#print axioms ArchS5.eLpNorm_two_tensor
#print axioms ArchS5.memLp_two_tensor
#print axioms ArchS5.memLp_conj
#print axioms ArchS5.integrable_conj_mul_kernel_mul
#print axioms ArchS5.inner_intOp_eq_integral
#print axioms ArchS5.inner_intOp_left_eq_integral
#print axioms ArchS5.memLp_kernelAdjoint
#print axioms ArchS5.kernelAdjoint_ae_eq
#print axioms ArchS5.inner_intOp_kernelAdjoint
#print axioms ArchS5.adjoint_intOp
#print axioms ArchS5.kernelAdjoint_kernelAdjoint
#print axioms ArchS5.kernelAdjoint_eq_self
#print axioms ArchS5.isSelfAdjoint_intOp
#print axioms ArchS5.isSymmetric_intOp
#print axioms ArchS5.intOp_indicator_rect
#print axioms ArchS5.isCompactOperator_rankOne
#print axioms ArchS5.isCompactOperator_intOp_rect
#print axioms ArchS5.indicatorConstLp_compl_eq
#print axioms ArchS5.isCompactOperator_intOp_indicator
#print axioms ArchS5.isCompactOperator_intOp
#print axioms ArchS5.abs_iSup_sub_iSup_le
#print axioms ArchS5.abs_iInf_sub_iInf_le
#print axioms ArchS5.bddAbove_rayleighQuotient
#print axioms ArchS5.bddBelow_rayleighQuotient
#print axioms ArchS5.rayleighQuotient_le_topEig
#print axioms ArchS5.re_inner_le_topEig_mul
#print axioms ArchS5.le_topEig_of
#print axioms ArchS5.topEig_le_of_forall
#print axioms ArchS5.topEig_le_of_forall'
#print axioms ArchS5.topEig_eq_iSup_sphere
#print axioms ArchS5.abs_topEig_le_norm
#print axioms ArchS5.rayleighQuotient_sub_le
#print axioms ArchS5.abs_topEig_sub_le
#print axioms ArchS5.topEig_le_add_norm_sub
#print axioms ArchS5.topEig_mono
#print axioms ArchS5.norm_sq_apply_le_of_nonneg
#print axioms ArchS5.exists_eigenvector_topEig
#print axioms ArchS5.hasEigenvalue_topEig
#print axioms ArchS5.exists_isMaxOn_sphere
#print axioms ArchS5.eigenvalue_le_topEig
#print axioms ArchS5.rayleighInf_le
#print axioms ArchS5.abs_rayleighInf_le
#print axioms ArchS5.bddAbove_rayleighInf
#print axioms ArchS5.abs_rayleighInf_sub_le
#print axioms ArchS5.abs_minmaxEig_sub_le
#print axioms ArchS5.minmaxEig_le_add_norm_sub
#print axioms ArchS5.abs_minmaxEig_le_norm
#print axioms ArchS5.exists_ne_zero_of_finrank_pos
#print axioms ArchS5.le_minmaxEig
#print axioms ArchS5.exists_mem_orthogonal_of_finrank_lt
#print axioms ArchS5.minmaxEig_le
#print axioms ArchS5.minmaxEig_eq_of_bounds
#print axioms ArchS5.rayleighInf_span_singleton
#print axioms ArchS5.minmaxEig_one
#print axioms ArchS5.abs_topEig_intOp_sub_le
#print axioms ArchS5.abs_minmaxEig_intOp_sub_le
#print axioms ArchS5.intOp_orthogonalComplement_iSup_eigenspaces_eq_bot
#print axioms ArchS5.finiteDimensional_eigenspace_intOp
#print axioms ArchS5.exists_eigenvector_topEig_intOp
#print axioms ArchS5.volI_prod
#print axioms ArchS5.ae_mem_Icc_prod
#print axioms ArchS5.memLp_of_continuous
#print axioms ArchS5.kernelOfContinuous_ae_eq
#print axioms ArchS5.intOp_kernelOfContinuous_ae_eq
#print axioms ArchS5.kernelOfContinuous_sub
#print axioms ArchS5.norm_kernelOfContinuous_le
#print axioms ArchS5.abs_topEig_kernelOfContinuous_sub_le
#print axioms ArchS5.abs_minmaxEig_kernelOfContinuous_sub_le
#print axioms ArchS5.isHermitianKernel_kernelOfContinuous
#print axioms ArchS5.intOp_kernelOfContinuous_compact_selfAdjoint
#print axioms ArchS5.kernelApply_eq_inner_sectionConj
#print axioms ArchS5.norm_sectionConj
#print axioms ArchS5.enorm_kernelApply_sq_eq
#print axioms ArchS5.ofReal_norm_sectionConj_sq
#print axioms ArchS5.sum_enorm_kernelApply_sq_le
#print axioms ArchS5.sum_eLpNorm_intOp_sq_le
#print axioms ArchS5.norm_sq_eq_toReal_eLpNorm
#print axioms ArchS5.sum_norm_intOp_sq_le
#print axioms ArchS5.summable_norm_intOp_sq
#print axioms ArchS5.tsum_norm_intOp_sq_le
#print axioms ArchS5.hasSum_norm_inner_sq
#print axioms ArchS5.tsum_enorm_kernelApply_sq_eq
#print axioms ArchS5.tsum_eLpNorm_intOp_sq_eq
#print axioms ArchS5.hasSum_norm_intOp_sq
#print axioms ArchS5.norm_eigen
#print axioms ArchS5.sum_eigenvalue_sq_le
#print axioms ArchS5.summable_eigenvalue_sq
#print axioms ArchS5.tsum_eigenvalue_sq_le
#print axioms ArchS5.tsum_real_eigenvalue_sq_le
#print axioms ArchS5.card_mul_sq_le_of_eigen
#print axioms ArchS5.tsum_eigenvalue_sq_compl_le
#print axioms ArchS5.re_inner_sum_eigen
#print axioms ArchS5.norm_sum_sq_orthonormal
#print axioms ArchS5.card_le_of_eigen_gt
#print axioms ArchS5.card_le_of_eigen_gt_intOp
#print axioms ArchS5.tensorKernel_ae_eq
#print axioms ArchS5.intOp_tensorKernel
#print axioms ArchS5.intOp_tensorKernel_mem_span
#print axioms ArchS5.intOp_sum_tensorKernel_mem_span
#print axioms ArchS5.card_le_of_eigen_gt_tensor
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
#print axioms ArchPipeline.weil_nonneg_pole_free_eightieth

-- Archimedean programme: S6 (Sonin/prolate structure) and the S6+S9 certified prolate spectrum (2026-10-11).
#print axioms ArchS6.IsOrthProj.compl
#print axioms ArchS6.IsOrthProj.inner_sub_eq_zero
#print axioms ArchS6.IsOrthProj.norm_sq_eq
#print axioms ArchS6.IsOrthProj.norm_le
#print axioms ArchS6.IsOrthProj.eq_zero_of_norm_compl
#print axioms ArchS6.IsOrthProj.inner_eq_zero_of
#print axioms ArchS6.IsOrthProj.re_inner_self
#print axioms ArchS6.hasSum_mem
#print axioms ArchS6.exists_hasSum_orthonormal
#print axioms ArchS6.ProjPair.PhatPP_apply
#print axioms ArchS6.ProjPair.isOrthProj_P₁
#print axioms ArchS6.ProjPair.isOrthProj_hatP₁
#print axioms ArchS6.ProjPair.isOrthProj_P
#print axioms ArchS6.ProjPair.isOrthProj_hatP
#print axioms ArchS6.ProjPair.norm_F
#print axioms ArchS6.ProjPair.inner_F_F
#print axioms ArchS6.ProjPair.mem_sonin
#print axioms ArchS6.ProjPair.mem_sonin_iff_hatP₁
#print axioms ArchS6.ProjPair.isClosed_sonin
#print axioms ArchS6.ProjPair.mem_sonin_iff_fixed
#print axioms ArchS6.ProjPair.re_inner_PhatPP
#print axioms ArchS6.ProjPair.re_inner_PhatPP_le
#print axioms ArchS6.ProjPair.PhatPP_of_P₁_eq
#print axioms ArchS6.ProjPair.inner_PhatPP
#print axioms ArchS6.ProlateBasis.lam_sq_lt_one
#print axioms ArchS6.ProlateBasis.s_pos
#print axioms ArchS6.ProlateBasis.s_sq
#print axioms ArchS6.ProlateBasis.norm_ξ
#print axioms ArchS6.ProlateBasis.norm_η
#print axioms ArchS6.ProlateBasis.P₁_η
#print axioms ArchS6.ProlateBasis.ψ_eq
#print axioms ArchS6.ProlateBasis.η_eq
#print axioms ArchS6.ProlateBasis.P₁_ψ
#print axioms ArchS6.ProlateBasis.P_ψ
#print axioms ArchS6.ProlateBasis.P_ξ
#print axioms ArchS6.ProlateBasis.inner_ξ_ψ
#print axioms ArchS6.ProlateBasis.inner_ψ_ξ
#print axioms ArchS6.ProlateBasis.inner_η_η
#print axioms ArchS6.ProlateBasis.inner_ψ_ψ'
#print axioms ArchS6.ProlateBasis.inner_ψ_ψ
#print axioms ArchS6.ProlateBasis.norm_ψ
#print axioms ArchS6.ProlateBasis.ψ_eq_ζ
#print axioms ArchS6.ProlateBasis.η_eq_ζ
#print axioms ArchS6.ProlateBasis.orthonormal_ζ
#print axioms ArchS6.ProlateBasis.P₁_ζ
#print axioms ArchS6.ProlateBasis.P_ζ
#print axioms ArchS6.ProlateBasis.inner_ξ_ζ
#print axioms ArchS6.ProlateBasis.inner_ζ_ξ
#print axioms ArchS6.ProlateBasis.hatP₁_ξ
#print axioms ArchS6.ProlateBasis.hatP₁_ξ'
#print axioms ArchS6.ProlateBasis.P₁hatP₁P₁_ξ
#print axioms ArchS6.ProlateBasis.F_ψ
#print axioms ArchS6.ProlateBasis.PhatPP_ψ
#print axioms ArchS6.ProlateBasis.PhatPP_ζ
#print axioms ArchS6.ProlateBasis.inner_sonin_ξ
#print axioms ArchS6.ProlateBasis.inner_sonin_η
#print axioms ArchS6.ProlateBasis.inner_sonin_ψ
#print axioms ArchS6.ProlateBasis.inner_sonin_ζ
#print axioms ArchS6.ProlateBasis.inner_ζ_sonin
#print axioms ArchS6.ProlateBasis.mem_sonin_of_orthogonal
#print axioms ArchS6.ProlateBasis.hasSum_P₁
#print axioms ArchS6.ProlateBasis.hasSum_hatP₁_P₁
#print axioms ArchS6.ProlateBasis.hasSum_hatP₁_P₁'
#print axioms ArchS6.ProlateBasis.soninProj_mem
#print axioms ArchS6.ProlateBasis.sub_soninProj_mem
#print axioms ArchS6.ProlateBasis.hasSum_PhatPP
#print axioms ArchS6.ProlateBasis.hasSum_inner_PhatPP
#print axioms ArchS6.ProlateBasis.tsum_le_inner_PhatPP
#print axioms ArchS6.ProlateBasis.inner_ξ_A_ξ
#print axioms ArchS6.integral_smul_fourier_Lp
#print axioms ArchS6.integral_smul_fourierInv_Lp
#print axioms ArchS6.integral_fourier_smul_eq
#print axioms ArchS6.integral_fourierInv_smul_eq
#print axioms ArchS6.testSchwartz_apply
#print axioms ArchS6.smul_eq_testSchwartz_smul
#print axioms ArchS6.fourier_ae_eq
#print axioms ArchS6.fourierInv_ae_eq
#print axioms ArchS6.L2R_eq_of_integrable
#print axioms ArchS6.measurePreserving_neg_real
#print axioms ArchS6.reflectL_apply
#print axioms ArchS6.coeFn_reflect
#print axioms ArchS6.ae_eq_comp_neg
#print axioms ArchS6.reflect_reflect
#print axioms ArchS6.integrable_reflect
#print axioms ArchS6.continuous_fourier_L2R
#print axioms ArchS6.continuous_fourierInv_L2R
#print axioms ArchS6.fourierInv_eq_reflect_fourier
#print axioms ArchS6.fourier_reflect
#print axioms ArchS6.fourierInv_reflect
#print axioms ArchS6.mem_evenL2
#print axioms ArchS6.isClosed_evenL2
#print axioms ArchS6.fourier_mem_evenL2
#print axioms ArchS6.fourierInv_eq_fourier_of_even
#print axioms ArchS6.fourier_fourier_of_even
#print axioms ArchS6.inner_fourier_of_even
#print axioms ArchS6.coe_fourierEven
#print axioms ArchS6.fourierEven_fourierEven
#print axioms ArchS6.inner_fourierEven
#print axioms ArchS6.memLp_indicator_L2I
#print axioms ArchS6.coeFn_extendFun
#print axioms ArchS6.indicator_ae_eq_of_L2I
#print axioms ArchS6.coeFn_extendIcc
#print axioms ArchS6.coeFn_restrictFun
#print axioms ArchS6.norm_restrictFun_le
#print axioms ArchS6.coeFn_restrictIcc
#print axioms ArchS6.restrictIcc_extendIcc
#print axioms ArchS6.coeFn_extendIcc_restrictIcc
#print axioms ArchS6.inner_extendIcc_left
#print axioms ArchS6.inner_extendIcc_right
#print axioms ArchS6.integrable_extendIcc
#print axioms ArchS6.P1_apply
#print axioms ArchS6.coeFn_P1
#print axioms ArchS6.P1_P1
#print axioms ArchS6.inner_P1
#print axioms ArchS6.isOrthProj_P1
#print axioms ArchS6.P1_extendIcc
#print axioms ArchS6.neg_mem_Icc_neg_one_one
#print axioms ArchS6.P1_reflect
#print axioms ArchS6.P1_mem_evenL2
#print axioms ArchS6.P1_eq_zero_iff
#print axioms ArchS6.coe_P1even
#print axioms ArchS6.evenPair_P₁
#print axioms ArchS6.evenPair_F
#print axioms ArchS6.evenPair_hatP₁
#print axioms ArchS6.mem_sonin_evenPair
#print axioms ArchS6.continuous_kcomp
#print axioms ArchS6.exists_bound_Icc
#print axioms ArchS6.intOp_kernelOfContinuous_comp
#print axioms ArchS6.continuous_fourierK
#print axioms ArchS6.continuous_fourierInvK
#print axioms ArchS6.fourier_extendIcc_eq
#print axioms ArchS6.fourierInv_extendIcc_eq
#print axioms ArchS6.restrict_fourier_extend
#print axioms ArchS6.restrict_fourierInv_extend
#print axioms ArchS6.continuous_sincK
#print axioms ArchS6.integral_cexp_mul_I
#print axioms ArchS6.sincK_eq
#print axioms ArchS6.sincK_symm
#print axioms ArchS6.sincOp_compact_selfAdjoint
#print axioms ArchS6.sincOp_eq_comp
#print axioms ArchS6.fourierL_apply
#print axioms ArchS6.fourierInvL_apply
#print axioms ArchS6.hatP1_apply
#print axioms ArchS6.restrictIcc_P1
#print axioms ArchS6.restrict_P1hatP1P1_extend
#print axioms ArchS6.P1_hatP1_P1_eq
#print axioms ArchS6.inner_finFourierInv
#print axioms ArchS6.inner_sincOp
#print axioms ArchS6.norm_finFourier_le
#print axioms ArchS6.re_inner_sincOp
#print axioms ArchS6.re_inner_sincOp_le
#print axioms ArchS6.isClosed_eigenspace
#print axioms ArchS6.eigHB_apply
#print axioms ArchS6.norm_eigIdx
#print axioms ArchS6.eigenvalue_real
#print axioms ArchS6.exists_eigenBasis
#print axioms ArchS6.EigenBasis.coe_toHilbertBasis
#print axioms ArchS6.EigenBasis.hasSum
#print axioms ArchS6.EigenBasis.hasSum_inner_mul_inner
#print axioms ArchS6.EigenBasis.abs_μ_le
#print axioms ArchS6.EigenBasis.μ_eq_inner
#print axioms ArchS6.ae_ne_zero_real
#print axioms ArchS6.c2_mul_c2
#print axioms ArchS6.conj_c2
#print axioms ArchS6.inner_Eplus_reflect
#print axioms ArchS6.inner_reflect_Eplus
#print axioms ArchS6.inner_Jfun
#print axioms ArchS6.J_apply
#print axioms ArchS6.inner_J
#print axioms ArchS6.J_mem_evenL2
#print axioms ArchS6.P1_Eplus
#print axioms ArchS6.P1_J
#print axioms ArchS6.coeFn_J_of
#print axioms ArchS6.continuous_cosK
#print axioms ArchS6.cosK_symm
#print axioms ArchS6.Cop_compact_selfAdjoint
#print axioms ArchS6.coeFn_Cop
#print axioms ArchS6.cosTrans_neg
#print axioms ArchS6.fourierK_add_neg
#print axioms ArchS6.integrable_fourierK_mul
#print axioms ArchS6.fourier_Eplus_ae
#print axioms ArchS6.fourier_J
#print axioms ArchS6.fourier_J_ae
#print axioms ArchS6.P1_fourier_J
#print axioms ArchS6.J_restrict
#print axioms ArchS6.norm_coef_le
#print axioms ArchS6.norm_cexp_coef_le
#print axioms ArchS6.hasDerivAt_entireFT
#print axioms ArchS6.differentiable_entireFT
#print axioms ArchS6.entireFT_ofReal
#print axioms ArchS6.tendsto_add_inv
#print axioms ArchS6.eq_zero_of_fourier_ae_zero_Ioo
#print axioms ArchS6.eq_zero_of_P1_fourier
#print axioms ArchS6.eq_zero_of_P1_fourier_eq_zero
#print axioms ArchS6.abs_lt_one_of_eigen
#print axioms ArchS6.ne_zero_of_eigen
#print axioms ArchS6.coe_evenOf
#print axioms ArchS6.P1_fourier_J_eigen
#print axioms ArchS6.prolateBasisOf_ξ
#print axioms ArchS6.prolateBasisOf_lam
#print axioms ArchS6.prolateBasisOf_lam_ne_zero
#print axioms ArchS6.exists_eigenBasis_Cop
#print axioms ArchS6.exists_prolateBasis
#print axioms ArchS6.sonin_prolate_structure
#print axioms ArchS6.sincOp_restrict_ξ
#print axioms ArchS6.ae_eq_phi
#print axioms ArchS6.fourier_ξ_ae
#print axioms ArchS6.continuous_cosTrans
#print axioms ArchS6.continuous_phi
#print axioms ArchS6.coeFn_ofRealL
#print axioms ArchS6.coeFn_reL
#print axioms ArchS6.coeFn_imL
#print axioms ArchS6.decomp
#print axioms ArchS6.inner_ofRealL
#print axioms ArchS6.inner_ofRealL_left
#print axioms ArchS6.norm_ofRealL
#print axioms ArchS6.continuous_cosKR
#print axioms ArchS6.cosKR_symm
#print axioms ArchS6.CopR_compact_selfAdjoint
#print axioms ArchS6.cosTrans_ofRealL
#print axioms ArchS6.Cop_ofRealL
#print axioms ArchS6.complexify_e
#print axioms ArchS6.complexify_μ
#print axioms ArchS6.exists_eigenBasis_CopR
#print axioms ArchS6.realProlateBasis_ξ
#print axioms ArchS6.realProlateBasis_lam
#print axioms ArchS6.sonin_prolate_structure_real
#print axioms ArchS6.phi_complexify
#print axioms ArchS6.continuous_phiR
#print axioms ArchS6.ae_eq_phiR
#print axioms ArchS6.fourier_ξ_ae_real
#print axioms ArchS6.intervalIntegral_eq_Icc
#print axioms ArchS6.memLp_continuous
#print axioms ArchS6.coeFn_toL2
#print axioms ArchS6.inner_L2IR
#print axioms ArchS6.inner_eq_ipS9
#print axioms ArchS6.ip_phiR
#print axioms ArchS6.ne_zero_μ
#print axioms ArchS6.abs_μ_lt_one
#print axioms ArchS6.T_phiR
#print axioms ArchS6.parseval_ip
#print axioms ArchS6.exists_S9_family
#print axioms ArchS6.phi_neg
#print axioms ArchS6.coeFn_ξ
#print axioms ArchS6.coeFn_η
#print axioms ArchS6.coe_ψ
#print axioms ArchS6.coeFn_ψ
#print axioms ArchS6.coeFn_ζ
#print axioms ArchS6.phiR_neg
#print axioms ArchS6.coeFn_ξ_real
#print axioms ArchS6.coeFn_ζ_real
#print axioms ArchS6.cosTrans_eq_fourier
#print axioms ArchS6.integrable_moment_Eplus
#print axioms ArchS6.contDiff_cosTrans
#print axioms ArchS6.contDiff_phi
#print axioms ArchS6.contDiff_phiR

-- Archimedean programme: S7 (CC Thm 4.7), S7b (CC Lemma 4.1), S10 (certified chi), S8 update (2026-10-11).
#print axioms ArchS7.integrand_eq
#print axioms ArchS7.integral_coeff
#print axioms ArchS7.cc84_coeff
#print axioms ArchS7.eps_eq_tsum
#print axioms ArchS7.eps_abs_eq_tsum
#print axioms ArchS7.hasSum_norm_inner_sq
#print axioms ArchS7.tsum_ofReal_norm_inner_sq
#print axioms ArchS7.tsum_norm_sq_swap
#print axioms ArchS7.hsSq_indep
#print axioms ArchS7.hsSq_adjoint
#print axioms ArchS7.ProlateBasis.hasSum_norm_hatP_P
#print axioms ArchS7.ProlateBasis.ofReal_norm_hatP_P
#print axioms ArchS7.ProlateBasis.tsum_PhatPP
#print axioms ArchS7.Scaling.inner_F_θ_F
#print axioms ArchS7.Scaling.norm_inner_le
#print axioms ArchS7.ProlateBasis.inner_ζ_θ_ξ
#print axioms ArchS7.ProlateBasis.τ_eq
#print axioms ArchS7.ProlateBasis.delta_term
#print axioms ArchS7.ProlateBasis.inner_ψ_θ_ψ
#print axioms ArchS7.ProlateBasis.inner_ξ_θ_η
#print axioms ArchS7.ProlateBasis.inner_η_θ_ξ
#print axioms ArchS7.ProlateBasis.cζ_neg
#print axioms ArchS7.ProlateBasis.abs_lam_le_abs_τ
#print axioms ArchS7.ProlateBasis.lam_sq_le_abs_τ
#print axioms ArchS7.ProlateBasis.norm_ξ_ζ_coeff
#print axioms ArchS7.ProlateBasis.norm_cζ_le
#print axioms ArchS7.ProlateBasis.summable_lam_sq
#print axioms ArchS7.ProlateBasis.summable_ε_terms
#print axioms ArchS7.ProlateBasis.summable_cζ_terms
#print axioms ArchS7.ProlateBasis.δS_eq
#print axioms ArchS7.ProlateBasis.δS_abs_eq
#print axioms ArchS7.ProlateBasis.continuous_εS
#print axioms ArchS7.ProlateBasis.norm_εS_le
#print axioms ArchS7.ProlateBasis.integrable_mul_εS
#print axioms ArchS7.ProlateBasis.integrable_mul_cζ
#print axioms ArchS7.ProlateBasis.integral_δS
#print axioms ArchS7.hasSum_of_tsum_ofReal
#print axioms ArchS7.ProlateBasis.thm47
#print axioms ArchS7.ProlateBasis.thm47_nonneg
#print axioms ArchS7.ae_ne_real
#print axioms ArchS7.ae_comp_mul
#print axioms ArchS7.cosTransR_neg
#print axioms ArchS7.phiR_neg
#print axioms ArchS7.phiR_abs
#print axioms ArchS7.c2_eq
#print axioms ArchS7.xi_ae
#print axioms ArchS7.zeta_ae
#print axioms ArchS7.inner_evenL2
#print axioms ArchS7.inner_dil
#print axioms ArchS7.εS_term
#print axioms ArchS7.εS_eq_eps
#print axioms ArchS7.integral_εS_eq_Eplus
#print axioms ArchS7.xiRep_conj
#print axioms ArchS7.hreal_of_pointwise
#print axioms ArchS7.thm47_concrete
#print axioms ArchS7.thm47_concrete_nonneg
#print axioms ArchS7.thF_congr
#print axioms ArchS7.memLp_comp_mul
#print axioms ArchS7.memLp_thF
#print axioms ArchS7.exp_half_sq
#print axioms ArchS7.integral_thF
#print axioms ArchS7.coeFn_thRaw
#print axioms ArchS7.inner_thRaw
#print axioms ArchS7.thL_apply
#print axioms ArchS7.coeFn_thL
#print axioms ArchS7.thL_add
#print axioms ArchS7.thL_zero
#print axioms ArchS7.thL_neg_thL
#print axioms ArchS7.inner_thL_left
#print axioms ArchS7.reflect_thL
#print axioms ArchS7.thL_mem_evenL2
#print axioms ArchS7.P1_thL_neg
#print axioms ArchS7.fourier_congr_ae
#print axioms ArchS7.fourier_thF
#print axioms ArchS7.integrable_thF
#print axioms ArchS7.fourier_thL
#print axioms ArchS7.fourier_thL_fourier
#print axioms ArchS7.norm_sq_eq_integral
#print axioms ArchS7.continuous_thF_apply
#print axioms ArchS7.continuous_thL_of_compact
#print axioms ArchS7.continuous_thL
#print axioms ArchS7.coe_thE
#print axioms ArchS7.scalingEven_θ
#print axioms ArchS7.isPointwise_scalingEven
#print axioms ArchS7.thm47_even
#print axioms ArchS7.thE_add
#print axioms ArchS7.norm_thE
#print axioms ArchS7.inner_thE_left
#print axioms ArchS7.inner_thE_thE
#print axioms ArchS7.inner_smul_right_E
#print axioms ArchS7.inner_self_E
#print axioms ArchS7.inner_conj_symm_E
#print axioms ArchS7.continuous_thE
#print axioms ArchS7.integrable_smul_thE
#print axioms ArchS7.integrable_conj_smul_thE
#print axioms ArchS7.norm_thetaLin_le
#print axioms ArchS7.theta_apply
#print axioms ArchS7.adjoint_theta
#print axioms ArchS7.inner_adjoint_theta
#print axioms ArchS7.hcoef_theta
#print axioms ArchS7.thm47_theta
#print axioms ArchS7.thm47_theta_nonneg
#print axioms ArchS7.thm47_weil
#print axioms ArchS7.integral_cos_mul
#print axioms ArchS7.integral_square_cos
#print axioms ArchS7.hasSum_inner_intOp
#print axioms ArchS7.continuous_ktK
#print axioms ArchS7.coeFn_intOp_Kt
#print axioms ArchS7.hbOf_apply
#print axioms ArchS7.inner_reflect_left
#print axioms ArchS7.inner_J_even
#print axioms ArchS7.term_eq
#print axioms ArchS7.conj_cosK_mul_ktK
#print axioms ArchS7.continuous_kprod
#print axioms ArchS7.integral_kprod
#print axioms ArchS7.inner_K0_Kt
#print axioms ArchS7.hasSum_δS
#print axioms ArchS7.δS_eq_deltaK
#print axioms ArchS7.δS_abs_eq_deltaK
#print axioms ArchS7.thm47_weil'
#print axioms ArchS7.thm47_weil'_nonneg
#print axioms ArchS7b.integral_cos_mul_unit
#print axioms ArchS7b.integral_cosKR_mul
#print axioms ArchS7b.integral_integral_cosKR
#print axioms ArchS7b.deltaK_eq_double
#print axioms ArchS7b.abs_cosKR_le
#print axioms ArchS7b.memLp_kRow
#print axioms ArchS7b.inner_kRow_left
#print axioms ArchS7b.inner_kRow_kRow
#print axioms ArchS7b.norm_kRow_sq_le
#print axioms ArchS7b.hasSum_inner_mul
#print axioms ArchS7b.hasSum_inner_sq
#print axioms ArchS7b.continuous_cosTransR
#print axioms ArchS7b.hasSum_cosTransR_mul
#print axioms ArchS7b.abs_cosTransR_mul_le
#print axioms ArchS7b.summable_abs_cosTransR_mul
#print axioms ArchS7b.tsum_abs_cosTransR_mul_le
#print axioms ArchS7b.continuous_term
#print axioms ArchS7b.tsum_integral_cosTransR
#print axioms ArchS7b.cosTransR_eq
#print axioms ArchS7b.term_eq
#print axioms ArchS7b.setIntegral_Icc01
#print axioms ArchS7b.δS_eq_deltaK
#print axioms ArchS7b.δS_abs_eq_deltaK
#print axioms ArchS7b.integral_δS_eq_Dfun
#print axioms ArchS7b.thm47_concrete_O1
#print axioms ArchS7b.thm47_concrete_O1_nonneg
#print axioms ArchS8.cosPhi_bound
#print axioms ArchS8.outer_of_cosPhi

-- Archimedean programme: S10 summability (EigenFamily.toProlateData).

-- Archimedean programme: S6 follow-ups (enumeration, M_n bounds, trace class, L1) and S10 ι-generic summability.
#print axioms ArchS6.separableSpace_L2IR
#print axioms ArchS6.countable_of_orthonormal
#print axioms ArchS6.bumpSet_subset
#print axioms ArchS6.bumpSet_lt
#print axioms ArchS6.disjoint_bumpSet
#print axioms ArchS6.volI_bumpSet_pos
#print axioms ArchS6.bump_ne_zero
#print axioms ArchS6.inner_bump
#print axioms ArchS6.infinite_of_complete
#print axioms ArchS6.exists_equiv_nat
#print axioms ArchS6.sq_le_sobolev
#print axioms ArchS6.exists_bound_compact
#print axioms ArchS6.integrable_kernel_mul
#print axioms ArchS6.hasDerivAt_kInt
#print axioms ArchS6.continuous_k0
#print axioms ArchS6.continuous_k1
#print axioms ArchS6.continuous_k2
#print axioms ArchS6.continuous_k3
#print axioms ArchS6.hasDerivAt_arg
#print axioms ArchS6.hasDerivAt_k0
#print axioms ArchS6.hasDerivAt_k1
#print axioms ArchS6.hasDerivAt_k2
#print axioms ArchS6.abs_k0_le
#print axioms ArchS6.abs_k1_le
#print axioms ArchS6.abs_k2_le
#print axioms ArchS6.cosTransR_eq_kInt
#print axioms ArchS6.phiR_eq
#print axioms ArchS6.hasDerivAt_phiR
#print axioms ArchS6.hasDerivAt_dphiR
#print axioms ArchS6.continuous_kInt_k2
#print axioms ArchS6.continuous_kInt_k1
#print axioms ArchS6.continuous_kInt_k0
#print axioms ArchS6.deriv_phiR
#print axioms ArchS6.continuous_section
#print axioms ArchS6.kInt_eq_inner
#print axioms ArchS6.norm_toL2_sq_le
#print axioms ArchS6.sum_sq_kInt_le
#print axioms ArchS6.aW_lt_bW
#print axioms ArchS6.cW_pos
#print axioms ArchS6.continuous_dphi
#print axioms ArchS6.continuous_ddphi
#print axioms ArchS6.continuous_phiR'
#print axioms ArchS6.intervalIntegrable_sq
#print axioms ArchS6.Sint_nonneg
#print axioms ArchS6.continuous_Sint_integrand
#print axioms ArchS6.le_Sint
#print axioms ArchS6.sobolev_to_Q
#print axioms ArchS6.abs_phiR_le_Q
#print axioms ArchS6.abs_deriv_phiR_le_Q
#print axioms ArchS6.mu_sq_mul_Sint
#print axioms ArchS6.summable_mu_sq_mul_S
#print axioms ArchS6.Qb_sq
#print axioms ArchS6.exp_neg_log_three
#print axioms ArchS6.exp_log_three
#print axioms ArchS6.summable_mu_sq
#print axioms ArchS6.mu_sq_lt_one
#print axioms ArchS6.summable_wMN_aux
#print axioms ArchS6.prolateData_lam
#print axioms ArchS6.prolateData_phi
#print axioms ArchS6.prolateData_T
#print axioms ArchS6.exists_prolateData
#print axioms ArchS6.abs_aC
#print axioms ArchS6.hasSum_abs_aC
#print axioms ArchS6.summable_abs_aC
#print axioms ArchS6.hasSum_cosKR
#print axioms ArchS6.integrable_e
#print axioms ArchS6.integrable_mom
#print axioms ArchS6.abs_cMom_le
#print axioms ArchS6.integrable_Fterm
#print axioms ArchS6.integral_Fterm
#print axioms ArchS6.integral_norm_Fterm
#print axioms ArchS6.integral_abs_mom_le
#print axioms ArchS6.summable_integral_norm_Fterm
#print axioms ArchS6.mu_eq_integral
#print axioms ArchS6.hasSum_mu
#print axioms ArchS6.sum_cMom_sq_le
#print axioms ArchS6.sum_abs_mu_le
#print axioms ArchS6.summable_abs_mu
#print axioms ArchS6.tsum_abs_mu_le
#print axioms ArchS6.summable_abs_tau
#print axioms ArchS6.prolateData
#print axioms ArchS6.integrableOn_e
#print axioms ArchS6.integrableOn_phiR
#print axioms ArchS6.integral_sq_e
#print axioms ArchS6.integral_abs_e_le_one
#print axioms ArchS6.integral_abs_phiR_le_one

-- Archimedean programme: S7 final, CC Thm 4.7 with no interface hypotheses (2026-10-11).
#print axioms ArchS7.exp_image_univ
#print axioms ArchS7.lintegral_comp_exp
#print axioms ArchS7.integral_comp_exp'
#print axioms ArchS7.integrable_comp_exp_iff
#print axioms ArchS7.ae_comp_exp
#print axioms ArchS7.logF_congr
#print axioms ArchS7.sqrt2_exp_sq
#print axioms ArchS7.conj_logF_mul
#print axioms ArchS7.norm_logF_sq
#print axioms ArchS7.aestronglyMeasurable_logF
#print axioms ArchS7.integrable_norm_logF_sq
#print axioms ArchS7.memLp_logF
#print axioms ArchS7.coeFn_logRaw
#print axioms ArchS7.inner_logRaw
#print axioms ArchS7.norm_logRaw_sq
#print axioms ArchS7.norm_logRaw_le
#print axioms ArchS7.logL_apply
#print axioms ArchS7.coeFn_logL
#print axioms ArchS7.integral_even_eq
#print axioms ArchS7.even_ae
#print axioms ArchS7.inner_even_eq
#print axioms ArchS7.inner_logL_even
#print axioms ArchS7.coeFn_transL
#print axioms ArchS7.ae_comp_sub
#print axioms ArchS7.logL_thL
#print axioms ArchS7.norm_mo
#print axioms ArchS7.continuous_mo
#print axioms ArchS7.memLp_mo_mul
#print axioms ArchS7.coeFn_modL
#print axioms ArchS7.fourier_comp_sub
#print axioms ArchS7.fourier_transL
#print axioms ArchS7.mellinL_apply
#print axioms ArchS7.inner_thE_spectral
#print axioms ArchS7.norm_sq_adjoint_theta_spectral
#print axioms ArchS7.norm_mz
#print axioms ArchS7.measurableSet_one_lt_abs
#print axioms ArchS7.kapF_neg
#print axioms ArchS7.norm_kapF_sq
#print axioms ArchS7.kd_neg
#print axioms ArchS7.continuousOn_kapG
#print axioms ArchS7.aestronglyMeasurable_kapF
#print axioms ArchS7.integrableOn_kd_Ioi
#print axioms ArchS7.integrable_kd
#print axioms ArchS7.memLp_kapF
#print axioms ArchS7.coeFn_kap
#print axioms ArchS7.kap_mem_evenL2
#print axioms ArchS7.integral_even_eq_real
#print axioms ArchS7.norm_kap_sq
#print axioms ArchS7.ofReal_exp_cpow
#print axioms ArchS7.norm_fourier_le
#print axioms ArchS7.cexp_add_cexp_neg
#print axioms ArchS7.norm_Gpart_le
#print axioms ArchS7.integrable_phi
#print axioms ArchS7.norm_fourier_phi_le
#print axioms ArchS7.fourier_phi_eq_cos
#print axioms ArchS7.continuousOn_cpow_zt
#print axioms ArchS7.continuous_fourier_phi
#print axioms ArchS7.integrableOn_Gm
#print axioms ArchS7.inner_subst
#print axioms ArchS7.integral_Gm_eq
#print axioms ArchS7.integrable_betaF
#print axioms ArchS7.fourier_betaF
#print axioms ArchS7.tendsto_trunc
#print axioms ArchS7.inner_kap_phi
#print axioms ArchS7.fourier_betaF_eq_inner
#print axioms ArchS7.SmoothClass.memLp
#print axioms ArchS7.Tpf_apply
#print axioms ArchS7.mellin_PFP_smooth
#print axioms ArchS7.chi_nonneg
#print axioms ArchS7.chi_le_one
#print axioms ArchS7.chi_zero
#print axioms ArchS7.chi_neg
#print axioms ArchS7.contDiff_chi
#print axioms ArchS7.tendsto_chi
#print axioms ArchS7.norm_le_of_ae_mul
#print axioms ArchS7.memLp_chi_mul
#print axioms ArchS7.tendsto_chi_mul
#print axioms ArchS7.exists_smooth_near
#print axioms ArchS7.inner_kap_P1
#print axioms ArchS7.mellin_PFP_of_P1
#print axioms ArchS7.countable_of_orthonormal_evenL2
#print axioms ArchS7.exists_countable_hilbertBasis
#print axioms ArchS7.norm_hatP_P
#print axioms ArchS7.adjoint_PFP_comp
#print axioms ArchS7.coe_PFP
#print axioms ArchS7.mellin_PFP_even
#print axioms ArchS7.norm_paperFT_le
#print axioms ArchS7.hsq_le_sq
#print axioms ArchS7.ofReal_norm_adjoint_PFP
#print axioms ArchS7.tsum_inner_kap
#print axioms ArchS7.integrable_hsq_mul_Nnorm
#print axioms ArchS7.hasSum_hatP_P_theta
#print axioms ArchS7.thm47_weil_O1
#print axioms ArchS7.cc_thm47
#print axioms ArchS7.cc_thm47_nonneg
#print axioms ArchS7.exists_prolate_enumeration

-- Archimedean programme: S11 spectral certificate for K_I (2026-10-11).

-- Archimedean programme: S12 final assembly -- CC Theorem 1, Thm 6.11, conceptual one-condition rung (2026-10-11).

-- Pole-free Weil converse (e9, 2026-10-12): Weil positivity on PoleFree2 tests implies RH,
-- unconditionally on this island; plus the RR-square composition (RR-square on every window => RH).
#print axioms RvMBridgePF.weighted_approx
#print axioms RvMBridgePF.weighted_dominance
#print axioms RvMBridgePF.weil_positivity_poleFree_implies_rh
#print axioms RvMBridgePF.rh_iff_poleFree_weil_positivity
#print axioms RvMBridgePF.RRSquare.hodge_index
#print axioms RvMBridgePF.RRSquare.hodge_index_of_domain
#print axioms RvMBridgePF.rh_of_rr_windows
#print axioms re_weilForm_eq_archW_sub_prime
