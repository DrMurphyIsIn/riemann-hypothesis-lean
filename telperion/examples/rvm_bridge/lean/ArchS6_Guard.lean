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
import ArchS6_Enum
import ArchS6_Sobolev
import ArchS6_Bounds
import ArchS6_ProlateData
import ArchS6_Trace
import ArchS6_L1

/-! ArchS6_Guard: `#print axioms` for every top-level theorem of stage S6.
Required output: exactly `[propext, Classical.choice, Quot.sound]` on every line.
conjecture1_proved = False. -/

-- ArchS6_Abstract
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
-- ArchS6_Fourier
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
-- ArchS6_Proj
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
-- ArchS6_Kernel
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
-- ArchS6_Eigen
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
-- ArchS6_Even
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
-- ArchS6_Strict
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
-- ArchS6_Prolate
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
-- ArchS6_Real
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
-- ArchS6_Bridge
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
-- ArchS6_Functions
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
-- ArchS6_Enum
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
-- ArchS6_Sobolev
#print axioms ArchS6.sq_le_sobolev
-- ArchS6_Bounds
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
-- ArchS6_ProlateData
#print axioms ArchS6.exp_neg_log_three
#print axioms ArchS6.exp_log_three
#print axioms ArchS6.summable_mu_sq
#print axioms ArchS6.mu_sq_lt_one
#print axioms ArchS6.summable_wMN_aux
#print axioms ArchS6.prolateData_lam
#print axioms ArchS6.prolateData_phi
#print axioms ArchS6.prolateData_T
#print axioms ArchS6.exists_prolateData
-- ArchS6_Trace
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
-- ArchS6_L1
#print axioms ArchS6.integrableOn_e
#print axioms ArchS6.integrableOn_phiR
#print axioms ArchS6.integral_sq_e
#print axioms ArchS6.integral_abs_e_le_one
#print axioms ArchS6.integral_abs_phiR_le_one
