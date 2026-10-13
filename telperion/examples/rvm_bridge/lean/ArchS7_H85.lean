import ArchS7_Density

/-!
# ArchS7_H85: CC (85) in Hilbert–Schmidt form, from S3's Mellin-diagonal identity (interface O1)

**Theorem (`hasSum_hatP_P_theta`).**  For `IsWeilTest g` and every Hilbert basis `e` of `L²(ℝ)_ev`,
`Σ_k ‖P̂ P ϑ(g) e_k‖² = Lfun g = archW g + Dfun g`, i.e. `Tr(ϑ(g∗g*) P P̂ P) = W∞ + D` (CC (85),
Prop 2.2(iii)).

Proof: `‖P̂ P z‖ = ‖P F P z‖`; swap to a countable Hilbert basis `f_j` and the adjoint,
`(P F P ϑ(g))† f = ϑ(g)† (P F P f)`; the Mellin-diagonal form of `‖ϑ(g)† y‖²` (`ArchS7_LogMap`);
`𝓕Λ(P F P f)(w) = ⟨κ_{-2πw}, f⟩` (`ArchS7_Density`); Parseval `Σ_j |⟨κ, f_j⟩|² = ‖κ‖² = Nnorm`
(`ArchS7_Kappa`); and S3's `Lfun_eq_integral_Nnorm`.

* `thm47_weil_O1`: CC Thm 4.7 for `IsWeilTest g` with (85) discharged.

conjecture1_proved = False.
-/

open MeasureTheory Set Filter Topology FourierTransform
open scoped InnerProductSpace ComplexConjugate ENNReal

noncomputable section

namespace ArchS7

open ArchS6 ArchS3 ArchS8

set_option linter.unusedSectionVars false

instance fact_two_ne_top : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

/-! ### A countable Hilbert basis of `L²(ℝ)_ev` -/

theorem countable_of_orthonormal_evenL2 {ι : Type*} {v : ι → evenL2} (hv : Orthonormal ℂ v) :
    Countable ι := by
  refine Pairwise.countable_of_isOpen_disjoint (s := fun i ↦ Metric.ball (v i) (1 / 2))
    (fun i j hij ↦ ?_) (fun _ ↦ Metric.isOpen_ball)
    (fun i ↦ ⟨v i, Metric.mem_ball_self (by norm_num)⟩)
  refine Metric.ball_disjoint_ball ?_
  rw [dist_eq_norm]
  have h2 : ‖v i - v j‖ ^ 2 = 2 := by
    rw [@norm_sub_sq ℂ, hv.1 i, hv.1 j, hv.2 hij]; simp; norm_num
  have : (1 : ℝ) ≤ ‖v i - v j‖ := by nlinarith [norm_nonneg (v i - v j)]
  linarith

theorem exists_countable_hilbertBasis :
    ∃ (ι : Type) (_ : Countable ι), Nonempty (HilbertBasis ι ℂ evenL2) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ evenL2
  exact ⟨w, countable_of_orthonormal_evenL2 b.orthonormal, ⟨b⟩⟩

/-! ### Operator identities on `L²(ℝ)_ev` -/

theorem norm_hatP_P (z : evenL2) :
    ‖evenPair.hatP (evenPair.P z)‖ = ‖evenPair.P (evenPair.F (evenPair.P z))‖ := by
  have h : evenPair.hatP (evenPair.P z) = evenPair.F (evenPair.P (evenPair.F (evenPair.P z))) := by
    simp only [ProjPair.hatP_apply, ProjPair.hatP₁_apply, ProjPair.P_apply, map_sub, evenPair.F_F]
  rw [h, evenPair.norm_F]

/-- `(P F P V)† f = V† (P F P f)`. -/
theorem adjoint_PFP_comp (V : evenL2 →L[ℂ] evenL2) (f : evenL2) :
    (ContinuousLinearMap.adjoint (evenPair.P ∘L evenPair.F ∘L evenPair.P ∘L V)) f
      = (ContinuousLinearMap.adjoint V) (evenPair.P (evenPair.F (evenPair.P f))) := by
  apply ext_inner_right ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  simp only [ContinuousLinearMap.comp_apply]
  rw [← evenPair.isOrthProj_P.2, ← evenPair.inner_F, ← evenPair.isOrthProj_P.2]

/-- The `L²(ℝ)` picture of `P F P f`. -/
theorem coe_PFP (f : evenL2) :
    ((evenPair.P (evenPair.F (evenPair.P f)) : evenL2) : L2R)
      = (𝓕 ((f : L2R) - P1 (f : L2R)) : L2R) - P1 (𝓕 ((f : L2R) - P1 (f : L2R)) : L2R) := rfl

theorem mellin_PFP_even (f : evenL2) :
    (mellinL ((evenPair.P (evenPair.F (evenPair.P f)) : evenL2) : L2R) : ℝ → ℂ) =ᵐ[volume]
      fun w ↦ ⟪kap (-2 * Real.pi * w), (f : L2R)⟫_ℂ := by
  rw [coe_PFP]
  set a : L2R := (f : L2R) - P1 (f : L2R)
  have ha : a ∈ evenL2 := evenL2.sub_mem f.2 (P1_mem_evenL2 f.2)
  have h1 : P1 a = 0 := by simp only [a, map_sub, P1_P1, sub_self]
  have h := mellin_PFP_of_P1 ha h1
  rw [Tpf_apply] at h
  filter_upwards [h] with w hw
  rw [hw, inner_sub_right, inner_kap_P1, sub_zero]

theorem norm_paperFT_le (g : ℝ → ℂ) (r : ℝ) : ‖Zeta23.paperFT g r‖ ≤ ∫ u, ‖g u‖ := by
  unfold Zeta23.paperFT
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; funext u
  rw [norm_mul, Complex.norm_exp]
  simp

theorem hsq_le_sq (g : ℝ → ℂ) (r : ℝ) : RvMBridge31.hsq g r ≤ (∫ u, ‖g u‖) ^ 2 := by
  unfold RvMBridge31.hsq
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_paperFT_le g r) 2

/-- Per basis vector: `‖ϑ(g)† (P F P f)‖² = ∫ hsq g(-2πw) |⟨κ_{-2πw}, f⟩|² dw`. -/
theorem ofReal_norm_adjoint_PFP {g : ℝ → ℂ} (hW : WeilExplicit.IsWeilTest g) (hg : Integrable g)
    (f : evenL2) :
    ENNReal.ofReal (‖(ContinuousLinearMap.adjoint (theta g hg))
        (evenPair.P (evenPair.F (evenPair.P f)))‖ ^ 2)
      = ∫⁻ w, ENNReal.ofReal (RvMBridge31.hsq g (-2 * Real.pi * w))
          * ENNReal.ofReal (‖⟪kap (-2 * Real.pi * w), (f : L2R)⟫_ℂ‖ ^ 2) := by
  set y := evenPair.P (evenPair.F (evenPair.P f))
  rw [norm_sq_adjoint_theta_spectral hW hg y]
  have hM : Integrable fun w ↦ ‖(mellinL (y : L2R) : ℝ → ℂ) w‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).1 (Lp.memLp _)
  have hc : Continuous fun w : ℝ ↦ RvMBridge31.hsq g (-2 * Real.pi * w) :=
    (RvMBridge32.continuous_hsq hW).comp (continuous_const.mul continuous_id)
  have hint : Integrable fun w ↦ RvMBridge31.hsq g (-2 * Real.pi * w)
      * ‖(mellinL (y : L2R) : ℝ → ℂ) w‖ ^ 2 :=
    hM.bdd_mul hc.aestronglyMeasurable (Eventually.of_forall fun w ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (RvMBridge31.hsq_nonneg _ _)]
      exact hsq_le_sq g _)
  rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun w ↦ by
    have := RvMBridge31.hsq_nonneg g (-2 * Real.pi * w); positivity)]
  refine lintegral_congr_ae ?_
  filter_upwards [mellin_PFP_even f] with w hw
  rw [hw, ENNReal.ofReal_mul (RvMBridge31.hsq_nonneg _ _)]

/-- Parseval for `κ_t`: `Σ_j |⟨κ_t, f_j⟩|² = ‖κ_t‖² = Nnorm t`. -/
theorem tsum_inner_kap {ι : Type*} (fb : HilbertBasis ι ℂ evenL2) (t : ℝ) :
    ∑' j, ENNReal.ofReal (‖⟪kap t, ((fb j : evenL2) : L2R)⟫_ℂ‖ ^ 2) = ENNReal.ofReal (Nnorm t) := by
  set κE : evenL2 := ⟨kap t, kap_mem_evenL2 t⟩
  have h := tsum_ofReal_norm_inner_sq fb κE
  have e1 : ∀ j, ‖⟪kap t, ((fb j : evenL2) : L2R)⟫_ℂ‖ = ‖⟪fb j, κE⟫_ℂ‖ := by
    intro j
    rw [Submodule.coe_inner, norm_inner_symm]
  have e2 : ‖κE‖ = ‖kap t‖ := rfl
  simp_rw [e1]
  rw [h, e2, norm_kap_sq]

theorem integrable_hsq_mul_Nnorm {g : ℝ → ℂ} (hW : WeilExplicit.IsWeilTest g) :
    Integrable fun r ↦ RvMBridge31.hsq g r * Nnorm r := by
  have h1 := RvMBridge31.integrable_hsq_mul_psiR hW
  have h2 := (RvMBridge31.integrable_hsq hW).mul_const (Real.log Real.pi)
  have h3 := integrable_hsq_mul_deltaHat hW
  refine ((h1.sub h2).add h3).congr (Eventually.of_forall fun r ↦ ?_)
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [← ell_eq_Nnorm, ell]
  ring

/-- **CC (85) / Prop 2.2(iii), Hilbert–Schmidt form**: for `IsWeilTest g` and any Hilbert basis `e`,
`Σ_k ‖P̂ P ϑ(g) e_k‖² = Lfun g = W∞(g∗g*) + D(g∗g*)`. -/
theorem hasSum_hatP_P_theta {g : ℝ → ℂ} (hW : WeilExplicit.IsWeilTest g) (hg : Integrable g)
    {κ : Type*} (e : HilbertBasis κ ℂ evenL2) :
    HasSum (fun k ↦ ‖evenPair.hatP (evenPair.P (theta g hg (e k)))‖ ^ 2) (Lfun g) := by
  obtain ⟨ι, hι, ⟨fb⟩⟩ := exists_countable_hilbertBasis
  set V := theta g hg
  set Z : evenL2 →L[ℂ] evenL2 := evenPair.P ∘L evenPair.F ∘L evenPair.P ∘L V
  have hZ : ∀ k, ‖evenPair.hatP (evenPair.P (V (e k)))‖ = ‖Z (e k)‖ := fun k ↦ by
    rw [norm_hatP_P]; rfl
  refine hasSum_of_tsum_ofReal (fun k ↦ sq_nonneg _) (cc_cor_2_3 hW) ?_
  simp_rw [hZ]
  rw [tsum_norm_sq_swap e fb Z]
  have hadj : ∀ j, (ContinuousLinearMap.adjoint Z) (fb j)
      = (ContinuousLinearMap.adjoint V) (evenPair.P (evenPair.F (evenPair.P (fb j)))) :=
    fun j ↦ adjoint_PFP_comp V (fb j)
  have key : ∑' j, ENNReal.ofReal (‖(ContinuousLinearMap.adjoint Z) (fb j)‖ ^ 2)
      = ∑' j, ∫⁻ w, ENNReal.ofReal (RvMBridge31.hsq g (-2 * Real.pi * w))
          * ENNReal.ofReal (‖⟪kap (-2 * Real.pi * w), ((fb j : evenL2) : L2R)⟫_ℂ‖ ^ 2) :=
    tsum_congr fun j ↦ by rw [hadj j, ofReal_norm_adjoint_PFP hW hg]
  refine key.trans ?_
  have hmeas : ∀ j, AEMeasurable (fun w ↦ ENNReal.ofReal (RvMBridge31.hsq g (-2 * Real.pi * w))
      * ENNReal.ofReal (‖⟪kap (-2 * Real.pi * w), ((fb j : evenL2) : L2R)⟫_ℂ‖ ^ 2)) volume := by
    intro j
    have hm : AEMeasurable (fun w ↦ ⟪kap (-2 * Real.pi * w), ((fb j : evenL2) : L2R)⟫_ℂ) volume :=
      (Lp.aestronglyMeasurable _).aemeasurable.congr (mellin_PFP_even (fb j))
    exact (ENNReal.measurable_ofReal.comp ((RvMBridge32.continuous_hsq hW).comp
      (continuous_const.mul continuous_id)).measurable).aemeasurable.mul
      (ENNReal.measurable_ofReal.comp_aemeasurable (hm.norm.pow_const 2))
  rw [← lintegral_tsum hmeas]
  simp_rw [ENNReal.tsum_mul_left, tsum_inner_kap fb]
  have hint := (integrable_hsq_mul_Nnorm hW).comp_mul_left' (show (-2 * Real.pi) ≠ 0 by
    have := Real.pi_pos; linarith)
  simp_rw [← ENNReal.ofReal_mul (RvMBridge31.hsq_nonneg _ _)]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun w ↦ mul_nonneg
    (RvMBridge31.hsq_nonneg _ _) (Nnorm_nonneg _))]
  congr 1
  rw [Lfun_eq_integral_Nnorm hW]
  have := MeasureTheory.Measure.integral_comp_mul_left
    (fun r ↦ RvMBridge31.hsq g r * Nnorm r) (-2 * Real.pi)
  rw [this, smul_eq_mul, abs_inv, abs_mul, abs_neg, abs_two, abs_of_pos Real.pi_pos]
  ring

/-- **CC Theorem 4.7 for `IsWeilTest g`, with (85) discharged** (O1 is now a theorem):
`‖S ϑ(g)‖²_HS = archW g + Re (D.Eplus (autocorr g))`. -/
theorem thm47_weil_O1 {ι : Type*} (bR : EigenBasis CopR ι) (D : ProlateDataNat) (σ : ℕ ≃ ι)
    (hDlam : ∀ n, D.lam n = bR.μ (σ n)) (hDphi : ∀ n, D.phi n = phiR bR (σ n))
    (hτ : Summable fun i ↦ |(realProlateBasis bR).τ i|)
    {g : ℝ → ℂ} (hW : WeilExplicit.IsWeilTest g)
    {κ : Type*} (e : HilbertBasis κ ℂ evenL2) :
    HasSum (fun k ↦ ‖ArchS6.ProlateBasis.soninProj (S := evenPair)
        (theta g (hW.1.continuous.integrable_of_hasCompactSupport hW.2) (e k))‖ ^ 2)
      (ArchS3.archW g + (D.Eplus (WeilExplicit.autocorr g)).re) :=
  thm47_weil' bR D σ hDlam hDphi hτ hW e
    (hasSum_hatP_P_theta hW (hW.1.continuous.integrable_of_hasCompactSupport hW.2) e)

end ArchS7
