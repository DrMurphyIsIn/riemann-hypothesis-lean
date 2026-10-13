import ArchS6_Proj

/-!
# ArchS6_Kernel: the finite Fourier transform and the sinc kernel

* `kcomp`, `intOp_kernelOfContinuous_comp`: composition of continuous-kernel operators on `[a,b]`
  is the continuous-kernel operator with kernel `∫_a^b k₁(x,y) k₂(y,z) dy` (Fubini).
* `restrict_fourier_extend`: `R 𝓕 E = T_{e^{-2πixy}}` on `L²([a,b])` (CC's `P₁ F_{e_ℝ} P₁`, eq. (68)
  with the opposite sign), and `restrict_fourierInv_extend`: `R 𝓕⁻ E = T_{e^{2πixy}}`.
* `sincK_eq`: `∫_{-1}^{1} e^{2πi(x-y)ω} dω = 2 sinc(2π(x-y)) = sin(2π(x-y))/(π(x-y))`.
* `P1_hatP1_P1_eq`: **CC's `P₁ P̂₁ P₁` (with `P̂₁ = F⁻¹ P₁ F`) on `L²(ℝ)` is `E ∘ T_sinc ∘ R`**, i.e.
  restricted to `ran P₁ ≅ L²([-1,1])` it is the integral operator with the sinc kernel.
* `sincOp_compact_selfAdjoint` (via S5), `re_inner_sincOp` (`⟪T_sinc h, h⟫ = ‖R 𝓕 E h‖²`),
  `re_inner_sincOp_le` (`≤ ‖h‖²`).

conjecture1_proved = False.
-/

open MeasureTheory Set Filter FourierTransform Complex
open scoped ENNReal InnerProductSpace Real

noncomputable section

namespace ArchS6

open ArchS5

set_option linter.unusedSectionVars false

/-! ### Composition of continuous kernels -/

section Comp

variable (a b : ℝ)

/-- The composed kernel `(k₁ ⋆ k₂)(x, z) = ∫_{[a,b]} k₁(x,y) k₂(y,z) dy`. -/
def kcomp (k₁ k₂ : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := ∫ y in Icc a b, k₁ (p.1, y) * k₂ (y, p.2)

theorem continuous_kcomp {k₁ k₂ : ℝ × ℝ → ℂ} (h₁ : Continuous k₁) (h₂ : Continuous k₂) :
    Continuous (kcomp a b k₁ k₂) :=
  continuous_parametric_integral_of_continuous
    (f := fun (p : ℝ × ℝ) (y : ℝ) ↦ k₁ (p.1, y) * k₂ (y, p.2))
    ((h₁.comp (by fun_prop)).mul (h₂.comp (by fun_prop))) isCompact_Icc

theorem exists_bound_Icc {k : ℝ × ℝ → ℂ} (hk : Continuous k) :
    ∃ C, ∀ p ∈ Icc a b ×ˢ Icc a b, ‖k p‖ ≤ C :=
  (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hk.continuousOn

/-- **Composition of continuous-kernel operators on `[a, b]`.** -/
theorem intOp_kernelOfContinuous_comp {k₁ k₂ : ℝ × ℝ → ℂ} (h₁ : Continuous k₁)
    (h₂ : Continuous k₂) (f : L2I a b) :
    intOp (kernelOfContinuous a b k₁ h₁) (intOp (kernelOfContinuous a b k₂ h₂) f) =
      intOp (kernelOfContinuous a b (kcomp a b k₁ k₂) (continuous_kcomp a b h₁ h₂)) f := by
  apply Lp.ext
  set g := intOp (kernelOfContinuous a b k₂ h₂) f
  have hg := intOp_kernelOfContinuous_ae_eq h₂ f
  have hfi : Integrable (f : ℝ → ℂ) (volI a b) := (Lp.memLp f).integrable (by norm_num)
  obtain ⟨C₁, hC₁⟩ := exists_bound_Icc a b h₁
  obtain ⟨C₂, hC₂⟩ := exists_bound_Icc a b h₂
  filter_upwards [intOp_kernelOfContinuous_ae_eq h₁ g,
    intOp_kernelOfContinuous_ae_eq (continuous_kcomp a b h₁ h₂) f,
    ae_restrict_mem (μ := volume) measurableSet_Icc] with x e1 e2 hx
  rw [e1, e2]
  have step1 : ∫ y in Icc a b, k₁ (x, y) * g y =
      ∫ y in Icc a b, ∫ z in Icc a b, k₁ (x, y) * (k₂ (y, z) * f z) := by
    refine integral_congr_ae ?_
    filter_upwards [hg] with y hy
    rw [hy, integral_const_mul]
  -- integrability on the square
  have hint : Integrable (Function.uncurry fun y z ↦ k₁ (x, y) * (k₂ (y, z) * f z))
      ((volI a b).prod (volI a b)) := by
    have hF : Integrable (fun p : ℝ × ℝ ↦ (1 : ℂ) * f p.2) ((volI a b).prod (volI a b)) :=
      (integrable_const (1 : ℂ)).mul_prod hfi
    have hb : Integrable (fun p : ℝ × ℝ ↦ (k₁ (x, p.1) * k₂ (p.1, p.2)) * ((1 : ℂ) * f p.2))
        ((volI a b).prod (volI a b)) := by
      refine hF.bdd_mul (c := C₁ * C₂) ?_ ?_
      · exact ((h₁.comp (by fun_prop)).mul (h₂.comp (by fun_prop))).aestronglyMeasurable
      · filter_upwards [ae_mem_Icc_prod a b] with p hp
        rw [norm_mul]
        have h1 := hC₁ (x, p.1) ⟨hx, hp.1⟩
        have h2 := hC₂ p hp
        exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
    refine hb.congr (ae_of_all _ fun p ↦ ?_)
    simp only [one_mul, Function.uncurry]
    ring
  rw [step1, integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
  simp only [kcomp]
  rw [← integral_mul_const]
  congr 1
  funext y
  ring

end Comp

/-! ### The finite Fourier transform -/

/-- The kernel `e^{-2πixy}` of `F_{e_ℝ}`. -/
def fourierK (p : ℝ × ℝ) : ℂ := cexp (↑(-2 * π * p.1 * p.2) * I)
/-- The kernel `e^{2πixy}` of `F_{e_ℝ}⁻¹`. -/
def fourierInvK (p : ℝ × ℝ) : ℂ := cexp (↑(2 * π * p.1 * p.2) * I)

theorem continuous_fourierK : Continuous fourierK := by unfold fourierK; fun_prop
theorem continuous_fourierInvK : Continuous fourierInvK := by unfold fourierInvK; fun_prop

theorem fourier_extendIcc_eq (a b : ℝ) (h : L2I a b) (w : ℝ) :
    𝓕 (extendIcc a b h : ℝ → ℂ) w = ∫ v in Icc a b, fourierK (w, v) * h v := by
  rw [Real.fourier_real_eq_integral_exp_smul, ← integral_indicator measurableSet_Icc]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_extendIcc a b h] with v hv
  rw [hv]
  by_cases hm : v ∈ Icc a b
  · rw [indicator_of_mem hm, indicator_of_mem hm, fourierK, smul_eq_mul]
    congr 3; ring
  · rw [indicator_of_notMem hm, indicator_of_notMem hm, smul_zero]

theorem fourierInv_extendIcc_eq (a b : ℝ) (h : L2I a b) (w : ℝ) :
    𝓕⁻ (extendIcc a b h : ℝ → ℂ) w = ∫ v in Icc a b, fourierInvK (w, v) * h v := by
  rw [Real.fourierInv_eq_fourier_neg, fourier_extendIcc_eq]
  congr 1; funext v
  simp only [fourierK, fourierInvK]
  congr 4; ring

/-- **`R 𝓕 E` is the integral operator with kernel `e^{-2πixy}` on `[a, b]`.** -/
theorem restrict_fourier_extend (a b : ℝ) (h : L2I a b) :
    restrictIcc a b (𝓕 (extendIcc a b h : L2R)) =
      intOp (kernelOfContinuous a b fourierK continuous_fourierK) h := by
  apply Lp.ext
  filter_upwards [coeFn_restrictIcc a b (𝓕 (extendIcc a b h : L2R)),
    ae_restrict_of_ae (fourier_ae_eq _ (integrable_extendIcc a b h)),
    intOp_kernelOfContinuous_ae_eq continuous_fourierK h] with x e1 e2 e3
  rw [e1, e2, e3, fourier_extendIcc_eq]

/-- `R 𝓕⁻ E` is the integral operator with kernel `e^{2πixy}` on `[a, b]`. -/
theorem restrict_fourierInv_extend (a b : ℝ) (h : L2I a b) :
    restrictIcc a b (𝓕⁻ (extendIcc a b h : L2R)) =
      intOp (kernelOfContinuous a b fourierInvK continuous_fourierInvK) h := by
  apply Lp.ext
  filter_upwards [coeFn_restrictIcc a b (𝓕⁻ (extendIcc a b h : L2R)),
    ae_restrict_of_ae (fourierInv_ae_eq _ (integrable_extendIcc a b h)),
    intOp_kernelOfContinuous_ae_eq continuous_fourierInvK h] with x e1 e2 e3
  rw [e1, e2, e3, fourierInv_extendIcc_eq]

/-! ### The sinc kernel -/

/-- The kernel of `P₁ F⁻¹ P₁ F P₁` on `[-1, 1]`: `∫_{-1}^1 e^{2πixω} e^{-2πiωy} dω`. -/
def sincK : ℝ × ℝ → ℂ := kcomp (-1) 1 fourierInvK fourierK

theorem continuous_sincK : Continuous sincK :=
  continuous_kcomp (-1) 1 continuous_fourierInvK continuous_fourierK

theorem integral_cexp_mul_I (t : ℝ) :
    ∫ ω in Icc (-1 : ℝ) 1, cexp (↑t * I * ↑ω) = ((2 * Real.sinc t : ℝ) : ℂ) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  by_cases ht : t = 0
  · subst ht; simp; norm_num
  have hc : (↑t * I : ℂ) ≠ 0 := mul_ne_zero (by exact_mod_cast ht) I_ne_zero
  rw [integral_exp_mul_complex hc, Real.sinc_of_ne_zero ht]
  have e1 : cexp (↑t * I * ↑(1 : ℝ)) = ↑(Real.cos t) + ↑(Real.sin t) * I := by
    rw [Complex.ofReal_one, mul_one, Complex.exp_mul_I]; simp [← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
  have e2 : cexp (↑t * I * ↑(-1 : ℝ)) = ↑(Real.cos t) - ↑(Real.sin t) * I := by
    have : (↑t * I * ↑(-1 : ℝ) : ℂ) = ↑(-t) * I := by push_cast; ring
    rw [this, Complex.exp_mul_I]
    simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  rw [e1, e2]
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  push_cast
  field_simp
  ring_nf

/-- **The sinc kernel**: `∫_{-1}^{1} e^{2πi(x-y)ω} dω = 2 sinc(2π(x-y))`. -/
theorem sincK_eq (p : ℝ × ℝ) : sincK p = ((2 * Real.sinc (2 * π * (p.1 - p.2)) : ℝ) : ℂ) := by
  rw [← integral_cexp_mul_I]
  unfold sincK kcomp
  refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
  simp only [fourierInvK, fourierK]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem sincK_symm (x y : ℝ) : sincK (y, x) = (starRingEnd ℂ) (sincK (x, y)) := by
  rw [sincK_eq, sincK_eq, Complex.conj_ofReal]
  congr 2
  rw [← Real.sinc_neg]
  congr 1; ring

/-- The sinc operator on `L²([-1, 1])`. -/
def sincOp : L2I (-1) 1 →L[ℂ] L2I (-1) 1 :=
  intOp (kernelOfContinuous (-1) 1 sincK continuous_sincK)

theorem sincOp_compact_selfAdjoint : IsCompactOperator sincOp ∧ IsSelfAdjoint sincOp :=
  intOp_kernelOfContinuous_compact_selfAdjoint continuous_sincK sincK_symm

/-- The finite Fourier transform `B = R 𝓕 E` on `L²([-1,1])`. -/
def finFourier : L2I (-1) 1 →L[ℂ] L2I (-1) 1 :=
  intOp (kernelOfContinuous (-1) 1 fourierK continuous_fourierK)

/-- `B* = R 𝓕⁻ E`. -/
def finFourierInv : L2I (-1) 1 →L[ℂ] L2I (-1) 1 :=
  intOp (kernelOfContinuous (-1) 1 fourierInvK continuous_fourierInvK)

theorem sincOp_eq_comp (h : L2I (-1) 1) : sincOp h = finFourierInv (finFourier h) :=
  (intOp_kernelOfContinuous_comp (-1) 1 continuous_fourierInvK continuous_fourierK h).symm

/-! ### `P₁ P̂₁ P₁` on `L²(ℝ)` -/

/-- `𝓕` on `L²(ℝ)` as a continuous linear map. -/
def fourierL : L2R →L[ℂ] L2R := (Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv
/-- `𝓕⁻` on `L²(ℝ)` as a continuous linear map. -/
def fourierInvL : L2R →L[ℂ] L2R := (Lp.fourierTransformₗᵢ ℝ ℂ).symm.toContinuousLinearEquiv

theorem fourierL_apply (f : L2R) : fourierL f = 𝓕 f := rfl
theorem fourierInvL_apply (f : L2R) : fourierInvL f = 𝓕⁻ f := rfl

/-- CC's `P̂₁ = F⁻¹ P₁ F` on `L²(ℝ)` (CC §4, after (61)). -/
def hatP1 : L2R →L[ℂ] L2R := fourierInvL ∘L P1 ∘L fourierL

theorem hatP1_apply (f : L2R) : hatP1 f = 𝓕⁻ (P1 (𝓕 f)) := rfl

theorem restrictIcc_P1 (f : L2R) : restrictIcc (-1) 1 (P1 f) = restrictIcc (-1) 1 f := by
  rw [P1_apply, restrictIcc_extendIcc]

/-- `R P₁ P̂₁ P₁ E = T_sinc` on `L²([-1, 1])`. -/
theorem restrict_P1hatP1P1_extend (h : L2I (-1) 1) :
    restrictIcc (-1) 1 (P1 (hatP1 (P1 (extendIcc (-1) 1 h)))) = sincOp h := by
  rw [restrictIcc_P1, hatP1_apply, P1_extendIcc, P1_apply, restrict_fourier_extend,
    restrict_fourierInv_extend, sincOp_eq_comp]
  rfl

/-- **CC's `P₁ P̂₁ P₁` is the sinc-kernel operator on `ran P₁ ≅ L²([-1, 1])`.** -/
theorem P1_hatP1_P1_eq :
    P1 ∘L hatP1 ∘L P1 = (extendIcc (-1) 1).toContinuousLinearMap ∘L sincOp ∘L restrictIcc (-1) 1 := by
  ext1 f
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
  have h1 : P1 f = extendIcc (-1) 1 (restrictIcc (-1) 1 f) := rfl
  rw [← restrict_P1hatP1P1_extend, ← h1, ← P1_apply, P1_P1, P1_P1]

theorem inner_finFourierInv (u h : L2I (-1) 1) :
    ⟪finFourierInv u, h⟫_ℂ = ⟪u, finFourier h⟫_ℂ := by
  rw [finFourierInv, finFourier, ← restrict_fourierInv_extend, ← restrict_fourier_extend,
    ← inner_extendIcc_right, ← inner_extendIcc_left]
  conv_lhs => rw [← Lp.inner_fourier_eq]
  rw [FourierInvPair.fourier_fourierInv_eq]

/-- `⟪T_sinc h, h⟫ = ‖B h‖²` with `B = R 𝓕 E`: the sinc operator is `B* B`. -/
theorem inner_sincOp (h : L2I (-1) 1) :
    ⟪sincOp h, h⟫_ℂ = ⟪finFourier h, finFourier h⟫_ℂ := by
  rw [sincOp_eq_comp, inner_finFourierInv]

theorem norm_finFourier_le (h : L2I (-1) 1) : ‖finFourier h‖ ≤ ‖h‖ := by
  rw [finFourier, ← restrict_fourier_extend]
  calc ‖restrictIcc (-1) 1 (𝓕 (extendIcc (-1) 1 h : L2R))‖
      ≤ ‖(𝓕 (extendIcc (-1) 1 h : L2R) : L2R)‖ := norm_restrictFun_le _ _ _
    _ = ‖h‖ := by rw [Lp.norm_fourier_eq, LinearIsometry.norm_map]

theorem re_inner_sincOp (h : L2I (-1) 1) :
    RCLike.re ⟪sincOp h, h⟫_ℂ = ‖finFourier h‖ ^ 2 := by
  rw [inner_sincOp, inner_self_eq_norm_sq]

/-- `0 ≤ T_sinc ≤ 1` as quadratic forms. -/
theorem re_inner_sincOp_le (h : L2I (-1) 1) :
    0 ≤ RCLike.re ⟪sincOp h, h⟫_ℂ ∧ RCLike.re ⟪sincOp h, h⟫_ℂ ≤ ‖h‖ ^ 2 := by
  rw [re_inner_sincOp]
  exact ⟨sq_nonneg _, by gcongr; exact norm_finFourier_le h⟩

end ArchS6
