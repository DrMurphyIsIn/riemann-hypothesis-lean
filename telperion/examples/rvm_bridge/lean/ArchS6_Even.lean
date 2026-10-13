import ArchS6_Kernel

/-!
# ArchS6_Even: the even picture and S9's operator `2cos(2πxω)` on `[0, 1]`

CC work in `L²(ℝ)_ev` with `⟨η|ξ⟩ = ∫₀^∞ η̄ ξ` (CC (16)); stage S9 works with the integral operator
`(Tf)(ω) = ∫₀¹ 2cos(2πxω) f(x) dx` on `[0, 1]`.  This file links the two.

* `J : L²([0,1]) →ₗᵢ L²(ℝ)`, `J h = (E₊ h + R E₊ h)/√2` (even extension, supported in `[-1,1]`),
  a linear isometry for Mathlib's `L²(ℝ)` norm (`∫_ℝ`).  Its range is `L²(ℝ)_ev ∩ ran P₁`
  (`J_restrict`).
* `cosK (x, y) = 2cos(2πxy)` (S9's `K`), `Cop = T_{cosK}` on `L²([0,1])`, compact self-adjoint (S5).
* **`P1_fourier_J`: `P₁ 𝓕 J = J C`.**  So an eigenvector `C e = λ e` gives `P₁ F ξ = λ ξ` with
  `ξ = J e` (CC (68)-(69)), and conversely.

Normalisation dictionary: for even `ξ` supported in `[-1,1]`, CC's `‖ξ‖²_CC = ∫₀^∞ |ξ|² = ½ ∫_ℝ |ξ|²`.
If `e ∈ L²([0,1])` has `∫₀¹ |e|² = 1` (S9's normalisation `ip ξ ξ = 1`), then `J e` restricted to
`[0, 1]` is `e/√2`, i.e. `J e = U ξ_CC` with the unitary `U : (L²(ℝ)_ev, ⟨·|·⟩_CC) → (L²(ℝ)_ev, ⟪·,·⟫)`,
`U ξ = ξ/√2`.  `U` preserves inner products, so every inner-product statement of `ArchS6_Abstract`
for `J e` is the same statement for CC's `ξ_n`.

conjecture1_proved = False.
-/

open MeasureTheory Set Filter FourierTransform Complex
open scoped ENNReal InnerProductSpace Real

noncomputable section

namespace ArchS6

open ArchS5

set_option linter.unusedSectionVars false

theorem ae_ne_zero_real : ∀ᵐ x : ℝ, x ≠ 0 := by
  rw [ae_iff]
  simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton, measure_singleton]

/-- `1/√2` as a complex number. -/
def c2 : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

theorem c2_mul_c2 : c2 * c2 = 1 / 2 := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  rw [c2, Complex.ofReal_inv]
  field_simp
  exact h.symm

theorem conj_c2 : (starRingEnd ℂ) c2 = c2 := Complex.conj_ofReal _

/-- Extension by zero from `[0, 1]`. -/
abbrev Eplus : L2I 0 1 →ₗᵢ[ℂ] L2R := extendIcc 0 1

theorem inner_Eplus_reflect (h k : L2I 0 1) : ⟪Eplus h, reflect (Eplus k)⟫_ℂ = 0 := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [coeFn_extendIcc 0 1 h, coeFn_reflect (Eplus k),
    ae_eq_comp_neg (coeFn_extendIcc 0 1 k), ae_ne_zero_real] with x e1 e2 e3 hx
  rw [e1, e2, e3, Pi.zero_apply]
  by_cases hm : x ∈ Icc (0 : ℝ) 1
  · have hm' : -x ∉ Icc (0 : ℝ) 1 := by
      intro h'; exact hx (le_antisymm (by linarith [h'.1]) hm.1)
    rw [indicator_of_notMem hm', inner_zero_right]
  · rw [indicator_of_notMem hm, inner_zero_left]

theorem inner_reflect_Eplus (h k : L2I 0 1) : ⟪reflect (Eplus h), Eplus k⟫_ℂ = 0 := by
  rw [← inner_conj_symm, inner_Eplus_reflect, map_zero]

/-- The raw map `J h = (E₊ h + R E₊ h)/√2`. -/
def Jfun (h : L2I 0 1) : L2R := c2 • (Eplus h + reflect (Eplus h))

theorem inner_Jfun (h k : L2I 0 1) : ⟪Jfun h, Jfun k⟫_ℂ = ⟪h, k⟫_ℂ := by
  simp only [Jfun, inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    inner_Eplus_reflect, inner_reflect_Eplus, LinearIsometry.inner_map_map, conj_c2]
  rw [add_zero, zero_add, ← mul_add, ← mul_assoc, c2_mul_c2]; ring

/-- `J : L²([0,1]) → L²(ℝ)`, a linear isometry onto the even functions supported in `[-1, 1]`. -/
def J : L2I 0 1 →ₗᵢ[ℂ] L2R where
  toFun := Jfun
  map_add' h k := by simp only [Jfun, map_add]; rw [← smul_add]; congr 1; abel
  map_smul' c h := by simp only [Jfun, map_smul, RingHom.id_apply]; rw [← smul_add, smul_comm]
  norm_map' h := by
    have h1 := congrArg RCLike.re (inner_Jfun h h)
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at h1
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1

theorem J_apply (h : L2I 0 1) : J h = c2 • (Eplus h + reflect (Eplus h)) := rfl

theorem inner_J (h k : L2I 0 1) : ⟪J h, J k⟫_ℂ = ⟪h, k⟫_ℂ := inner_Jfun h k

theorem J_mem_evenL2 (h : L2I 0 1) : J h ∈ evenL2 := by
  rw [mem_evenL2, J_apply, map_smul, map_add, reflect_reflect, add_comm]

theorem P1_Eplus (h : L2I 0 1) : P1 (Eplus h) = Eplus h := by
  apply Lp.ext
  filter_upwards [coeFn_P1 (Eplus h), coeFn_extendIcc 0 1 h] with x e1 e2
  rw [e1]
  by_cases hm' : x ∈ Icc (-1 : ℝ) 1
  · rw [indicator_of_mem hm']
  · rw [indicator_of_notMem hm', e2, indicator_of_notMem]
    intro h'; exact hm' ⟨by linarith [h'.1], h'.2⟩

theorem P1_J (h : L2I 0 1) : P1 (J h) = J h := by
  rw [J_apply, map_smul, map_add, P1_reflect, P1_Eplus]

/-- Coefficients of `J k` when `k = F` a.e. on `[0, 1]`. -/
theorem coeFn_J_of (k : L2I 0 1) {F : ℝ → ℂ} (hF : (k : ℝ → ℂ) =ᵐ[volI 0 1] F) :
    (J k : ℝ → ℂ) =ᵐ[volume]
      fun w ↦ c2 * ((Icc (0 : ℝ) 1).indicator F w + (Icc (0 : ℝ) 1).indicator F (-w)) := by
  have hi := (ae_eq_restrict_iff_indicator_ae_eq (μ := volume) measurableSet_Icc).1 hF
  filter_upwards [Lp.coeFn_smul c2 (Eplus k + reflect (Eplus k)),
    Lp.coeFn_add (Eplus k) (reflect (Eplus k)), coeFn_extendIcc 0 1 k, hi,
    coeFn_reflect (Eplus k), ae_eq_comp_neg (coeFn_extendIcc 0 1 k),
    ae_eq_comp_neg hi] with w e1 e2 e3 e4 e5 e6 e7
  rw [J_apply, e1, Pi.smul_apply, e2, Pi.add_apply, e3, e4, e5, e6, e7, smul_eq_mul]

/-! ### S9's operator -/

/-- S9's kernel `K(ω, x) = 2cos(2πxω)` (symmetric). -/
def cosK (p : ℝ × ℝ) : ℂ := ((2 * Real.cos (2 * π * p.1 * p.2) : ℝ) : ℂ)

theorem continuous_cosK : Continuous cosK := by unfold cosK; fun_prop

theorem cosK_symm (x y : ℝ) : cosK (y, x) = (starRingEnd ℂ) (cosK (x, y)) := by
  rw [cosK, cosK, Complex.conj_ofReal]
  congr 3; ring

/-- `C`: S9's operator on `L²([0, 1])`. -/
def Cop : L2I 0 1 →L[ℂ] L2I 0 1 := intOp (kernelOfContinuous 0 1 cosK continuous_cosK)

theorem Cop_compact_selfAdjoint : IsCompactOperator Cop ∧ IsSelfAdjoint Cop :=
  intOp_kernelOfContinuous_compact_selfAdjoint continuous_cosK cosK_symm

/-- `(C h)(ω) = ∫₀¹ 2cos(2πωv) h(v) dv` as a function of `ω ∈ ℝ` (S9's `T h`). -/
def cosTrans (h : L2I 0 1) (w : ℝ) : ℂ := ∫ v in Icc (0 : ℝ) 1, cosK (w, v) * h v

theorem coeFn_Cop (h : L2I 0 1) : (Cop h : ℝ → ℂ) =ᵐ[volI 0 1] cosTrans h :=
  intOp_kernelOfContinuous_ae_eq continuous_cosK h

theorem cosTrans_neg (h : L2I 0 1) (w : ℝ) : cosTrans h (-w) = cosTrans h w := by
  unfold cosTrans cosK
  congr 1; funext v
  congr 3
  rw [show 2 * π * -w * v = -(2 * π * w * v) by ring, Real.cos_neg]

theorem fourierK_add_neg (w v : ℝ) : fourierK (w, v) + fourierK (-w, v) = cosK (w, v) := by
  simp only [fourierK, cosK]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [show (-2 * (π : ℂ) * -(w : ℂ) * v) = 2 * π * w * v by ring,
    show (-2 * (π : ℂ) * w * v) = -(2 * π * w * v) by ring, Complex.cos_neg, Complex.sin_neg]
  ring

theorem integrable_fourierK_mul (a b w : ℝ) (h : L2I a b) :
    Integrable (fun v ↦ fourierK (w, v) * h v) (volI a b) := by
  refine ((Lp.memLp h).integrable (by norm_num)).bdd_mul (c := 1) ?_ (ae_of_all _ fun v ↦ ?_)
  · exact (continuous_fourierK.comp (by fun_prop : Continuous fun v : ℝ ↦ (w, v))).aestronglyMeasurable
  · simp only [fourierK]
    rw [Complex.norm_exp_ofReal_mul_I]

theorem fourier_Eplus_ae (h : L2I 0 1) :
    ((𝓕 (Eplus h : L2R) : L2R) : ℝ → ℂ) =ᵐ[volume]
      fun w ↦ ∫ v in Icc (0 : ℝ) 1, fourierK (w, v) * h v := by
  filter_upwards [fourier_ae_eq _ (integrable_extendIcc 0 1 h)] with w hw
  rw [hw, fourier_extendIcc_eq]

theorem fourier_J (h : L2I 0 1) :
    (𝓕 (J h : L2R) : L2R) = c2 • ((𝓕 (Eplus h : L2R) : L2R) + reflect (𝓕 (Eplus h : L2R))) := by
  rw [J_apply, ← fourierL_apply, map_smul, map_add, fourierL_apply, fourierL_apply,
    fourier_reflect]

theorem fourier_J_ae (h : L2I 0 1) :
    ((𝓕 (J h : L2R) : L2R) : ℝ → ℂ) =ᵐ[volume] fun w ↦ c2 * cosTrans h w := by
  rw [fourier_J]
  filter_upwards [Lp.coeFn_smul c2 ((𝓕 (Eplus h : L2R) : L2R) + reflect (𝓕 (Eplus h : L2R))),
    Lp.coeFn_add (𝓕 (Eplus h : L2R) : L2R) (reflect (𝓕 (Eplus h : L2R))),
    fourier_Eplus_ae h, coeFn_reflect (𝓕 (Eplus h : L2R)),
    ae_eq_comp_neg (fourier_Eplus_ae h)] with w e1 e2 e3 e4 e5
  rw [e1, Pi.smul_apply, e2, Pi.add_apply, e3, e4, e5, smul_eq_mul]
  congr 1
  rw [← integral_add (integrable_fourierK_mul 0 1 w h) (integrable_fourierK_mul 0 1 (-w) h)]
  unfold cosTrans
  congr 1; funext v
  rw [← add_mul, fourierK_add_neg]

/-- **`P₁ 𝓕 J = J C`**: the even prolate operator is S9's operator `2cos(2πxω)` on `[0, 1]`. -/
theorem P1_fourier_J (h : L2I 0 1) : P1 (𝓕 (J h : L2R)) = J (Cop h) := by
  apply Lp.ext
  filter_upwards [coeFn_P1 (𝓕 (J h : L2R)), fourier_J_ae h, coeFn_J_of (Cop h) (coeFn_Cop h),
    ae_ne_zero_real] with w e1 e2 e3 hw
  rw [e1, e3]
  by_cases hm : w ∈ Icc (-1 : ℝ) 1
  · rw [indicator_of_mem hm, e2]
    rcases lt_or_gt_of_ne hw with hneg | hpos
    · have h1 : w ∉ Icc (0 : ℝ) 1 := fun h' ↦ by linarith [h'.1]
      have h2 : -w ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [hm.1]⟩
      rw [indicator_of_notMem h1, indicator_of_mem h2, zero_add, cosTrans_neg]
    · have h1 : w ∈ Icc (0 : ℝ) 1 := ⟨hpos.le, hm.2⟩
      have h2 : -w ∉ Icc (0 : ℝ) 1 := fun h' ↦ by linarith [h'.1]
      rw [indicator_of_mem h1, indicator_of_notMem h2, add_zero]
  · have h1 : w ∉ Icc (0 : ℝ) 1 := fun h' ↦ hm ⟨by linarith [h'.1], h'.2⟩
    have h2 : -w ∉ Icc (0 : ℝ) 1 := fun h' ↦ hm ⟨by linarith [h'.2], by linarith [h'.1]⟩
    rw [indicator_of_notMem hm, indicator_of_notMem h1, indicator_of_notMem h2, add_zero,
      mul_zero]

/-- The range of `J` is `L²(ℝ)_ev ∩ ran P₁`. -/
theorem J_restrict {f : L2R} (hf : f ∈ evenL2) (hP : P1 f = f) :
    J (((Real.sqrt 2 : ℝ) : ℂ) • restrictIcc 0 1 f) = f := by
  have hev : (f : ℝ → ℂ) =ᵐ[volume] fun x ↦ f (-x) := by
    have := coeFn_reflect f
    rw [mem_evenL2.1 hf] at this
    exact this
  have hsupp := coeFn_P1 f
  rw [hP] at hsupp
  have hk : ((((Real.sqrt 2 : ℝ) : ℂ) • restrictIcc 0 1 f : L2I 0 1) : ℝ → ℂ) =ᵐ[volI 0 1]
      fun x ↦ ((Real.sqrt 2 : ℝ) : ℂ) * f x := by
    filter_upwards [Lp.coeFn_smul ((Real.sqrt 2 : ℝ) : ℂ) (restrictIcc 0 1 f),
      coeFn_restrictIcc 0 1 f] with x e1 e2
    rw [e1, Pi.smul_apply, e2, smul_eq_mul]
  have hc : c2 * ((Real.sqrt 2 : ℝ) : ℂ) = 1 := by
    rw [c2, ← Complex.ofReal_mul, inv_mul_cancel₀ (Real.sqrt_pos.2 (by norm_num)).ne',
      Complex.ofReal_one]
  apply Lp.ext
  filter_upwards [coeFn_J_of _ hk, hev, hsupp, ae_eq_comp_neg hsupp, ae_ne_zero_real]
    with w e1 e2 e3 e4 hw
  rw [e1]
  rcases lt_or_gt_of_ne hw with hneg | hpos
  · have h1 : w ∉ Icc (0 : ℝ) 1 := fun h' ↦ by linarith [h'.1]
    rw [indicator_of_notMem h1, zero_add]
    by_cases h2 : -w ∈ Icc (0 : ℝ) 1
    · rw [indicator_of_mem h2, ← mul_assoc, hc, one_mul, e2]
    · rw [indicator_of_notMem h2, mul_zero, e3, indicator_of_notMem]
      intro h'; exact h2 ⟨by linarith, by linarith [h'.1]⟩
  · have h2 : -w ∉ Icc (0 : ℝ) 1 := fun h' ↦ by linarith [h'.1]
    rw [indicator_of_notMem h2, add_zero]
    by_cases h1 : w ∈ Icc (0 : ℝ) 1
    · rw [indicator_of_mem h1, ← mul_assoc, hc, one_mul]
    · rw [indicator_of_notMem h1, mul_zero, e3, indicator_of_notMem]
      intro h'; exact h1 ⟨by linarith, h'.2⟩

end ArchS6
