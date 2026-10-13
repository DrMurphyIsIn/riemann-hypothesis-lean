import ArchS6_Kernel

/-!
# ArchS6_Strict: `|λ(n)| < 1` (no nonzero function is concentrated in `[-1,1]` on both sides)

`eq_zero_of_P1_fourier`: if `f ∈ L²(ℝ)` has `P₁ f = f` and `P₁ 𝓕 f = 𝓕 f` then `f = 0`.
Proof: `𝓕 f` is a.e. the restriction to `ℝ` of the entire function
`z ↦ ∫_{-1}^{1} e^{-2πizv} f(v) dv` (`entireFT`, differentiated under the integral sign); it vanishes on
an open interval, hence everywhere (identity theorem), so `‖f‖ = ‖𝓕 f‖ = 0`.

`abs_lt_one_of_eigen`: a unit `ξ ∈ ran P₁` with `P₁ 𝓕 ξ = λ ξ` has `|λ| < 1`.  This is what makes
CC's `ζ_n = ψ_n/√(1 - λ(n)²)` well defined (CC Prop 4.5 (iii)); CC use it implicitly.

conjecture1_proved = False.
-/

open MeasureTheory Set Filter FourierTransform Complex Topology Metric
open scoped ENNReal InnerProductSpace Real

noncomputable section

namespace ArchS6

open ArchS5

set_option linter.unusedSectionVars false

/-- The entire extension `z ↦ ∫_{-1}^{1} e^{-2πizv} h(v) dv` of the finite Fourier transform. -/
def entireFT (h : L2I (-1) 1) (z : ℂ) : ℂ :=
  ∫ v in Icc (-1 : ℝ) 1, cexp ((-2 * π * I * v) * z) * h v

theorem norm_coef_le {v : ℝ} (hv : v ∈ Icc (-1 : ℝ) 1) : ‖(-2 * π * I * v : ℂ)‖ ≤ 2 * π := by
  have hv' : |v| ≤ 1 := abs_le.2 ⟨hv.1, hv.2⟩
  rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  nlinarith [Real.pi_pos]

theorem norm_cexp_coef_le {v : ℝ} (hv : v ∈ Icc (-1 : ℝ) 1) {z₀ z : ℂ} (hz : z ∈ ball z₀ 1) :
    ‖cexp ((-2 * π * I * v) * z)‖ ≤ Real.exp (2 * π * (‖z₀‖ + 1)) := by
  refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ?_)
  rw [norm_mul]
  have hz' : ‖z‖ ≤ ‖z₀‖ + 1 := by
    have := norm_le_norm_add_norm_sub' z z₀
    rw [mem_ball, dist_eq_norm] at hz
    linarith
  exact mul_le_mul (norm_coef_le hv) hz' (norm_nonneg _) (by positivity)

theorem hasDerivAt_entireFT (h : L2I (-1) 1) (z₀ : ℂ) :
    HasDerivAt (entireFT h)
      (∫ v in Icc (-1 : ℝ) 1, (-2 * π * I * v) * cexp ((-2 * π * I * v) * z₀) * h v) z₀ := by
  have hhi : Integrable (h : ℝ → ℂ) (volI (-1) 1) := (Lp.memLp h).integrable (by norm_num)
  set M := Real.exp (2 * π * (‖z₀‖ + 1))
  have hcont : ∀ z : ℂ, Continuous fun v : ℝ ↦ cexp ((-2 * π * I * v) * z) := fun z ↦ by
    fun_prop
  have hmem := ae_restrict_mem (μ := volume) (measurableSet_Icc (a := (-1 : ℝ)) (b := 1))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volI (-1) 1)
    (F := fun (z : ℂ) (v : ℝ) ↦ cexp ((-2 * π * I * v) * z) * h v)
    (F' := fun (z : ℂ) (v : ℝ) ↦ (-2 * π * I * v) * cexp ((-2 * π * I * v) * z) * h v)
    (bound := fun v ↦ 2 * π * M * ‖h v‖) (x₀ := z₀) (s := ball z₀ 1) (ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z ↦ (hcont z).aestronglyMeasurable.mul (Lp.aestronglyMeasurable h))
    (hhi.bdd_mul (c := M) (hcont z₀).aestronglyMeasurable (by
      filter_upwards [hmem] with v hv
      exact norm_cexp_coef_le hv (mem_ball_self one_pos)))
    (((by fun_prop : Continuous fun v : ℝ ↦ (-2 * π * I * v : ℂ)).mul
      (hcont z₀)).aestronglyMeasurable.mul (Lp.aestronglyMeasurable h))
    (by
      filter_upwards [hmem] with v hv z hz
      rw [norm_mul, norm_mul, mul_assoc]
      have h1 := norm_coef_le hv
      have h2 := norm_cexp_coef_le hv hz
      have : ‖cexp ((-2 * π * I * v) * z)‖ * ‖(h : ℝ → ℂ) v‖ ≤ M * ‖(h : ℝ → ℂ) v‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      calc ‖(-2 * π * I * v : ℂ)‖ * (‖cexp ((-2 * π * I * v) * z)‖ * ‖(h : ℝ → ℂ) v‖)
          ≤ (2 * π) * (M * ‖(h : ℝ → ℂ) v‖) :=
            mul_le_mul h1 this (by positivity) (by positivity)
        _ = 2 * π * M * ‖(h : ℝ → ℂ) v‖ := by ring)
    (hhi.norm.const_mul _)
    (ae_of_all _ fun v z _ ↦ by
      have := (((hasDerivAt_id z).const_mul (-2 * π * I * v : ℂ)).cexp).mul_const ((h : ℝ → ℂ) v)
      simp only [id, mul_one] at this
      exact this.congr_deriv (by ring))
  exact key.2

theorem differentiable_entireFT (h : L2I (-1) 1) : Differentiable ℂ (entireFT h) :=
  fun z ↦ (hasDerivAt_entireFT h z).differentiableAt

theorem entireFT_ofReal (h : L2I (-1) 1) (w : ℝ) :
    entireFT h w = ∫ v in Icc (-1 : ℝ) 1, fourierK (w, v) * h v := by
  unfold entireFT fourierK
  congr 1; funext v
  congr 2
  push_cast; ring

theorem tendsto_add_inv (m c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ ((m + c * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) atTop (𝓝[≠] (m : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have h : Tendsto (fun n : ℕ ↦ (m + c * (1 / ((n : ℝ) + 1)))) atTop (𝓝 (m + c * 0)) :=
      tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul c)
    rw [mul_zero, add_zero] at h
    exact (Complex.continuous_ofReal.tendsto m).comp h
  · refine Eventually.of_forall fun n ↦ ?_
    simp only [mem_compl_iff, mem_singleton_iff]
    intro heq
    have : m + c * (1 / ((n : ℝ) + 1)) = m := by exact_mod_cast heq
    have hpos : (0 : ℝ) < c * (1 / ((n : ℝ) + 1)) := by positivity
    linarith

/-- **Uniqueness**: if `f` is supported in `[-1, 1]` and `𝓕 f` vanishes a.e. on a nonempty open
interval, then `f = 0` (`𝓕 f` extends to an entire function). -/
theorem eq_zero_of_fourier_ae_zero_Ioo {f : L2R} (h1 : P1 f = f) {a b : ℝ} (hab : a < b)
    (hz : ∀ᵐ w ∂volume, w ∈ Ioo a b → ((𝓕 f : L2R) : ℝ → ℂ) w = 0) : f = 0 := by
  set h := restrictIcc (-1) 1 f
  have hf : extendIcc (-1) 1 h = f := h1
  set G : ℝ → ℂ := fun w ↦ ∫ v in Icc (-1 : ℝ) 1, fourierK (w, v) * h v with hGdef
  have hFG : ((𝓕 f : L2R) : ℝ → ℂ) =ᵐ[volume] G := by
    rw [← hf]
    filter_upwards [fourier_ae_eq _ (integrable_extendIcc _ _ h)] with w hw
    rw [hw, fourier_extendIcc_eq]
  have hGcont : Continuous G := by
    have : G = 𝓕 (extendIcc (-1) 1 h : ℝ → ℂ) := funext fun w ↦ (fourier_extendIcc_eq _ _ _ _).symm
    rw [this]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner
      (integrable_extendIcc _ _ h)
  have hG0 : EqOn G 0 (Ioo a b) := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ isOpen_Ioo hGcont.continuousOn
      continuousOn_const
    rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hz, hFG] with w hw e hw'
    rw [← e]; exact hw hw'
  have han : AnalyticOnNhd ℂ (entireFT h) univ := fun z _ ↦ (differentiable_entireFT h).analyticAt z
  set m := (a + b) / 2
  set c := (b - a) / 4
  have hc : 0 < c := by simp only [c]; linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] (m : ℂ), entireFT h z = 0 := by
    refine (tendsto_add_inv m c hc).frequently (Frequently.of_forall fun n ↦ ?_)
    rw [entireFT_ofReal]
    have hpos : (0 : ℝ) < c * (1 / ((n : ℝ) + 1)) := by positivity
    have hle : c * (1 / ((n : ℝ) + 1)) ≤ c := by
      have : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      nlinarith
    exact hG0 ⟨by simp only [m]; linarith, by simp only [m, c] at hle ⊢; linarith⟩
  have hall := han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (mem_univ _) hfreq
  have hG : ∀ w, G w = 0 := fun w ↦ by
    have := hall (mem_univ (w : ℂ))
    rw [entireFT_ofReal] at this
    exact this
  have hF0 : (𝓕 f : L2R) = 0 := by
    apply Lp.ext
    filter_upwards [hFG, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with w e1 e2
    rw [e1, e2, hG]; rfl
  have : ‖f‖ = 0 := by rw [← Lp.norm_fourier_eq, hF0, norm_zero]
  exact norm_eq_zero.1 this

/-- **No nonzero `f ∈ L²(ℝ)` has both `f` and `𝓕 f` supported in `[-1, 1]`.** -/
theorem eq_zero_of_P1_fourier {f : L2R} (h1 : P1 f = f) (h2 : P1 (𝓕 f) = 𝓕 f) : f = 0 := by
  refine eq_zero_of_fourier_ae_zero_Ioo h1 (a := 1) (b := 2) (by norm_num) ?_
  have := coeFn_P1 (𝓕 f)
  rw [h2] at this
  filter_upwards [this] with w e1 hw
  rw [e1, indicator_of_notMem]
  intro h'; exact absurd h'.2 (not_le.2 hw.1)

/-- If `f` is supported in `[-1, 1]` and `𝓕 f` vanishes on `[-1, 1]`, then `f = 0`. -/
theorem eq_zero_of_P1_fourier_eq_zero {f : L2R} (h1 : P1 f = f) (h2 : P1 (𝓕 f) = 0) : f = 0 := by
  refine eq_zero_of_fourier_ae_zero_Ioo h1 (a := -1) (b := 1) (by norm_num) ?_
  have := (P1_eq_zero_iff _).1 h2
  rw [EventuallyEq, ae_restrict_iff' measurableSet_Icc] at this
  filter_upwards [this] with w hw hw'
  exact hw (Ioo_subset_Icc_self hw')

/-- **`|λ| < 1`** for every eigenvalue of `P₁ F P₁` on `ran P₁`. -/
theorem abs_lt_one_of_eigen {ξ : L2R} (hξ : ‖ξ‖ = 1) (hP : P1 ξ = ξ) {c : ℝ}
    (heig : P1 (𝓕 ξ) = (c : ℂ) • ξ) : |c| < 1 := by
  have hnorm : ‖P1 (𝓕 ξ)‖ = |c| := by
    rw [heig, norm_smul, hξ, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hle : |c| ≤ 1 := by
    rw [← hnorm, ← hξ, ← Lp.norm_fourier_eq ξ]; exact isOrthProj_P1.norm_le _
  refine lt_of_le_of_ne hle fun heq ↦ ?_
  have hpy := isOrthProj_P1.norm_sq_eq (𝓕 ξ : L2R)
  rw [hnorm, heq, Lp.norm_fourier_eq, hξ] at hpy
  have h0 : ‖(𝓕 ξ : L2R) - P1 (𝓕 ξ)‖ = 0 := by nlinarith [norm_nonneg ((𝓕 ξ : L2R) - P1 (𝓕 ξ))]
  have hfix : P1 (𝓕 ξ) = 𝓕 ξ := (sub_eq_zero.1 (norm_eq_zero.1 h0)).symm
  have := eq_zero_of_P1_fourier hP hfix
  rw [this, norm_zero] at hξ
  exact zero_ne_one hξ

/-- Every eigenvalue of `P₁ F P₁` on `ran P₁` is nonzero (no eigenvalue `0`). -/
theorem ne_zero_of_eigen {ξ : L2R} (hξ : ‖ξ‖ = 1) (hP : P1 ξ = ξ) {c : ℝ}
    (heig : P1 (𝓕 ξ) = (c : ℂ) • ξ) : c ≠ 0 := by
  intro hc
  rw [hc, Complex.ofReal_zero, zero_smul] at heig
  have := eq_zero_of_P1_fourier_eq_zero hP heig
  rw [this, norm_zero] at hξ
  exact zero_ne_one hξ

end ArchS6
