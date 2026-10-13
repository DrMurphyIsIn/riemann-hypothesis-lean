import ArchS7_Lemma41
import ArchS3_Limits

/-!
# ArchS7_LogMap: the Mellin picture of `L²(ℝ)_ev` (first half of the (85) bridge)

The log map `Λ f (u) = √2 e^{u/2} f(e^u)` sends `L²(ℝ)_ev` isometrically into `L²(ℝ)`, intertwines the
scaling `θ s = ϑ(e^s)` with the translation `u ↦ u - s`, and `𝓕 ∘ Λ` is CC's Mellin transform
(diagonalising `ϑ`).  Consequences:

* `inner_thE_spectral`: `⟨y, ϑ(e^u) y⟩ = ∫ e^{-2πiuw} |𝓕Λy(w)|² dw`;
* `norm_sq_adjoint_theta_spectral`: `‖ϑ(g)† y‖² = ∫ hsq g (-2πw) |𝓕Λy(w)|² dw` for `IsWeilTest g`
  (the Mellin-diagonal form of `ϑ(g)ϑ(g)† = ϑ(g∗g*)`).

conjecture1_proved = False.
-/

open MeasureTheory Set Filter Topology FourierTransform
open scoped InnerProductSpace ComplexConjugate ENNReal

noncomputable section

namespace ArchS7

open ArchS6

set_option linter.unusedSectionVars false

/-! ### The substitution `x = e^u` -/

theorem exp_image_univ : Real.exp '' univ = Ioi 0 := by rw [image_univ, Real.range_exp]

theorem lintegral_comp_exp (f : ℝ → ℝ≥0∞) :
    ∫⁻ u, ENNReal.ofReal (Real.exp u) * f (Real.exp u) = ∫⁻ x in Ioi 0, f x := by
  have := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun x _ ↦ (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn f
  rw [exp_image_univ, Measure.restrict_univ] at this
  rw [this]
  simp only [abs_of_pos (Real.exp_pos _)]

theorem integral_comp_exp' (G : ℝ → ℂ) :
    ∫ u, (Real.exp u : ℂ) * G (Real.exp u) = ∫ x in Ioi 0, G x := by
  have := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ ↦ (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn G
  rw [exp_image_univ, Measure.restrict_univ] at this
  rw [this]
  congr 1; funext u
  rw [abs_of_pos (Real.exp_pos _), Complex.real_smul]

theorem integrable_comp_exp_iff (G : ℝ → ℂ) :
    Integrable (fun u ↦ (Real.exp u : ℂ) * G (Real.exp u)) ↔ IntegrableOn G (Ioi 0) := by
  have := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ ↦ (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn G
  rw [exp_image_univ, integrableOn_univ] at this
  rw [this]
  have e : (fun u ↦ |Real.exp u| • G (Real.exp u)) = fun u ↦ (Real.exp u : ℂ) * G (Real.exp u) := by
    funext u; rw [abs_of_pos (Real.exp_pos _), Complex.real_smul]
  rw [e]

/-- A.e. equality survives `u ↦ e^u`. -/
theorem ae_comp_exp {F G : ℝ → ℂ} (h : F =ᵐ[volume] G) :
    (fun u ↦ F (Real.exp u)) =ᵐ[volume] fun u ↦ G (Real.exp u) := by
  have h0 : volume {x | ¬ F x = G x} = 0 := ae_iff.1 h
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null h0
  have h1 : ∫⁻ u, ENNReal.ofReal (Real.exp u) * N.indicator 1 (Real.exp u) = 0 := by
    rw [lintegral_comp_exp]
    refine le_antisymm ?_ bot_le
    calc ∫⁻ x in Ioi 0, N.indicator 1 x ≤ ∫⁻ x, N.indicator 1 x := setLIntegral_le_lintegral _ _
      _ = volume N := lintegral_indicator_one hNm
      _ = 0 := hN0
  have hmeas : Measurable fun u ↦ ENNReal.ofReal (Real.exp u) * N.indicator 1 (Real.exp u) :=
    (ENNReal.measurable_ofReal.comp Real.measurable_exp).mul
      ((measurable_one.indicator hNm).comp Real.measurable_exp)
  have h2 := (lintegral_eq_zero_iff hmeas).1 h1
  filter_upwards [h2] with u hu
  by_contra hne
  have hmem : Real.exp u ∈ N := hNsub hne
  simp only [Pi.zero_apply, indicator_of_mem hmem, Pi.one_apply, mul_one,
    ENNReal.ofReal_eq_zero] at hu
  exact absurd hu (not_le.2 (Real.exp_pos u))

/-! ### The log map -/

/-- `Λ F (u) = √2 e^{u/2} F(e^u)`. -/
def logF (F : ℝ → ℂ) (u : ℝ) : ℂ := ((Real.sqrt 2 * Real.exp (u / 2) : ℝ) : ℂ) * F (Real.exp u)

theorem logF_congr {F G : ℝ → ℂ} (h : F =ᵐ[volume] G) : logF F =ᵐ[volume] logF G := by
  filter_upwards [ae_comp_exp h] with u hu
  simp only [logF] at *; rw [hu]

theorem sqrt2_exp_sq (u : ℝ) :
    ((Real.sqrt 2 * Real.exp (u / 2) : ℝ) : ℂ) * ((Real.sqrt 2 * Real.exp (u / 2) : ℝ) : ℂ)
      = 2 * (Real.exp u : ℂ) := by
  rw [← Complex.ofReal_mul]
  have : Real.sqrt 2 * Real.exp (u / 2) * (Real.sqrt 2 * Real.exp (u / 2)) = 2 * Real.exp u := by
    rw [show Real.sqrt 2 * Real.exp (u / 2) * (Real.sqrt 2 * Real.exp (u / 2))
        = (Real.sqrt 2 * Real.sqrt 2) * (Real.exp (u / 2) * Real.exp (u / 2)) by ring,
      Real.mul_self_sqrt (by norm_num), ← Real.exp_add, add_halves]
  rw [this]; push_cast; ring

theorem conj_logF_mul (F G : ℝ → ℂ) (u : ℝ) :
    conj (logF F u) * logF G u = (Real.exp u : ℂ) * (2 * (conj (F (Real.exp u)) * G (Real.exp u))) := by
  simp only [logF, map_mul, Complex.conj_ofReal]
  linear_combination (conj (F (Real.exp u)) * G (Real.exp u)) * sqrt2_exp_sq u

theorem norm_logF_sq (F : ℝ → ℂ) (u : ℝ) :
    ‖logF F u‖ ^ 2 = Real.exp u * (2 * ‖F (Real.exp u)‖ ^ 2) := by
  have he : Real.exp (u / 2) ^ 2 = Real.exp u := by rw [sq, ← Real.exp_add, add_halves]
  rw [logF, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), mul_pow,
    mul_pow, Real.sq_sqrt (by norm_num), he]
  ring

theorem aestronglyMeasurable_logF (f : L2R) : AEStronglyMeasurable (logF f) volume :=
  ((by fun_prop : Continuous fun u : ℝ ↦ ((Real.sqrt 2 * Real.exp (u / 2) : ℝ) : ℂ)).stronglyMeasurable.mul
    ((Lp.stronglyMeasurable f).comp_measurable Real.measurable_exp)).aestronglyMeasurable

theorem integrable_norm_logF_sq (f : L2R) : Integrable fun u ↦ ‖logF f u‖ ^ 2 := by
  have hf : Integrable fun x ↦ ((2 * ‖(f : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) :=
    (((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).1 (Lp.memLp f)).const_mul 2).ofReal
  have h := (integrable_comp_exp_iff fun x ↦ ((2 * ‖(f : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ)).2 hf.integrableOn
  have h2 := h.re
  refine h2.congr (Eventually.of_forall fun u ↦ ?_)
  show RCLike.re (((Real.exp u : ℝ) : ℂ) * ((2 * ‖(f : ℝ → ℂ) (Real.exp u)‖ ^ 2 : ℝ) : ℂ))
    = ‖logF f u‖ ^ 2
  rw [norm_logF_sq, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]

theorem memLp_logF (f : L2R) : MemLp (logF f) 2 volume :=
  (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_logF f)).2 (integrable_norm_logF_sq f)

/-- `Λ f` as an element of `L²(ℝ)`. -/
def logRaw (f : L2R) : L2R := (memLp_logF f).toLp _

theorem coeFn_logRaw (f : L2R) : (logRaw f : ℝ → ℂ) =ᵐ[volume] logF f := MemLp.coeFn_toLp _

theorem inner_logRaw (f g : L2R) :
    ⟪logRaw f, logRaw g⟫_ℂ = 2 * ∫ x in Ioi 0, conj ((f : ℝ → ℂ) x) * (g : ℝ → ℂ) x := by
  rw [MeasureTheory.L2.inner_def]
  have h1 : (fun u ↦ ⟪(logRaw f : ℝ → ℂ) u, (logRaw g : ℝ → ℂ) u⟫_ℂ) =ᵐ[volume]
      fun u ↦ (Real.exp u : ℂ) * (2 * (conj ((f : ℝ → ℂ) (Real.exp u)) * (g : ℝ → ℂ) (Real.exp u))) := by
    filter_upwards [coeFn_logRaw f, coeFn_logRaw g] with u e1 e2
    rw [e1, e2, RCLike.inner_apply', conj_logF_mul]
  rw [integral_congr_ae h1,
    integral_comp_exp' (fun x ↦ 2 * (conj ((f : ℝ → ℂ) x) * (g : ℝ → ℂ) x)), integral_const_mul]

theorem norm_logRaw_sq (f : L2R) :
    ‖logRaw f‖ ^ 2 = 2 * ∫ x in Ioi 0, ‖(f : ℝ → ℂ) x‖ ^ 2 := by
  have h := inner_logRaw f f
  rw [inner_self_eq_norm_sq_to_K] at h
  have e : (fun x ↦ conj ((f : ℝ → ℂ) x) * (f : ℝ → ℂ) x)
      = fun x ↦ ((‖(f : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
    funext x; rw [Complex.conj_mul']; push_cast; rfl
  rw [e, integral_complex_ofReal] at h
  have h3 : ((‖logRaw f‖ ^ 2 : ℝ) : ℂ) = ((2 * ∫ x in Ioi 0, ‖(f : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; rw [← h]; rfl
  exact Complex.ofReal_injective h3

theorem norm_logRaw_le (f : L2R) : ‖logRaw f‖ ≤ Real.sqrt 2 * ‖f‖ := by
  have h1 := norm_logRaw_sq f
  have h2 : ∫ x in Ioi 0, ‖(f : ℝ → ℂ) x‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [norm_sq_eq_integral]
    exact setIntegral_le_integral
      ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).1 (Lp.memLp f))
      (Eventually.of_forall fun x ↦ by positivity)
  have h3 : ‖logRaw f‖ ^ 2 ≤ (Real.sqrt 2 * ‖f‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]; linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3

/-- `Λ` as a continuous linear map `L²(ℝ) → L²(ℝ)`. -/
def logL : L2R →L[ℂ] L2R :=
  LinearMap.mkContinuous
    { toFun := logRaw
      map_add' := fun f g ↦ by
        apply Lp.ext
        filter_upwards [coeFn_logRaw (f + g), logF_congr (Lp.coeFn_add f g),
          Lp.coeFn_add (logRaw f) (logRaw g), coeFn_logRaw f, coeFn_logRaw g] with u e1 e2 e3 e4 e5
        rw [e1, e2, e3, Pi.add_apply, e4, e5]
        simp only [logF, Pi.add_apply]; ring
      map_smul' := fun c f ↦ by
        apply Lp.ext
        filter_upwards [coeFn_logRaw (c • f), logF_congr (Lp.coeFn_smul c f),
          Lp.coeFn_smul c (logRaw f), coeFn_logRaw f] with u e1 e2 e3 e4
        rw [e1, e2, RingHom.id_apply, e3, Pi.smul_apply, e4]
        simp only [logF, Pi.smul_apply, smul_eq_mul]; ring }
    (Real.sqrt 2) norm_logRaw_le

theorem logL_apply (f : L2R) : logL f = logRaw f := rfl

theorem coeFn_logL (f : L2R) : (logL f : ℝ → ℂ) =ᵐ[volume] logF f := coeFn_logRaw f

/-! ### Even functions: `Λ` is isometric -/

theorem integral_even_eq {h : ℝ → ℂ} (hi : Integrable h) (he : h =ᵐ[volume] fun x ↦ h (-x)) :
    ∫ x, h x = 2 * ∫ x in Ioi 0, h x := by
  rw [← integral_add_compl measurableSet_Ioi hi, compl_Ioi]
  have : ∫ x in Iic 0, h x = ∫ x in Ioi 0, h x := by
    have hn := integral_comp_neg_Ioi (c := (0 : ℝ)) (f := h)
    rw [neg_zero] at hn
    rw [← hn]
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards [he] with x hx _
    exact hx.symm
  rw [this]; ring

theorem even_ae {f : L2R} (hf : f ∈ evenL2) : (f : ℝ → ℂ) =ᵐ[volume] fun x ↦ (f : ℝ → ℂ) (-x) := by
  have h := coeFn_reflect f
  rw [mem_evenL2.1 hf] at h
  exact h

theorem inner_even_eq {f g : L2R} (hf : f ∈ evenL2) (hg : g ∈ evenL2) :
    ⟪f, g⟫_ℂ = 2 * ∫ x in Ioi 0, conj ((f : ℝ → ℂ) x) * (g : ℝ → ℂ) x := by
  rw [MeasureTheory.L2.inner_def]
  have e : (fun x ↦ ⟪(f : ℝ → ℂ) x, (g : ℝ → ℂ) x⟫_ℂ) = fun x ↦ conj ((f : ℝ → ℂ) x) * (g : ℝ → ℂ) x := by
    funext x; rw [RCLike.inner_apply']
  rw [e]
  refine integral_even_eq ?_ ?_
  · have := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) f g
    refine this.congr (Eventually.of_forall fun x ↦ ?_)
    simp only [RCLike.inner_apply']
  · filter_upwards [even_ae hf, even_ae hg] with x e1 e2
    rw [e1, e2]

/-- **`Λ` preserves inner products on `L²(ℝ)_ev`.** -/
theorem inner_logL_even {f g : L2R} (hf : f ∈ evenL2) (hg : g ∈ evenL2) :
    ⟪logL f, logL g⟫_ℂ = ⟪f, g⟫_ℂ := by
  rw [logL_apply, logL_apply, inner_logRaw, inner_even_eq hf hg]

/-! ### `Λ` intertwines `θ` with translations -/

/-- Translation `η ↦ η(· - s)` on `L²(ℝ)`. -/
def transL (s : ℝ) : L2R →ₗᵢ[ℂ] L2R :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun u : ℝ ↦ u - s) (measurePreserving_sub_right volume s)

theorem coeFn_transL (s : ℝ) (η : L2R) :
    (transL s η : ℝ → ℂ) =ᵐ[volume] fun u ↦ (η : ℝ → ℂ) (u - s) :=
  Lp.coeFn_compMeasurePreserving _ _

theorem ae_comp_sub {F G : ℝ → ℂ} (h : F =ᵐ[volume] G) (s : ℝ) :
    (fun u ↦ F (u - s)) =ᵐ[volume] fun u ↦ G (u - s) :=
  (measurePreserving_sub_right volume s).quasiMeasurePreserving.ae_eq h

theorem logL_thL (s : ℝ) (f : L2R) : logL (thL s f) = transL s (logL f) := by
  apply Lp.ext
  filter_upwards [coeFn_logL (thL s f), logF_congr (coeFn_thL s f), coeFn_transL s (logL f),
    ae_comp_sub (coeFn_logL f) s] with u e1 e2 e3 e4
  rw [e1, e2, e3, e4]
  simp only [logF, thF]
  have h1 : Real.exp (-s) * Real.exp u = Real.exp (u - s) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : ((Real.sqrt 2 * Real.exp (u / 2) : ℝ) : ℂ) * (Real.exp (-s / 2) : ℂ)
      = ((Real.sqrt 2 * Real.exp ((u - s) / 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, mul_assoc, ← Real.exp_add]; congr 3; ring
  rw [h1, ← mul_assoc, h2]

/-! ### Fourier transform of a translation -/

/-- The modulation factor `e^{-2πisw}`. -/
def mo (s w : ℝ) : ℂ := Complex.exp (↑(-2 * Real.pi * s * w) * Complex.I)

theorem norm_mo (s w : ℝ) : ‖mo s w‖ = 1 := by
  rw [mo, Complex.norm_exp_ofReal_mul_I]

theorem continuous_mo (s : ℝ) : Continuous (mo s) := by unfold mo; fun_prop

theorem memLp_mo_mul (s : ℝ) (η : L2R) : MemLp (fun w ↦ mo s w * (η : ℝ → ℂ) w) 2 volume :=
  (Lp.memLp η).of_le ((continuous_mo s).aestronglyMeasurable.mul (Lp.aestronglyMeasurable η))
    (Eventually.of_forall fun w ↦ by rw [norm_mul, norm_mo, one_mul])

/-- Modulation by `e^{-2πisw}` as a linear isometry of `L²(ℝ)`. -/
def modL (s : ℝ) : L2R →ₗᵢ[ℂ] L2R where
  toFun η := (memLp_mo_mul s η).toLp _
  map_add' η ζ := by
    apply Lp.ext
    filter_upwards [(memLp_mo_mul s (η + ζ)).coeFn_toLp, Lp.coeFn_add η ζ,
      Lp.coeFn_add ((memLp_mo_mul s η).toLp _) ((memLp_mo_mul s ζ).toLp _),
      (memLp_mo_mul s η).coeFn_toLp, (memLp_mo_mul s ζ).coeFn_toLp] with w e1 e2 e3 e4 e5
    rw [e3, Pi.add_apply, e4, e5, e1, e2, Pi.add_apply]; ring
  map_smul' c η := by
    apply Lp.ext
    filter_upwards [(memLp_mo_mul s (c • η)).coeFn_toLp, Lp.coeFn_smul c η,
      Lp.coeFn_smul c ((memLp_mo_mul s η).toLp _), (memLp_mo_mul s η).coeFn_toLp] with w e1 e2 e3 e4
    rw [RingHom.id_apply, e3, Pi.smul_apply, e4, e1, e2, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  norm_map' η := by
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    refine (eLpNorm_congr_ae (memLp_mo_mul s η).coeFn_toLp).trans ?_
    refine eLpNorm_congr_norm_ae (Eventually.of_forall fun w ↦ ?_)
    rw [norm_mul, norm_mo, one_mul]

theorem coeFn_modL (s : ℝ) (η : L2R) :
    (modL s η : ℝ → ℂ) =ᵐ[volume] fun w ↦ mo s w * (η : ℝ → ℂ) w :=
  (memLp_mo_mul s η).coeFn_toLp

theorem fourier_comp_sub (s : ℝ) (F : ℝ → ℂ) (w : ℝ) :
    𝓕 (fun u ↦ F (u - s)) w = mo s w * 𝓕 F w := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_add_right_eq_self (μ := volume)
      (fun v ↦ Complex.exp (↑(-2 * Real.pi * v * w) * Complex.I) • F (v - s)) s,
    ← integral_const_mul]
  congr 1; funext v
  simp only [add_sub_cancel_right, smul_eq_mul, mo]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2; push_cast; ring

/-- **`𝓕` turns translation into modulation on `L²(ℝ)`.** -/
theorem fourier_transL (s : ℝ) (η : L2R) :
    (𝓕 (transL s η : L2R) : L2R) = modL s (𝓕 η) := by
  refine L2R_eq_of_integrable (A := fun η ↦ (𝓕 (transL s η : L2R) : L2R))
    (B := fun η ↦ modL s (𝓕 η)) (continuous_fourier_L2R.comp (transL s).continuous)
    ((modL s).continuous.comp continuous_fourier_L2R) (fun η hη ↦ ?_) η
  have hint : Integrable (transL s η : ℝ → ℂ) :=
    (hη.comp_sub_right s).congr (coeFn_transL s η).symm
  apply Lp.ext
  filter_upwards [fourier_ae_eq (transL s η) hint, coeFn_modL s (𝓕 η), fourier_ae_eq η hη] with w e1 e2 e3
  rw [e1, e2, e3, fourier_congr_ae (coeFn_transL s η), fourier_comp_sub]

/-! ### The spectral formula -/

/-- `𝓕Λy`, CC's Mellin transform (up to the variable `t = -2πw`). -/
def mellinL : L2R →L[ℂ] L2R := fourierL ∘L logL

theorem mellinL_apply (f : L2R) : mellinL f = 𝓕 (logL f) := rfl

/-- **`⟨y, ϑ(e^u) y⟩ = ∫ e^{-2πiuw} |𝓕Λy(w)|² dw`** on `L²(ℝ)_ev`. -/
theorem inner_thE_spectral (y : evenL2) (u : ℝ) :
    ⟪y, thE u y⟫_ℂ = ∫ w, mo u w * ((‖(mellinL y : ℝ → ℂ) w‖ ^ 2 : ℝ) : ℂ) := by
  rw [Submodule.coe_inner, coe_thE, ← inner_logL_even y.2 (thL_mem_evenL2 u y.2), logL_thL,
    ← Lp.inner_fourier_eq, fourier_transL, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_modL u (𝓕 (logL (y : L2R)))] with w e1
  rw [e1, RCLike.inner_apply', mellinL_apply]
  rw [← mul_assoc, mul_comm _ (mo u w), mul_assoc, Complex.conj_mul']
  push_cast; ring

/-- **The Mellin-diagonal form of `‖ϑ(g)† y‖²`.** -/
theorem norm_sq_adjoint_theta_spectral {g : ℝ → ℂ} (hW : WeilExplicit.IsWeilTest g)
    (hg : Integrable g) (y : evenL2) :
    ‖(ContinuousLinearMap.adjoint (theta g hg)) y‖ ^ 2
      = ∫ w, RvMBridge31.hsq g (-2 * Real.pi * w) * ‖(mellinL y : ℝ → ℂ) w‖ ^ 2 := by
  set M : ℝ → ℝ := fun w ↦ ‖(mellinL y : ℝ → ℂ) w‖ ^ 2
  have hM : Integrable M :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).1 (Lp.memLp _)
  have hA := RvMBridge5.isWeilTest_autocorr hW
  have hAi : Integrable (WeilExplicit.autocorr g) :=
    hA.1.continuous.integrable_of_hasCompactSupport hA.2
  have h1 := hcoef_theta g hg hW.1.continuous y
  simp_rw [show ∀ u, ⟪y, scalingEven.θ u y⟫_ℂ = ⟪y, thE u y⟫_ℂ from fun _ ↦ rfl,
    inner_thE_spectral] at h1
  have hF : Integrable (Function.uncurry fun u w ↦
      WeilExplicit.autocorr g u * (mo u w * ((M w : ℝ) : ℂ))) (volume.prod volume) := by
    have hB : Integrable (fun z : ℝ × ℝ ↦ WeilExplicit.autocorr g z.1 * ((M z.2 : ℝ) : ℂ))
        (volume.prod volume) := hAi.mul_prod hM.ofReal
    refine Integrable.mono' hB.norm ?_ (Eventually.of_forall fun z ↦ ?_)
    · refine (hA.1.continuous.comp continuous_fst).aestronglyMeasurable.mul ?_
      refine ((by unfold mo; fun_prop : Continuous fun z : ℝ × ℝ ↦ mo z.1 z.2).aestronglyMeasurable).mul ?_
      exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
        hM.1.comp_snd)
    · simp only [Function.uncurry, norm_mul, norm_mo, one_mul]
      rfl
  simp_rw [← integral_const_mul] at h1
  rw [integral_integral_swap hF] at h1
  have h2 : ∀ w, ∫ u, WeilExplicit.autocorr g u * (mo u w * ((M w : ℝ) : ℂ))
      = ((RvMBridge31.hsq g (-2 * Real.pi * w) * M w : ℝ) : ℂ) := by
    intro w
    have hp := RvMBridge31.paperFT_autocorr_eq hW (-2 * Real.pi * w)
    unfold Zeta23.paperFT at hp
    rw [show (fun u ↦ WeilExplicit.autocorr g u * (mo u w * ((M w : ℝ) : ℂ)))
        = fun u ↦ (WeilExplicit.autocorr g u * Complex.exp (Complex.I * ((-2 * Real.pi * w : ℝ) : ℂ)
          * (u : ℂ))) * ((M w : ℝ) : ℂ) by
      funext u; unfold mo
      rw [show (((-2 * Real.pi * u * w : ℝ) : ℂ) * Complex.I)
          = Complex.I * ((-2 * Real.pi * w : ℝ) : ℂ) * (u : ℂ) by push_cast; ring]
      ring,
      integral_mul_const, hp]
    push_cast; ring
  simp_rw [h2] at h1
  rw [integral_complex_ofReal] at h1
  exact_mod_cast h1

end ArchS7
