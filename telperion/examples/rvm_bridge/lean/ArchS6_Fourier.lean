import Mathlib

/-!
# ArchS6_Fourier: the `L²` Fourier transform on `L¹ ∩ L²`, reflection, even functions

Mathlib (this pin) defines the Fourier transform on `L²(ℝ)` as the isometric extension of the
Schwartz-space Fourier transform (`MeasureTheory.Lp.fourierTransformₗᵢ`, notation `𝓕`, `𝓕⁻`), with
Plancherel (`Lp.norm_fourier_eq`, `Lp.inner_fourier_eq`) and agreement on Schwartz functions and on
tempered distributions.  It does **not** identify `𝓕 f` with the Fourier integral when `f ∈ L¹ ∩ L²`.
This file proves that identification, which is what every concrete kernel computation needs.

Conventions (Mathlib's, = CC's `F_{e_ℝ}`): `𝓕 f (w) = ∫ e^{-2πi v w} f(v) dv`,
`𝓕⁻ f (w) = ∫ e^{2πi v w} f(v) dv`.

* `fourier_ae_eq`, `fourierInv_ae_eq`: for `f ∈ L²` with `f` integrable, `𝓕 f = 𝓕 (⇑f)` a.e.
* `reflect`: `f ↦ f(-·)` on `L²`; `fourierInv_eq_reflect_fourier`, `fourier_reflect`.
* `evenL2`: the closed subspace `L²(ℝ)_ev`; on it `𝓕⁻ = 𝓕`, `𝓕 ∘ 𝓕 = 1`, `⟪𝓕 f, g⟫ = ⟪f, 𝓕 g⟫`.

conjecture1_proved = False.
-/

open MeasureTheory SchwartzMap FourierTransform Filter
open scoped ENNReal Topology InnerProductSpace ContDiff

noncomputable section

namespace ArchS6

set_option linter.unusedSectionVars false

/-- `L²(ℝ)` with complex values and Lebesgue measure. -/
abbrev L2R : Type := Lp (α := ℝ) ℂ 2 volume

/-! ### The Fourier integral against Schwartz functions -/

/-- The `L²` Fourier transform tested against a Schwartz function (tempered distributions). -/
theorem integral_smul_fourier_Lp (f : L2R) (φ : 𝓢(ℝ, ℂ)) :
    ∫ x, φ x • (𝓕 f : L2R) x = ∫ x, (𝓕 φ : 𝓢(ℝ, ℂ)) x • f x := by
  rw [← Lp.toTemperedDistribution_apply (𝓕 f) φ, ← Lp.fourier_toTemperedDistribution_eq,
    TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply]

/-- The inverse `L²` Fourier transform tested against a Schwartz function. -/
theorem integral_smul_fourierInv_Lp (f : L2R) (φ : 𝓢(ℝ, ℂ)) :
    ∫ x, φ x • (𝓕⁻ f : L2R) x = ∫ x, (𝓕⁻ φ : 𝓢(ℝ, ℂ)) x • f x := by
  rw [← Lp.toTemperedDistribution_apply (𝓕⁻ f) φ, ← Lp.fourierInv_toTemperedDistribution_eq,
    TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply]

/-- Multiplication formula `∫ 𝓕φ · g = ∫ φ · 𝓕g` for integrable functions on `ℝ`. -/
theorem integral_fourier_smul_eq {φ g : ℝ → ℂ} (hφ : Integrable φ) (hg : Integrable g) :
    ∫ x, 𝓕 φ x • g x = ∫ x, φ x • 𝓕 g x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := (volume : Measure ℝ))
    (ν := volume) (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner hφ hg
  refine h.trans ?_
  congr 1
  funext x
  congr 1
  simp only [Real.fourier_eq, VectorFourier.fourierIntegral, LinearMap.flip_apply,
    innerₗ_apply_apply, real_inner_comm]

/-- Multiplication formula for the inverse transform. -/
theorem integral_fourierInv_smul_eq {φ g : ℝ → ℂ} (hφ : Integrable φ) (hg : Integrable g) :
    ∫ x, 𝓕⁻ φ x • g x = ∫ x, φ x • 𝓕⁻ g x := by
  have hcont : Continuous fun p : ℝ × ℝ ↦ (-innerₗ ℝ) p.1 p.2 := by
    simp only [LinearMap.neg_apply, innerₗ_apply_apply]
    exact continuous_inner.neg
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := (volume : Measure ℝ))
    (ν := volume) (L := -innerₗ ℝ) Real.continuous_fourierChar hcont hφ hg
  refine h.trans ?_
  congr 1
  funext x
  congr 1
  simp only [Real.fourierInv_eq, VectorFourier.fourierIntegral, LinearMap.flip_apply,
    LinearMap.neg_apply, innerₗ_apply_apply, real_inner_comm, neg_neg]

/-- Smooth compactly supported real test functions, viewed as complex Schwartz functions. -/
def testSchwartz (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) : 𝓢(ℝ, ℂ) :=
  (hgc.comp_left (g := Complex.ofRealCLM) (by simp)).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hg)

theorem testSchwartz_apply (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (x : ℝ) :
    testSchwartz g hg hgc x = (g x : ℂ) := rfl

theorem smul_eq_testSchwartz_smul (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (F : ℝ → ℂ) : (fun x ↦ g x • F x) = fun x ↦ testSchwartz g hg hgc x • F x := by
  funext x
  rw [testSchwartz_apply, Complex.real_smul, smul_eq_mul]

/-! ### `𝓕` on `L¹ ∩ L²` -/

/-- **The `L²` Fourier transform is the Fourier integral on `L¹ ∩ L²`.** -/
theorem fourier_ae_eq (f : L2R) (hf : Integrable (f : ℝ → ℂ)) :
    (𝓕 f : L2R) =ᵐ[volume] 𝓕 (f : ℝ → ℂ) := by
  have hcont : Continuous (𝓕 (f : ℝ → ℂ)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf
  refine ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp _).locallyIntegrable (by norm_num))
    hcont.locallyIntegrable fun g hg hgc ↦ ?_
  rw [smul_eq_testSchwartz_smul g hg hgc, smul_eq_testSchwartz_smul g hg hgc,
    integral_smul_fourier_Lp, SchwartzMap.fourier_coe,
    integral_fourier_smul_eq (SchwartzMap.integrable _) hf]

/-- The inverse `L²` Fourier transform is the inverse Fourier integral on `L¹ ∩ L²`. -/
theorem fourierInv_ae_eq (f : L2R) (hf : Integrable (f : ℝ → ℂ)) :
    (𝓕⁻ f : L2R) =ᵐ[volume] 𝓕⁻ (f : ℝ → ℂ) := by
  have hcont : Continuous (𝓕⁻ (f : ℝ → ℂ)) := by
    rw [Real.fourierInv_eq_fourier_comp_neg]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner
      hf.comp_neg
  refine ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp _).locallyIntegrable (by norm_num))
    hcont.locallyIntegrable fun g hg hgc ↦ ?_
  rw [smul_eq_testSchwartz_smul g hg hgc, smul_eq_testSchwartz_smul g hg hgc,
    integral_smul_fourierInv_Lp, SchwartzMap.fourierInv_coe,
    integral_fourierInv_smul_eq (SchwartzMap.integrable _) hf]

/-! ### Density of `L¹ ∩ L²` -/

/-- Two continuous maps on `L²(ℝ)` that agree on the integrable elements agree everywhere. -/
theorem L2R_eq_of_integrable {Y : Type*} [TopologicalSpace Y] [T2Space Y] {A B : L2R → Y}
    (hA : Continuous A) (hB : Continuous B)
    (h : ∀ f : L2R, Integrable (f : ℝ → ℂ) → A f = B f) (f : L2R) : A f = B f := by
  have hd := SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2) (μ := volume)
    ENNReal.ofNat_ne_top
  have := hd.equalizer hA hB (funext fun φ ↦ h _ ?_)
  · exact congrFun this f
  · exact φ.integrable.congr (φ.coeFn_toLp 2 volume).symm

/-! ### Reflection -/

/-- `x ↦ -x` preserves Lebesgue measure. -/
theorem measurePreserving_neg_real : MeasurePreserving (fun x : ℝ ↦ -x) volume volume :=
  Measure.measurePreserving_neg volume

/-- The reflection `f ↦ f(-·)` on `L²(ℝ)`, a linear isometry. -/
def reflect : L2R →ₗᵢ[ℂ] L2R :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ ↦ -x) measurePreserving_neg_real

/-- The reflection as a continuous linear map. -/
def reflectL : L2R →L[ℂ] L2R := reflect.toContinuousLinearMap

theorem reflectL_apply (f : L2R) : reflectL f = reflect f := rfl

theorem coeFn_reflect (f : L2R) : (reflect f : ℝ → ℂ) =ᵐ[volume] fun x ↦ f (-x) :=
  Lp.coeFn_compMeasurePreserving _ _

theorem ae_eq_comp_neg {F G : ℝ → ℂ} (h : F =ᵐ[volume] G) :
    (fun x ↦ F (-x)) =ᵐ[volume] fun x ↦ G (-x) :=
  measurePreserving_neg_real.quasiMeasurePreserving.ae_eq_comp h

theorem reflect_reflect (f : L2R) : reflect (reflect f) = f := by
  apply Lp.ext
  filter_upwards [coeFn_reflect (reflect f), ae_eq_comp_neg (coeFn_reflect f)] with x h1 h2
  rw [h1, h2, neg_neg]

theorem integrable_reflect {f : L2R} (hf : Integrable (f : ℝ → ℂ)) :
    Integrable (reflect f : ℝ → ℂ) :=
  hf.comp_neg.congr (coeFn_reflect f).symm

theorem continuous_fourier_L2R : Continuous (fun f : L2R ↦ (𝓕 f : L2R)) :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).continuous

theorem continuous_fourierInv_L2R : Continuous (fun f : L2R ↦ (𝓕⁻ f : L2R)) :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).symm.continuous

/-- `𝓕⁻ = R ∘ 𝓕` on `L²(ℝ)`. -/
theorem fourierInv_eq_reflect_fourier (f : L2R) : (𝓕⁻ f : L2R) = reflect (𝓕 f) := by
  refine L2R_eq_of_integrable continuous_fourierInv_L2R
    (reflect.continuous.comp continuous_fourier_L2R) (fun f hf ↦ ?_) f
  change (𝓕⁻ f : L2R) = reflect (𝓕 f)
  apply Lp.ext
  filter_upwards [fourierInv_ae_eq f hf, coeFn_reflect (𝓕 f),
    ae_eq_comp_neg (fourier_ae_eq f hf)] with x h1 h2 h3
  rw [h1, h2, h3, Real.fourierInv_eq_fourier_neg]

/-- `𝓕 ∘ R = R ∘ 𝓕` on `L²(ℝ)`. -/
theorem fourier_reflect (f : L2R) : (𝓕 (reflect f) : L2R) = reflect (𝓕 f) := by
  refine L2R_eq_of_integrable (continuous_fourier_L2R.comp reflect.continuous)
    (reflect.continuous.comp continuous_fourier_L2R) (fun f hf ↦ ?_) f
  change (𝓕 (reflect f) : L2R) = reflect (𝓕 f)
  apply Lp.ext
  have h0 : 𝓕 (reflect f : ℝ → ℂ) = 𝓕 (fun x ↦ (f : ℝ → ℂ) (-x)) := by
    funext w; exact Real.fourier_congr_ae (coeFn_reflect f) w
  filter_upwards [fourier_ae_eq _ (integrable_reflect hf), coeFn_reflect (𝓕 f),
    ae_eq_comp_neg (fourier_ae_eq f hf)] with x h1 h2 h3
  rw [h1, h2, h3, h0, ← Real.fourierInv_eq_fourier_comp_neg, Real.fourierInv_eq_fourier_neg]

/-- `𝓕⁻ ∘ R = R ∘ 𝓕⁻`. -/
theorem fourierInv_reflect (f : L2R) : (𝓕⁻ (reflect f) : L2R) = reflect (𝓕⁻ f) := by
  rw [fourierInv_eq_reflect_fourier, fourierInv_eq_reflect_fourier, fourier_reflect]

/-! ### Even functions -/

/-- `L²(ℝ)_ev`: the closed subspace of even functions. -/
def evenL2 : Submodule ℂ L2R := LinearMap.ker ((reflectL - 1 : L2R →L[ℂ] L2R) : L2R →ₗ[ℂ] L2R)

theorem mem_evenL2 {f : L2R} : f ∈ evenL2 ↔ reflect f = f := by
  simp [evenL2, reflectL_apply, sub_eq_zero]

theorem isClosed_evenL2 : IsClosed (evenL2 : Set L2R) :=
  (reflectL - 1 : L2R →L[ℂ] L2R).isClosed_ker

instance : CompleteSpace evenL2 := isClosed_evenL2.completeSpace_coe

theorem fourier_mem_evenL2 {f : L2R} (hf : f ∈ evenL2) : (𝓕 f : L2R) ∈ evenL2 := by
  rw [mem_evenL2] at hf ⊢
  rw [← fourier_reflect, hf]

/-- On even functions `𝓕⁻ = 𝓕`. -/
theorem fourierInv_eq_fourier_of_even {f : L2R} (hf : f ∈ evenL2) : (𝓕⁻ f : L2R) = 𝓕 f := by
  rw [fourierInv_eq_reflect_fourier, ← fourier_reflect, mem_evenL2.1 hf]

/-- On even functions `𝓕 ∘ 𝓕 = 1` (CC: "`F_{e_ℝ}` is its own inverse on `L²(ℝ)_ev`"). -/
theorem fourier_fourier_of_even {f : L2R} (hf : f ∈ evenL2) : (𝓕 (𝓕 f : L2R) : L2R) = f := by
  rw [← fourierInv_eq_fourier_of_even hf]
  exact FourierInvPair.fourier_fourierInv_eq f

/-- `⟪𝓕 f, g⟫ = ⟪f, 𝓕 g⟫` when `g` is even (`𝓕` is self-adjoint on `L²(ℝ)_ev`). -/
theorem inner_fourier_of_even (f : L2R) {g : L2R} (hg : g ∈ evenL2) :
    ⟪(𝓕 f : L2R), g⟫_ℂ = ⟪f, (𝓕 g : L2R)⟫_ℂ := by
  conv_lhs => rw [← fourier_fourier_of_even hg]
  rw [Lp.inner_fourier_eq]

/-- The Fourier transform restricted to `L²(ℝ)_ev`. -/
def fourierEven : evenL2 →L[ℂ] evenL2 :=
  ((Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap.comp
    evenL2.subtypeL).codRestrict evenL2 fun f ↦ fourier_mem_evenL2 f.2

theorem coe_fourierEven (f : evenL2) : (fourierEven f : L2R) = 𝓕 (f : L2R) := rfl

theorem fourierEven_fourierEven (f : evenL2) : fourierEven (fourierEven f) = f :=
  Subtype.ext (by rw [coe_fourierEven, coe_fourierEven, fourier_fourier_of_even f.2])

theorem inner_fourierEven (f g : evenL2) :
    ⟪fourierEven f, g⟫_ℂ = ⟪f, fourierEven g⟫_ℂ := by
  rw [Submodule.coe_inner, Submodule.coe_inner, coe_fourierEven, coe_fourierEven,
    inner_fourier_of_even _ g.2]

end ArchS6
