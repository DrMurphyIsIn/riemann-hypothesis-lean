import Mathlib

/-!
# ArchS5_KernelOp: integral operators with square-integrable kernels (stage S5, part 1)

For σ-finite (indeed s-finite) measure spaces `(α, μ)`, `(β, ν)` and a kernel
`K ∈ L²(μ ⊗ ν)` (scalars `𝕜 = ℝ` or `ℂ`), the integral operator

    (T_K f)(x) = ∫ K(x, y) f(y) dν(y)

is a bounded linear map `L²(ν) → L²(μ)` with `‖T_K‖ ≤ ‖K‖_{L²(μ⊗ν)}` (Cauchy-Schwarz in `y`,
then Tonelli in `x`).  The assignment `K ↦ T_K` is itself a continuous linear map of norm `≤ 1`
(`intOpL`), so `‖T_K - T_{K'}‖ ≤ ‖K - K'‖`.

Main declarations (namespace `ArchS5`):
* `kernelApply ν K f x = ∫ y, K (x, y) * f y ∂ν` (pointwise transform of plain functions);
* `eLpNorm_kernelApply_le` : `eLpNorm (kernelApply ν K f) 2 μ ≤ eLpNorm K 2 (μ.prod ν) * eLpNorm f 2 ν`;
* `intOpL : Lp 𝕜 2 (μ.prod ν) →L[𝕜] Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 μ`, `intOp K := intOpL K`;
* `intOp_ae_eq` : `intOp K f =ᵐ[μ] fun x ↦ ∫ y, K (x, y) * f y ∂ν`;
* `norm_intOp_le`, `norm_intOp_sub_le`, `norm_intOpL_le`.

conjecture1_proved = False.  Nothing here is RH progress; this is reusable infrastructure.
-/

open MeasureTheory Filter Set
open scoped ENNReal NNReal

noncomputable section

namespace ArchS5

set_option linter.unusedSectionVars false

variable {𝕜 : Type*} [RCLike 𝕜]
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-! ### A small `L²` helper -/

/-- The square of the `L²` seminorm is the integral of the squared extended norm. -/
theorem eLpNorm_two_sq {γ E : Type*} [MeasurableSpace γ] [NormedAddCommGroup E] {m : Measure γ}
    (g : γ → E) : eLpNorm g 2 m ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂m := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  simp only [ENNReal.toReal_ofNat, Nat.cast_ofNat]
  norm_num

/-! ### The pointwise transform -/

variable (ν : Measure β) in
/-- The pointwise integral transform `x ↦ ∫ K(x, y) f(y) dν(y)` of plain functions. -/
def kernelApply (K : α × β → 𝕜) (f : β → 𝕜) (x : α) : 𝕜 := ∫ y, K (x, y) * f y ∂ν

variable {μ : Measure α} {ν : Measure β}

theorem kernelApply_congr_right {K : α × β → 𝕜} {f g : β → 𝕜} (h : f =ᵐ[ν] g) :
    kernelApply ν K f = kernelApply ν K g := by
  funext x
  refine integral_congr_ae ?_
  filter_upwards [h] with y hy
  rw [hy]

theorem kernelApply_congr_left_of_ae_ae {K K' : α × β → 𝕜} {f : β → 𝕜}
    (h : ∀ᵐ x ∂μ, (fun y ↦ K (x, y)) =ᵐ[ν] fun y ↦ K' (x, y)) :
    kernelApply ν K f =ᵐ[μ] kernelApply ν K' f := by
  filter_upwards [h] with x hx
  refine integral_congr_ae ?_
  filter_upwards [hx] with y hy
  rw [hy]

theorem kernelApply_congr_left [SFinite ν] {K K' : α × β → 𝕜} {f : β → 𝕜}
    (h : K =ᵐ[μ.prod ν] K') : kernelApply ν K f =ᵐ[μ] kernelApply ν K' f :=
  kernelApply_congr_left_of_ae_ae (Measure.ae_ae_of_ae_prod h)

/-- Pointwise Cauchy-Schwarz: `|T_K f (x)| ≤ ‖K(x, ·)‖₂ ‖f‖₂`. -/
theorem enorm_kernelApply_le {K : α × β → 𝕜} {f : β → 𝕜} (hK : StronglyMeasurable K)
    (hf : AEStronglyMeasurable f ν) (x : α) :
    ‖kernelApply ν K f x‖ₑ ≤ eLpNorm (fun y ↦ K (x, y)) 2 ν * eLpNorm f 2 ν := by
  have hKx : AEStronglyMeasurable (fun y ↦ K (x, y)) ν :=
    (hK.comp_measurable measurable_prodMk_left).aestronglyMeasurable
  calc ‖kernelApply ν K f x‖ₑ ≤ ∫⁻ y, ‖K (x, y) * f y‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (fun y ↦ K (x, y) * f y) 1 ν := eLpNorm_one_eq_lintegral_enorm.symm
    _ ≤ (1 : ℝ≥0) * eLpNorm (fun y ↦ K (x, y)) 2 ν * eLpNorm f 2 ν := by
        refine eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hKx hf (· * ·) 1 ?_
        exact ae_of_all _ fun y ↦ by simp [nnnorm_mul]
    _ = _ := by rw [ENNReal.coe_one, one_mul]

/-- Tonelli for the squared `L²` norms of the sections of a kernel. -/
theorem lintegral_eLpNorm_section_sq [SFinite ν] {K : α × β → 𝕜}
    (hK : AEStronglyMeasurable K (μ.prod ν)) :
    ∫⁻ x, eLpNorm (fun y ↦ K (x, y)) 2 ν ^ 2 ∂μ = eLpNorm K 2 (μ.prod ν) ^ 2 := by
  simp_rw [eLpNorm_two_sq]
  exact (lintegral_prod _ (hK.enorm.pow_const 2)).symm

/-- The Hilbert-Schmidt (Schur) bound `‖T_K f‖₂ ≤ ‖K‖₂ ‖f‖₂`, at the level of `eLpNorm`. -/
theorem eLpNorm_kernelApply_le [SFinite ν] {K : α × β → 𝕜} {f : β → 𝕜}
    (hK : StronglyMeasurable K) (hf : MemLp f 2 ν) :
    eLpNorm (kernelApply ν K f) 2 μ ≤ eLpNorm K 2 (μ.prod ν) * eLpNorm f 2 ν := by
  have hsq : eLpNorm (kernelApply ν K f) 2 μ ^ 2 ≤
      (eLpNorm K 2 (μ.prod ν) * eLpNorm f 2 ν) ^ 2 := by
    rw [eLpNorm_two_sq, mul_pow, ← lintegral_eLpNorm_section_sq hK.aestronglyMeasurable,
      ← lintegral_mul_const' _ _ (ENNReal.pow_ne_top hf.eLpNorm_ne_top)]
    refine lintegral_mono fun x ↦ ?_
    rw [← mul_pow]
    exact ENNReal.pow_le_pow_left (enorm_kernelApply_le hK hf.1 x)
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hsq

theorem stronglyMeasurable_kernelApply [SFinite ν] {K : α × β → 𝕜} {f : β → 𝕜}
    (hK : StronglyMeasurable K) (hf : StronglyMeasurable f) :
    StronglyMeasurable (kernelApply ν K f) :=
  (hK.mul (hf.comp_measurable measurable_snd)).integral_prod_right'

theorem memLp_kernelApply [SFinite ν] {K : α × β → 𝕜} {f : β → 𝕜} (hK : StronglyMeasurable K)
    (hK2 : MemLp K 2 (μ.prod ν)) (hfs : StronglyMeasurable f) (hf : MemLp f 2 ν) :
    MemLp (kernelApply ν K f) 2 μ :=
  ⟨(stronglyMeasurable_kernelApply hK hfs).aestronglyMeasurable,
    (eLpNorm_kernelApply_le hK hf).trans_lt (ENNReal.mul_lt_top hK2.2 hf.2)⟩

/-- Almost every section `K(x, ·)` of an `L²` kernel is in `L²`. -/
theorem ae_memLp_section [SFinite ν] {K : α × β → 𝕜} (hK : StronglyMeasurable K)
    (hK2 : MemLp K 2 (μ.prod ν)) : ∀ᵐ x ∂μ, MemLp (fun y ↦ K (x, y)) 2 ν := by
  have hfin : ∫⁻ x, eLpNorm (fun y ↦ K (x, y)) 2 ν ^ 2 ∂μ ≠ ∞ := by
    rw [lintegral_eLpNorm_section_sq hK2.1]; exact ENNReal.pow_ne_top hK2.eLpNorm_ne_top
  have hmeas : AEMeasurable (fun x ↦ eLpNorm (fun y ↦ K (x, y)) 2 ν ^ 2) μ := by
    simp_rw [eLpNorm_two_sq]
    exact ((hK.measurable.enorm.pow_const 2).lintegral_prod_right').aemeasurable
  filter_upwards [ae_lt_top' hmeas hfin] with x hx
  refine ⟨(hK.comp_measurable measurable_prodMk_left).aestronglyMeasurable, ?_⟩
  rw [lt_top_iff_ne_top] at hx ⊢
  intro h
  simp [h] at hx

theorem ae_integrable_section_mul [SFinite ν] {K : α × β → 𝕜} {f : β → 𝕜}
    (hK : StronglyMeasurable K) (hK2 : MemLp K 2 (μ.prod ν)) (hf : MemLp f 2 ν) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ K (x, y) * f y) ν := by
  filter_upwards [ae_memLp_section hK hK2] with x hx
  exact hx.integrable_mul hf

theorem kernelApply_add_right {K : α × β → 𝕜} {f g : β → 𝕜} {x : α}
    (hf : Integrable (fun y ↦ K (x, y) * f y) ν) (hg : Integrable (fun y ↦ K (x, y) * g y) ν) :
    kernelApply ν K (f + g) x = kernelApply ν K f x + kernelApply ν K g x := by
  simp only [kernelApply, Pi.add_apply, mul_add]
  exact integral_add hf hg

theorem kernelApply_smul_right (K : α × β → 𝕜) (f : β → 𝕜) (c : 𝕜) (x : α) :
    kernelApply ν K (c • f) x = c * kernelApply ν K f x := by
  have : ∀ y, K (x, y) * (c • f) y = c * (K (x, y) * f y) := fun y ↦ by
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  simp only [kernelApply, this, integral_const_mul]

theorem kernelApply_add_left {K K' : α × β → 𝕜} {f : β → 𝕜} {x : α}
    (hK : Integrable (fun y ↦ K (x, y) * f y) ν) (hK' : Integrable (fun y ↦ K' (x, y) * f y) ν) :
    kernelApply ν (K + K') f x = kernelApply ν K f x + kernelApply ν K' f x := by
  simp only [kernelApply, Pi.add_apply, add_mul]
  exact integral_add hK hK'

theorem kernelApply_smul_left (K : α × β → 𝕜) (f : β → 𝕜) (c : 𝕜) (x : α) :
    kernelApply ν (c • K) f x = c * kernelApply ν K f x := by
  have : ∀ y, (c • K) (x, y) * f y = c * (K (x, y) * f y) := fun y ↦ by
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  simp only [kernelApply, this, integral_const_mul]

/-! ### The operator on `L²` -/

section Lp

variable [SFinite ν]

theorem memLp_kernelApply_Lp (K : Lp 𝕜 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) :
    MemLp (kernelApply ν K f) 2 μ :=
  memLp_kernelApply (Lp.stronglyMeasurable K) (Lp.memLp K) (Lp.stronglyMeasurable f) (Lp.memLp f)

/-- Auxiliary: `T_K f` as an element of `L²(μ)` (use `intOp`). -/
def intOpAux (K : Lp 𝕜 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) : Lp 𝕜 2 μ :=
  (memLp_kernelApply_Lp K f).toLp _

theorem intOpAux_ae_eq (K : Lp 𝕜 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) :
    intOpAux K f =ᵐ[μ] kernelApply ν K f :=
  MemLp.coeFn_toLp _

theorem norm_intOpAux_le (K : Lp 𝕜 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) :
    ‖intOpAux K f‖ ≤ ‖K‖ * ‖f‖ := by
  rw [intOpAux, Lp.norm_toLp, Lp.norm_def K, Lp.norm_def f, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top K) (Lp.eLpNorm_ne_top f))
    (eLpNorm_kernelApply_le (Lp.stronglyMeasurable K) (Lp.memLp f))

theorem intOpAux_add_right (K : Lp 𝕜 2 (μ.prod ν)) (f g : Lp 𝕜 2 ν) :
    intOpAux K (f + g) = intOpAux K f + intOpAux K g := by
  ext1
  filter_upwards [intOpAux_ae_eq K (f + g), intOpAux_ae_eq K f, intOpAux_ae_eq K g,
    Lp.coeFn_add (intOpAux K f) (intOpAux K g),
    ae_integrable_section_mul (Lp.stronglyMeasurable K) (Lp.memLp K) (Lp.memLp f),
    ae_integrable_section_mul (Lp.stronglyMeasurable K) (Lp.memLp K) (Lp.memLp g)]
    with x h1 h2 h3 h4 h5 h6
  rw [h4, Pi.add_apply, h1, h2, h3, kernelApply_congr_right (Lp.coeFn_add f g),
    kernelApply_add_right h5 h6]

theorem intOpAux_smul_right (c : 𝕜) (K : Lp 𝕜 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) :
    intOpAux K (c • f) = c • intOpAux K f := by
  ext1
  filter_upwards [intOpAux_ae_eq K (c • f), intOpAux_ae_eq K f,
    Lp.coeFn_smul c (intOpAux K f)] with x h1 h2 h3
  rw [h3, Pi.smul_apply, h1, h2, kernelApply_congr_right (Lp.coeFn_smul c f),
    kernelApply_smul_right, smul_eq_mul]

theorem intOpAux_add_left (K K' : Lp 𝕜 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) :
    intOpAux (K + K') f = intOpAux K f + intOpAux K' f := by
  ext1
  filter_upwards [intOpAux_ae_eq (K + K') f, intOpAux_ae_eq K f, intOpAux_ae_eq K' f,
    Lp.coeFn_add (intOpAux K f) (intOpAux K' f),
    kernelApply_congr_left (f := ⇑f) (Lp.coeFn_add K K'),
    ae_integrable_section_mul (Lp.stronglyMeasurable K) (Lp.memLp K) (Lp.memLp f),
    ae_integrable_section_mul (Lp.stronglyMeasurable K') (Lp.memLp K') (Lp.memLp f)]
    with x h1 h2 h3 h4 h5 h6 h7
  rw [h4, Pi.add_apply, h1, h2, h3, h5, kernelApply_add_left h6 h7]

theorem intOpAux_smul_left (c : 𝕜) (K : Lp 𝕜 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) :
    intOpAux (c • K) f = c • intOpAux K f := by
  ext1
  filter_upwards [intOpAux_ae_eq (c • K) f, intOpAux_ae_eq K f,
    Lp.coeFn_smul c (intOpAux K f), kernelApply_congr_left (f := ⇑f) (Lp.coeFn_smul c K)]
    with x h1 h2 h3 h4
  rw [h3, Pi.smul_apply, h1, h2, h4, kernelApply_smul_left, smul_eq_mul]

variable (μ ν 𝕜) in
/-- The integral-operator map `K ↦ T_K`, as a continuous bilinear map of norm `≤ 1`:
`L²(μ ⊗ ν) → (L²(ν) →L L²(μ))`. -/
def intOpL : Lp 𝕜 2 (μ.prod ν) →L[𝕜] Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 μ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ 𝕜 intOpAux intOpAux_add_left intOpAux_smul_left intOpAux_add_right
      intOpAux_smul_right) 1
    (fun K f ↦ by rw [one_mul]; exact norm_intOpAux_le K f)

/-- The integral operator `T_K` with `L²` kernel `K`:
`(T_K f)(x) = ∫ K(x, y) f(y) dν(y)` (see `intOp_ae_eq`). -/
def intOp (K : Lp 𝕜 2 (μ.prod ν)) : Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 μ := intOpL 𝕜 μ ν K

@[simp] theorem intOpL_apply (K : Lp 𝕜 2 (μ.prod ν)) : intOpL 𝕜 μ ν K = intOp K := rfl

theorem intOp_apply (K : Lp 𝕜 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) : intOp K f = intOpAux K f := rfl

/-- The defining formula: `T_K f = ∫ K(·, y) f(y) dν(y)` almost everywhere. -/
theorem intOp_ae_eq (K : Lp 𝕜 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) :
    intOp K f =ᵐ[μ] fun x ↦ ∫ y, K (x, y) * f y ∂ν :=
  intOpAux_ae_eq K f

/-- Characterisation of `T_K f` by its values. -/
theorem intOp_apply_eq_iff (K : Lp 𝕜 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) (g : Lp 𝕜 2 μ) :
    intOp K f = g ↔ g =ᵐ[μ] fun x ↦ ∫ y, K (x, y) * f y ∂ν := by
  constructor
  · rintro rfl; exact intOp_ae_eq K f
  · intro h; ext1; exact (intOp_ae_eq K f).trans h.symm

/-- `‖T_K f‖ ≤ ‖K‖ ‖f‖`. -/
theorem norm_intOp_apply_le (K : Lp 𝕜 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) :
    ‖intOp K f‖ ≤ ‖K‖ * ‖f‖ :=
  norm_intOpAux_le K f

/-- **Hilbert-Schmidt bound**: `‖T_K‖ ≤ ‖K‖_{L²(μ⊗ν)}`. -/
theorem norm_intOp_le (K : Lp 𝕜 2 (μ.prod ν)) : ‖intOp K‖ ≤ ‖K‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (norm_intOp_apply_le K)

/-- The map `K ↦ T_K` has norm at most one. -/
theorem norm_intOpL_le : ‖intOpL 𝕜 μ ν‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

@[simp] theorem intOp_zero : intOp (0 : Lp 𝕜 2 (μ.prod ν)) = 0 := map_zero (intOpL 𝕜 μ ν)

theorem intOp_add (K K' : Lp 𝕜 2 (μ.prod ν)) : intOp (K + K') = intOp K + intOp K' :=
  map_add (intOpL 𝕜 μ ν) K K'

theorem intOp_sub (K K' : Lp 𝕜 2 (μ.prod ν)) : intOp (K - K') = intOp K - intOp K' :=
  map_sub (intOpL 𝕜 μ ν) K K'

theorem intOp_neg (K : Lp 𝕜 2 (μ.prod ν)) : intOp (-K) = -intOp K :=
  map_neg (intOpL 𝕜 μ ν) K

theorem intOp_smul (c : 𝕜) (K : Lp 𝕜 2 (μ.prod ν)) : intOp (c • K) = c • intOp K :=
  map_smul (intOpL 𝕜 μ ν) c K

/-- **Kernel perturbation**: `‖T_K - T_{K'}‖ ≤ ‖K - K'‖_{L²}`.  Galerkin truncations of the
kernel therefore control the operator in norm. -/
theorem norm_intOp_sub_le (K K' : Lp 𝕜 2 (μ.prod ν)) :
    ‖intOp K - intOp K'‖ ≤ ‖K - K'‖ := by
  rw [← intOp_sub]; exact norm_intOp_le _

/-- `K ↦ T_K` is `1`-Lipschitz. -/
theorem lipschitzWith_intOp :
    LipschitzWith 1 (fun K : Lp 𝕜 2 (μ.prod ν) ↦ intOp K) :=
  LipschitzWith.of_dist_le_mul fun K K' ↦ by
    simpa [dist_eq_norm] using norm_intOp_sub_le K K'

theorem continuous_intOp : Continuous (fun K : Lp 𝕜 2 (μ.prod ν) ↦ intOp K) :=
  (intOpL 𝕜 μ ν).continuous

end Lp

end ArchS5
