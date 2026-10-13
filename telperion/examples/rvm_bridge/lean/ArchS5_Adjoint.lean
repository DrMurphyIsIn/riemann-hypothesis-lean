import ArchS5_KernelOp

/-!
# ArchS5_Adjoint: the sesquilinear form and the adjoint of an `L²`-kernel operator (stage S5)

* `memLp_two_tensor` / `eLpNorm_two_tensor`: `(x, y) ↦ g(x) f(y)` is in `L²(μ ⊗ ν)` with norm
  `‖g‖₂ ‖f‖₂`.
* `inner_intOp_eq_integral` : `⟪g, T_K f⟫ = ∫∫ conj(g x) K(x, y) f(y) d(μ ⊗ ν)`.
* `kernelAdjoint K` : the kernel `(y, x) ↦ conj K(x, y)` in `L²(ν ⊗ μ)`;
  `adjoint_intOp` : `(T_K)† = T_{K*}`.
* `isSelfAdjoint_intOp` : a Hermitian kernel (`K(y, x) = conj K(x, y)` a.e.) gives a self-adjoint
  operator.

conjecture1_proved = False.
-/

open MeasureTheory Filter Set RCLike
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate

noncomputable section

namespace ArchS5

set_option linter.unusedSectionVars false

variable {𝕜 : Type*} [RCLike 𝕜]
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}

/-! ### Tensor products of `L²` functions -/

theorem eLpNorm_two_tensor [SFinite ν] {g : α → 𝕜} {f : β → 𝕜} (hg : AEStronglyMeasurable g μ)
    (hf : AEStronglyMeasurable f ν) :
    eLpNorm (fun p : α × β ↦ g p.1 * f p.2) 2 (μ.prod ν) = eLpNorm g 2 μ * eLpNorm f 2 ν := by
  refine le_antisymm ((ENNReal.pow_le_pow_left_iff two_ne_zero).1 (le_of_eq ?_))
    ((ENNReal.pow_le_pow_left_iff two_ne_zero).1 (le_of_eq ?_)) <;>
  rw [eLpNorm_two_sq, mul_pow, eLpNorm_two_sq, eLpNorm_two_sq]
  all_goals
    simp_rw [enorm_mul, mul_pow]
    rw [lintegral_prod_mul (hg.enorm.pow_const 2) (hf.enorm.pow_const 2)]

theorem memLp_two_tensor [SFinite ν] {g : α → 𝕜} {f : β → 𝕜} (hg : MemLp g 2 μ)
    (hf : MemLp f 2 ν) : MemLp (fun p : α × β ↦ g p.1 * f p.2) 2 (μ.prod ν) :=
  ⟨(hg.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul
      (hf.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd),
    by rw [eLpNorm_two_tensor hg.1 hf.1]; exact ENNReal.mul_lt_top hg.2 hf.2⟩

theorem memLp_conj {γ : Type*} [MeasurableSpace γ] {m : Measure γ} {p : ℝ≥0∞} {g : γ → 𝕜}
    (hg : MemLp g p m) : MemLp (fun x ↦ conj (g x)) p m :=
  hg.star.ae_eq (ae_of_all _ fun _ ↦ rfl)

/-! ### The sesquilinear form -/

variable [SFinite μ] [SFinite ν]

theorem integrable_conj_mul_kernel_mul (K : Lp 𝕜 2 (μ.prod ν)) {f : β → 𝕜} {g : α → 𝕜}
    (hf : MemLp f 2 ν) (hg : MemLp g 2 μ) :
    Integrable (fun p : α × β ↦ conj (g p.1) * K p * f p.2) (μ.prod ν) := by
  have h := (Lp.memLp K).integrable_mul (memLp_two_tensor (memLp_conj hg) hf)
  refine h.congr (ae_of_all _ fun p ↦ ?_)
  simp only [Pi.mul_apply]; ring

/-- **The sesquilinear form of `T_K`**: `⟪g, T_K f⟫ = ∫∫ conj(g x) K(x, y) f(y)`. -/
theorem inner_intOp_eq_integral (K : Lp 𝕜 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) (g : Lp 𝕜 2 μ) :
    ⟪g, intOp K f⟫_𝕜 = ∫ p, conj (g p.1) * K p * f p.2 ∂(μ.prod ν) := by
  rw [integral_prod _ (integrable_conj_mul_kernel_mul K (Lp.memLp f) (Lp.memLp g)),
    MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [intOp_ae_eq K f] with x hx
  rw [RCLike.inner_apply', hx, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp only; ring

/-- The form with the operator on the left: `⟪T_K f, g⟫ = ∫∫ g(x) conj K(x, y) conj f(y)`. -/
theorem inner_intOp_left_eq_integral (K : Lp 𝕜 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) (g : Lp 𝕜 2 μ) :
    ⟪intOp K f, g⟫_𝕜 = ∫ p, g p.1 * conj (K p) * conj (f p.2) ∂(μ.prod ν) := by
  rw [← inner_conj_symm, inner_intOp_eq_integral, ← integral_conj]
  refine integral_congr_ae (ae_of_all _ fun p ↦ ?_)
  simp only [map_mul, RCLike.conj_conj]

/-! ### The adjoint kernel -/

theorem memLp_kernelAdjoint (K : Lp 𝕜 2 (μ.prod ν)) :
    MemLp (fun q : β × α ↦ conj (K q.swap)) 2 (ν.prod μ) :=
  memLp_conj ((Lp.memLp K).comp_measurePreserving Measure.measurePreserving_swap)

/-- The adjoint kernel `K*(y, x) = conj K(x, y)`, an element of `L²(ν ⊗ μ)`. -/
def kernelAdjoint (K : Lp 𝕜 2 (μ.prod ν)) : Lp 𝕜 2 (ν.prod μ) :=
  (memLp_kernelAdjoint K).toLp _

theorem kernelAdjoint_ae_eq (K : Lp 𝕜 2 (μ.prod ν)) :
    kernelAdjoint K =ᵐ[ν.prod μ] fun q ↦ conj (K q.swap) :=
  MemLp.coeFn_toLp _

/-- `T_K f` paired against `g` equals `f` paired against `T_{K*} g`. -/
theorem inner_intOp_kernelAdjoint (K : Lp 𝕜 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) (g : Lp 𝕜 2 μ) :
    ⟪intOp K f, g⟫_𝕜 = ⟪f, intOp (kernelAdjoint K) g⟫_𝕜 := by
  rw [inner_intOp_left_eq_integral, inner_intOp_eq_integral,
    ← integral_prod_swap (fun p : α × β ↦ g p.1 * conj (K p) * conj (f p.2))]
  refine integral_congr_ae ?_
  filter_upwards [kernelAdjoint_ae_eq K] with q hq
  rw [hq]
  simp only [Prod.fst_swap, Prod.snd_swap]; ring

/-- **The adjoint of an integral operator** is the integral operator of the adjoint kernel. -/
theorem adjoint_intOp (K : Lp 𝕜 2 (μ.prod ν)) :
    ContinuousLinearMap.adjoint (intOp K) = intOp (kernelAdjoint K) :=
  ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun g f ↦ by
    rw [← inner_conj_symm, ← inner_intOp_kernelAdjoint, inner_conj_symm]).symm

theorem kernelAdjoint_kernelAdjoint (K : Lp 𝕜 2 (μ.prod ν)) :
    kernelAdjoint (kernelAdjoint K) = K := by
  ext1
  have h1 := kernelAdjoint_ae_eq (kernelAdjoint K)
  have h2 : (fun p : α × β ↦ (kernelAdjoint K) p.swap) =ᵐ[μ.prod ν]
      fun p ↦ conj (K p.swap.swap) :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp (kernelAdjoint_ae_eq K)
  filter_upwards [h1, h2] with p hp1 hp2
  rw [hp1]
  rw [hp2, RCLike.conj_conj, Prod.swap_swap]

/-! ### Hermitian kernels -/

/-- A kernel on `α × α` is *Hermitian* if `K(y, x) = conj K(x, y)` almost everywhere. -/
def IsHermitianKernel {μ : Measure α} (K : Lp 𝕜 2 (μ.prod μ)) : Prop :=
  ∀ᵐ p ∂(μ.prod μ), K p.swap = conj (K p)

theorem kernelAdjoint_eq_self {μ : Measure α} [SFinite μ] {K : Lp 𝕜 2 (μ.prod μ)}
    (hK : IsHermitianKernel K) : kernelAdjoint K = K := by
  ext1
  filter_upwards [kernelAdjoint_ae_eq K, hK] with p hp1 hp2
  rw [hp1, hp2, RCLike.conj_conj]

/-- **Self-adjointness**: a Hermitian `L²` kernel gives a self-adjoint operator. -/
theorem isSelfAdjoint_intOp {μ : Measure α} [SFinite μ] {K : Lp 𝕜 2 (μ.prod μ)}
    (hK : IsHermitianKernel K) : IsSelfAdjoint (intOp K) := by
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, adjoint_intOp, kernelAdjoint_eq_self hK]

theorem isSymmetric_intOp {μ : Measure α} [SFinite μ] {K : Lp 𝕜 2 (μ.prod μ)}
    (hK : IsHermitianKernel K) : (intOp K : Lp 𝕜 2 μ →ₗ[𝕜] Lp 𝕜 2 μ).IsSymmetric :=
  (isSelfAdjoint_intOp hK).isSymmetric

end ArchS5
