import ArchS5_HS

/-!
# ArchS5_HSRank: finite-rank kernel approximation bounds the number of large eigenvalues (stage S5)

The `Σ λ² ≤ ‖K‖²` bound of `ArchS5_HS` alone does not give tail bounds from a rank-`n` truncation
`K_n` of the kernel (that is the Eckart-Young-Mirsky inequality, not proved here).  What is proved
here is the per-index version, which is what a Taylor truncation `K_n = Σ_{j<n} g_j ⊗ f_j` feeds:

* `card_le_of_eigen_gt` (abstract): if `F` has range in an `r`-dimensional subspace and
  `v_1, …, v_m` are orthonormal eigenvectors of `T` with eigenvalues `> ‖T - F‖`, then `m ≤ r`;
* `card_le_of_eigen_gt_intOp` : the same with `‖K - K'‖_{L²}` in place of `‖T - F‖`;
* `tensorKernel g f` (`(x, y) ↦ g(x) f(y)`), `intOp_tensorKernel` (rank one) and
  `intOp_sum_tensorKernel_mem_span` (a sum of `n` tensors has range in an `n`-dimensional span).

So at most `n` orthonormal eigenvectors of `T_K` have eigenvalue `> ‖K - Σ_{j<n} g_j ⊗ f_j‖₂`
(`card_le_of_eigen_gt_tensor`).  Applied to `-K` it bounds the negative eigenvalues too.

conjecture1_proved = False.
-/

open MeasureTheory Filter Set RCLike Module
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate

noncomputable section

namespace ArchS5

set_option linter.unusedSectionVars false

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### Abstract counting lemma -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem re_inner_sum_eigen {m : ℕ} (T : E →L[𝕜] E) {v : Fin m → E} (hv : Orthonormal 𝕜 v)
    {lam : Fin m → ℝ} (hT : ∀ i, T (v i) = (lam i : 𝕜) • v i) (a : Fin m → 𝕜) :
    re ⟪T (∑ i, a i • v i), ∑ i, a i • v i⟫_𝕜 = ∑ i, lam i * ‖a i‖ ^ 2 := by
  have hTx : T (∑ i, a i • v i) = ∑ i, (a i * lam i) • v i := by
    simp only [map_sum, map_smul, hT, smul_smul]
  rw [hTx, hv.inner_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [show conj (a i * (lam i : 𝕜)) * a i = (lam i : 𝕜) * (conj (a i) * a i) by
    rw [map_mul, RCLike.conj_ofReal]; ring, RCLike.conj_mul,
    ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]

theorem norm_sum_sq_orthonormal {m : ℕ} {v : Fin m → E} (hv : Orthonormal 𝕜 v)
    (a : Fin m → 𝕜) : ‖∑ i, a i • v i‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), hv.inner_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- **Counting large eigenvalues against a finite-rank perturbation.**  If `F` maps into an
`r`-dimensional subspace `U` and `v_1, …, v_m` are orthonormal eigenvectors of `T` whose
eigenvalues all exceed `‖T - F‖`, then `m ≤ r`. -/
theorem card_le_of_eigen_gt (T F : E →L[𝕜] E) (U : Submodule 𝕜 E) [FiniteDimensional 𝕜 U]
    (hF : ∀ x, F x ∈ U) {m : ℕ} {v : Fin m → E} (hv : Orthonormal 𝕜 v) {lam : Fin m → ℝ}
    (hT : ∀ i, T (v i) = (lam i : 𝕜) • v i) (hgt : ∀ i, ‖T - F‖ < lam i) :
    m ≤ finrank 𝕜 U := by
  by_contra hlt
  push Not at hlt
  set W := Submodule.span 𝕜 (Set.range v)
  have : FiniteDimensional 𝕜 W := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)
  have hW : finrank 𝕜 W = m := by
    rw [finrank_span_eq_card hv.linearIndependent, Fintype.card_fin]
  let f : W →ₗ[𝕜] U := (F.toLinearMap.codRestrict U hF) ∘ₗ W.subtype
  obtain ⟨x, hxker, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := f) (by rw [hW]; exact hlt))
  have hFx : F x = 0 := by
    have := congrArg Subtype.val (LinearMap.mem_ker.1 hxker)
    simpa [f] using this
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).1 x.2
  have hx0' : (x : E) ≠ 0 := fun h ↦ hx0 (Subtype.ext h)
  -- quadratic form on `x`
  have hQ := re_inner_sum_eigen T hv hT a
  have hN := norm_sum_sq_orthonormal hv a
  rw [ha] at hQ hN
  have hle : re ⟪T x, x⟫_𝕜 ≤ ‖T - F‖ * ‖(x : E)‖ ^ 2 := by
    have h1 : T x = (T - F) x := by simp [hFx]
    rw [h1]
    calc re ⟪(T - F) x, x⟫_𝕜 ≤ ‖(T - F) x‖ * ‖(x : E)‖ := re_inner_le_norm _ _
      _ ≤ ‖T - F‖ * ‖(x : E)‖ * ‖(x : E)‖ := by gcongr; exact (T - F).le_opNorm _
      _ = _ := by ring
  rw [hQ, hN, Finset.mul_sum] at hle
  have hpos : 0 < ∑ i, (lam i - ‖T - F‖) * ‖a i‖ ^ 2 := by
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra h
      push Not at h
      apply hx0'
      rw [← ha]
      simp [h]
    refine Finset.sum_pos' (fun j _ ↦ mul_nonneg (sub_nonneg.2 (hgt j).le) (by positivity))
      ⟨i, Finset.mem_univ _, mul_pos (sub_pos.2 (hgt i)) (by positivity)⟩
  have : ∑ i, (lam i - ‖T - F‖) * ‖a i‖ ^ 2 =
      ∑ i, lam i * ‖a i‖ ^ 2 - ∑ i, ‖T - F‖ * ‖a i‖ ^ 2 := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ ↦ by ring
  linarith

end Abstract

/-! ### Kernels -/

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Counting for integral operators: if `T_{K'}` has range in an `r`-dimensional subspace, at most
`r` orthonormal eigenvectors of `T_K` have eigenvalue `> ‖K - K'‖_{L²}`. -/
theorem card_le_of_eigen_gt_intOp {μ : Measure α} [SFinite μ] (K K' : Lp 𝕜 2 (μ.prod μ))
    (U : Submodule 𝕜 (Lp 𝕜 2 μ)) [FiniteDimensional 𝕜 U] (hF : ∀ f, intOp K' f ∈ U) {m : ℕ}
    {v : Fin m → Lp 𝕜 2 μ} (hv : Orthonormal 𝕜 v) {lam : Fin m → ℝ}
    (hT : ∀ i, intOp K (v i) = (lam i : 𝕜) • v i) (hgt : ∀ i, ‖K - K'‖ < lam i) :
    m ≤ finrank 𝕜 U :=
  card_le_of_eigen_gt (intOp K) (intOp K') U hF hv hT fun i ↦
    (norm_intOp_sub_le K K').trans_lt (hgt i)

variable {μ : Measure α} {ν : Measure β} [SFinite ν]

/-- The tensor kernel `(x, y) ↦ g(x) f(y)` in `L²(μ ⊗ ν)`. -/
def tensorKernel (g : Lp 𝕜 2 μ) (f : Lp 𝕜 2 ν) : Lp 𝕜 2 (μ.prod ν) :=
  (memLp_two_tensor (Lp.memLp g) (Lp.memLp f)).toLp _

theorem tensorKernel_ae_eq (g : Lp 𝕜 2 μ) (f : Lp 𝕜 2 ν) :
    tensorKernel g f =ᵐ[μ.prod ν] fun p ↦ g p.1 * f p.2 :=
  MemLp.coeFn_toLp _

/-- A tensor kernel gives a rank-one operator: `T_{g ⊗ f} h = (∫ f h) • g`. -/
theorem intOp_tensorKernel (g : Lp 𝕜 2 μ) (f h : Lp 𝕜 2 ν) :
    intOp (tensorKernel g f) h = (∫ y, f y * h y ∂ν) • g := by
  rw [intOp_apply_eq_iff]
  filter_upwards [Lp.coeFn_smul (∫ y, f y * h y ∂ν) g,
    kernelApply_congr_left (f := ⇑h) (tensorKernel_ae_eq g f)] with x h1 h2
  rw [h1, Pi.smul_apply, smul_eq_mul]
  change _ = kernelApply ν _ h x
  rw [h2, kernelApply]
  simp only [mul_assoc, integral_const_mul]
  ring

theorem intOp_tensorKernel_mem_span (g : Lp 𝕜 2 μ) (f h : Lp 𝕜 2 ν) :
    intOp (tensorKernel g f) h ∈ 𝕜 ∙ g := by
  rw [intOp_tensorKernel]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self g)

/-- A sum of `n` tensor kernels has range in the span of the `n` left factors. -/
theorem intOp_sum_tensorKernel_mem_span {n : ℕ} (g : Fin n → Lp 𝕜 2 μ) (f : Fin n → Lp 𝕜 2 ν)
    (h : Lp 𝕜 2 ν) :
    intOp (∑ j, tensorKernel (g j) (f j)) h ∈ Submodule.span 𝕜 (Set.range g) := by
  rw [← intOpL_apply, map_sum, _root_.sum_apply]
  refine Submodule.sum_mem _ fun j _ ↦ ?_
  rw [intOpL_apply, intOp_tensorKernel]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- **Rank-`n` truncation bounds the eigenvalue count**: at most `n` orthonormal eigenvectors of
`T_K` have eigenvalue `> ‖K - Σ_{j<n} g_j ⊗ f_j‖_{L²}`.  Equivalently, the `(n+1)`-st largest
eigenvalue (with multiplicity) is at most this distance. -/
theorem card_le_of_eigen_gt_tensor {μ : Measure α} [SFinite μ] (K : Lp 𝕜 2 (μ.prod μ)) {n : ℕ}
    (g f : Fin n → Lp 𝕜 2 μ) {m : ℕ} {v : Fin m → Lp 𝕜 2 μ} (hv : Orthonormal 𝕜 v)
    {lam : Fin m → ℝ} (hT : ∀ i, intOp K (v i) = (lam i : 𝕜) • v i)
    (hgt : ∀ i, ‖K - ∑ j, tensorKernel (g j) (f j)‖ < lam i) : m ≤ n := by
  have : FiniteDimensional 𝕜 (Submodule.span 𝕜 (Set.range g)) :=
    FiniteDimensional.span_of_finite 𝕜 (Set.finite_range g)
  have hle := card_le_of_eigen_gt_intOp K (∑ j, tensorKernel (g j) (f j))
    (Submodule.span 𝕜 (Set.range g)) (intOp_sum_tensorKernel_mem_span g f) hv hT hgt
  have hr : finrank 𝕜 (Submodule.span 𝕜 (Set.range g)) ≤ Fintype.card (Fin n) :=
    finrank_range_le_card (R := 𝕜) g
  exact hle.trans (hr.trans_eq (Fintype.card_fin n))

end ArchS5
