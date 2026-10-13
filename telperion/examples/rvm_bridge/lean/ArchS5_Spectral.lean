import ArchS5_Compact
import ArchS5_MinMax

/-!
# ArchS5_Spectral: the spectral package for `L²`-kernel operators, and kernels on intervals

General finite measure spaces, Hermitian `K ∈ L²(μ ⊗ μ)`:
* `isSymmetric_intOp`, `isCompactOperator_intOp` (from the earlier S5 files);
* `intOp_orthogonalComplement_iSup_eigenspaces_eq_bot` : the eigenvectors of `T_K` are complete
  (Mathlib's spectral theorem for compact self-adjoint operators, specialised; bypass B2);
* `finiteDimensional_eigenspace_intOp` : nonzero eigenvalues have finite multiplicity;
* `exists_eigenvector_topEig_intOp` : `λ_max(T_K) = sup ⟪T_K f, f⟫` is attained when positive;
* `abs_topEig_intOp_sub_le`, `abs_minmaxEig_intOp_sub_le` : `|λ_k(T_K) - λ_k(T_{K'})| ≤ ‖K - K'‖₂`
  (Galerkin/kernel-truncation control of the spectrum, bypass B4).

Intervals `I = [a, b]` with Lebesgue measure:
* `kernelOfContinuous a b k` : a continuous `k : ℝ × ℝ → 𝕜` as an element of `L²(I × I)`;
* `intOp_kernelOfContinuous_ae_eq` : `T_k f (x) = ∫_I k(x, y) f(y) dy` a.e. on `I`;
* `norm_kernelOfContinuous_le` : `‖k‖_{L²(I×I)} ≤ C (b - a)` if `|k| ≤ C` on `I × I`;
* `abs_topEig_kernelOfContinuous_sub_le` : `|λ_max(T_k) - λ_max(T_{k'})| ≤ sup_{I×I} |k - k'| · (b - a)`.

conjecture1_proved = False.
-/

open MeasureTheory Filter Set Module
open scoped ENNReal NNReal InnerProductSpace

noncomputable section

namespace ArchS5

set_option linter.unusedSectionVars false

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### General measure spaces -/

section General

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Weyl + Hilbert-Schmidt: the top eigenvalue moves by at most the `L²` distance of kernels. -/
theorem abs_topEig_intOp_sub_le {μ : Measure α} [SFinite μ] (K K' : Lp 𝕜 2 (μ.prod μ)) :
    |topEig (intOp K) - topEig (intOp K')| ≤ ‖K - K'‖ :=
  (abs_topEig_sub_le _ _).trans (norm_intOp_sub_le K K')

/-- Weyl + Hilbert-Schmidt for every variational eigenvalue. -/
theorem abs_minmaxEig_intOp_sub_le {μ : Measure α} [SFinite μ] (K K' : Lp 𝕜 2 (μ.prod μ))
    (k : ℕ) : |minmaxEig (intOp K) k - minmaxEig (intOp K') k| ≤ ‖K - K'‖ :=
  (abs_minmaxEig_sub_le _ _ k).trans (norm_intOp_sub_le K K')

variable {μ : Measure α} [IsFiniteMeasure μ] {K : Lp 𝕜 2 (μ.prod μ)}

/-- **Spectral theorem** for Hermitian `L²` kernels: the eigenspaces of `T_K` span a dense
subspace (their joint orthogonal complement is zero). -/
theorem intOp_orthogonalComplement_iSup_eigenspaces_eq_bot (hK : IsHermitianKernel K) :
    (⨆ c, Module.End.eigenspace (intOp K : Lp 𝕜 2 μ →ₗ[𝕜] Lp 𝕜 2 μ) c)ᗮ = ⊥ :=
  ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot (isCompactOperator_intOp K)
    (isSymmetric_intOp hK)

/-- Nonzero eigenvalues of `T_K` have finite multiplicity. -/
theorem finiteDimensional_eigenspace_intOp (K : Lp 𝕜 2 (μ.prod μ)) {c : 𝕜} (hc : c ≠ 0) :
    FiniteDimensional 𝕜
      (Module.End.eigenspace (intOp K : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ).toLinearMap c) :=
  ContinuousLinearMap.finite_dimensional_eigenspace (isCompactOperator_intOp K) c hc

/-- **Rayleigh characterisation** for Hermitian `L²` kernels: if `λ_max(T_K) > 0` it is attained
at a unit eigenvector. -/
theorem exists_eigenvector_topEig_intOp (hK : IsHermitianKernel K) (hpos : 0 < topEig (intOp K)) :
    ∃ v : Lp 𝕜 2 μ, ‖v‖ = 1 ∧ intOp K v = (topEig (intOp K) : 𝕜) • v :=
  exists_eigenvector_topEig _ (isSymmetric_intOp hK) (isCompactOperator_intOp K) hpos

end General

/-! ### Kernels on an interval -/

section Interval

open MeasureTheory.Measure

variable (a b : ℝ)

/-- Lebesgue measure on `[a, b]`. -/
abbrev volI : Measure ℝ := volume.restrict (Icc a b)

theorem volI_prod : (volI a b).prod (volI a b) = (volume : Measure (ℝ × ℝ)).restrict
    (Icc a b ×ˢ Icc a b) := by
  rw [volI, prod_restrict, volume_eq_prod]

theorem ae_mem_Icc_prod :
    ∀ᵐ p ∂((volI a b).prod (volI a b)), p ∈ Icc a b ×ˢ Icc a b := by
  rw [volI_prod]
  exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)

variable {a b}

theorem memLp_of_continuous {k : ℝ × ℝ → 𝕜} (hk : Continuous k) :
    MemLp k 2 ((volI a b).prod (volI a b)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc a b ×ˢ Icc a b) hk.continuousOn
  refine MemLp.of_bound hk.aestronglyMeasurable C ?_
  filter_upwards [ae_mem_Icc_prod a b] with p hp
  exact hC p hp

variable (a b) in
/-- A continuous kernel `k : ℝ × ℝ → 𝕜`, viewed in `L²([a, b]²)`. -/
def kernelOfContinuous (k : ℝ × ℝ → 𝕜) (hk : Continuous k) :
    Lp 𝕜 2 ((volI a b).prod (volI a b)) :=
  (memLp_of_continuous hk).toLp k

theorem kernelOfContinuous_ae_eq {k : ℝ × ℝ → 𝕜} (hk : Continuous k) :
    kernelOfContinuous a b k hk =ᵐ[(volI a b).prod (volI a b)] k :=
  MemLp.coeFn_toLp _

/-- The defining formula on an interval: `T_k f (x) = ∫_{[a, b]} k(x, y) f(y) dy` a.e. -/
theorem intOp_kernelOfContinuous_ae_eq {k : ℝ × ℝ → 𝕜} (hk : Continuous k) (f : Lp 𝕜 2 (volI a b)) :
    intOp (kernelOfContinuous a b k hk) f =ᵐ[volI a b]
      fun x ↦ ∫ y in Icc a b, k (x, y) * f y := by
  filter_upwards [intOp_ae_eq (kernelOfContinuous a b k hk) f,
    kernelApply_congr_left (f := ⇑f) (kernelOfContinuous_ae_eq hk)] with x h1 h2
  rw [h1]
  exact h2

theorem kernelOfContinuous_sub {k k' : ℝ × ℝ → 𝕜} (hk : Continuous k) (hk' : Continuous k') :
    kernelOfContinuous a b k hk - kernelOfContinuous a b k' hk' =
      kernelOfContinuous a b (k - k') (hk.sub hk') := by
  ext1
  filter_upwards [Lp.coeFn_sub (kernelOfContinuous a b k hk) (kernelOfContinuous a b k' hk'),
    kernelOfContinuous_ae_eq (a := a) (b := b) hk, kernelOfContinuous_ae_eq (a := a) (b := b) hk',
    kernelOfContinuous_ae_eq (a := a) (b := b) (hk.sub hk')] with p h1 h2 h3 h4
  rw [h1, h4, Pi.sub_apply, h2, h3, Pi.sub_apply]

/-- Sup-norm control of the `L²([a,b]²)` norm: `‖k‖₂ ≤ C (b - a)` if `‖k‖ ≤ C` on `[a, b]²`. -/
theorem norm_kernelOfContinuous_le (hab : a ≤ b) {k : ℝ × ℝ → 𝕜} (hk : Continuous k) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ‖k (x, y)‖ ≤ C) :
    ‖kernelOfContinuous a b k hk‖ ≤ C * (b - a) := by
  have hbound : ∀ᵐ p ∂((volI a b).prod (volI a b)), ‖kernelOfContinuous a b k hk p‖ ≤ C := by
    filter_upwards [kernelOfContinuous_ae_eq (a := a) (b := b) hk, ae_mem_Icc_prod a b]
      with p h1 h2
    rw [h1]
    exact hC p.1 h2.1 p.2 h2.2
  refine (Lp.norm_le_of_ae_bound hC0 hbound).trans (le_of_eq ?_)
  have huniv : (measureUnivNNReal ((volI a b).prod (volI a b)) : ℝ) = (b - a) * (b - a) := by
    rw [measureUnivNNReal, ENNReal.coe_toNNReal_eq_toReal, ← univ_prod_univ, prod_prod]
    simp only [volI, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.2 hab)]
  rw [huniv, ENNReal.toReal_ofNat, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
    Real.sqrt_mul_self (sub_nonneg.2 hab), mul_comm]

/-- **Kernel perturbation on an interval**: the top eigenvalue of `T_k` moves by at most
`sup_{[a,b]²} |k - k'| · (b - a)`. -/
theorem abs_topEig_kernelOfContinuous_sub_le (hab : a ≤ b) {k k' : ℝ × ℝ → 𝕜} (hk : Continuous k)
    (hk' : Continuous k') {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ‖k (x, y) - k' (x, y)‖ ≤ C) :
    |topEig (intOp (kernelOfContinuous a b k hk)) - topEig (intOp (kernelOfContinuous a b k' hk'))|
      ≤ C * (b - a) := by
  refine (abs_topEig_intOp_sub_le _ _).trans ?_
  rw [kernelOfContinuous_sub]
  exact norm_kernelOfContinuous_le hab _ hC0 hC

/-- The same for every variational eigenvalue. -/
theorem abs_minmaxEig_kernelOfContinuous_sub_le (hab : a ≤ b) {k k' : ℝ × ℝ → 𝕜}
    (hk : Continuous k) (hk' : Continuous k') {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ‖k (x, y) - k' (x, y)‖ ≤ C) (n : ℕ) :
    |minmaxEig (intOp (kernelOfContinuous a b k hk)) n -
        minmaxEig (intOp (kernelOfContinuous a b k' hk')) n| ≤ C * (b - a) := by
  refine (abs_minmaxEig_intOp_sub_le _ _ n).trans ?_
  rw [kernelOfContinuous_sub]
  exact norm_kernelOfContinuous_le hab _ hC0 hC

/-- A continuous kernel with `k(y, x) = conj k(x, y)` is Hermitian. -/
theorem isHermitianKernel_kernelOfContinuous {k : ℝ × ℝ → 𝕜} (hk : Continuous k)
    (hsymm : ∀ x y, k (y, x) = (starRingEnd 𝕜) (k (x, y))) :
    IsHermitianKernel (kernelOfContinuous a b k hk) := by
  have h1 := kernelOfContinuous_ae_eq (a := a) (b := b) hk
  have h2 : (fun p : ℝ × ℝ ↦ kernelOfContinuous a b k hk p.swap) =ᵐ[(volI a b).prod (volI a b)]
      fun p ↦ k p.swap :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp h1
  filter_upwards [h1, h2] with p hp1 hp2
  rw [hp2, hp1]
  exact hsymm p.1 p.2

/-- The full spectral package for a continuous Hermitian kernel on `[a, b]`: `T_k` is compact
and self-adjoint. -/
theorem intOp_kernelOfContinuous_compact_selfAdjoint {k : ℝ × ℝ → 𝕜} (hk : Continuous k)
    (hsymm : ∀ x y, k (y, x) = (starRingEnd 𝕜) (k (x, y))) :
    IsCompactOperator (intOp (kernelOfContinuous a b k hk)) ∧
      IsSelfAdjoint (intOp (kernelOfContinuous a b k hk)) :=
  ⟨isCompactOperator_intOp _, isSelfAdjoint_intOp (isHermitianKernel_kernelOfContinuous hk hsymm)⟩

end Interval

end ArchS5
