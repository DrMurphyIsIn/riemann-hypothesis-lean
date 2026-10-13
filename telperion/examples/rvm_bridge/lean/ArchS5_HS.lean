import ArchS5_Adjoint

/-!
# ArchS5_HS: the Hilbert-Schmidt identity and the eigenvalue bound `Σ λ_n² ≤ ‖K‖²` (stage S5)

For `K ∈ L²(μ ⊗ ν)` and almost every `x`, the section `K(x, ·)` is in `L²(ν)`, and
`(T_K f)(x) = ⟪conj K(x, ·), f⟫` (`kernelApply_eq_inner_sectionConj`).  Bessel's inequality in
`y`, followed by Tonelli in `x`, gives for every **orthonormal family** `v` of `L²(ν)`:

    Σ_i ‖T_K v_i‖² ≤ ‖K‖²_{L²(μ⊗ν)}                 (`tsum_norm_intOp_sq_le`)

and Parseval gives equality for a countable **Hilbert basis** (`hasSum_norm_intOp_sq`).

Consequence for eigenvalues (no self-adjointness needed): if `T_K v_i = c_i v_i` with `v`
orthonormal, then `Σ_i |c_i|² ≤ ‖K‖²` (`tsum_eigenvalue_sq_le`), and at most `‖K‖²/ε²` of the
`|c_i|` are `≥ ε` (`card_mul_sq_le_of_eigen`).

conjecture1_proved = False.
-/

open MeasureTheory Filter Set RCLike
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate

noncomputable section

namespace ArchS5

set_option linter.unusedSectionVars false

variable {𝕜 : Type*} [RCLike 𝕜]
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} [SFinite ν]

/-! ### Sections of the kernel as vectors of `L²(ν)` -/

/-- The conjugated section `y ↦ conj K(x, y)` as an element of `L²(ν)` (for `x` with
`K(x, ·) ∈ L²`). -/
def sectionConj (K : Lp 𝕜 2 (μ.prod ν)) (x : α) (hx : MemLp (fun y ↦ K (x, y)) 2 ν) :
    Lp 𝕜 2 ν :=
  (memLp_conj hx).toLp _

/-- The integral transform at `x` is an inner product against the conjugated section. -/
theorem kernelApply_eq_inner_sectionConj (K : Lp 𝕜 2 (μ.prod ν)) (x : α)
    (hx : MemLp (fun y ↦ K (x, y)) 2 ν) (f : Lp 𝕜 2 ν) :
    kernelApply ν K f x = ⟪sectionConj K x hx, f⟫_𝕜 := by
  rw [MeasureTheory.L2.inner_def, kernelApply]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_conj hx)] with y hy
  rw [RCLike.inner_apply', sectionConj, hy, RCLike.conj_conj]

theorem norm_sectionConj (K : Lp 𝕜 2 (μ.prod ν)) (x : α) (hx : MemLp (fun y ↦ K (x, y)) 2 ν) :
    ‖sectionConj K x hx‖ = (eLpNorm (fun y ↦ K (x, y)) 2 ν).toReal := by
  rw [sectionConj, Lp.norm_toLp]
  congr 1
  exact eLpNorm_congr_norm_ae (ae_of_all _ fun y ↦ RCLike.norm_conj _)

theorem enorm_kernelApply_sq_eq (K : Lp 𝕜 2 (μ.prod ν)) (x : α)
    (hx : MemLp (fun y ↦ K (x, y)) 2 ν) (f : Lp 𝕜 2 ν) :
    ‖kernelApply ν K f x‖ₑ ^ 2 = ENNReal.ofReal (‖⟪f, sectionConj K x hx⟫_𝕜‖ ^ 2) := by
  rw [kernelApply_eq_inner_sectionConj K x hx, ← ofReal_norm,
    ENNReal.ofReal_pow (norm_nonneg _), norm_inner_symm]

theorem ofReal_norm_sectionConj_sq (K : Lp 𝕜 2 (μ.prod ν)) (x : α)
    (hx : MemLp (fun y ↦ K (x, y)) 2 ν) :
    ENNReal.ofReal (‖sectionConj K x hx‖ ^ 2) = eLpNorm (fun y ↦ K (x, y)) 2 ν ^ 2 := by
  rw [norm_sectionConj, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hx.eLpNorm_ne_top]

/-! ### Bessel: orthonormal families -/

variable {ι : Type*}

/-- Pointwise Bessel: `Σ_{i ∈ s} |T_K v_i (x)|² ≤ ‖K(x, ·)‖²`. -/
theorem sum_enorm_kernelApply_sq_le (K : Lp 𝕜 2 (μ.prod ν)) (x : α)
    (hx : MemLp (fun y ↦ K (x, y)) 2 ν) {v : ι → Lp 𝕜 2 ν} (hv : Orthonormal 𝕜 v)
    (s : Finset ι) :
    ∑ i ∈ s, ‖kernelApply ν K (v i) x‖ₑ ^ 2 ≤ eLpNorm (fun y ↦ K (x, y)) 2 ν ^ 2 := by
  have hB := hv.sum_inner_products_le (sectionConj K x hx) (s := s)
  calc ∑ i ∈ s, ‖kernelApply ν K (v i) x‖ₑ ^ 2
      = ENNReal.ofReal (∑ i ∈ s, ‖⟪v i, sectionConj K x hx⟫_𝕜‖ ^ 2) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ by positivity)]
        exact Finset.sum_congr rfl fun i _ ↦ enorm_kernelApply_sq_eq K x hx (v i)
    _ ≤ ENNReal.ofReal (‖sectionConj K x hx‖ ^ 2) := ENNReal.ofReal_le_ofReal hB
    _ = _ := ofReal_norm_sectionConj_sq K x hx

/-- **Bessel for integral operators** (finite sums, `eLpNorm` form). -/
theorem sum_eLpNorm_intOp_sq_le (K : Lp 𝕜 2 (μ.prod ν)) {v : ι → Lp 𝕜 2 ν}
    (hv : Orthonormal 𝕜 v) (s : Finset ι) :
    ∑ i ∈ s, eLpNorm (intOp K (v i)) 2 μ ^ 2 ≤ eLpNorm K 2 (μ.prod ν) ^ 2 := by
  calc ∑ i ∈ s, eLpNorm (intOp K (v i)) 2 μ ^ 2
      = ∫⁻ x, ∑ i ∈ s, ‖intOp K (v i) x‖ₑ ^ 2 ∂μ := by
        rw [lintegral_finsetSum' s fun i _ ↦ (Lp.aestronglyMeasurable _).enorm.pow_const 2]
        exact Finset.sum_congr rfl fun i _ ↦ eLpNorm_two_sq _
    _ ≤ ∫⁻ x, eLpNorm (fun y ↦ K (x, y)) 2 ν ^ 2 ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_memLp_section (Lp.stronglyMeasurable K) (Lp.memLp K),
          (eventually_all_finset s).2 fun i _ ↦ intOp_ae_eq K (v i)] with x hx hT
        calc ∑ i ∈ s, ‖intOp K (v i) x‖ₑ ^ 2 = ∑ i ∈ s, ‖kernelApply ν K (v i) x‖ₑ ^ 2 :=
              Finset.sum_congr rfl fun i hi ↦ by rw [hT i hi]; rfl
          _ ≤ _ := sum_enorm_kernelApply_sq_le K x hx hv s
    _ = _ := lintegral_eLpNorm_section_sq (Lp.aestronglyMeasurable K)

theorem norm_sq_eq_toReal_eLpNorm {γ : Type*} [MeasurableSpace γ] {m : Measure γ}
    (f : Lp 𝕜 2 m) : ‖f‖ ^ 2 = (eLpNorm f 2 m ^ 2).toReal := by
  rw [Lp.norm_def, ENNReal.toReal_pow]

/-- **Bessel for integral operators**: `Σ_{i ∈ s} ‖T_K v_i‖² ≤ ‖K‖²` for orthonormal `v`. -/
theorem sum_norm_intOp_sq_le (K : Lp 𝕜 2 (μ.prod ν)) {v : ι → Lp 𝕜 2 ν}
    (hv : Orthonormal 𝕜 v) (s : Finset ι) :
    ∑ i ∈ s, ‖intOp K (v i)‖ ^ 2 ≤ ‖K‖ ^ 2 := by
  simp_rw [norm_sq_eq_toReal_eLpNorm]
  rw [← ENNReal.toReal_sum fun i _ ↦ ENNReal.pow_ne_top (Lp.eLpNorm_ne_top _)]
  exact ENNReal.toReal_mono (ENNReal.pow_ne_top (Lp.eLpNorm_ne_top K))
    (sum_eLpNorm_intOp_sq_le K hv s)

theorem summable_norm_intOp_sq (K : Lp 𝕜 2 (μ.prod ν)) {v : ι → Lp 𝕜 2 ν}
    (hv : Orthonormal 𝕜 v) : Summable fun i ↦ ‖intOp K (v i)‖ ^ 2 :=
  summable_of_sum_le (fun i ↦ by positivity) (sum_norm_intOp_sq_le K hv)

/-- **Bessel for integral operators**: `Σ_i ‖T_K v_i‖² ≤ ‖K‖²` for orthonormal `v`
(any index type). -/
theorem tsum_norm_intOp_sq_le (K : Lp 𝕜 2 (μ.prod ν)) {v : ι → Lp 𝕜 2 ν}
    (hv : Orthonormal 𝕜 v) : ∑' i, ‖intOp K (v i)‖ ^ 2 ≤ ‖K‖ ^ 2 :=
  Real.tsum_le_of_sum_le (fun i ↦ by positivity) (sum_norm_intOp_sq_le K hv)

/-! ### Parseval: Hilbert bases -/

theorem hasSum_norm_inner_sq (b : HilbertBasis ι 𝕜 (Lp 𝕜 2 ν)) (h : Lp 𝕜 2 ν) :
    HasSum (fun i ↦ ‖⟪b i, h⟫_𝕜‖ ^ 2) (‖h‖ ^ 2) := by
  have := lp.hasSum_norm (p := 2) (by norm_num) (b.repr h)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map,
    HilbertBasis.repr_apply_apply] at this
  exact this

/-- Pointwise Parseval: `Σ_i |T_K b_i (x)|² = ‖K(x, ·)‖²`. -/
theorem tsum_enorm_kernelApply_sq_eq (K : Lp 𝕜 2 (μ.prod ν)) (x : α)
    (hx : MemLp (fun y ↦ K (x, y)) 2 ν) (b : HilbertBasis ι 𝕜 (Lp 𝕜 2 ν)) :
    ∑' i, ‖kernelApply ν K (b i) x‖ₑ ^ 2 = eLpNorm (fun y ↦ K (x, y)) 2 ν ^ 2 := by
  have hP := hasSum_norm_inner_sq b (sectionConj K x hx)
  simp_rw [enorm_kernelApply_sq_eq K x hx]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i ↦ by positivity) hP.summable, hP.tsum_eq,
    ofReal_norm_sectionConj_sq]

/-- **Hilbert-Schmidt identity** (`eLpNorm` form): for a countable Hilbert basis `b` of `L²(ν)`,
`Σ_i ‖T_K b_i‖² = ‖K‖²`. -/
theorem tsum_eLpNorm_intOp_sq_eq [Countable ι] (K : Lp 𝕜 2 (μ.prod ν))
    (b : HilbertBasis ι 𝕜 (Lp 𝕜 2 ν)) :
    ∑' i, eLpNorm (intOp K (b i)) 2 μ ^ 2 = eLpNorm K 2 (μ.prod ν) ^ 2 := by
  calc ∑' i, eLpNorm (intOp K (b i)) 2 μ ^ 2 = ∑' i, ∫⁻ x, ‖intOp K (b i) x‖ₑ ^ 2 ∂μ := by
        simp_rw [eLpNorm_two_sq]
    _ = ∫⁻ x, ∑' i, ‖intOp K (b i) x‖ₑ ^ 2 ∂μ :=
        (lintegral_tsum fun i ↦ (Lp.aestronglyMeasurable _).enorm.pow_const 2).symm
    _ = ∫⁻ x, eLpNorm (fun y ↦ K (x, y)) 2 ν ^ 2 ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_memLp_section (Lp.stronglyMeasurable K) (Lp.memLp K),
          ae_all_iff.2 fun i ↦ intOp_ae_eq K (b i)] with x hx hT
        rw [← tsum_enorm_kernelApply_sq_eq K x hx b]
        exact tsum_congr fun i ↦ by rw [hT i]; rfl
    _ = _ := lintegral_eLpNorm_section_sq (Lp.aestronglyMeasurable K)

/-- **Hilbert-Schmidt identity**: for a countable Hilbert basis `b` of `L²(ν)`,
`Σ_i ‖T_K b_i‖² = ‖K‖²_{L²(μ⊗ν)}`. -/
theorem hasSum_norm_intOp_sq [Countable ι] (K : Lp 𝕜 2 (μ.prod ν))
    (b : HilbertBasis ι 𝕜 (Lp 𝕜 2 ν)) :
    HasSum (fun i ↦ ‖intOp K (b i)‖ ^ 2) (‖K‖ ^ 2) := by
  have hfin : ∑' i, eLpNorm (intOp K (b i)) 2 μ ^ 2 ≠ ∞ := by
    rw [tsum_eLpNorm_intOp_sq_eq K b]; exact ENNReal.pow_ne_top (Lp.eLpNorm_ne_top K)
  have h := ENNReal.hasSum_toReal hfin
  rw [← ENNReal.tsum_toReal_eq fun i ↦ ENNReal.pow_ne_top (Lp.eLpNorm_ne_top _),
    tsum_eLpNorm_intOp_sq_eq K b, ← norm_sq_eq_toReal_eLpNorm] at h
  simpa only [← norm_sq_eq_toReal_eLpNorm] using h

/-! ### Eigenvalues -/

section Eigen

variable {μ : Measure α} [SFinite μ] {v : ι → Lp 𝕜 2 μ}

theorem norm_eigen (K : Lp 𝕜 2 (μ.prod μ)) (hv : Orthonormal 𝕜 v) {c : ι → 𝕜}
    (hc : ∀ i, intOp K (v i) = c i • v i) (i : ι) : ‖intOp K (v i)‖ = ‖c i‖ := by
  rw [hc, norm_smul, hv.1 i, mul_one]

/-- **Eigenvalue bound (finite sums)**: if `T_K v_i = c_i v_i` for orthonormal `v`, then
`Σ_{i ∈ s} |c_i|² ≤ ‖K‖²`. -/
theorem sum_eigenvalue_sq_le (K : Lp 𝕜 2 (μ.prod μ)) (hv : Orthonormal 𝕜 v) {c : ι → 𝕜}
    (hc : ∀ i, intOp K (v i) = c i • v i) (s : Finset ι) :
    ∑ i ∈ s, ‖c i‖ ^ 2 ≤ ‖K‖ ^ 2 := by
  simpa only [norm_eigen K hv hc] using sum_norm_intOp_sq_le K hv s

theorem summable_eigenvalue_sq (K : Lp 𝕜 2 (μ.prod μ)) (hv : Orthonormal 𝕜 v) {c : ι → 𝕜}
    (hc : ∀ i, intOp K (v i) = c i • v i) : Summable fun i ↦ ‖c i‖ ^ 2 :=
  summable_of_sum_le (fun i ↦ by positivity) (sum_eigenvalue_sq_le K hv hc)

/-- **Eigenvalue bound**: `Σ_i |c_i|² ≤ ‖K‖²_{L²}` over any orthonormal family of eigenvectors
`T_K v_i = c_i v_i` (in particular over an orthonormal eigenbasis of a Hermitian kernel). -/
theorem tsum_eigenvalue_sq_le (K : Lp 𝕜 2 (μ.prod μ)) (hv : Orthonormal 𝕜 v) {c : ι → 𝕜}
    (hc : ∀ i, intOp K (v i) = c i • v i) : ∑' i, ‖c i‖ ^ 2 ≤ ‖K‖ ^ 2 :=
  Real.tsum_le_of_sum_le (fun i ↦ by positivity) (sum_eigenvalue_sq_le K hv hc)

/-- Real eigenvalues (the self-adjoint case): `Σ_i λ_i² ≤ ‖K‖²`, summable. -/
theorem tsum_real_eigenvalue_sq_le (K : Lp 𝕜 2 (μ.prod μ)) (hv : Orthonormal 𝕜 v)
    {lam : ι → ℝ} (hc : ∀ i, intOp K (v i) = (lam i : 𝕜) • v i) :
    Summable (fun i ↦ lam i ^ 2) ∧ ∑' i, lam i ^ 2 ≤ ‖K‖ ^ 2 := by
  have h : ∀ i, ‖((lam i : ℝ) : 𝕜)‖ ^ 2 = lam i ^ 2 := fun i ↦ by
    rw [RCLike.norm_ofReal, sq_abs]
  have h1 := summable_eigenvalue_sq K hv hc
  have h2 := tsum_eigenvalue_sq_le K hv hc
  simp only [h] at h1 h2
  exact ⟨h1, h2⟩

/-- Counting: at most `‖K‖² / ε²` orthonormal eigenvectors have `|c_i| ≥ ε`. -/
theorem card_mul_sq_le_of_eigen (K : Lp 𝕜 2 (μ.prod μ)) (hv : Orthonormal 𝕜 v) {c : ι → 𝕜}
    (hc : ∀ i, intOp K (v i) = c i • v i) {ε : ℝ} (hε : 0 ≤ ε) (s : Finset ι)
    (hs : ∀ i ∈ s, ε ≤ ‖c i‖) : (s.card : ℝ) * ε ^ 2 ≤ ‖K‖ ^ 2 := by
  refine le_trans ?_ (sum_eigenvalue_sq_le K hv hc s)
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum fun i hi ↦ pow_le_pow_left₀ hε (hs i hi) 2

/-- Tail form: the eigenvalues outside a finite set `s` have square sum at most
`‖K‖² - Σ_{i ∈ s} |c_i|²`. -/
theorem tsum_eigenvalue_sq_compl_le (K : Lp 𝕜 2 (μ.prod μ)) (hv : Orthonormal 𝕜 v) {c : ι → 𝕜}
    (hc : ∀ i, intOp K (v i) = c i • v i) (s : Finset ι) :
    ∑' i : {i // i ∉ s}, ‖c i‖ ^ 2 ≤ ‖K‖ ^ 2 - ∑ i ∈ s, ‖c i‖ ^ 2 := by
  have hsum := summable_eigenvalue_sq K hv hc
  have := hsum.sum_add_tsum_subtype_compl s
  have h2 := tsum_eigenvalue_sq_le K hv hc
  linarith

end Eigen

end ArchS5
