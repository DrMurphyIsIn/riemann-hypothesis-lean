import Mathlib

/-!
# ArchS6_Eigen: an orthonormal eigenbasis for a compact self-adjoint operator

Mathlib gives `ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot` (the eigenspaces of a
compact symmetric operator span a dense subspace) but no orthonormal eigenbasis.  This file builds
one: choose a Hilbert basis of every eigenspace and collect them (`exists_eigenBasis`).  Bypass B2
only needs this; neither simplicity of the spectrum nor an ordering is used.

conjecture1_proved = False.
-/

open scoped InnerProductSpace ComplexConjugate
open Module End

noncomputable section

namespace ArchS6

set_option linter.unusedSectionVars false

universe u

variable {𝕜 : Type} [RCLike 𝕜] {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- An orthonormal family of eigenvectors of `T` with real eigenvalues, complete in `E`. -/
structure EigenBasis (T : E →L[𝕜] E) (ι : Type*) where
  e : ι → E
  μ : ι → ℝ
  orthonormal : Orthonormal 𝕜 e
  eigen : ∀ i, T (e i) = (μ i : 𝕜) • e i
  complete : ∀ x, (∀ i, ⟪e i, x⟫_𝕜 = 0) → x = 0

theorem isClosed_eigenspace (T : E →L[𝕜] E) (c : 𝕜) :
    IsClosed (eigenspace (T : E →ₗ[𝕜] E) c : Set E) := by
  have : (eigenspace (T : E →ₗ[𝕜] E) c : Set E) = {x | T x = c • x} := by
    ext x; simp
  rw [this]
  exact isClosed_eq T.continuous (continuous_const_smul c)

instance completeSpace_eigenspace (T : E →L[𝕜] E) (c : 𝕜) :
    CompleteSpace (eigenspace (T : E →ₗ[𝕜] E) c) :=
  (isClosed_eigenspace T c).completeSpace_coe

/-- The chosen Hilbert-basis index set of the eigenspace for `c`. -/
def eigIdx (T : E →L[𝕜] E) (c : 𝕜) : Set (eigenspace (T : E →ₗ[𝕜] E) c) :=
  Classical.choose (exists_hilbertBasis 𝕜 (eigenspace (T : E →ₗ[𝕜] E) c))

/-- The chosen Hilbert basis of the eigenspace for `c`. -/
def eigHB (T : E →L[𝕜] E) (c : 𝕜) : HilbertBasis (eigIdx T c) 𝕜 (eigenspace (T : E →ₗ[𝕜] E) c) :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis 𝕜 (eigenspace (T : E →ₗ[𝕜] E) c)))

theorem eigHB_apply (T : E →L[𝕜] E) (c : 𝕜) (v : eigIdx T c) : eigHB T c v = (v : _) := by
  have := Classical.choose_spec (Classical.choose_spec
    (exists_hilbertBasis 𝕜 (eigenspace (T : E →ₗ[𝕜] E) c)))
  exact congrFun this v

theorem norm_eigIdx (T : E →L[𝕜] E) (c : 𝕜) (v : eigIdx T c) :
    ‖((v.1 : eigenspace (T : E →ₗ[𝕜] E) c) : E)‖ = 1 := by
  have := (eigHB T c).orthonormal.1 v
  rw [eigHB_apply] at this
  simpa using this

/-- An eigenvector `x ≠ 0` of a symmetric operator has a real eigenvalue. -/
theorem eigenvalue_real {T : E →L[𝕜] E} (hT : (T : E →ₗ[𝕜] E).IsSymmetric) {c : 𝕜} {x : E}
    (hx : x ∈ eigenspace (T : E →ₗ[𝕜] E) c) (hx0 : x ≠ 0) : ((RCLike.re c : ℝ) : 𝕜) = c := by
  have h := hT.conj_eigenvalue_eq_self (hasEigenvalue_of_hasEigenvector ⟨hx, hx0⟩)
  exact RCLike.conj_eq_iff_re.1 h

/-- **Orthonormal eigenbasis** of a compact self-adjoint operator. -/
theorem exists_eigenBasis {T : E →L[𝕜] E} (hc : IsCompactOperator T)
    (hT : (T : E →ₗ[𝕜] E).IsSymmetric) :
    ∃ (ι : Type u) (_ : EigenBasis T ι), True := by
  let ι := Σ c : 𝕜, eigIdx T c
  let e : ι → E := fun i ↦ ((i.2.1 : eigenspace (T : E →ₗ[𝕜] E) i.1) : E)
  have hmem : ∀ i : ι, e i ∈ eigenspace (T : E →ₗ[𝕜] E) i.1 := fun i ↦ i.2.1.2
  have hne : ∀ i : ι, e i ≠ 0 := fun i h ↦ by
    have := norm_eigIdx T i.1 i.2
    simp only [e] at h
    rw [h, norm_zero] at this
    exact zero_ne_one this
  refine ⟨ι, ⟨e, fun i ↦ RCLike.re i.1, ⟨fun i ↦ norm_eigIdx T i.1 i.2, ?_⟩, fun i ↦ ?_, ?_⟩, trivial⟩
  · -- pairwise orthogonality
    rintro ⟨c, v⟩ ⟨c', v'⟩ hij
    by_cases hcc : c = c'
    · subst hcc
      have hv : v ≠ v' := fun h ↦ hij (by rw [h])
      have := (eigHB T c).orthonormal.2 hv
      simp only [eigHB_apply] at this
      simpa [e] using this
    · exact hT.orthogonalFamily_eigenspaces hcc v.1 v'.1
  · -- eigen-relation with real eigenvalue
    have h1 := mem_eigenspace_iff.1 (hmem i)
    rw [eigenvalue_real hT (hmem i) (hne i)]
    exact h1
  · -- completeness
    intro x hx
    have hperp : ∀ c, ∀ u ∈ eigenspace (T : E →ₗ[𝕜] E) c, ⟪x, u⟫_𝕜 = 0 := by
      intro c u hu
      let b := eigHB T c
      have hs := (b.hasSum_repr ⟨u, hu⟩)
      have hs2 := ((innerSL 𝕜 x).comp (eigenspace (T : E →ₗ[𝕜] E) c).subtypeL).hasSum hs
      have hz : ∀ j, ((innerSL 𝕜 x).comp (eigenspace (T : E →ₗ[𝕜] E) c).subtypeL)
          (b.repr ⟨u, hu⟩ j • b j) = 0 := by
        intro j
        simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
          innerSL_apply_apply, Submodule.coe_smul, inner_smul_right, eigHB_apply, b]
        have := hx ⟨c, j⟩
        rw [← inner_conj_symm] at this
        simp only [map_eq_zero] at this
        rw [this, mul_zero]
      simp only [hz] at hs2
      have := hs2.unique hasSum_zero
      simpa using this
    have hmem' : x ∈ (⨆ c, eigenspace (T : E →ₗ[𝕜] E) c)ᗮ := by
      rw [← Submodule.iInf_orthogonal, Submodule.mem_iInf]
      intro c
      rw [Submodule.mem_orthogonal']
      intro u hu
      exact hperp c u hu
    rw [ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hT] at hmem'
    exact (Submodule.mem_bot 𝕜).1 hmem'

namespace EigenBasis

variable {T : E →L[𝕜] E} {ι : Type*} (b : EigenBasis T ι)

/-- The eigenbasis as a Mathlib `HilbertBasis`. -/
def toHilbertBasis : HilbertBasis ι 𝕜 E :=
  HilbertBasis.mkOfOrthogonalEqBot b.orthonormal (by
    rw [Submodule.eq_bot_iff]
    intro x hx
    apply b.complete
    intro i
    rw [Submodule.mem_orthogonal'] at hx
    rw [← inner_conj_symm, hx (b.e i) (Submodule.subset_span ⟨i, rfl⟩), map_zero])

theorem coe_toHilbertBasis : ⇑b.toHilbertBasis = b.e :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- Expansion of every vector along the eigenbasis. -/
theorem hasSum (x : E) : HasSum (fun i ↦ ⟪b.e i, x⟫_𝕜 • b.e i) x := by
  have := b.toHilbertBasis.hasSum_repr x
  simpa [coe_toHilbertBasis, HilbertBasis.repr_apply_apply] using this

/-- Parseval: `Σ ⟪x, e_i⟫ ⟪e_i, y⟫ = ⟪x, y⟫`. -/
theorem hasSum_inner_mul_inner (x y : E) :
    HasSum (fun i ↦ ⟪x, b.e i⟫_𝕜 * ⟪b.e i, y⟫_𝕜) ⟪x, y⟫_𝕜 := by
  have := b.toHilbertBasis.hasSum_inner_mul_inner x y
  simpa [coe_toHilbertBasis] using this

/-- Eigenvalues are bounded by the operator norm. -/
theorem abs_μ_le (i : ι) : |b.μ i| ≤ ‖T‖ := by
  have h := T.le_opNorm (b.e i)
  rw [b.eigen i, norm_smul, b.orthonormal.1 i, mul_one, mul_one] at h
  simpa using h

/-- `μ_i = ⟪e_i, T e_i⟫`. -/
theorem μ_eq_inner (i : ι) : ((b.μ i : ℝ) : 𝕜) = ⟪b.e i, T (b.e i)⟫_𝕜 := by
  rw [b.eigen i, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
  simp

end EigenBasis

end ArchS6
