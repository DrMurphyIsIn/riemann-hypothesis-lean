import ArchS6_Abstract

/-!
# ArchS7_HS: Hilbert–Schmidt sums and CC (90) without trace class (bypass B1)

* `hasSum_norm_inner_sq`, `tsum_ofReal_norm_inner_sq`: Parseval for a Hilbert basis.
* `tsum_norm_sq_swap`: `Σ_i ‖V e_i‖² = Σ_j ‖V† f_j‖²` for any two Hilbert bases (in `ℝ≥0∞`).
* `hsSq`, `hsSq_indep`: the squared Hilbert–Schmidt norm, independent of the basis.
* `tsum_PhatPP` (**CC (90)**, HS form): for any operator `V` (CC: `ϑ(g)`, `ϑ(f) = V V†`),
  `‖P̂ P V‖²_HS = ‖S V‖²_HS + Σ λ(n)² ‖V† ζ_n‖²`, i.e.
  `Tr(ϑ(f) P P̂ P) = Tr(ϑ(f) S) + Σ λ(n)² ⟨ζ_n | ϑ(f) ζ_n⟩`.

conjecture1_proved = False.
-/

open scoped InnerProductSpace ComplexConjugate ENNReal
open Filter Topology

noncomputable section

namespace ArchS7

open ArchS6

set_option linter.unusedSectionVars false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Parseval: `‖x‖² = Σ |⟨b_i, x⟩|²`. -/
theorem hasSum_norm_inner_sq {ι : Type*} (b : HilbertBasis ι ℂ H) (x : H) :
    HasSum (fun i ↦ ‖⟪b i, x⟫_ℂ‖ ^ 2) (‖x‖ ^ 2) := by
  have h := Complex.reCLM.hasSum (b.hasSum_inner_mul_inner x x)
  simp only [Complex.reCLM_apply] at h
  convert h using 1
  · funext i
    rw [← inner_conj_symm x (b i), Complex.conj_mul']
    norm_cast
  · rw [inner_self_eq_norm_sq_to_K]; norm_cast

theorem tsum_ofReal_norm_inner_sq {ι : Type*} (b : HilbertBasis ι ℂ H) (x : H) :
    ∑' i, ENNReal.ofReal (‖⟪b i, x⟫_ℂ‖ ^ 2) = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i ↦ by positivity)
    (hasSum_norm_inner_sq b x).summable, (hasSum_norm_inner_sq b x).tsum_eq]

/-- `Σ_i ‖V e_i‖² = Σ_j ‖V† f_j‖²` for any two Hilbert bases. -/
theorem tsum_norm_sq_swap {ι κ : Type*} (e : HilbertBasis ι ℂ H) (f : HilbertBasis κ ℂ H)
    (V : H →L[ℂ] H) :
    ∑' i, ENNReal.ofReal (‖V (e i)‖ ^ 2)
      = ∑' j, ENNReal.ofReal (‖(ContinuousLinearMap.adjoint V) (f j)‖ ^ 2) := by
  calc ∑' i, ENNReal.ofReal (‖V (e i)‖ ^ 2)
      = ∑' i, ∑' j, ENNReal.ofReal (‖⟪f j, V (e i)⟫_ℂ‖ ^ 2) := by
        congr 1; funext i; rw [tsum_ofReal_norm_inner_sq]
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖⟪e i, (ContinuousLinearMap.adjoint V) (f j)⟫_ℂ‖ ^ 2) := by
        rw [ENNReal.tsum_comm]
        congr 1; funext j; congr 1; funext i
        rw [← ContinuousLinearMap.adjoint_inner_left, ← inner_conj_symm, Complex.norm_conj]
    _ = _ := by congr 1; funext j; rw [tsum_ofReal_norm_inner_sq]

/-- The squared Hilbert–Schmidt norm `‖V‖²_HS = Σ_i ‖V e_i‖²` in a Hilbert basis `e`. -/
def hsSq {ι : Type*} (e : HilbertBasis ι ℂ H) (V : H →L[ℂ] H) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (‖V (e i)‖ ^ 2)

/-- The Hilbert–Schmidt norm does not depend on the basis. -/
theorem hsSq_indep {ι κ : Type*} (e : HilbertBasis ι ℂ H) (e' : HilbertBasis κ ℂ H)
    (V : H →L[ℂ] H) : hsSq e V = hsSq e' V := by
  rw [hsSq, hsSq, tsum_norm_sq_swap e e V, tsum_norm_sq_swap e' e V]

theorem hsSq_adjoint {ι : Type*} (e : HilbertBasis ι ℂ H) (V : H →L[ℂ] H) :
    hsSq e (ContinuousLinearMap.adjoint V) = hsSq e V := by
  rw [hsSq, hsSq, tsum_norm_sq_swap e e V]

/-! ### CC (90) -/

namespace ProlateBasis

variable {S : ProjPair H} {ι : Type*} (b : ArchS6.ProlateBasis S ι)

/-- Pointwise (76)+(81): `‖P̂ P x‖² = Σ λ² |⟨ζ_n, x⟩|² + ‖S x‖²`. -/
theorem hasSum_norm_hatP_P (x : H) :
    HasSum (fun i ↦ b.lam i ^ 2 * ‖⟪b.ζ i, x⟫_ℂ‖ ^ 2)
      (‖S.hatP (S.P x)‖ ^ 2 - ‖ArchS6.ProlateBasis.soninProj (S := S) x‖ ^ 2) := by
  have h := b.hasSum_inner_PhatPP x
  have e : RCLike.re ⟪x, S.PhatPP x⟫_ℂ = ‖S.hatP (S.P x)‖ ^ 2 := by
    rw [← S.re_inner_PhatPP x, ← inner_conj_symm, RCLike.conj_re]
  rwa [e] at h

theorem ofReal_norm_hatP_P (x : H) :
    ENNReal.ofReal (‖S.hatP (S.P x)‖ ^ 2)
      = ENNReal.ofReal (‖ArchS6.ProlateBasis.soninProj (S := S) x‖ ^ 2)
        + ∑' i, ENNReal.ofReal (b.lam i ^ 2) * ENNReal.ofReal (‖⟪b.ζ i, x⟫_ℂ‖ ^ 2) := by
  have h := hasSum_norm_hatP_P b x
  have hnn : ∀ i, 0 ≤ b.lam i ^ 2 * ‖⟪b.ζ i, x⟫_ℂ‖ ^ 2 := fun i ↦ by positivity
  have hsum : 0 ≤ ‖S.hatP (S.P x)‖ ^ 2 - ‖ArchS6.ProlateBasis.soninProj (S := S) x‖ ^ 2 :=
    h.nonneg hnn
  simp_rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn h.summable, h.tsum_eq,
    ← ENNReal.ofReal_add (by positivity) hsum]
  congr 1; ring

/-- **CC (90) in Hilbert–Schmidt form.**  For any operator `V` and any Hilbert basis `e`,
`‖P̂ P V‖²_HS = ‖S V‖²_HS + Σ λ(n)² ‖V† ζ_n‖²`.  With `V = ϑ(g)`, `ϑ(f) = V V†`, this is
`Tr(ϑ(f) P P̂ P) = Tr(ϑ(f) S) + Σ λ(n)² ⟨ζ_n | ϑ(f) ζ_n⟩`. -/
theorem tsum_PhatPP {κ : Type*} (e : HilbertBasis κ ℂ H) (V : H →L[ℂ] H) :
    ∑' k, ENNReal.ofReal (‖S.hatP (S.P (V (e k)))‖ ^ 2)
      = ∑' k, ENNReal.ofReal (‖ArchS6.ProlateBasis.soninProj (S := S) (V (e k))‖ ^ 2)
        + ∑' i, ENNReal.ofReal (b.lam i ^ 2)
            * ENNReal.ofReal (‖(ContinuousLinearMap.adjoint V) (b.ζ i)‖ ^ 2) := by
  simp_rw [ofReal_norm_hatP_P b]
  rw [ENNReal.tsum_add, ENNReal.tsum_comm]
  congr 1
  congr 1; funext i
  rw [ENNReal.tsum_mul_left, ← tsum_ofReal_norm_inner_sq e]
  congr 2; funext k
  rw [← ContinuousLinearMap.adjoint_inner_left, ← inner_conj_symm, Complex.norm_conj]

end ProlateBasis

end ArchS7
