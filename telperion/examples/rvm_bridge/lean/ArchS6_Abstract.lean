import Mathlib

/-!
# ArchS6_Abstract: CC Prop 4.5 and the spectral decomposition (81) as Hilbert-space algebra

Connes–Consani, arXiv:2006.13771, §4.  Bypass B2 of the blueprint: no pairs-of-projections
(Halmos) theory, no angle operator, no simplicity of the prolate spectrum.

Setting (`ProjPair`): a complex Hilbert space `H` with
* `P₁` an orthogonal projection (idempotent, self-adjoint),
* `F` a self-adjoint involution (`F F = 1`, `F* = F`; on `L²(ℝ)_ev` this is `F_{e_ℝ}`).
Put `P̂₁ = F P₁ F`, `P = 1 - P₁`, `P̂ = 1 - P̂₁` (CC (62)), and Sonin's space
`S(1,1) = {ξ | P₁ ξ = 0 ∧ P₁ (F ξ) = 0}` (CC Def 4.4).

Data (`ProlateBasis`): an orthonormal family `ξ i` in `ran P₁`, complete in `ran P₁`, with
`P₁ F ξ i = λ i • ξ i` (CC (69)) and `|λ i| < 1`.  This is exactly what the spectral theorem for the
compact self-adjoint operator `P₁ F P₁` on `ran P₁` provides (see `ArchS6_Prolate`).

Results (CC numbering):
* `P₁_η` (74): `P₁ η = λ ξ` with `η = F ξ`.
* `inner_ψ_ψ`, `norm_ψ`, `orthonormal_ζ` (Prop 4.5 (iii)): `ψ = P η`, `‖ψ‖ = √(1 - λ²)`, `ζ`
  orthonormal.
* `hatP₁_ξ` (78), `hatP₁_ξ'` (80), `P₁hatP₁P₁_ξ` (70), `PhatPP_ζ` (`P P̂ P ζ = λ² ζ`).
* `hasSum_P₁` (`P₁ = Σ |ξ⟩⟨ξ|`), `hasSum_hatP₁_P₁` (79), `hasSum_hatP₁_P₁'` (80).
* `mem_sonin_iff_fixed`: Sonin's space is the eigenspace of `P P̂ P` for the eigenvalue 1.
* `hasSum_PhatPP` (81): `P P̂ P = Σ λ² |ζ⟩⟨ζ| + S`, `S` the orthogonal projection on Sonin's space.
* `hasSum_inner_PhatPP` (76) in quadratic-form form, with the exact remainder `‖S x‖²`.
* `inner_ξ_A_ξ` (77) for any operator `A` with `⟨ξ|Aξ⟩ = ⟨η|Aη⟩`.

conjecture1_proved = False.
-/

open scoped InnerProductSpace ComplexConjugate
open Filter Topology

noncomputable section

namespace ArchS6

set_option linter.unusedSectionVars false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### Orthogonal projections, pointwise -/

/-- An orthogonal projection, given pointwise. -/
def IsOrthProj (Q : H →L[ℂ] H) : Prop :=
  (∀ x, Q (Q x) = Q x) ∧ ∀ x y, ⟪Q x, y⟫_ℂ = ⟪x, Q y⟫_ℂ

namespace IsOrthProj

variable {Q : H →L[ℂ] H}

theorem compl (hQ : IsOrthProj Q) : IsOrthProj (1 - Q) := by
  refine ⟨fun x ↦ ?_, fun x y ↦ ?_⟩
  · simp [map_sub, hQ.1]
  · simp [hQ.2]

theorem inner_sub_eq_zero (hQ : IsOrthProj Q) (x : H) : ⟪Q x, x - Q x⟫_ℂ = 0 := by
  rw [inner_sub_right, hQ.2 x (Q x), hQ.1, hQ.2 x x, sub_self]

/-- Pythagoras for an orthogonal projection. -/
theorem norm_sq_eq (hQ : IsOrthProj Q) (x : H) :
    ‖x‖ ^ 2 = ‖Q x‖ ^ 2 + ‖x - Q x‖ ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (Q x) (x - Q x)
    (hQ.inner_sub_eq_zero x)
  simp only [add_sub_cancel] at h
  rw [sq, sq, sq, h]

theorem norm_le (hQ : IsOrthProj Q) (x : H) : ‖Q x‖ ≤ ‖x‖ := by
  have h := hQ.norm_sq_eq x
  have : ‖Q x‖ ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x - Q x‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

/-- If `‖x - Q x‖ = ‖x‖` then `Q x = 0`. -/
theorem eq_zero_of_norm_compl (hQ : IsOrthProj Q) {x : H} (h : ‖x - Q x‖ = ‖x‖) : Q x = 0 := by
  have h2 := hQ.norm_sq_eq x
  rw [h] at h2
  have : ‖Q x‖ ^ 2 = 0 := by linarith
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)

theorem inner_eq_zero_of (hQ : IsOrthProj Q) {u v : H} (hu : Q u = u) (hv : Q v = 0) :
    ⟪u, v⟫_ℂ = 0 := by
  rw [← hu, hQ.2, hv, inner_zero_right]

theorem re_inner_self (hQ : IsOrthProj Q) (x : H) : RCLike.re ⟪Q x, x⟫_ℂ = ‖Q x‖ ^ 2 := by
  have : ⟪Q x, x⟫_ℂ = ⟪Q x, Q x⟫_ℂ := by rw [hQ.2 x (Q x), hQ.1]; exact hQ.2 x x
  rw [this, inner_self_eq_norm_sq]

end IsOrthProj

/-- If every term of a convergent series lies in a closed submodule, so does the sum. -/
theorem hasSum_mem {ι : Type*} (M : Submodule ℂ H) (hM : IsClosed (M : Set H)) {f : ι → H}
    {z : H} (hs : HasSum f z) (h : ∀ i, f i ∈ M) : z ∈ M :=
  hM.mem_of_tendsto hs (Eventually.of_forall fun _ ↦ M.sum_mem fun i _ ↦ h i)

/-- Bessel/Riesz–Fischer: the Fourier series of `x` along an orthonormal family converges, and
its sum has the same coefficients as `x`. -/
theorem exists_hasSum_orthonormal [CompleteSpace H] {ι : Type*} {v : ι → H}
    (hv : Orthonormal ℂ v) (x : H) :
    ∃ z, HasSum (fun i ↦ ⟪v i, x⟫_ℂ • v i) z ∧ ∀ j, ⟪v j, z⟫_ℂ = ⟪v j, x⟫_ℂ := by
  classical
  have hsum : Summable fun i ↦ ⟪v i, x⟫_ℂ • v i := by
    have := (hv.orthogonalFamily.summable_iff_norm_sq_summable
      (fun i ↦ ⟪v i, x⟫_ℂ)).2 (Orthonormal.inner_products_summable x hv)
    simpa [LinearIsometry.toSpanSingleton_apply] using this
  refine ⟨_, hsum.hasSum, fun j ↦ ?_⟩
  have h1 := (innerSL ℂ (v j)).hasSum hsum.hasSum
  have h2 : (fun i ↦ innerSL ℂ (v j) (⟪v i, x⟫_ℂ • v i)) =
      fun i ↦ if i = j then ⟪v j, x⟫_ℂ else 0 := by
    funext i
    rw [innerSL_apply_apply, inner_smul_right]
    by_cases hij : i = j
    · subst hij; simp [hv.1 i, inner_self_eq_norm_sq_to_K]
    · rw [if_neg hij, hv.2 (Ne.symm hij), mul_zero]
  rw [h2] at h1
  exact h1.unique (hasSum_ite_eq j _)

/-! ### Pairs of projections -/

/-- A pair `(P₁, F)`: `P₁` an orthogonal projection, `F` a self-adjoint involution. -/
structure ProjPair (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  P₁ : H →L[ℂ] H
  F : H →L[ℂ] H
  P₁_P₁ : ∀ x, P₁ (P₁ x) = P₁ x
  inner_P₁ : ∀ x y, ⟪P₁ x, y⟫_ℂ = ⟪x, P₁ y⟫_ℂ
  F_F : ∀ x, F (F x) = x
  inner_F : ∀ x y, ⟪F x, y⟫_ℂ = ⟪x, F y⟫_ℂ

namespace ProjPair

variable (S : ProjPair H)

/-- `P̂₁ = F P₁ F`. -/
def hatP₁ : H →L[ℂ] H := S.F ∘L S.P₁ ∘L S.F
/-- `P = 1 - P₁` (CC (62)). -/
def P : H →L[ℂ] H := 1 - S.P₁
/-- `P̂ = 1 - P̂₁` (CC (62)). -/
def hatP : H →L[ℂ] H := 1 - S.hatP₁
/-- The positive operator `P P̂ P` of CC (81). -/
def PhatPP : H →L[ℂ] H := S.P ∘L S.hatP ∘L S.P

@[simp] theorem hatP₁_apply (x : H) : S.hatP₁ x = S.F (S.P₁ (S.F x)) := rfl
@[simp] theorem P_apply (x : H) : S.P x = x - S.P₁ x := rfl
@[simp] theorem hatP_apply (x : H) : S.hatP x = x - S.hatP₁ x := rfl
theorem PhatPP_apply (x : H) : S.PhatPP x = S.P (S.hatP (S.P x)) := rfl

theorem isOrthProj_P₁ : IsOrthProj S.P₁ := ⟨S.P₁_P₁, S.inner_P₁⟩

theorem isOrthProj_hatP₁ : IsOrthProj S.hatP₁ := by
  refine ⟨fun x ↦ ?_, fun x y ↦ ?_⟩
  · simp [S.F_F, S.P₁_P₁]
  · simp only [hatP₁_apply]
    rw [S.inner_F, S.inner_P₁, S.inner_F]

theorem isOrthProj_P : IsOrthProj S.P := S.isOrthProj_P₁.compl
theorem isOrthProj_hatP : IsOrthProj S.hatP := S.isOrthProj_hatP₁.compl

theorem norm_F (x : H) : ‖S.F x‖ = ‖x‖ := by
  have h : ⟪S.F x, S.F x⟫_ℂ = ⟪x, x⟫_ℂ := by rw [S.inner_F, S.F_F]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖S.F x‖ ^ 2 = ‖x‖ ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h'

theorem inner_F_F (x y : H) : ⟪S.F x, S.F y⟫_ℂ = ⟪x, y⟫_ℂ := by rw [S.inner_F, S.F_F]

/-! #### Sonin's space -/

/-- Sonin's space `S(1,1) = {ξ | P₁ ξ = 0, P₁ (F ξ) = 0}` (CC Def 4.4). -/
def sonin : Submodule ℂ H :=
  LinearMap.ker (S.P₁ : H →ₗ[ℂ] H) ⊓ LinearMap.ker ((S.P₁ ∘L S.F : H →L[ℂ] H) : H →ₗ[ℂ] H)

theorem mem_sonin {x : H} : x ∈ S.sonin ↔ S.P₁ x = 0 ∧ S.P₁ (S.F x) = 0 := by
  simp [sonin]

theorem mem_sonin_iff_hatP₁ {x : H} : x ∈ S.sonin ↔ S.P₁ x = 0 ∧ S.hatP₁ x = 0 := by
  rw [mem_sonin]
  refine and_congr_right fun _ ↦ ⟨fun h ↦ by simp [h], fun h ↦ ?_⟩
  have := congrArg S.F h
  simpa [S.F_F] using this

theorem isClosed_sonin : IsClosed (S.sonin : Set H) := by
  have h1 := S.P₁.isClosed_ker
  have h2 := (S.P₁ ∘L S.F).isClosed_ker
  simpa [sonin, Submodule.coe_inf] using h1.inter h2

instance [CompleteSpace H] : CompleteSpace S.sonin := S.isClosed_sonin.completeSpace_coe

/-- **Sonin's space is the eigenspace of `P P̂ P` for the eigenvalue 1** (used in CC (90)). -/
theorem mem_sonin_iff_fixed {x : H} : x ∈ S.sonin ↔ S.PhatPP x = x := by
  constructor
  · intro hx
    rw [mem_sonin_iff_hatP₁] at hx
    simp [PhatPP_apply, hx.1, hx.2]
  · intro hx
    have hP := S.isOrthProj_P
    have hhP := S.isOrthProj_hatP
    have e1 : ‖x‖ ≤ ‖S.hatP (S.P x)‖ := by
      calc ‖x‖ = ‖S.P (S.hatP (S.P x))‖ := by rw [← PhatPP_apply, hx]
        _ ≤ _ := hP.norm_le _
    have e2 := hhP.norm_le (S.P x)
    have e3 := hP.norm_le x
    have hPx : S.P₁ x = 0 := by
      apply S.isOrthProj_P₁.eq_zero_of_norm_compl
      have : ‖S.P x‖ = ‖x‖ := le_antisymm e3 (e1.trans e2)
      simpa using this
    have hPx' : S.P x = x := by simp [hPx]
    have hh : S.hatP₁ x = 0 := by
      apply S.isOrthProj_hatP₁.eq_zero_of_norm_compl
      have : ‖S.hatP x‖ = ‖x‖ := by
        rw [hPx'] at e1 e2; exact le_antisymm e2 e1
      simpa using this
    exact (mem_sonin_iff_hatP₁ S).2 ⟨hPx, hh⟩

/-- `P P̂ P` is positive and contractive in the quadratic-form sense. -/
theorem re_inner_PhatPP (x : H) : RCLike.re ⟪S.PhatPP x, x⟫_ℂ = ‖S.hatP (S.P x)‖ ^ 2 := by
  have h : ⟪S.PhatPP x, x⟫_ℂ = ⟪S.hatP (S.P x), S.P x⟫_ℂ := by
    rw [PhatPP_apply, S.isOrthProj_P.2]
  rw [h, S.isOrthProj_hatP.re_inner_self]

theorem re_inner_PhatPP_le (x : H) : RCLike.re ⟪S.PhatPP x, x⟫_ℂ ≤ ‖x‖ ^ 2 := by
  rw [re_inner_PhatPP]
  have := (S.isOrthProj_hatP.norm_le (S.P x)).trans (S.isOrthProj_P.norm_le x)
  gcongr

theorem PhatPP_of_P₁_eq (x : H) (hx : S.P₁ x = x) : S.PhatPP x = 0 := by
  simp [PhatPP_apply, hx]

theorem inner_PhatPP (x y : H) : ⟪S.PhatPP x, y⟫_ℂ = ⟪x, S.PhatPP y⟫_ℂ := by
  simp only [PhatPP_apply]
  rw [S.isOrthProj_P.2, S.isOrthProj_hatP.2, S.isOrthProj_P.2]

end ProjPair

/-! ### Prolate data -/

/-- An orthonormal eigenbasis of `P₁ F P₁` on `ran P₁` with eigenvalues `|λ| < 1`
(CC (69): `P₁ F_{e_ℝ} P₁ φ_n = λ(n) P₁ φ_n`; `ξ_n = P₁ φ_n / ‖P₁ φ_n‖`). -/
structure ProlateBasis (S : ProjPair H) (ι : Type*) where
  ξ : ι → H
  lam : ι → ℝ
  orthonormal : Orthonormal ℂ ξ
  P₁_ξ : ∀ i, S.P₁ (ξ i) = ξ i
  eigen : ∀ i, S.P₁ (S.F (ξ i)) = (lam i : ℂ) • ξ i
  complete : ∀ x, S.P₁ x = x → (∀ i, ⟪ξ i, x⟫_ℂ = 0) → x = 0
  abs_lam_lt_one : ∀ i, |lam i| < 1

namespace ProlateBasis

variable {S : ProjPair H} {ι : Type*} (b : ProlateBasis S ι)

/-- `η_n = F ξ_n`. -/
def η (i : ι) : H := S.F (b.ξ i)
/-- `ψ_n = P η_n`. -/
def ψ (i : ι) : H := S.P (b.η i)
/-- `s_n = √(1 - λ_n²)`. -/
def s (i : ι) : ℝ := Real.sqrt (1 - b.lam i ^ 2)
/-- `ζ_n = ψ_n / √(1 - λ_n²)` (CC (76)). -/
def ζ (i : ι) : H := ((b.s i)⁻¹ : ℂ) • b.ψ i
/-- `τ(n) = λ(n) / √(1 - λ(n)²)` (CC Prop 4.5 (iv)). -/
def τ (i : ι) : ℝ := b.lam i / b.s i

theorem lam_sq_lt_one (i : ι) : b.lam i ^ 2 < 1 := by
  have := b.abs_lam_lt_one i
  nlinarith [abs_nonneg (b.lam i), sq_abs (b.lam i)]

theorem s_pos (i : ι) : 0 < b.s i := Real.sqrt_pos.2 (by linarith [b.lam_sq_lt_one i])

theorem s_sq (i : ι) : b.s i ^ 2 = 1 - b.lam i ^ 2 :=
  Real.sq_sqrt (by linarith [b.lam_sq_lt_one i])

theorem norm_ξ (i : ι) : ‖b.ξ i‖ = 1 := b.orthonormal.1 i

theorem norm_η (i : ι) : ‖b.η i‖ = 1 := by rw [η, S.norm_F, b.norm_ξ]

/-- CC (74): `P₁ η_n = λ(n) ξ_n`. -/
theorem P₁_η (i : ι) : S.P₁ (b.η i) = (b.lam i : ℂ) • b.ξ i := b.eigen i

theorem ψ_eq (i : ι) : b.ψ i = b.η i - (b.lam i : ℂ) • b.ξ i := by
  simp [ψ, b.P₁_η]

/-- `η_n = ψ_n + λ(n) ξ_n`. -/
theorem η_eq (i : ι) : b.η i = b.ψ i + (b.lam i : ℂ) • b.ξ i := by
  rw [ψ_eq]; abel

theorem P₁_ψ (i : ι) : S.P₁ (b.ψ i) = 0 := by
  simp [ψ, S.P₁_P₁]

theorem P_ψ (i : ι) : S.P (b.ψ i) = b.ψ i := by simp [b.P₁_ψ]

theorem P_ξ (i : ι) : S.P (b.ξ i) = 0 := by simp [b.P₁_ξ]

theorem inner_ξ_ψ (i j : ι) : ⟪b.ξ i, b.ψ j⟫_ℂ = 0 :=
  S.isOrthProj_P₁.inner_eq_zero_of (b.P₁_ξ i) (b.P₁_ψ j)

theorem inner_ψ_ξ (i j : ι) : ⟪b.ψ i, b.ξ j⟫_ℂ = 0 := by
  rw [← inner_conj_symm, b.inner_ξ_ψ, map_zero]

theorem inner_η_η (i j : ι) : ⟪b.η i, b.η j⟫_ℂ = ⟪b.ξ i, b.ξ j⟫_ℂ := S.inner_F_F _ _

theorem inner_ψ_ψ' (i j : ι) :
    ⟪b.ψ i, b.ψ j⟫_ℂ = ⟪b.ξ i, b.ξ j⟫_ℂ * (1 - (b.lam i : ℂ) * b.lam j) := by
  have h := b.inner_η_η i j
  rw [b.η_eq i, b.η_eq j] at h
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    b.inner_ξ_ψ, b.inner_ψ_ξ, Complex.conj_ofReal, mul_zero, add_zero, zero_add] at h
  linear_combination h

/-- CC Prop 4.5 (iii): the `ψ_n` are pairwise orthogonal with `‖ψ_n‖² = 1 - λ(n)²`. -/
theorem inner_ψ_ψ [DecidableEq ι] (i j : ι) :
    ⟪b.ψ i, b.ψ j⟫_ℂ = if i = j then ((1 - b.lam i ^ 2 : ℝ) : ℂ) else 0 := by
  rw [b.inner_ψ_ψ', orthonormal_iff_ite.1 b.orthonormal]
  split_ifs with h
  · subst h; push_cast; ring
  · simp

theorem norm_ψ (i : ι) : ‖b.ψ i‖ = b.s i := by
  classical
  have h := congrArg RCLike.re (b.inner_ψ_ψ i i)
  rw [if_pos rfl, inner_self_eq_norm_sq] at h
  have h' : ‖b.ψ i‖ ^ 2 = b.s i ^ 2 := by
    rw [b.s_sq, h, RCLike.re_to_complex, Complex.ofReal_re]
  exact (pow_left_inj₀ (norm_nonneg _) (b.s_pos i).le two_ne_zero).1 h'

/-- `ψ_n = √(1 - λ²) ζ_n`. -/
theorem ψ_eq_ζ (i : ι) : b.ψ i = (b.s i : ℂ) • b.ζ i := by
  rw [ζ, smul_smul, ← Complex.ofReal_inv, ← Complex.ofReal_mul, mul_inv_cancel₀ (b.s_pos i).ne',
    Complex.ofReal_one, one_smul]

/-- `η_n = √(1 - λ²) ζ_n + λ ξ_n`, i.e. CC's `ζ_n = (η_n - λ ξ_n) / √(1 - λ²)`. -/
theorem η_eq_ζ (i : ι) : b.η i = (b.s i : ℂ) • b.ζ i + (b.lam i : ℂ) • b.ξ i := by
  rw [← ψ_eq_ζ, η_eq]

/-- CC Prop 4.5 (iii): the `ζ_n` form an orthonormal family. -/
theorem orthonormal_ζ : Orthonormal ℂ b.ζ := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  simp only [ζ, inner_smul_left, inner_smul_right, b.inner_ψ_ψ, ← Complex.ofReal_inv,
    Complex.conj_ofReal]
  split_ifs with h
  · subst h
    rw [← b.s_sq]
    have : (b.s i : ℂ) ≠ 0 := by exact_mod_cast (b.s_pos i).ne'
    push_cast
    field_simp
  · simp

theorem P₁_ζ (i : ι) : S.P₁ (b.ζ i) = 0 := by simp [ζ, b.P₁_ψ]

theorem P_ζ (i : ι) : S.P (b.ζ i) = b.ζ i := by simp [b.P₁_ζ]

theorem inner_ξ_ζ (i j : ι) : ⟪b.ξ i, b.ζ j⟫_ℂ = 0 := by
  simp [ζ, b.inner_ξ_ψ]

theorem inner_ζ_ξ (i j : ι) : ⟪b.ζ i, b.ξ j⟫_ℂ = 0 := by
  simp [ζ, b.inner_ψ_ξ]

/-- CC (78): `P̂₁ ξ_n = λ(n) η_n`. -/
theorem hatP₁_ξ (i : ι) : S.hatP₁ (b.ξ i) = (b.lam i : ℂ) • b.η i := by
  simp only [ProjPair.hatP₁_apply, b.eigen, map_smul]; rfl

/-- CC (80), pointwise: `P̂₁ ξ_n = λ(n)² ξ_n + λ(n) ψ_n`. -/
theorem hatP₁_ξ' (i : ι) :
    S.hatP₁ (b.ξ i) = ((b.lam i ^ 2 : ℝ) : ℂ) • b.ξ i + (b.lam i : ℂ) • b.ψ i := by
  rw [b.hatP₁_ξ, b.η_eq, smul_add, smul_smul]
  push_cast
  rw [sq]; abel

/-- CC (70): `P₁ P̂₁ P₁ ξ_n = λ(n)² ξ_n`. -/
theorem P₁hatP₁P₁_ξ (i : ι) :
    S.P₁ (S.hatP₁ (S.P₁ (b.ξ i))) = ((b.lam i ^ 2 : ℝ) : ℂ) • b.ξ i := by
  rw [b.P₁_ξ, b.hatP₁_ξ', map_add, map_smul, map_smul, b.P₁_ξ, b.P₁_ψ, smul_zero, add_zero]

theorem F_ψ (i : ι) : S.F (b.ψ i) = b.ξ i - (b.lam i : ℂ) • b.η i := by
  rw [ψ_eq, map_sub, map_smul, η, S.F_F]

/-- `P P̂ P ψ_n = λ(n)² ψ_n`. -/
theorem PhatPP_ψ (i : ι) : S.PhatPP (b.ψ i) = ((b.lam i ^ 2 : ℝ) : ℂ) • b.ψ i := by
  have h1 : S.P₁ (S.F (b.ψ i)) = ((1 - b.lam i ^ 2 : ℝ) : ℂ) • b.ξ i := by
    rw [b.F_ψ, map_sub, map_smul, b.P₁_ξ, b.P₁_η, smul_smul]
    push_cast; rw [sub_smul, one_smul, sq]
  have h2 : S.hatP₁ (b.ψ i) = ((1 - b.lam i ^ 2 : ℝ) : ℂ) • b.η i := by
    rw [ProjPair.hatP₁_apply, h1, map_smul]; rfl
  rw [ProjPair.PhatPP_apply, b.P_ψ, ProjPair.hatP_apply, h2, map_sub, map_smul, b.P_ψ]
  have : S.P (b.η i) = b.ψ i := rfl
  rw [this]
  push_cast
  rw [sub_smul, one_smul]; abel

/-- CC (81) eigenvectors: `P P̂ P ζ_n = λ(n)² ζ_n`. -/
theorem PhatPP_ζ (i : ι) : S.PhatPP (b.ζ i) = ((b.lam i ^ 2 : ℝ) : ℂ) • b.ζ i := by
  rw [ζ, map_smul, b.PhatPP_ψ, smul_comm]

/-! #### Orthogonality to Sonin's space -/

theorem inner_sonin_ξ {x : H} (hx : x ∈ S.sonin) (i : ι) : ⟪x, b.ξ i⟫_ℂ = 0 := by
  rw [← b.P₁_ξ i, ← S.inner_P₁, (S.mem_sonin.1 hx).1, inner_zero_left]

theorem inner_sonin_η {x : H} (hx : x ∈ S.sonin) (i : ι) : ⟪x, b.η i⟫_ℂ = 0 := by
  rw [η, ← S.inner_F, ← b.P₁_ξ i, ← S.inner_P₁, (S.mem_sonin.1 hx).2, inner_zero_left]

theorem inner_sonin_ψ {x : H} (hx : x ∈ S.sonin) (i : ι) : ⟪x, b.ψ i⟫_ℂ = 0 := by
  rw [ψ_eq, inner_sub_right, inner_smul_right, b.inner_sonin_η hx, b.inner_sonin_ξ hx]; simp

theorem inner_sonin_ζ {x : H} (hx : x ∈ S.sonin) (i : ι) : ⟪x, b.ζ i⟫_ℂ = 0 := by
  rw [ζ, inner_smul_right, b.inner_sonin_ψ hx, mul_zero]

theorem inner_ζ_sonin {x : H} (hx : x ∈ S.sonin) (i : ι) : ⟪b.ζ i, x⟫_ℂ = 0 := by
  rw [← inner_conj_symm, b.inner_sonin_ζ hx, map_zero]

/-- The key completeness step: a vector in `ker P₁` orthogonal to every `ζ_n` lies in Sonin's
space. -/
theorem mem_sonin_of_orthogonal {x : H} (hx : S.P₁ x = 0) (h : ∀ i, ⟪b.ζ i, x⟫_ℂ = 0) :
    x ∈ S.sonin := by
  refine S.mem_sonin.2 ⟨hx, ?_⟩
  apply b.complete _ (S.P₁_P₁ _)
  intro i
  have hψ : ⟪b.ψ i, x⟫_ℂ = 0 := by
    rw [b.ψ_eq_ζ, inner_smul_left, h i, mul_zero]
  have hξ : ⟪b.ξ i, x⟫_ℂ = 0 := by rw [← b.P₁_ξ i, S.inner_P₁, hx, inner_zero_right]
  rw [← S.inner_P₁, b.P₁_ξ, ← S.inner_F, ← η, b.η_eq, inner_add_left, inner_smul_left, hψ, hξ]
  simp

/-! #### Expansions -/

variable [CompleteSpace H]

/-- `P₁ = Σ |ξ_n⟩⟨ξ_n|` (CC proof of Prop 4.5 (ii)). -/
theorem hasSum_P₁ (x : H) : HasSum (fun i ↦ ⟪b.ξ i, x⟫_ℂ • b.ξ i) (S.P₁ x) := by
  obtain ⟨z, hz, hzc⟩ := exists_hasSum_orthonormal b.orthonormal x
  have hzm : z ∈ LinearMap.ker (S.P : H →ₗ[ℂ] H) :=
    hasSum_mem _ S.P.isClosed_ker hz fun i ↦ by simp [b.P₁_ξ]
  have hz1 : S.P₁ z = z := by
    have := LinearMap.mem_ker.1 hzm
    simp only [ContinuousLinearMap.coe_coe, ProjPair.P_apply] at this
    exact (sub_eq_zero.1 this).symm
  have : S.P₁ x - z = 0 := by
    apply b.complete
    · rw [map_sub, S.P₁_P₁, hz1]
    · intro i
      rw [inner_sub_right, hzc, ← S.inner_P₁, b.P₁_ξ, sub_self]
  rwa [sub_eq_zero.1 this]

/-- CC (79): `P̂₁ P₁ = Σ λ(n) |η_n⟩⟨ξ_n|`. -/
theorem hasSum_hatP₁_P₁ (x : H) :
    HasSum (fun i ↦ (⟪b.ξ i, x⟫_ℂ * b.lam i) • b.η i) (S.hatP₁ (S.P₁ x)) := by
  have := S.hatP₁.hasSum (b.hasSum_P₁ x)
  convert this using 1
  funext i
  rw [map_smul, b.hatP₁_ξ, smul_smul]

/-- CC (80): `P̂₁ P₁ = Σ λ(n)² |ξ_n⟩⟨ξ_n| + Σ λ(n) |ψ_n⟩⟨ξ_n|`. -/
theorem hasSum_hatP₁_P₁' (x : H) :
    HasSum (fun i ↦ ⟪b.ξ i, x⟫_ℂ • (((b.lam i ^ 2 : ℝ) : ℂ) • b.ξ i + (b.lam i : ℂ) • b.ψ i))
      (S.hatP₁ (S.P₁ x)) := by
  have := S.hatP₁.hasSum (b.hasSum_P₁ x)
  convert this using 1
  funext i
  rw [map_smul, b.hatP₁_ξ']

/-- The orthogonal projection `S` on Sonin's space (CC Thm 4.7). -/
def soninProj : H →L[ℂ] H := S.sonin.starProjection

omit b in
theorem soninProj_mem (x : H) : soninProj (S := S) x ∈ S.sonin := by
  exact S.sonin.starProjection_apply_mem x

omit b in
theorem sub_soninProj_mem (x : H) : x - soninProj (S := S) x ∈ S.soninᗮ := by
  exact S.sonin.sub_starProjection_mem_orthogonal x

/-- **CC (81)**: `P P̂ P = Σ λ(n)² |ζ_n⟩⟨ζ_n| + S`, with `S` the projection on Sonin's space. -/
theorem hasSum_PhatPP (x : H) :
    HasSum (fun i ↦ (((b.lam i ^ 2 : ℝ) : ℂ) * ⟪b.ζ i, x⟫_ℂ) • b.ζ i)
      (S.PhatPP x - soninProj (S := S) x) := by
  obtain ⟨z, hz, hzc⟩ := exists_hasSum_orthonormal b.orthonormal_ζ x
  set Sx := soninProj (S := S) x
  have hSx := soninProj_mem (S := S) x
  -- `z ∈ ker P₁` and `z ⊥ Sonin`
  have hz1 : S.P₁ z = 0 := by
    have : z ∈ LinearMap.ker (S.P₁ : H →ₗ[ℂ] H) :=
      hasSum_mem _ S.P₁.isClosed_ker hz fun i ↦ by simp [b.P₁_ζ]
    exact this
  have hz2 : z ∈ S.soninᗮ :=
    hasSum_mem _ (Submodule.isClosed_orthogonal _) hz fun i ↦
      Submodule.smul_mem _ _ fun y hy ↦ b.inner_sonin_ζ hy i
  -- `P x - S x = z`
  have key : S.P x - Sx = z := by
    have hd : S.P x - Sx - z ∈ S.sonin := by
      refine b.mem_sonin_of_orthogonal ?_ fun i ↦ ?_
      · rw [map_sub, map_sub, hz1, (S.mem_sonin.1 hSx).1]
        simp [S.P₁_P₁]
      · rw [inner_sub_right, inner_sub_right, hzc, ← S.isOrthProj_P.2, b.P_ζ,
          b.inner_ζ_sonin hSx]
        simp
    have hd' : S.P x - Sx - z ∈ S.soninᗮ := by
      refine Submodule.sub_mem _ ?_ hz2
      have h1 := sub_soninProj_mem (S := S) x
      have h2 : S.P x - x ∈ S.soninᗮ := by
        intro y hy
        have : S.P x - x = -S.P₁ x := by simp
        rw [this, inner_neg_right, ← S.inner_P₁, (S.mem_sonin.1 hy).1, inner_zero_left, neg_zero]
      have := Submodule.add_mem _ h2 h1
      convert this using 1
      abel
    have := Submodule.mem_inf.2 ⟨hd, hd'⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot, sub_eq_zero] at this
    exact this
  have h := S.PhatPP.hasSum hz
  have hlhs : S.PhatPP z = S.PhatPP x - Sx := by
    rw [← key, map_sub, (S.mem_sonin_iff_fixed).1 hSx]
    congr 1
    simp only [ProjPair.PhatPP_apply]
    rw [S.isOrthProj_P.1]
  rw [hlhs] at h
  convert h using 1
  funext i
  rw [map_smul, b.PhatPP_ζ, smul_smul, mul_comm]

/-- **CC (76)** with its exact remainder: `⟨x | P P̂ P x⟩ = Σ λ(n)² |⟨ζ_n|x⟩|² + ‖S x‖²`. -/
theorem hasSum_inner_PhatPP (x : H) :
    HasSum (fun i ↦ b.lam i ^ 2 * ‖⟪b.ζ i, x⟫_ℂ‖ ^ 2)
      (RCLike.re ⟪x, S.PhatPP x⟫_ℂ - ‖soninProj (S := S) x‖ ^ 2) := by
  have h := (innerSL ℂ x).hasSum (b.hasSum_PhatPP x)
  have h2 := Complex.reCLM.hasSum h
  have hS : RCLike.re ⟪x, soninProj (S := S) x⟫_ℂ = ‖soninProj (S := S) x‖ ^ 2 := by
    have h1 := sub_soninProj_mem (S := S) x
    have h0 : ⟪soninProj (S := S) x, x - soninProj (S := S) x⟫_ℂ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (soninProj_mem x) h1
    rw [inner_sub_right, sub_eq_zero] at h0
    rw [← inner_conj_symm, RCLike.conj_re, h0, inner_self_eq_norm_sq]
  simp only [innerSL_apply_apply, map_sub, Complex.reCLM_apply] at h2
  convert h2 using 1
  · funext i
    rw [inner_smul_right, mul_assoc, ← inner_conj_symm (b.ζ i) x, Complex.conj_mul',
      Complex.norm_conj]
    norm_cast
  · rw [← hS]; rfl

/-- CC (76): `Σ λ(n)² |ζ_n⟩⟨ζ_n| ≤ P P̂ P` as quadratic forms. -/
theorem tsum_le_inner_PhatPP (x : H) :
    ∑' i, b.lam i ^ 2 * ‖⟪b.ζ i, x⟫_ℂ‖ ^ 2 ≤ RCLike.re ⟪x, S.PhatPP x⟫_ℂ := by
  rw [(b.hasSum_inner_PhatPP x).tsum_eq]
  linarith [sq_nonneg ‖soninProj (S := S) x‖]

/-- CC Prop 4.5 (iv), (77), for an arbitrary operator `A` with `⟨ξ|Aξ⟩ = ⟨η|Aη⟩` (CC: `A = ϑ(ρ⁻¹)`,
using `ϑ(ρ) = F ϑ(ρ⁻¹) F` and reality of `ξ_n`):
`⟨ξ|Aξ⟩ = ⟨ζ|Aζ⟩ + τ (⟨ξ|Aζ⟩ + ⟨ζ|Aξ⟩)`. -/
theorem inner_ξ_A_ξ (A : H →L[ℂ] H) (i : ι)
    (hA : ⟪b.η i, A (b.η i)⟫_ℂ = ⟪b.ξ i, A (b.ξ i)⟫_ℂ) :
    ⟪b.ξ i, A (b.ξ i)⟫_ℂ = ⟪b.ζ i, A (b.ζ i)⟫_ℂ +
      (b.τ i : ℂ) * (⟪b.ξ i, A (b.ζ i)⟫_ℂ + ⟪b.ζ i, A (b.ξ i)⟫_ℂ) := by
  rw [b.η_eq_ζ i] at hA
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal] at hA
  have hs := b.s_pos i
  have hs2 : ((b.s i : ℂ)) ^ 2 = 1 - (b.lam i : ℂ) ^ 2 := by exact_mod_cast b.s_sq i
  have hsne : (b.s i : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have key : (b.s i : ℂ) * ((b.s i : ℂ) * ⟪b.ξ i, A (b.ξ i)⟫_ℂ - (b.s i : ℂ) * ⟪b.ζ i, A (b.ζ i)⟫_ℂ -
      (b.lam i : ℂ) * (⟪b.ξ i, A (b.ζ i)⟫_ℂ + ⟪b.ζ i, A (b.ξ i)⟫_ℂ)) = 0 := by
    linear_combination (-1 : ℂ) * hA + ⟪b.ξ i, A (b.ξ i)⟫_ℂ * hs2
  have key' := (mul_eq_zero.1 key).resolve_left hsne
  rw [τ, Complex.ofReal_div]
  field_simp
  linear_combination key'

end ProlateBasis

end ArchS6
