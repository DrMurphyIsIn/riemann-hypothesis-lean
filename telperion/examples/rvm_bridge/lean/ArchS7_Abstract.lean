import ArchS7_HS

/-!
# ArchS7_Abstract: CC Theorem 4.7 over an abstract pair of projections

Connes–Consani, arXiv:2006.13771, Thm 4.7: `Tr(ϑ(f) S) = W∞(f) + ∫ f(ρ⁻¹) ε(ρ) d*ρ` with
`ε(ρ) = Σ λ(n)/√(1-λ(n)²) ⟨ξ_n | ϑ(ρ⁻¹) ζ_n⟩` (84), and its proof (85)-(90).

Setting: S6's `ProjPair S` and `ProlateBasis S ι`, plus a `Scaling S`: operators `θ t` (CC's `ϑ(e^t)`)
that are isometric, satisfy `F θ(t) F = θ(-t)` (CC: `ϑ(ρ) = F⁻¹ ϑ(ρ⁻¹) F`), shrink supports for
`t ≥ 0` (`θ(-t)` maps `ran P₁` into itself, CC (82)), and have continuous matrix coefficients.
The additive variable is `t = log ρ`.

* `inner_ζ_θ_ξ` (**CC (82)**): `⟨ζ_m | ϑ(ρ⁻¹) ξ_n⟩ = 0` for `ρ ≥ 1`.
* `delta_term` (**CC (86)-(89), termwise**): `λ⟨ξ|ϑ(ρ⁻¹)η⟩ = λ²⟨ζ|ϑ(ρ⁻¹)ζ⟩ + τ⟨ξ|ϑ(ρ⁻¹)ζ⟩`.
* `cζ_neg`: `⟨ζ_n | ϑ(ρ) ζ_n⟩ = ⟨ζ_n | ϑ(ρ⁻¹) ζ_n⟩` (CC: "invariant under ρ ↦ ρ⁻¹").
* `δS_eq` (**CC (89)**): `δ(ρ) = Σ λ² ⟨ζ_n|ϑ(ρ⁻¹)ζ_n⟩ + ε(ρ)` for `ρ ≥ 1`, with `δ` the series (75).
* `integral_δS` (integrated (89)): `∫ f δ = Σ λ² ‖V† ζ_n‖² + ∫ f ε` when `‖V† v‖² = ∫ f ⟨v|θ v⟩`.
* `thm47` (**CC Thm 4.7**, HS form): from (85) `‖P̂ P V‖²_HS = W + ∫ f δ`, conclude
  `‖S V‖²_HS = W + ∫ f ε`, with `S` the projection on Sonin's space.
* `thm47_nonneg` (**CC (83)**): `W + Re ∫ f ε ≥ 0`.

conjecture1_proved = False.
-/

open scoped InnerProductSpace ComplexConjugate ENNReal
open MeasureTheory Filter Topology

noncomputable section

namespace ArchS7

open ArchS6

set_option linter.unusedSectionVars false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The scaling action `θ t = ϑ(e^t)` (CC (61)) relative to a pair `(P₁, F)`. -/
structure Scaling (S : ProjPair H) where
  θ : ℝ → H →L[ℂ] H
  norm_θ : ∀ t x, ‖θ t x‖ = ‖x‖
  F_θ_F : ∀ t x, S.F (θ t (S.F x)) = θ (-t) x
  P₁_θ : ∀ t, 0 ≤ t → ∀ x, S.P₁ x = x → S.P₁ (θ (-t) x) = θ (-t) x
  cont : ∀ x y, Continuous fun t ↦ ⟪x, θ t y⟫_ℂ

namespace Scaling

variable {S : ProjPair H} (T : Scaling S)

theorem inner_F_θ_F (t : ℝ) (x y : H) : ⟪S.F x, T.θ t (S.F y)⟫_ℂ = ⟪x, T.θ (-t) y⟫_ℂ := by
  rw [S.inner_F, T.F_θ_F]

theorem norm_inner_le (t : ℝ) (x y : H) : ‖⟪x, T.θ t y⟫_ℂ‖ ≤ ‖x‖ * ‖y‖ := by
  have := norm_inner_le_norm (𝕜 := ℂ) x (T.θ t y)
  rwa [T.norm_θ] at this

end Scaling

namespace ProlateBasis

variable {S : ProjPair H} {ι : Type*} (b : ArchS6.ProlateBasis S ι) (T : Scaling S)

/-! ### The termwise identities -/

/-- **CC (82)**: `⟨ζ_m | ϑ(ρ⁻¹) ξ_n⟩ = 0` for `ρ = e^t ≥ 1`. -/
theorem inner_ζ_θ_ξ {t : ℝ} (ht : 0 ≤ t) (i j : ι) :
    ⟪b.ζ i, T.θ (-t) (b.ξ j)⟫_ℂ = 0 := by
  have hu : S.P₁ (T.θ (-t) (b.ξ j)) = T.θ (-t) (b.ξ j) := T.P₁_θ t ht _ (b.P₁_ξ j)
  rw [← inner_conj_symm, S.isOrthProj_P₁.inner_eq_zero_of hu (b.P₁_ζ i), map_zero]

/-- CC's footnote 8: `λ √(1-λ²) + λ² τ = τ`. -/
theorem τ_eq (i : ι) : b.τ i = b.lam i * b.s i + b.lam i ^ 2 * b.τ i := by
  have hs := b.s_pos i
  have h2 := b.s_sq i
  unfold ArchS6.ProlateBasis.τ
  field_simp
  linear_combination (-(b.lam i)) * h2

variable (hreal : ∀ i t, ⟪b.ξ i, T.θ t (b.ξ i)⟫_ℂ = ⟪b.ξ i, T.θ (-t) (b.ξ i)⟫_ℂ)
include hreal

/-- **CC (86)-(89) termwise**, for `ρ = e^t ≥ 1`:
`λ⟨ξ|ϑ(ρ⁻¹)η⟩ = λ²⟨ζ|ϑ(ρ⁻¹)ζ⟩ + τ⟨ξ|ϑ(ρ⁻¹)ζ⟩`. -/
theorem delta_term {t : ℝ} (ht : 0 ≤ t) (i : ι) :
    (b.lam i : ℂ) * ⟪b.ξ i, T.θ (-t) (b.η i)⟫_ℂ
      = ((b.lam i ^ 2 : ℝ) : ℂ) * ⟪b.ζ i, T.θ (-t) (b.ζ i)⟫_ℂ
        + (b.τ i : ℂ) * ⟪b.ξ i, T.θ (-t) (b.ζ i)⟫_ℂ := by
  have hA : ⟪b.η i, T.θ (-t) (b.η i)⟫_ℂ = ⟪b.ξ i, T.θ (-t) (b.ξ i)⟫_ℂ := by
    rw [ArchS6.ProlateBasis.η, T.inner_F_θ_F, neg_neg, hreal]
  have h77 := b.inner_ξ_A_ξ (T.θ (-t)) i hA
  rw [inner_ζ_θ_ξ b T ht i i, add_zero] at h77
  have hfoot : ((b.τ i : ℝ) : ℂ) = (b.lam i : ℂ) * (b.s i : ℂ) + (b.lam i : ℂ) ^ 2 * (b.τ i : ℂ) := by
    exact_mod_cast τ_eq b i
  rw [b.η_eq_ζ i, map_add, map_smul, map_smul, inner_add_right, inner_smul_right,
    inner_smul_right]
  push_cast
  linear_combination ((b.lam i : ℂ) ^ 2) * h77 - ⟪b.ξ i, T.θ (-t) (b.ζ i)⟫_ℂ * hfoot

/-- The diagonal coefficient `cζ_n(t) = ⟨ζ_n | ϑ(e^t) ζ_n⟩`. -/
def cζ (i : ι) (t : ℝ) : ℂ := ⟪b.ζ i, T.θ t (b.ζ i)⟫_ℂ

omit hreal in
theorem inner_ψ_θ_ψ (i : ι) (t : ℝ) :
    ⟪b.ψ i, T.θ t (b.ψ i)⟫_ℂ
      = ⟪b.ξ i, T.θ (-t) (b.ξ i)⟫_ℂ - (b.lam i : ℂ) * ⟪b.ξ i, T.θ (-t) (b.η i)⟫_ℂ
        - (b.lam i : ℂ) * ⟪b.η i, T.θ (-t) (b.ξ i)⟫_ℂ
        + (b.lam i : ℂ) ^ 2 * ⟪b.ξ i, T.θ t (b.ξ i)⟫_ℂ := by
  have hξ : b.ξ i = S.F (b.η i) := by rw [ArchS6.ProlateBasis.η, S.F_F]
  have h1 : ⟪b.η i, T.θ t (b.η i)⟫_ℂ = ⟪b.ξ i, T.θ (-t) (b.ξ i)⟫_ℂ := by
    rw [ArchS6.ProlateBasis.η, T.inner_F_θ_F]
  have h2 : ⟪b.η i, T.θ t (b.ξ i)⟫_ℂ = ⟪b.ξ i, T.θ (-t) (b.η i)⟫_ℂ := by
    conv_lhs => rw [hξ]
    rw [ArchS6.ProlateBasis.η, T.inner_F_θ_F, ← ArchS6.ProlateBasis.η]
  have h3 : ⟪b.ξ i, T.θ t (b.η i)⟫_ℂ = ⟪b.η i, T.θ (-t) (b.ξ i)⟫_ℂ := by
    conv_lhs => rw [hξ, ArchS6.ProlateBasis.η]
    rw [T.inner_F_θ_F, ← ArchS6.ProlateBasis.η]
  rw [b.ψ_eq, map_sub, map_smul, inner_sub_left, inner_sub_right, inner_sub_right,
    inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right, h1, h2, h3,
    Complex.conj_ofReal]
  ring

omit hreal in
theorem inner_ξ_θ_η (i : ι) (t : ℝ) :
    ⟪b.ξ i, T.θ t (b.η i)⟫_ℂ = ⟪b.η i, T.θ (-t) (b.ξ i)⟫_ℂ := by
  have hξ : b.ξ i = S.F (b.η i) := by rw [ArchS6.ProlateBasis.η, S.F_F]
  conv_lhs => rw [hξ, ArchS6.ProlateBasis.η]
  rw [T.inner_F_θ_F, ← ArchS6.ProlateBasis.η]

omit hreal in
theorem inner_η_θ_ξ (i : ι) (t : ℝ) :
    ⟪b.η i, T.θ t (b.ξ i)⟫_ℂ = ⟪b.ξ i, T.θ (-t) (b.η i)⟫_ℂ := by
  rw [inner_ξ_θ_η b T i (-t), neg_neg]

/-- `⟨ζ_n | ϑ(ρ) ζ_n⟩ = ⟨ζ_n | ϑ(ρ⁻¹) ζ_n⟩` (CC, proof of Thm 4.7). -/
theorem cζ_neg (i : ι) (t : ℝ) : cζ b T i (-t) = cζ b T i t := by
  have e : ∀ u, cζ b T i u
      = ((b.s i)⁻¹ : ℂ) * ((b.s i)⁻¹ : ℂ) * ⟪b.ψ i, T.θ u (b.ψ i)⟫_ℂ := by
    intro u
    rw [cζ, ArchS6.ProlateBasis.ζ, map_smul, inner_smul_left, inner_smul_right,
      ← Complex.ofReal_inv, Complex.conj_ofReal]
    ring
  rw [e, e, inner_ψ_θ_ψ, inner_ψ_θ_ψ, neg_neg, inner_ξ_θ_η b T i t, inner_η_θ_ξ b T i t]
  simp only [hreal i t]
  ring

/-! ### The series (75), (84), (89) -/

omit hreal in
/-- CC (75): `δ(e^t) = Σ λ(n) ⟨ξ_n | ϑ(e^{-t}) η_n⟩` (`= Tr(ϑ(ρ⁻¹) P̂₁ P₁)` by (79)). -/
def δS (t : ℝ) : ℂ := ∑' i, (b.lam i : ℂ) * ⟪b.ξ i, T.θ (-t) (b.η i)⟫_ℂ

omit hreal in
/-- **CC (84)**: `ε(e^t) = Σ λ(n)/√(1-λ(n)²) ⟨ξ_n | ϑ(e^{-t}) ζ_n⟩`. -/
def εS (t : ℝ) : ℂ := ∑' i, (b.τ i : ℂ) * ⟪b.ξ i, T.θ (-t) (b.ζ i)⟫_ℂ

omit hreal in
theorem abs_lam_le_abs_τ (i : ι) : |b.lam i| ≤ |b.τ i| := by
  have hs := b.s_pos i
  have hs1 : b.s i ≤ 1 := by
    unfold ArchS6.ProlateBasis.s
    rw [Real.sqrt_le_one]
    nlinarith [sq_nonneg (b.lam i)]
  rw [ArchS6.ProlateBasis.τ, abs_div, abs_of_pos hs, le_div_iff₀ hs]
  exact mul_le_of_le_one_right (abs_nonneg _) hs1

omit hreal in
theorem lam_sq_le_abs_τ (i : ι) : b.lam i ^ 2 ≤ |b.τ i| := by
  have h1 := b.abs_lam_lt_one i
  have h2 := abs_lam_le_abs_τ b i
  have : b.lam i ^ 2 ≤ |b.lam i| := by
    rw [← sq_abs]; nlinarith [abs_nonneg (b.lam i)]
  linarith

omit hreal in
theorem norm_ξ_ζ_coeff (t : ℝ) (i : ι) : ‖⟪b.ξ i, T.θ t (b.ζ i)⟫_ℂ‖ ≤ 1 := by
  have := T.norm_inner_le t (b.ξ i) (b.ζ i)
  rwa [b.norm_ξ, b.orthonormal_ζ.1 i, one_mul] at this

omit hreal in
theorem norm_cζ_le (i : ι) (t : ℝ) : ‖cζ b T i t‖ ≤ 1 := by
  have := T.norm_inner_le t (b.ζ i) (b.ζ i)
  rwa [b.orthonormal_ζ.1 i, one_mul] at this

variable (hτ : Summable fun i ↦ |b.τ i|)
include hτ

omit hreal in
theorem summable_lam_sq : Summable fun i ↦ b.lam i ^ 2 :=
  hτ.of_nonneg_of_le (fun _ ↦ sq_nonneg _) (lam_sq_le_abs_τ b)

omit hreal in
theorem summable_ε_terms (t : ℝ) :
    Summable fun i ↦ (b.τ i : ℂ) * ⟪b.ξ i, T.θ t (b.ζ i)⟫_ℂ := by
  refine Summable.of_norm_bounded hτ fun i ↦ ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (norm_ξ_ζ_coeff b T t i)

omit hreal in
theorem summable_cζ_terms (t : ℝ) :
    Summable fun i ↦ ((b.lam i ^ 2 : ℝ) : ℂ) * cζ b T i t := by
  refine Summable.of_norm_bounded (summable_lam_sq b hτ) fun i ↦ ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact mul_le_of_le_one_right (sq_nonneg _) (norm_cζ_le b T i t)

/-- **CC (89)**: `δ(ρ) = Σ λ(n)² ⟨ζ_n | ϑ(ρ⁻¹) ζ_n⟩ + ε(ρ)` for `ρ = e^t ≥ 1`. -/
theorem δS_eq {t : ℝ} (ht : 0 ≤ t) :
    δS b T t = ∑' i, ((b.lam i ^ 2 : ℝ) : ℂ) * cζ b T i (-t) + εS b T t := by
  rw [δS, εS, ← (summable_cζ_terms b T hτ (-t)).tsum_add (summable_ε_terms b T hτ (-t))]
  congr 1; funext i
  exact delta_term b T hreal ht i

/-- The even form of (89): `δ(e^{|x|}) = Σ λ² cζ_n(x) + ε(e^{|x|})` for every real `x`. -/
theorem δS_abs_eq (x : ℝ) :
    δS b T |x| = ∑' i, ((b.lam i ^ 2 : ℝ) : ℂ) * cζ b T i x + εS b T |x| := by
  rw [δS_eq b T hreal hτ (abs_nonneg x)]
  congr 2; funext i; congr 1
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h, cζ_neg b T hreal]
  · rw [abs_of_neg h, neg_neg]

omit hreal in
theorem continuous_εS : Continuous (εS b T) := by
  refine continuous_tsum (fun i ↦ ?_) hτ fun i t ↦ ?_
  · exact continuous_const.mul ((T.cont _ _).comp continuous_neg)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (norm_ξ_ζ_coeff b T _ i)

omit hreal in
theorem norm_εS_le (t : ℝ) : ‖εS b T t‖ ≤ ∑' i, |b.τ i| := by
  refine (norm_tsum_le_tsum_norm (summable_ε_terms b T hτ (-t)).norm).trans
    ((summable_ε_terms b T hτ (-t)).norm.tsum_le_tsum (fun i ↦ ?_) hτ)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (norm_ξ_ζ_coeff b T _ i)

/-! ### Integration against `f = g ∗ g*` -/

omit hreal in
theorem integrable_mul_εS {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable fun x ↦ f x * εS b T |x| :=
  hf.mul_bdd ((continuous_εS b T hτ).comp continuous_abs).aestronglyMeasurable
    (Eventually.of_forall fun x ↦ norm_εS_le b T hτ |x|)

omit hreal hτ in
theorem integrable_mul_cζ {f : ℝ → ℂ} (hf : Integrable f) (i : ι) :
    Integrable fun x ↦ f x * cζ b T i x :=
  hf.mul_bdd (T.cont _ _).aestronglyMeasurable (Eventually.of_forall fun x ↦ norm_cζ_le b T i x)

/-- **Integrated (89)**.  If `‖V† v‖² = ∫ f(x) ⟨v | ϑ(e^x) v⟩ dx` (CC: `⟨v|ϑ(f)v⟩` with
`ϑ(f) = V V†`), then `∫ f(x) δ(e^{|x|}) dx = Σ λ(n)² ‖V† ζ_n‖² + ∫ f(x) ε(e^{|x|}) dx`. -/
theorem integral_δS [Countable ι] {f : ℝ → ℂ} (hf : Integrable f) (V : H →L[ℂ] H)
    (hcoef : ∀ v, ((‖(ContinuousLinearMap.adjoint V) v‖ ^ 2 : ℝ) : ℂ) = ∫ x, f x * ⟪v, T.θ x v⟫_ℂ) :
    ∫ x, f x * δS b T |x|
      = ((∑' i, b.lam i ^ 2 * ‖(ContinuousLinearMap.adjoint V) (b.ζ i)‖ ^ 2 : ℝ) : ℂ)
        + ∫ x, f x * εS b T |x| := by
  have hF : ∀ i, Integrable fun x ↦ ((b.lam i ^ 2 : ℝ) : ℂ) * (f x * cζ b T i x) :=
    fun i ↦ (integrable_mul_cζ b T hf i).const_mul _
  have hFs : Summable fun i ↦ ∫ x, ‖((b.lam i ^ 2 : ℝ) : ℂ) * (f x * cζ b T i x)‖ := by
    refine (summable_lam_sq b hτ).mul_right (∫ x, ‖f x‖) |>.of_nonneg_of_le
      (fun i ↦ integral_nonneg fun x ↦ norm_nonneg _) fun i ↦ ?_
    rw [← integral_const_mul]
    refine integral_mono (hF i).norm (hf.norm.const_mul _) fun x ↦ ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (b.lam i))]
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_right (norm_nonneg _) (norm_cζ_le b T i x)) (sq_nonneg _)
  have hsplit : (fun x ↦ f x * δS b T |x|)
      = fun x ↦ (∑' i, ((b.lam i ^ 2 : ℝ) : ℂ) * (f x * cζ b T i x)) + f x * εS b T |x| := by
    funext x
    rw [δS_abs_eq b T hreal hτ, mul_add, ← (summable_cζ_terms b T hτ x).tsum_mul_left]
    congr 2; funext i; ring
  rw [hsplit, integral_add, ← integral_tsum_of_summable_integral_norm hF hFs]
  · congr 1
    rw [Complex.ofReal_tsum]
    congr 1; funext i
    rw [integral_const_mul, Complex.ofReal_mul]
    congr 1
    exact (hcoef (b.ζ i)).symm
  · have := (hasSum_integral_of_summable_integral_norm hF hFs)
    rw [show (fun x ↦ ∑' i, ((b.lam i ^ 2 : ℝ) : ℂ) * (f x * cζ b T i x))
        = fun x ↦ f x * ∑' i, ((b.lam i ^ 2 : ℝ) : ℂ) * cζ b T i x by
      funext x; rw [← (summable_cζ_terms b T hτ x).tsum_mul_left]; congr 1; funext i; ring]
    have hb : ∀ x, ‖∑' i, ((b.lam i ^ 2 : ℝ) : ℂ) * cζ b T i x‖ ≤ ∑' i, b.lam i ^ 2 := fun x ↦ by
      refine (norm_tsum_le_tsum_norm (summable_cζ_terms b T hτ x).norm).trans
        ((summable_cζ_terms b T hτ x).norm.tsum_le_tsum (fun i ↦ ?_) (summable_lam_sq b hτ))
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_of_le_one_right (sq_nonneg _) (norm_cζ_le b T i x)
    refine hf.mul_bdd ?_ (Eventually.of_forall hb)
    exact (continuous_tsum (f := fun i x ↦ ((b.lam i ^ 2 : ℝ) : ℂ) * cζ b T i x)
      (fun i ↦ continuous_const.mul (T.cont _ _))
      (summable_lam_sq b hτ) fun i x ↦ by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact mul_le_of_le_one_right (sq_nonneg _) (norm_cζ_le b T i x)).aestronglyMeasurable
  · exact integrable_mul_εS b T hτ hf

end ProlateBasis

/-! ### Theorem 4.7 -/

/-- From `Σ ofReal a = ofReal c` with `a ≥ 0`, `c ≥ 0`, get `HasSum a c`. -/
theorem hasSum_of_tsum_ofReal {κ : Type*} {a : κ → ℝ} {c : ℝ} (ha : ∀ k, 0 ≤ a k) (hc : 0 ≤ c)
    (h : ∑' k, ENNReal.ofReal (a k) = ENNReal.ofReal c) : HasSum a c := by
  have hfin : ∑' k, ENNReal.ofReal (a k) ≠ ∞ := by rw [h]; exact ENNReal.ofReal_ne_top
  have hs : Summable a := by
    have := ENNReal.summable_toReal hfin
    simpa [ENNReal.toReal_ofReal (ha _)] using this
  have e := ENNReal.ofReal_tsum_of_nonneg ha hs
  rw [h, ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg ha) hc] at e
  rw [← e]; exact hs.hasSum

namespace ProlateBasis

variable {S : ProjPair H} {ι : Type*} (b : ArchS6.ProlateBasis S ι) (T : Scaling S)

/-- **CC Theorem 4.7, Hilbert–Schmidt form (bypass B1).**

Let `V` be an operator (CC: `ϑ(g)`, so that `ϑ(f) = V V†` for `f = g ∗ g*`) and `f` an integrable
function with `‖V† v‖² = ∫ f(x) ⟨v | ϑ(e^x) v⟩ dx`.  Assume CC (85),
`Tr(ϑ(f) P P̂ P) = ‖P̂ P V‖²_HS = W + ∫ f(x) δ(e^{|x|}) dx`, with `δ` the series (75).  Then
`Tr(ϑ(f) S) = ‖S V‖²_HS = W + ∫ f(x) ε(e^{|x|}) dx`, with `ε` the series (84) and `S` the orthogonal
projection on Sonin's space.  Both Hilbert–Schmidt sums are taken in an arbitrary Hilbert basis. -/
theorem thm47 [Countable ι]
    (hreal : ∀ i t, ⟪b.ξ i, T.θ t (b.ξ i)⟫_ℂ = ⟪b.ξ i, T.θ (-t) (b.ξ i)⟫_ℂ)
    (hτ : Summable fun i ↦ |b.τ i|) {κ : Type*} (e : HilbertBasis κ ℂ H) (V : H →L[ℂ] H)
    {f : ℝ → ℂ} (hf : Integrable f)
    (hcoef : ∀ v, ((‖(ContinuousLinearMap.adjoint V) v‖ ^ 2 : ℝ) : ℂ) = ∫ x, f x * ⟪v, T.θ x v⟫_ℂ)
    (W : ℝ)
    (h85 : HasSum (fun k ↦ ‖S.hatP (S.P (V (e k)))‖ ^ 2) (W + (∫ x, f x * δS b T |x|).re)) :
    HasSum (fun k ↦ ‖ArchS6.ProlateBasis.soninProj (S := S) (V (e k))‖ ^ 2)
      (W + (∫ x, f x * εS b T |x|).re) := by
  set A : ℝ := ∑' i, b.lam i ^ 2 * ‖(ContinuousLinearMap.adjoint V) (b.ζ i)‖ ^ 2 with hAdef
  have hAs : Summable fun i ↦ b.lam i ^ 2 * ‖(ContinuousLinearMap.adjoint V) (b.ζ i)‖ ^ 2 := by
    refine ((summable_lam_sq b hτ).mul_right (‖ContinuousLinearMap.adjoint V‖ ^ 2)).of_nonneg_of_le
      (fun i ↦ by positivity) fun i ↦ ?_
    gcongr
    have := (ContinuousLinearMap.adjoint V).le_opNorm (b.ζ i)
    rwa [b.orthonormal_ζ.1 i, mul_one] at this
  have hA0 : 0 ≤ A := tsum_nonneg fun i ↦ by positivity
  have hδ := integral_δS b T hreal hτ hf V hcoef
  have hre : (∫ x, f x * δS b T |x|).re = A + (∫ x, f x * εS b T |x|).re := by
    rw [hδ, Complex.add_re, Complex.ofReal_re]
  set c : ℝ := W + (∫ x, f x * εS b T |x|).re with hcdef
  have hLHS : W + (∫ x, f x * δS b T |x|).re = c + A := by rw [hre]; ring
  rw [hLHS] at h85
  have hnn : 0 ≤ c + A := h85.nonneg fun k ↦ sq_nonneg _
  have h90 := tsum_PhatPP b e V
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ sq_nonneg _) h85.summable, h85.tsum_eq] at h90
  simp_rw [← ENNReal.ofReal_mul (sq_nonneg (b.lam _))] at h90
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i ↦ by positivity) hAs, ← hAdef] at h90
  set X := ∑' k, ENNReal.ofReal (‖ArchS6.ProlateBasis.soninProj (S := S) (V (e k))‖ ^ 2)
  have hX : X ≠ ∞ := by
    intro h; rw [h, top_add] at h90; exact ENNReal.ofReal_ne_top h90
  have hreal' := congrArg ENNReal.toReal h90
  rw [ENNReal.toReal_ofReal hnn, ENNReal.toReal_add hX ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hA0] at hreal'
  have hc : c = X.toReal := by linarith
  refine hasSum_of_tsum_ofReal (fun k ↦ sq_nonneg _) (hc ▸ ENNReal.toReal_nonneg) ?_
  rw [hc, ENNReal.ofReal_toReal hX]

/-- **CC (83)**: the functional `W∞ + E` is positive (`= ‖S V‖²_HS ≥ 0`). -/
theorem thm47_nonneg [Countable ι]
    (hreal : ∀ i t, ⟪b.ξ i, T.θ t (b.ξ i)⟫_ℂ = ⟪b.ξ i, T.θ (-t) (b.ξ i)⟫_ℂ)
    (hτ : Summable fun i ↦ |b.τ i|) {κ : Type*} (e : HilbertBasis κ ℂ H) (V : H →L[ℂ] H)
    {f : ℝ → ℂ} (hf : Integrable f)
    (hcoef : ∀ v, ((‖(ContinuousLinearMap.adjoint V) v‖ ^ 2 : ℝ) : ℂ) = ∫ x, f x * ⟪v, T.θ x v⟫_ℂ)
    (W : ℝ)
    (h85 : HasSum (fun k ↦ ‖S.hatP (S.P (V (e k)))‖ ^ 2) (W + (∫ x, f x * δS b T |x|).re)) :
    0 ≤ W + (∫ x, f x * εS b T |x|).re :=
  (thm47 b T hreal hτ e V hf hcoef W h85).nonneg fun _ ↦ sq_nonneg _

end ProlateBasis

end ArchS7
