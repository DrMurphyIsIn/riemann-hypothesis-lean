import ArchS6_Even
import ArchS6_Eigen
import ArchS6_Strict

/-!
# ArchS6_Prolate: the concrete prolate basis and the Sonin/prolate structure theorem

* `prolateBasisOf b`: from any orthonormal eigenbasis `b` of S9's operator `C` (kernel `2cos(2πxω)`
  on `[0,1]`), `ξ_i = J e_i` is a `ProlateBasis` for CC's pair `(P₁, F_{e_ℝ})` on `L²(ℝ)_ev`, with
  `λ_i = μ_i` (the eigenvalue of `C`).  Completeness uses `J_restrict`; `|λ| < 1` uses
  `abs_lt_one_of_eigen`.
* `exists_prolateBasis`: such a basis exists (spectral theorem, `exists_eigenBasis`).
* **`sonin_prolate_structure`** (S6 capstone, CC Prop 4.5 + (81)): there is an orthonormal basis
  `ξ_n` of `ran P₁ ⊂ L²(ℝ)_ev` with `P₁ F ξ_n = λ_n ξ_n`, `0 < |λ_n| < 1`, `P₁ = Σ |ξ_n⟩⟨ξ_n|`,
  `P P̂ P = Σ λ_n² |ζ_n⟩⟨ζ_n| + S`, and Sonin's space `S(1,1)` is the eigenspace of `P P̂ P` for 1.
* `sincOp_restrict_ξ`: `R ξ_n` is an eigenvector of the sinc operator with eigenvalue `λ_n²` (CC (70)).
* `phi`, `ae_eq_phi`, `fourier_ξ_ae`, `continuous_phi`: the analytic continuation
  `ξ_n^an = λ_n⁻¹ C e_n` used by S8 (`= e_n` on `[0,1]`, `F ξ_n = λ_n ξ_n^an / √2` on `ℝ`).

conjecture1_proved = False.
-/

open MeasureTheory Set Filter FourierTransform Complex
open scoped ENNReal InnerProductSpace Real

noncomputable section

namespace ArchS6

open ArchS5

set_option linter.unusedSectionVars false

/-- `J h` as an element of `L²(ℝ)_ev`. -/
def evenOf (h : L2I 0 1) : evenL2 := ⟨J h, J_mem_evenL2 h⟩

theorem coe_evenOf (h : L2I 0 1) : (evenOf h : L2R) = J h := rfl

theorem P1_fourier_J_eigen {e : L2I 0 1} {c : ℝ} (he : Cop e = (c : ℂ) • e) :
    P1 (𝓕 (J e : L2R)) = (c : ℂ) • J e := by
  rw [P1_fourier_J, he, LinearIsometry.map_smul]

/-- **The concrete prolate basis** built from an eigenbasis of S9's operator `C`. -/
def prolateBasisOf {ι : Type*} (b : EigenBasis Cop ι) : ProlateBasis evenPair ι where
  ξ i := evenOf (b.e i)
  lam := b.μ
  orthonormal := by
    refine ⟨fun i ↦ ?_, fun i j hij ↦ ?_⟩
    · show ‖evenOf (b.e i)‖ = 1
      rw [Submodule.coe_norm, coe_evenOf, LinearIsometry.norm_map, b.orthonormal.1 i]
    · show ⟪evenOf (b.e i), evenOf (b.e j)⟫_ℂ = 0
      rw [Submodule.coe_inner, coe_evenOf, coe_evenOf, inner_J]
      exact b.orthonormal.2 hij
  P₁_ξ i := Subtype.ext (P1_J _)
  eigen i := Subtype.ext (by
    show P1 (𝓕 (J (b.e i) : L2R)) = _
    rw [P1_fourier_J_eigen (b.eigen i)]; rfl)
  complete x hx hperp := by
    have hx' : P1 (x : L2R) = x := congrArg Subtype.val hx
    set y : L2I 0 1 := ((Real.sqrt 2 : ℝ) : ℂ) • restrictIcc 0 1 (x : L2R)
    have hJ : J y = x := J_restrict x.2 hx'
    have hy : y = 0 := b.complete y fun i ↦ by
      have := hperp i
      rw [Submodule.coe_inner, coe_evenOf, ← hJ, inner_J] at this
      exact this
    apply Subtype.ext
    rw [← hJ, hy, map_zero]; rfl
  abs_lam_lt_one i := by
    refine abs_lt_one_of_eigen ?_ (P1_J _) (P1_fourier_J_eigen (b.eigen i))
    rw [LinearIsometry.norm_map, b.orthonormal.1 i]

theorem prolateBasisOf_ξ {ι : Type*} (b : EigenBasis Cop ι) (i : ι) :
    ((prolateBasisOf b).ξ i : L2R) = J (b.e i) := rfl

theorem prolateBasisOf_lam {ι : Type*} (b : EigenBasis Cop ι) (i : ι) :
    (prolateBasisOf b).lam i = b.μ i := rfl

/-- The eigenvalues are nonzero. -/
theorem prolateBasisOf_lam_ne_zero {ι : Type*} (b : EigenBasis Cop ι) (i : ι) : b.μ i ≠ 0 := by
  refine ne_zero_of_eigen ?_ (P1_J _) (P1_fourier_J_eigen (b.eigen i))
  rw [LinearIsometry.norm_map, b.orthonormal.1 i]

/-- An eigenbasis of `C` exists. -/
theorem exists_eigenBasis_Cop : ∃ (ι : Type) (_ : EigenBasis Cop ι), True :=
  exists_eigenBasis Cop_compact_selfAdjoint.1
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 Cop_compact_selfAdjoint.2)

/-- A prolate basis for CC's pair exists. -/
theorem exists_prolateBasis : ∃ (ι : Type) (_ : ProlateBasis evenPair ι), True := by
  obtain ⟨ι, b, -⟩ := exists_eigenBasis_Cop
  exact ⟨ι, prolateBasisOf b, trivial⟩

/-- **The Sonin/prolate structure theorem (CC Prop 4.5 and (81)) on `L²(ℝ)_ev`.**
There is an orthonormal family `ξ_n` in `ran P₁`, complete there, with `P₁ F ξ_n = λ_n ξ_n`,
`0 < |λ_n| < 1`, such that `P₁ = Σ |ξ_n⟩⟨ξ_n|`, `P P̂ P = Σ λ_n² |ζ_n⟩⟨ζ_n| + S`, and `S(1,1)` is the
eigenspace of `P P̂ P` for the eigenvalue `1`.  Each `ξ_n` is `J e_n` for a unit eigenvector `e_n` of
S9's operator `C` with eigenvalue `λ_n`. -/
theorem sonin_prolate_structure :
    ∃ (ι : Type) (b : ProlateBasis evenPair ι),
      (∀ i, b.lam i ≠ 0 ∧ |b.lam i| < 1) ∧
      (∀ i, ∃ e : L2I 0 1, ‖e‖ = 1 ∧ Cop e = (b.lam i : ℂ) • e ∧ (b.ξ i : L2R) = J e) ∧
      (∀ x, HasSum (fun i ↦ ⟪b.ξ i, x⟫_ℂ • b.ξ i) (evenPair.P₁ x)) ∧
      (∀ x, HasSum (fun i ↦ (((b.lam i ^ 2 : ℝ) : ℂ) * ⟪b.ζ i, x⟫_ℂ) • b.ζ i)
        (evenPair.PhatPP x - ProlateBasis.soninProj (S := evenPair) x)) ∧
      (∀ x, x ∈ evenPair.sonin ↔ evenPair.PhatPP x = x) := by
  obtain ⟨ι, b, -⟩ := exists_eigenBasis_Cop
  refine ⟨ι, prolateBasisOf b, fun i ↦ ⟨prolateBasisOf_lam_ne_zero b i,
    (prolateBasisOf b).abs_lam_lt_one i⟩, fun i ↦ ⟨b.e i, b.orthonormal.1 i, b.eigen i, rfl⟩,
    (prolateBasisOf b).hasSum_P₁, (prolateBasisOf b).hasSum_PhatPP,
    fun x ↦ evenPair.mem_sonin_iff_fixed⟩

/-! ### The sinc operator -/

/-- CC (70) for the sinc operator: `R ξ_n` is an eigenvector of `T_sinc` with eigenvalue `λ_n²`. -/
theorem sincOp_restrict_ξ {ι : Type*} (b : EigenBasis Cop ι) (i : ι) :
    sincOp (restrictIcc (-1) 1 (J (b.e i))) =
      ((b.μ i ^ 2 : ℝ) : ℂ) • restrictIcc (-1) 1 (J (b.e i)) := by
  have h := (prolateBasisOf b).P₁hatP₁P₁_ξ i
  have h' := congrArg Subtype.val h
  simp only [Submodule.coe_smul] at h'
  -- `P₁ P̂₁ P₁` on `L²(ℝ)_ev` is the restriction of `P1 ∘ hatP1 ∘ P1`
  have e1 : ((evenPair.P₁ (evenPair.hatP₁ (evenPair.P₁ ((prolateBasisOf b).ξ i)))) : L2R) =
      P1 (hatP1 (P1 (J (b.e i)))) := by
    rw [evenPair_P₁, evenPair_hatP₁, evenPair_P₁]; rfl
  rw [e1, prolateBasisOf_ξ, prolateBasisOf_lam] at h'
  have h2 := congrArg (restrictIcc (-1) 1) h'
  rw [map_smul] at h2
  have e2 : P1 (hatP1 (P1 (J (b.e i)))) =
      extendIcc (-1) 1 (sincOp (restrictIcc (-1) 1 (J (b.e i)))) := by
    have := congrArg (fun T ↦ T (J (b.e i))) P1_hatP1_P1_eq
    simpa using this
  rw [e2, restrictIcc_extendIcc] at h2
  exact h2

/-! ### The analytic continuation used by S8 -/

/-- `ξ_n^an = λ_n⁻¹ (C e_n)` as a function on `ℝ` (S8's `phi n`, complex-valued here). -/
def phi {ι : Type*} (b : EigenBasis Cop ι) (i : ι) (w : ℝ) : ℂ :=
  ((b.μ i)⁻¹ : ℂ) * cosTrans (b.e i) w

/-- `ξ_n^an = e_n` on `[0, 1]` (S9's normalised eigenfunction, `∫₀¹ |e_n|² = 1`). -/
theorem ae_eq_phi {ι : Type*} (b : EigenBasis Cop ι) (i : ι) :
    (b.e i : ℝ → ℂ) =ᵐ[volI 0 1] phi b i := by
  have hne : (b.μ i : ℂ) ≠ 0 := by exact_mod_cast prolateBasisOf_lam_ne_zero b i
  have h1 := coeFn_Cop (b.e i)
  rw [show Cop (b.e i) = ((b.μ i : ℂ)) • b.e i from b.eigen i] at h1
  filter_upwards [h1, Lp.coeFn_smul ((b.μ i : ℂ)) (b.e i)] with w e1 e2
  rw [e2, Pi.smul_apply, smul_eq_mul] at e1
  rw [phi, ← e1, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- `F_{e_ℝ} ξ_n = λ_n ξ_n^an / √2` on `ℝ` (with Mathlib's `L²(ℝ)` normalisation). -/
theorem fourier_ξ_ae {ι : Type*} (b : EigenBasis Cop ι) (i : ι) :
    ((𝓕 (J (b.e i) : L2R) : L2R) : ℝ → ℂ) =ᵐ[volume] fun w ↦ c2 * (b.μ i : ℂ) * phi b i w := by
  have hne : (b.μ i : ℂ) ≠ 0 := by exact_mod_cast prolateBasisOf_lam_ne_zero b i
  filter_upwards [fourier_J_ae (b.e i)] with w hw
  rw [hw, phi, mul_assoc, ← mul_assoc (b.μ i : ℂ), mul_inv_cancel₀ hne, one_mul]

theorem continuous_cosTrans (h : L2I 0 1) : Continuous (cosTrans h) := by
  have hG : Continuous fun w : ℝ ↦ 𝓕 (Eplus h : ℝ → ℂ) w :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner
      (integrable_extendIcc 0 1 h)
  have heq : cosTrans h = fun w ↦ 𝓕 (Eplus h : ℝ → ℂ) w + 𝓕 (Eplus h : ℝ → ℂ) (-w) := by
    funext w
    rw [fourier_extendIcc_eq, fourier_extendIcc_eq,
      ← integral_add (integrable_fourierK_mul 0 1 w h) (integrable_fourierK_mul 0 1 (-w) h)]
    unfold cosTrans
    congr 1; funext v
    rw [← add_mul, fourierK_add_neg]
  rw [heq]
  exact hG.add (hG.comp continuous_neg)

theorem continuous_phi {ι : Type*} (b : EigenBasis Cop ι) (i : ι) : Continuous (phi b i) :=
  continuous_const.mul (continuous_cosTrans _)

end ArchS6
