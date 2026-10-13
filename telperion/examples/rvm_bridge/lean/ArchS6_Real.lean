import ArchS6_Prolate

/-!
# ArchS6_Real: a real-valued prolate basis

CC use that the `ξ_n` are real-valued (Prop 4.5 (iv), (82)); S8's `ProlateData.phi` is real-valued.
This file produces a prolate basis whose `ξ_n = J e_n` come from **real** eigenfunctions `e_n` of the
real operator `C_ℝ` (kernel `2cos(2πxω)` on `L²([0,1]; ℝ)`, S9's `T` exactly), via complexification.

* `ofRealL`, `reL`, `imL`: `L²(ℝ-valued) ⇄ L²(ℂ-valued)`; `decomp`: `x = re x + i·im x`;
  `inner_ofRealL`: `⟪ι f, ι g⟫_ℂ = ⟪f, g⟫_ℝ`.
* `CopR`, `Cop_ofRealL`: `C (ι e) = ι (C_ℝ e)`.
* `complexify`: a real eigenbasis of `C_ℝ` is a (complex) eigenbasis of `C`.
* `realProlateBasis bR = prolateBasisOf (complexify bR)`, `exists_eigenBasis_CopR`.
* `phiR`: the real analytic continuation `ξ_n^an = λ_n⁻¹ ∫₀¹ 2cos(2πωv) e_n(v) dv`,
  `phi_complexify` (`phi = ↑phiR`), `ae_eq_phiR` (`= e_n` on `[0,1]`), `continuous_phiR`.

conjecture1_proved = False.
-/

open MeasureTheory Set Filter Complex
open scoped InnerProductSpace Real ComplexConjugate

noncomputable section

namespace ArchS6

open ArchS5

set_option linter.unusedSectionVars false

/-- Real `L²([a, b])`. -/
abbrev L2IR (a b : ℝ) : Type := Lp ℝ 2 (volI a b)

variable (a b : ℝ)

/-- Complexification `L²([a,b]; ℝ) → L²([a,b]; ℂ)`. -/
def ofRealL : L2IR a b →L[ℝ] L2I a b := Complex.ofRealCLM.compLpL 2 (volI a b)
/-- Real part. -/
def reL : L2I a b →L[ℝ] L2IR a b := Complex.reCLM.compLpL 2 (volI a b)
/-- Imaginary part. -/
def imL : L2I a b →L[ℝ] L2IR a b := Complex.imCLM.compLpL 2 (volI a b)

variable {a b}

theorem coeFn_ofRealL (f : L2IR a b) :
    (ofRealL a b f : ℝ → ℂ) =ᵐ[volI a b] fun x ↦ ((f x : ℝ) : ℂ) :=
  Complex.ofRealCLM.coeFn_compLp' f

theorem coeFn_reL (x : L2I a b) : (reL a b x : ℝ → ℝ) =ᵐ[volI a b] fun t ↦ (x t).re :=
  Complex.reCLM.coeFn_compLp' x

theorem coeFn_imL (x : L2I a b) : (imL a b x : ℝ → ℝ) =ᵐ[volI a b] fun t ↦ (x t).im :=
  Complex.imCLM.coeFn_compLp' x

theorem decomp (x : L2I a b) :
    x = ofRealL a b (reL a b x) + Complex.I • ofRealL a b (imL a b x) := by
  apply Lp.ext
  filter_upwards [coeFn_ofRealL (reL a b x), coeFn_ofRealL (imL a b x), coeFn_reL x, coeFn_imL x,
    Lp.coeFn_add (ofRealL a b (reL a b x)) (Complex.I • ofRealL a b (imL a b x)),
    Lp.coeFn_smul Complex.I (ofRealL a b (imL a b x))] with t e1 e2 e3 e4 e5 e6
  rw [e5, Pi.add_apply, e6, Pi.smul_apply, e1, e2, e3, e4, smul_eq_mul, mul_comm]
  exact (Complex.re_add_im _).symm

theorem inner_ofRealL (f g : L2IR a b) :
    ⟪ofRealL a b f, ofRealL a b g⟫_ℂ = ((⟪f, g⟫_ℝ : ℝ) : ℂ) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def, ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_ofRealL f, coeFn_ofRealL g] with t e1 e2
  rw [e1, e2]
  simp [mul_comm]

theorem inner_ofRealL_left (f : L2IR a b) (x : L2I a b) :
    ⟪ofRealL a b f, x⟫_ℂ =
      ((⟪f, reL a b x⟫_ℝ : ℝ) : ℂ) + Complex.I * ((⟪f, imL a b x⟫_ℝ : ℝ) : ℂ) := by
  conv_lhs => rw [decomp x]
  rw [inner_add_right, inner_smul_right, inner_ofRealL, inner_ofRealL]

theorem norm_ofRealL (f : L2IR a b) : ‖ofRealL a b f‖ = ‖f‖ := by
  have h := congrArg RCLike.re (inner_ofRealL f f)
  rw [inner_self_eq_norm_sq, RCLike.re_to_complex, Complex.ofReal_re,
    real_inner_self_eq_norm_sq] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-! ### The real operator -/

/-- S9's kernel, real-valued. -/
def cosKR (p : ℝ × ℝ) : ℝ := 2 * Real.cos (2 * π * p.1 * p.2)

theorem continuous_cosKR : Continuous cosKR := by unfold cosKR; fun_prop

theorem cosKR_symm (x y : ℝ) : cosKR (y, x) = (starRingEnd ℝ) (cosKR (x, y)) := by
  rw [conj_trivial, cosKR, cosKR]; congr 2; ring

/-- `C_ℝ`: S9's operator on real `L²([0, 1])`. -/
def CopR : L2IR 0 1 →L[ℝ] L2IR 0 1 := intOp (kernelOfContinuous 0 1 cosKR continuous_cosKR)

theorem CopR_compact_selfAdjoint : IsCompactOperator CopR ∧ IsSelfAdjoint CopR :=
  intOp_kernelOfContinuous_compact_selfAdjoint continuous_cosKR cosKR_symm

/-- `(C_ℝ e)(ω) = ∫₀¹ 2cos(2πωv) e(v) dv` (S9's `T e`). -/
def cosTransR (e : L2IR 0 1) (w : ℝ) : ℝ := ∫ v in Icc (0 : ℝ) 1, cosKR (w, v) * e v

theorem cosTrans_ofRealL (e : L2IR 0 1) (w : ℝ) :
    cosTrans (ofRealL 0 1 e) w = ((cosTransR e w : ℝ) : ℂ) := by
  rw [cosTrans, cosTransR, ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_ofRealL e] with v hv
  rw [hv, cosK, cosKR]; push_cast; ring

theorem Cop_ofRealL (e : L2IR 0 1) : Cop (ofRealL 0 1 e) = ofRealL 0 1 (CopR e) := by
  apply Lp.ext
  filter_upwards [coeFn_Cop (ofRealL 0 1 e), coeFn_ofRealL (CopR e),
    (intOp_kernelOfContinuous_ae_eq continuous_cosKR e :
      (CopR e : ℝ → ℝ) =ᵐ[volI 0 1] _)] with x e1 e2 e3
  rw [e1, e2, cosTrans_ofRealL]
  congr 1
  exact e3.symm

/-- **Complexification of a real eigenbasis.** -/
def complexify {ι : Type*} (bR : EigenBasis CopR ι) : EigenBasis Cop ι where
  e i := ofRealL 0 1 (bR.e i)
  μ := bR.μ
  orthonormal := by
    refine ⟨fun i ↦ ?_, fun i j hij ↦ ?_⟩
    · show ‖ofRealL 0 1 (bR.e i)‖ = 1
      rw [norm_ofRealL, bR.orthonormal.1 i]
    · show ⟪ofRealL 0 1 (bR.e i), ofRealL 0 1 (bR.e j)⟫_ℂ = 0
      rw [inner_ofRealL, bR.orthonormal.2 hij, Complex.ofReal_zero]
  eigen i := by
    show Cop (ofRealL 0 1 (bR.e i)) = _
    rw [Cop_ofRealL, show CopR (bR.e i) = bR.μ i • bR.e i from bR.eigen i, map_smul]
    exact (Complex.coe_smul _ _).symm
  complete x hx := by
    have hre : reL 0 1 x = 0 := bR.complete _ fun i ↦ by
      have := hx i
      rw [inner_ofRealL_left] at this
      have h := congrArg Complex.re this
      simpa using h
    have him : imL 0 1 x = 0 := bR.complete _ fun i ↦ by
      have := hx i
      rw [inner_ofRealL_left] at this
      have h := congrArg Complex.im this
      simpa using h
    rw [decomp x, hre, him, map_zero, smul_zero, add_zero]

theorem complexify_e {ι : Type*} (bR : EigenBasis CopR ι) (i : ι) :
    (complexify bR).e i = ofRealL 0 1 (bR.e i) := rfl

theorem complexify_μ {ι : Type*} (bR : EigenBasis CopR ι) (i : ι) :
    (complexify bR).μ i = bR.μ i := rfl

/-- A real eigenbasis of `C_ℝ` exists. -/
theorem exists_eigenBasis_CopR : ∃ (ι : Type) (_ : EigenBasis CopR ι), True :=
  exists_eigenBasis CopR_compact_selfAdjoint.1
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 CopR_compact_selfAdjoint.2)

/-- The prolate basis `ξ_n = J e_n` with `e_n` real eigenfunctions of `C_ℝ`. -/
def realProlateBasis {ι : Type*} (bR : EigenBasis CopR ι) : ProlateBasis evenPair ι :=
  prolateBasisOf (complexify bR)

theorem realProlateBasis_ξ {ι : Type*} (bR : EigenBasis CopR ι) (i : ι) :
    ((realProlateBasis bR).ξ i : L2R) = J (ofRealL 0 1 (bR.e i)) := rfl

theorem realProlateBasis_lam {ι : Type*} (bR : EigenBasis CopR ι) (i : ι) :
    (realProlateBasis bR).lam i = bR.μ i := rfl

/-- **The Sonin/prolate structure theorem with real prolates.** -/
theorem sonin_prolate_structure_real :
    ∃ (ι : Type) (bR : EigenBasis CopR ι),
      (∀ i, bR.μ i ≠ 0 ∧ |bR.μ i| < 1) ∧
      (∀ x, HasSum (fun i ↦ ⟪(realProlateBasis bR).ξ i, x⟫_ℂ • (realProlateBasis bR).ξ i)
        (evenPair.P₁ x)) ∧
      (∀ x, HasSum (fun i ↦ (((bR.μ i ^ 2 : ℝ) : ℂ) * ⟪(realProlateBasis bR).ζ i, x⟫_ℂ) •
          (realProlateBasis bR).ζ i)
        (evenPair.PhatPP x - ProlateBasis.soninProj (S := evenPair) x)) := by
  obtain ⟨ι, bR, -⟩ := exists_eigenBasis_CopR
  exact ⟨ι, bR, fun i ↦ ⟨prolateBasisOf_lam_ne_zero (complexify bR) i,
    (realProlateBasis bR).abs_lam_lt_one i⟩, (realProlateBasis bR).hasSum_P₁,
    (realProlateBasis bR).hasSum_PhatPP⟩

/-! ### The real analytic continuation (S8's `phi`) -/

/-- `ξ_n^an(ω) = λ_n⁻¹ ∫₀¹ 2cos(2πωv) e_n(v) dv`, real-valued. -/
def phiR {ι : Type*} (bR : EigenBasis CopR ι) (i : ι) (w : ℝ) : ℝ :=
  (bR.μ i)⁻¹ * cosTransR (bR.e i) w

theorem phi_complexify {ι : Type*} (bR : EigenBasis CopR ι) (i : ι) (w : ℝ) :
    phi (complexify bR) i w = ((phiR bR i w : ℝ) : ℂ) := by
  rw [phi, complexify_e, complexify_μ, cosTrans_ofRealL, phiR]; push_cast; ring

theorem continuous_phiR {ι : Type*} (bR : EigenBasis CopR ι) (i : ι) : Continuous (phiR bR i) := by
  have h := Complex.continuous_re.comp (continuous_phi (complexify bR) i)
  have : phiR bR i = Complex.re ∘ phi (complexify bR) i := by
    funext w; simp [phi_complexify]
  rw [this]; exact h

/-- `ξ_n^an = e_n` on `[0, 1]`. -/
theorem ae_eq_phiR {ι : Type*} (bR : EigenBasis CopR ι) (i : ι) :
    (bR.e i : ℝ → ℝ) =ᵐ[volI 0 1] phiR bR i := by
  filter_upwards [ae_eq_phi (complexify bR) i, coeFn_ofRealL (bR.e i)] with w e1 e2
  rw [complexify_e, e2, phi_complexify] at e1
  exact_mod_cast e1

/-- `F_{e_ℝ} ξ_n = λ_n ξ_n^an / √2` on `ℝ` (Mathlib normalisation of `L²(ℝ)`). -/
theorem fourier_ξ_ae_real {ι : Type*} (bR : EigenBasis CopR ι) (i : ι) :
    ((FourierTransform.fourier (J (ofRealL 0 1 (bR.e i)) : L2R) : L2R) : ℝ → ℂ) =ᵐ[volume]
      fun w ↦ c2 * (bR.μ i : ℂ) * (phiR bR i w : ℂ) := by
  filter_upwards [fourier_ξ_ae (complexify bR) i] with w hw
  rw [← complexify_e, hw, phi_complexify, complexify_μ]

end ArchS6
