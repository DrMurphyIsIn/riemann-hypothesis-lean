import ArchS7_Theta
import ArchS5_HS

/-!
# ArchS7_Lemma41: CC Lemma 4.1 / (75) without trace class (interface O2)

CC Lemma 4.1 and (75): for `ρ = e^t ≥ 1`,
`δ(ρ) = Tr(ϑ(ρ⁻¹) P̂₁ P₁) = Σ_n λ(n) ⟨ξ_n | ϑ(ρ⁻¹) η_n⟩`, with `δ` CC's (48)/(49).

Bypass B1: the n-th term is the pairing `⟨C ξ_n, C_t ξ_n⟩` of two continuous-kernel operators on
`L²([0,1])`, `C` with kernel `2cos(2πxy)` (S9's operator) and `C_t` with kernel `e^{t/2} 2cos(2πe^t xy)`.
Summed over the (complete) prolate basis this is the Hilbert–Schmidt pairing of the kernels
(`hasSum_inner_intOp`, polarisation of S5's Hilbert–Schmidt identity), i.e. the explicit double integral
`∫∫_{[0,1]²} 4 e^{t/2} cos(2πxy) cos(2πe^t xy)`, which is S3's `deltaK t` by
`∫∫_{[0,1]²} cos(cxy) = ∫₀¹ sinc(cx) dx` (`integral_square_cos`).

* `hasSum_inner_intOp`: `Σ_i ⟨T_{K₁} b_i, T_{K₂} b_i⟩ = ⟨K₁, K₂⟩` for a Hilbert basis `b`.
* `term_eq`: `λ_n ⟨ξ_n | ϑ(e^{-t}) η_n⟩ = ⟨C e_n, C_t e_n⟩`.
* `inner_K0_Kt`: `⟨K, K_t⟩ = deltaK t` for `t ≥ 0`.
* **`hasSum_δS`, `δS_eq_deltaK`** (CC (75) = (48)): `δS t = deltaK t` for `t ≥ 0`.
* `thm47_weil'`: Thm 4.7 with `h85` stated with S3's `Dfun`, i.e. **h85 is now exactly S3's M2 (O1)**.

conjecture1_proved = False.
-/

open MeasureTheory Set Filter Topology FourierTransform
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace ArchS7

open ArchS6 ArchS5 ArchS8

set_option linter.unusedSectionVars false

/-! ### Elementary integrals -/

theorem integral_cos_mul (a : ℝ) : ∫ y in (0 : ℝ)..1, Real.cos (a * y) = Real.sinc a := by
  by_cases ha : a = 0
  · subst ha; simp [Real.sinc_zero]
  · rw [intervalIntegral.integral_comp_mul_left (fun y ↦ Real.cos y) ha, integral_cos,
      Real.sinc_of_ne_zero ha]
    simp [div_eq_inv_mul]

/-- `∫₀¹∫₀¹ cos(c x y) dy dx = ∫₀¹ sinc(c x) dx` (S3's `sincInt`). -/
theorem integral_square_cos (c : ℝ) :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, Real.cos (c * x * y) = ArchS3.sincInt c := by
  unfold ArchS3.sincInt
  congr 1; funext x
  exact integral_cos_mul (c * x)

/-! ### Polarised Hilbert–Schmidt identity -/

theorem hasSum_inner_intOp {ι : Type*} [Countable ι]
    (K₁ K₂ : Lp ℂ 2 ((volI 0 1).prod (volI 0 1))) (b : HilbertBasis ι ℂ (L2I 0 1)) :
    HasSum (fun i ↦ ⟪intOp K₁ (b i), intOp K₂ (b i)⟫_ℂ) ⟪K₁, K₂⟫_ℂ := by
  have hadd : ∀ c : ℂ, HasSum (fun i ↦ ‖intOp K₁ (b i) + c • intOp K₂ (b i)‖ ^ 2)
      (‖K₁ + c • K₂‖ ^ 2) := fun c ↦ by
    have h := hasSum_norm_intOp_sq (K₁ + c • K₂) b
    simpa only [intOp_add, intOp_smul, _root_.add_apply,
      _root_.smul_apply] using h
  have hsub : ∀ c : ℂ, HasSum (fun i ↦ ‖intOp K₁ (b i) - c • intOp K₂ (b i)‖ ^ 2)
      (‖K₁ - c • K₂‖ ^ 2) := fun c ↦ by
    have h := hasSum_norm_intOp_sq (K₁ - c • K₂) b
    simpa only [intOp_sub, intOp_smul, _root_.sub_apply,
      _root_.smul_apply] using h
  rw [Complex.hasSum_iff]
  constructor
  · have h := ((hadd 1).sub (hsub 1)).div_const 4
    simp only [one_smul] at h
    have e1 : (fun i ↦ (⟪intOp K₁ (b i), intOp K₂ (b i)⟫_ℂ).re) = fun i ↦
        (‖intOp K₁ (b i) + intOp K₂ (b i)‖ ^ 2 - ‖intOp K₁ (b i) - intOp K₂ (b i)‖ ^ 2) / 4 := by
      funext i
      have := re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (𝕜 := ℂ)
        (intOp K₁ (b i)) (intOp K₂ (b i))
      rw [RCLike.re_to_complex] at this
      rw [this]; ring
    have e2 : (⟪K₁, K₂⟫_ℂ).re = (‖K₁ + K₂‖ ^ 2 - ‖K₁ - K₂‖ ^ 2) / 4 := by
      have := re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (𝕜 := ℂ) K₁ K₂
      rw [RCLike.re_to_complex] at this
      rw [this]; ring
    rw [e1, e2]; exact h
  · have h := ((hsub (RCLike.I : ℂ)).sub (hadd (RCLike.I : ℂ))).div_const 4
    have e1 : (fun i ↦ (⟪intOp K₁ (b i), intOp K₂ (b i)⟫_ℂ).im) = fun i ↦
        (‖intOp K₁ (b i) - (RCLike.I : ℂ) • intOp K₂ (b i)‖ ^ 2
          - ‖intOp K₁ (b i) + (RCLike.I : ℂ) • intOp K₂ (b i)‖ ^ 2) / 4 := by
      funext i
      have := im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four (𝕜 := ℂ)
        (intOp K₁ (b i)) (intOp K₂ (b i))
      rw [RCLike.im_to_complex] at this
      rw [this]; ring
    have e2 : (⟪K₁, K₂⟫_ℂ).im = (‖K₁ - (RCLike.I : ℂ) • K₂‖ ^ 2
        - ‖K₁ + (RCLike.I : ℂ) • K₂‖ ^ 2) / 4 := by
      have := im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four (𝕜 := ℂ)
        K₁ K₂
      rw [RCLike.im_to_complex] at this
      rw [this]; ring
    rw [e1, e2]; exact h

/-! ### The kernels -/

/-- `C_t`'s kernel: `e^{t/2} · 2cos(2π e^t x y)`. -/
def ktK (t : ℝ) (p : ℝ × ℝ) : ℂ := (Real.exp (t / 2) : ℂ) * cosK (Real.exp t * p.1, p.2)

theorem continuous_ktK (t : ℝ) : Continuous (ktK t) := by
  unfold ktK cosK; fun_prop

/-- S9's kernel on `[0,1]²` (so `intOp K0 = Cop`). -/
abbrev K0 : Lp ℂ 2 ((volI 0 1).prod (volI 0 1)) := kernelOfContinuous 0 1 cosK continuous_cosK

/-- `C_t`'s kernel as an `L²([0,1]²)` element. -/
abbrev Kt (t : ℝ) : Lp ℂ 2 ((volI 0 1).prod (volI 0 1)) :=
  kernelOfContinuous 0 1 (ktK t) (continuous_ktK t)

theorem coeFn_intOp_Kt (t : ℝ) (e : L2I 0 1) :
    (intOp (Kt t) e : ℝ → ℂ) =ᵐ[volI 0 1]
      fun w ↦ (Real.exp (t / 2) : ℂ) * cosTrans e (Real.exp t * w) := by
  filter_upwards [intOp_kernelOfContinuous_ae_eq (continuous_ktK t) e] with w hw
  rw [hw, cosTrans, ← integral_const_mul]
  congr 1; funext y
  rw [ktK]; ring

/-! ### The termwise identity -/

/-- The Hilbert basis of `L²([0,1])` given by a complete real eigenbasis of `C_ℝ`. -/
def hbOf {ι : Type*} (bR : EigenBasis CopR ι) : HilbertBasis ι ℂ (L2I 0 1) :=
  HilbertBasis.mkOfOrthogonalEqBot (complexify bR).orthonormal (by
    rw [Submodule.eq_bot_iff]
    intro x hx
    refine (complexify bR).complete x fun i ↦ ?_
    exact (Submodule.mem_orthogonal _ _).1 hx _ (Submodule.subset_span ⟨i, rfl⟩))

theorem hbOf_apply {ι : Type*} (bR : EigenBasis CopR ι) (i : ι) :
    hbOf bR i = (complexify bR).e i := by
  rw [hbOf, HilbertBasis.coe_mkOfOrthogonalEqBot]

theorem inner_reflect_left (a X : L2R) : ⟪reflect a, X⟫_ℂ = ⟪a, reflect X⟫_ℂ := by
  conv_lhs => rw [← reflect_reflect X]
  exact LinearIsometry.inner_map_map reflect a (reflect X)

/-- `⟨J e, X⟩ = √2 ⟨e, X|_{[0,1]}⟩` for even `X`. -/
theorem inner_J_even (e : L2I 0 1) {X : L2R} (hX : X ∈ evenL2) :
    ⟪J e, X⟫_ℂ = 2 * c2 * ⟪e, restrictIcc 0 1 X⟫_ℂ := by
  rw [J_apply, inner_smul_left, inner_add_left, inner_reflect_left, mem_evenL2.1 hX,
    inner_extendIcc_left, conj_c2]
  ring

/-- **The n-th term of (75) is `⟨C e_n, C_t e_n⟩`.** -/
theorem term_eq {ι : Type*} (bR : EigenBasis CopR ι) (i : ι) (t : ℝ) :
    ((realProlateBasis bR).lam i : ℂ)
        * ⟪(realProlateBasis bR).ξ i, scalingEven.θ (-t) ((realProlateBasis bR).η i)⟫_ℂ
      = ⟪Cop ((complexify bR).e i), intOp (Kt t) ((complexify bR).e i)⟫_ℂ := by
  set e := (complexify bR).e i
  set lam := bR.μ i
  have hlam : (realProlateBasis bR).lam i = lam := rfl
  set X : L2R := thL (-t) (𝓕 (J e : L2R) : L2R)
  have hXev : X ∈ evenL2 := thL_mem_evenL2 _ (fourier_mem_evenL2 (J_mem_evenL2 e))
  have hL : ⟪(realProlateBasis bR).ξ i, scalingEven.θ (-t) ((realProlateBasis bR).η i)⟫_ℂ
      = ⟪J e, X⟫_ℂ := by
    rw [Submodule.coe_inner]; rfl
  -- the common value
  set G : ℝ → ℂ := fun w ↦ (Real.exp (t / 2) : ℂ) * cosTrans e (Real.exp t * w)
  have hXrep : (restrictIcc 0 1 X : ℝ → ℂ) =ᵐ[volI 0 1] fun w ↦ c2 * G w := by
    have h1 : (X : ℝ → ℂ) =ᵐ[volume] fun w ↦ c2 * G w := by
      filter_upwards [coeFn_thL (-t) (𝓕 (J e : L2R) : L2R), thF_congr (fourier_J_ae e) (-t)]
        with w e1 e2
      rw [e1, e2]
      simp only [thF, neg_neg, G]; ring
    filter_upwards [coeFn_restrictIcc 0 1 X, ae_restrict_of_ae h1] with w e1 e2
    rw [e1, e2]
  have hcop : (Cop e : ℝ → ℂ) =ᵐ[volI 0 1] fun w ↦ (lam : ℂ) * e w := by
    have := Lp.coeFn_smul (lam : ℂ) e
    rw [← show Cop e = (lam : ℂ) • e from (complexify bR).eigen i] at this
    filter_upwards [this] with w hw
    rw [hw]; rfl
  have hLHS : ⟪J e, X⟫_ℂ = ∫ w, conj (e w) * G w ∂(volI 0 1) := by
    rw [inner_J_even e hXev, MeasureTheory.L2.inner_def]
    have h2 : (fun w ↦ ⟪(e : ℝ → ℂ) w, (restrictIcc 0 1 X : ℝ → ℂ) w⟫_ℂ) =ᵐ[volI 0 1]
        fun w ↦ c2 * (conj (e w) * G w) := by
      filter_upwards [hXrep] with w hw
      rw [hw, RCLike.inner_apply']; ring
    rw [integral_congr_ae h2, integral_const_mul, ← mul_assoc, mul_assoc 2 c2 c2, c2_mul_c2]
    ring
  have hRHS : ⟪Cop e, intOp (Kt t) e⟫_ℂ = (lam : ℂ) * ∫ w, conj (e w) * G w ∂(volI 0 1) := by
    rw [MeasureTheory.L2.inner_def, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hcop, coeFn_intOp_Kt t e] with w e1 e2
    rw [e1, e2, RCLike.inner_apply', map_mul, Complex.conj_ofReal]
    ring
  rw [hL, hLHS, hRHS, hlam]

/-! ### `⟨K, K_t⟩ = deltaK t` -/

/-- The product kernel `conj(cosK) · ktK`, as a real function. -/
def kprod (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  2 * Real.exp (t / 2) * (Real.cos (2 * Real.pi * (Real.exp t + 1) * p.1 * p.2)
    + Real.cos (2 * Real.pi * (Real.exp t - 1) * p.1 * p.2))

theorem conj_cosK_mul_ktK (t : ℝ) (p : ℝ × ℝ) :
    conj (cosK p) * ktK t p = (kprod t p : ℂ) := by
  have hc : Real.cos (2 * Real.pi * (Real.exp t + 1) * p.1 * p.2)
      + Real.cos (2 * Real.pi * (Real.exp t - 1) * p.1 * p.2)
      = 2 * Real.cos (2 * Real.pi * (Real.exp t * p.1) * p.2) * Real.cos (2 * Real.pi * p.1 * p.2) := by
    rw [show 2 * Real.pi * (Real.exp t + 1) * p.1 * p.2
        = 2 * Real.pi * (Real.exp t * p.1) * p.2 + 2 * Real.pi * p.1 * p.2 by ring,
      show 2 * Real.pi * (Real.exp t - 1) * p.1 * p.2
        = 2 * Real.pi * (Real.exp t * p.1) * p.2 - 2 * Real.pi * p.1 * p.2 by ring,
      Real.cos_add, Real.cos_sub]
    ring
  unfold kprod ktK cosK
  rw [Complex.conj_ofReal, hc]
  push_cast; ring

theorem continuous_kprod (t : ℝ) : Continuous (kprod t) := by unfold kprod; fun_prop

theorem integral_kprod (t : ℝ) :
    ∫ p, kprod t p ∂((volI 0 1).prod (volI 0 1))
      = 2 * Real.exp (t / 2) * (ArchS3.sincInt (2 * Real.pi * (Real.exp t + 1))
        + ArchS3.sincInt (2 * Real.pi * (Real.exp t - 1))) := by
  have hint : Integrable (kprod t) ((volI 0 1).prod (volI 0 1)) := by
    refine Integrable.mono' (integrable_const (4 * Real.exp (t / 2)))
      (continuous_kprod t).aestronglyMeasurable (Eventually.of_forall fun p ↦ ?_)
    unfold kprod
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
    have h1 := Real.abs_cos_le_one (2 * Real.pi * (Real.exp t + 1) * p.1 * p.2)
    have h2 := Real.abs_cos_le_one (2 * Real.pi * (Real.exp t - 1) * p.1 * p.2)
    have := abs_add_le (Real.cos (2 * Real.pi * (Real.exp t + 1) * p.1 * p.2))
      (Real.cos (2 * Real.pi * (Real.exp t - 1) * p.1 * p.2))
    have hE := Real.exp_pos (t / 2)
    nlinarith
  rw [integral_prod _ hint]
  have hI : ∀ (F : ℝ → ℝ), ∫ x, F x ∂(volI 0 1) = ∫ x in (0 : ℝ)..1, F x := fun F ↦ by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  simp only [hI]
  have hcI : ∀ c x, IntervalIntegrable (fun y ↦ Real.cos (c * x * y)) volume 0 1 :=
    fun c x ↦ (by fun_prop : Continuous fun y ↦ Real.cos (c * x * y)).intervalIntegrable _ _
  have inner_eq : ∀ x, ∫ y in (0 : ℝ)..1, kprod t (x, y)
      = 2 * Real.exp (t / 2) * ((∫ y in (0 : ℝ)..1, Real.cos (2 * Real.pi * (Real.exp t + 1) * x * y))
        + ∫ y in (0 : ℝ)..1, Real.cos (2 * Real.pi * (Real.exp t - 1) * x * y)) := by
    intro x
    unfold kprod
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hcI _ x) (hcI _ x)]
  simp_rw [inner_eq]
  have hcont : ∀ c, Continuous fun x ↦ ∫ y in (0 : ℝ)..1, Real.cos (c * x * y) := fun c ↦ by
    have : (fun x ↦ ∫ y in (0 : ℝ)..1, Real.cos (c * x * y)) = fun x ↦ Real.sinc (c * x) := by
      funext x; exact integral_cos_mul (c * x)
    rw [this]; exact Real.continuous_sinc.comp (continuous_const.mul continuous_id)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    ((hcont _).intervalIntegrable _ _) ((hcont _).intervalIntegrable _ _),
    integral_square_cos, integral_square_cos]

/-- **`⟨K, K_t⟩_{L²([0,1]²)} = deltaK t`** (`t ≥ 0`): CC (48)/(49). -/
theorem inner_K0_Kt {t : ℝ} (ht : 0 ≤ t) : ⟪K0, Kt t⟫_ℂ = (ArchS3.deltaK t : ℂ) := by
  rw [MeasureTheory.L2.inner_def]
  have h : (fun p ↦ ⟪(K0 : ℝ × ℝ → ℂ) p, (Kt t : ℝ × ℝ → ℂ) p⟫_ℂ)
      =ᵐ[(volI 0 1).prod (volI 0 1)] fun p ↦ (kprod t p : ℂ) := by
    filter_upwards [kernelOfContinuous_ae_eq (a := 0) (b := 1) continuous_cosK,
      kernelOfContinuous_ae_eq (a := 0) (b := 1) (continuous_ktK t)] with p e1 e2
    rw [e1, e2, RCLike.inner_apply', conj_cosK_mul_ktK]
  rw [integral_congr_ae h, integral_complex_ofReal, integral_kprod, ArchS3.deltaK,
    abs_of_nonneg ht]

/-! ### CC (75) = (48) -/

/-- **CC Lemma 4.1 + (75), HS form**: `Σ_n λ(n) ⟨ξ_n | ϑ(e^{-t}) η_n⟩ = δ(e^t)` for `t ≥ 0`. -/
theorem hasSum_δS {ι : Type*} [Countable ι] (bR : EigenBasis CopR ι) {t : ℝ} (ht : 0 ≤ t) :
    HasSum (fun i ↦ ((realProlateBasis bR).lam i : ℂ)
        * ⟪(realProlateBasis bR).ξ i, scalingEven.θ (-t) ((realProlateBasis bR).η i)⟫_ℂ)
      (ArchS3.deltaK t : ℂ) := by
  have h := hasSum_inner_intOp K0 (Kt t) (hbOf bR)
  simp only [hbOf_apply] at h
  rw [inner_K0_Kt ht] at h
  convert h using 1
  funext i
  exact term_eq bR i t

theorem δS_eq_deltaK {ι : Type*} [Countable ι] (bR : EigenBasis CopR ι) {t : ℝ} (ht : 0 ≤ t) :
    ProlateBasis.δS (realProlateBasis bR) scalingEven t = (ArchS3.deltaK t : ℂ) :=
  (hasSum_δS bR ht).tsum_eq

theorem δS_abs_eq_deltaK {ι : Type*} [Countable ι] (bR : EigenBasis CopR ι) (x : ℝ) :
    ProlateBasis.δS (realProlateBasis bR) scalingEven |x| = (ArchS3.deltaK x : ℂ) := by
  rw [δS_eq_deltaK bR (abs_nonneg x), ArchS3.deltaK, ArchS3.deltaK, abs_abs]

/-! ### Theorem 4.7 with (85) in S3's form -/

/-- **CC Theorem 4.7 for `IsWeilTest g`, with (85) stated in S3's own terms**:
if `‖P̂ P ϑ(g)‖²_HS = archW g + Dfun g` (CC Prop 2.2(iii)/(85) = S3's M2, interface O1), then
`‖S ϑ(g)‖²_HS = archW g + Re (D.Eplus (autocorr g))`. -/
theorem thm47_weil' {ι : Type*} (bR : EigenBasis CopR ι) (D : ProlateDataNat) (σ : ℕ ≃ ι)
    (hDlam : ∀ n, D.lam n = bR.μ (σ n)) (hDphi : ∀ n, D.phi n = phiR bR (σ n))
    (hτ : Summable fun i ↦ |(realProlateBasis bR).τ i|)
    {g : ℝ → ℂ} (hW : WeilExplicit.IsWeilTest g)
    {κ : Type*} (e : HilbertBasis κ ℂ evenL2)
    (h85 : HasSum (fun k ↦ ‖evenPair.hatP (evenPair.P
        (theta g (hW.1.continuous.integrable_of_hasCompactSupport hW.2) (e k)))‖ ^ 2)
      (ArchS3.archW g + ArchS3.Dfun g)) :
    HasSum (fun k ↦ ‖ArchS6.ProlateBasis.soninProj (S := evenPair)
        (theta g (hW.1.continuous.integrable_of_hasCompactSupport hW.2) (e k))‖ ^ 2)
      (ArchS3.archW g + (D.Eplus (WeilExplicit.autocorr g)).re) := by
  have : Countable ι := σ.symm.injective.countable
  refine thm47_weil bR D σ hDlam hDphi hτ hW e ?_
  have hD : (∫ x, WeilExplicit.autocorr g x
      * ProlateBasis.δS (realProlateBasis bR) scalingEven |x|).re = ArchS3.Dfun g := by
    rw [ArchS3.Dfun]
    congr 2; funext x
    rw [δS_abs_eq_deltaK]
  rwa [hD]

/-- **CC (83) for `IsWeilTest g`**, from S3's (85). -/
theorem thm47_weil'_nonneg {ι : Type*} (bR : EigenBasis CopR ι) (D : ProlateDataNat) (σ : ℕ ≃ ι)
    (hDlam : ∀ n, D.lam n = bR.μ (σ n)) (hDphi : ∀ n, D.phi n = phiR bR (σ n))
    (hτ : Summable fun i ↦ |(realProlateBasis bR).τ i|)
    {g : ℝ → ℂ} (hW : WeilExplicit.IsWeilTest g)
    {κ : Type*} (e : HilbertBasis κ ℂ evenL2)
    (h85 : HasSum (fun k ↦ ‖evenPair.hatP (evenPair.P
        (theta g (hW.1.continuous.integrable_of_hasCompactSupport hW.2) (e k)))‖ ^ 2)
      (ArchS3.archW g + ArchS3.Dfun g)) :
    0 ≤ ArchS3.archW g + (D.Eplus (WeilExplicit.autocorr g)).re :=
  (thm47_weil' bR D σ hDlam hDphi hτ hW e h85).nonneg fun _ ↦ sq_nonneg _

end ArchS7
