import ArchS7_Concrete

/-!
# ArchS7b_Lemma41: CC Lemma 4.1 with (75), the prolate series of `δ` (obligation O2 of S7)

Connes–Consani, arXiv:2006.13771, §4: Lemma 4.1 / (63) `δ(ρ) = Tr(ϑ(ρ⁻¹) P̂₁ P₁)` for `ρ ≥ 1`, and
with (79) the series (75) `δ(ρ) = Σ λ(n) ⟨ξ_n | ϑ(ρ⁻¹) η_n⟩`, where `δ` is (48).

We prove the identity "series (75) = closed form (48)" directly, for S6's concrete real prolate basis
and any pointwise scaling, without trace class:

* `term_eq`: `λ_n ⟨ξ_n | ϑ(e^{-t}) η_n⟩ = e^{t/2} ∫₀¹ (C e_n)(v) (C e_n)(e^t v) dv`, `C` = S9's operator
  with kernel `2cos(2πvy)` on `L²([0,1]; ℝ)` (uses S7's `xi_ae`, `inner_dil`, S6's `fourier_ξ_ae_real`).
* `hasSum_cosTransR_mul`: Parseval along the eigenbasis, `Σ_n (C e_n)(v)(C e_n)(w) = ∫₀¹ 2cos(2πvy)2cos(2πwy) dy`.
* `tsum_integral_cosTransR`: termwise integration (Tonelli bound from Bessel; no eigenvalue decay used).
* `deltaK_eq_double`: `deltaK t = e^{t/2} ∫₀¹∫₀¹ 2cos(2πvy) 2cos(2π e^t vy)` (CC (49) via sinc).
* `δS_eq_deltaK` (**O2**): `δS t = deltaK t` for `t ≥ 0`; `δS_abs_eq_deltaK`: `δS |x| = deltaK x`.
* `thm47_concrete_O1`: S7's `thm47_concrete` with `h85` in S3's form `archW g + Dfun g` (O1 only).

conjecture1_proved = False.
-/

open MeasureTheory Set Filter
open scoped InnerProductSpace ComplexConjugate ENNReal

noncomputable section

namespace ArchS7b

open ArchS6 ArchS7 ArchS3 ArchS5

theorem integral_cos_mul_unit (c : ℝ) :
    ∫ y in (0 : ℝ)..1, Real.cos (c * y) = Real.sinc c := by
  by_cases hc : c = 0
  · subst hc; simp
  rw [intervalIntegral.integral_comp_mul_left (fun x ↦ Real.cos x) hc, integral_cos,
    Real.sinc_of_ne_zero hc]
  simp [div_eq_inv_mul]

theorem integral_cosKR_mul (ρ v : ℝ) :
    ∫ y in (0 : ℝ)..1, cosKR (v, y) * cosKR (ρ * v, y)
      = 2 * (Real.sinc (2 * Real.pi * (ρ + 1) * v) + Real.sinc (2 * Real.pi * (ρ - 1) * v)) := by
  have h : (fun y ↦ cosKR (v, y) * cosKR (ρ * v, y)) = fun y ↦
      2 * Real.cos (2 * Real.pi * (ρ + 1) * v * y) + 2 * Real.cos (2 * Real.pi * (ρ - 1) * v * y) := by
    funext y
    simp only [cosKR]
    have := cos_mul_cos_eq (2 * Real.pi * (ρ * v) * y) (2 * Real.pi * v * y)
    rw [show 2 * Real.pi * (ρ + 1) * v * y = 2 * Real.pi * (ρ * v) * y + 2 * Real.pi * v * y by ring,
      show 2 * Real.pi * (ρ - 1) * v * y = 2 * Real.pi * (ρ * v) * y - 2 * Real.pi * v * y by ring]
    linear_combination 4 * this
  rw [h, intervalIntegral.integral_add ((by fun_prop : Continuous fun y : ℝ ↦
      2 * Real.cos (2 * Real.pi * (ρ + 1) * v * y)).intervalIntegrable 0 1)
      ((by fun_prop : Continuous fun y : ℝ ↦
      2 * Real.cos (2 * Real.pi * (ρ - 1) * v * y)).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_cos_mul_unit, integral_cos_mul_unit]
  ring

/-- The double integral `∫₀¹∫₀¹ 2cos(2πvy) · 2cos(2πρvy)` is CC (49)'s bracket. -/
theorem integral_integral_cosKR (ρ : ℝ) :
    ∫ v in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, cosKR (v, y) * cosKR (ρ * v, y)
      = 2 * (sincInt (2 * Real.pi * (ρ + 1)) + sincInt (2 * Real.pi * (ρ - 1))) := by
  simp_rw [integral_cosKR_mul]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    (intervalIntegrable_sinc_mul _ _ _) (intervalIntegrable_sinc_mul _ _ _)]
  rfl

/-- `deltaK t = e^{t/2} ∫₀¹∫₀¹ 2cos(2πvy) · 2cos(2π e^t vy)` for `t ≥ 0`. -/
theorem deltaK_eq_double {t : ℝ} (ht : 0 ≤ t) :
    deltaK t = Real.exp (t / 2)
      * ∫ v in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, cosKR (v, y) * cosKR (Real.exp t * v, y) := by
  rw [integral_integral_cosKR, deltaK, abs_of_nonneg ht]
  ring


/-! ### Rows of the kernel in `L²([0,1]; ℝ)` and Parseval -/

theorem abs_cosKR_le (p : ℝ × ℝ) : |cosKR p| ≤ 2 := by
  unfold cosKR; rw [abs_mul, abs_two]; nlinarith [Real.abs_cos_le_one (2 * Real.pi * p.1 * p.2)]

theorem memLp_kRow (w : ℝ) : MemLp (fun y ↦ cosKR (w, y)) 2 (volI 0 1) :=
  MemLp.of_bound (continuous_cosKR.comp (continuous_const.prodMk continuous_id) :
    Continuous fun y ↦ cosKR (w, y)).aestronglyMeasurable 2
    (ae_of_all _ fun y ↦ by rw [Real.norm_eq_abs]; exact abs_cosKR_le _)

/-- The row `y ↦ 2cos(2πwy)` as an element of `L²([0,1]; ℝ)`. -/
def kRow (w : ℝ) : L2IR 0 1 := (memLp_kRow w).toLp _

theorem inner_kRow_left (w : ℝ) (e : L2IR 0 1) : ⟪kRow w, e⟫_ℝ = cosTransR e w := by
  rw [MeasureTheory.L2.inner_def, cosTransR]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_kRow w).coeFn_toLp] with y hy
  rw [kRow, hy, real_inner_eq_re_inner, RCLike.inner_apply]
  simp [mul_comm]

theorem inner_kRow_kRow (w w' : ℝ) :
    ⟪kRow w, kRow w'⟫_ℝ = ∫ y in Icc (0 : ℝ) 1, cosKR (w, y) * cosKR (w', y) := by
  rw [inner_kRow_left, cosTransR]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_kRow w').coeFn_toLp] with y hy
  rw [kRow, hy, mul_comm]

theorem norm_kRow_sq_le (w : ℝ) : ‖kRow w‖ ^ 2 ≤ 4 := by
  rw [← real_inner_self_eq_norm_sq, inner_kRow_kRow]
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (0 : ℝ) 1)
    (f := fun y ↦ cosKR (w, y) * cosKR (w, y)) (C := 4) measure_Icc_lt_top
    (fun y _ ↦ by
      rw [Real.norm_eq_abs, abs_mul]
      nlinarith [abs_cosKR_le (w, y), abs_nonneg (cosKR (w, y))])
  rw [Real.norm_eq_abs] at h
  have hv : volume.real (Icc (0 : ℝ) 1) = 1 := by simp
  rw [hv, mul_one] at h
  exact (le_abs_self _).trans h

variable {ι : Type*} (bR : EigenBasis CopR ι)

/-- Parseval: `⟪x, y⟫ = Σ ⟪x, e_i⟫⟪e_i, y⟫` along the real eigenbasis. -/
theorem hasSum_inner_mul (x y : L2IR 0 1) :
    HasSum (fun i ↦ ⟪x, bR.e i⟫_ℝ * ⟪bR.e i, y⟫_ℝ) ⟪x, y⟫_ℝ := by
  have h := (innerSL ℝ x).hasSum (bR.hasSum y)
  simp only [innerSL_apply_apply, inner_smul_right] at h
  have e : (fun i ↦ ⟪x, bR.e i⟫_ℝ * ⟪bR.e i, y⟫_ℝ) = fun i ↦ ⟪bR.e i, y⟫_ℝ * ⟪x, bR.e i⟫_ℝ :=
    funext fun i ↦ mul_comm _ _
  rw [e]; exact h

theorem hasSum_inner_sq (x : L2IR 0 1) :
    HasSum (fun i ↦ ⟪x, bR.e i⟫_ℝ ^ 2) (‖x‖ ^ 2) := by
  have h := hasSum_inner_mul bR x x
  rw [real_inner_self_eq_norm_sq] at h
  convert h using 1
  funext i; rw [real_inner_comm (bR.e i) x, sq]

theorem continuous_cosTransR (e : L2IR 0 1) : Continuous (cosTransR e) := by
  have : cosTransR e = fun w ↦ (cosTrans (ofRealL 0 1 e) w).re := by
    funext w; rw [cosTrans_ofRealL, Complex.ofReal_re]
  rw [this]
  exact Complex.continuous_re.comp (continuous_cosTrans _)

/-- The pointwise Parseval sum: `Σ_i (C e_i)(v) (C e_i)(w) = ∫₀¹ 2cos(2πvy) 2cos(2πwy) dy`. -/
theorem hasSum_cosTransR_mul (v w : ℝ) :
    HasSum (fun i ↦ cosTransR (bR.e i) v * cosTransR (bR.e i) w)
      (∫ y in Icc (0 : ℝ) 1, cosKR (v, y) * cosKR (w, y)) := by
  have h := hasSum_inner_mul bR (kRow v) (kRow w)
  rw [inner_kRow_kRow] at h
  convert h using 1
  funext i
  rw [inner_kRow_left, real_inner_comm, inner_kRow_left]

theorem abs_cosTransR_mul_le (v w : ℝ) (i : ι) :
    |cosTransR (bR.e i) v * cosTransR (bR.e i) w|
      ≤ (⟪kRow v, bR.e i⟫_ℝ ^ 2 + ⟪kRow w, bR.e i⟫_ℝ ^ 2) / 2 := by
  rw [inner_kRow_left, inner_kRow_left, abs_mul]
  nlinarith [sq_nonneg (|cosTransR (bR.e i) v| - |cosTransR (bR.e i) w|),
    sq_abs (cosTransR (bR.e i) v), sq_abs (cosTransR (bR.e i) w)]

theorem summable_abs_cosTransR_mul (v w : ℝ) :
    Summable fun i ↦ |cosTransR (bR.e i) v * cosTransR (bR.e i) w| :=
  Summable.of_nonneg_of_le (fun _ ↦ abs_nonneg _) (abs_cosTransR_mul_le bR v w)
    (((hasSum_inner_sq bR (kRow v)).add (hasSum_inner_sq bR (kRow w))).div_const 2).summable

theorem tsum_abs_cosTransR_mul_le (v w : ℝ) :
    ∑' i, |cosTransR (bR.e i) v * cosTransR (bR.e i) w| ≤ 4 := by
  have h := hasSum_le (abs_cosTransR_mul_le bR v w) (summable_abs_cosTransR_mul bR v w).hasSum
    (((hasSum_inner_sq bR (kRow v)).add (hasSum_inner_sq bR (kRow w))).div_const 2)
  nlinarith [norm_kRow_sq_le v, norm_kRow_sq_le w]

/-! ### Termwise integration -/

theorem continuous_term (i : ι) (ρ : ℝ) :
    Continuous fun v ↦ cosTransR (bR.e i) v * cosTransR (bR.e i) (ρ * v) :=
  (continuous_cosTransR _).mul ((continuous_cosTransR _).comp (continuous_const.mul continuous_id))

/-- `Σ_i ∫₀¹ (C e_i)(v)(C e_i)(ρv) dv = ∫₀¹∫₀¹ 2cos(2πvy) 2cos(2πρvy)`: the series is integrated
termwise (Tonelli bound from Bessel, no decay of the eigenvalues needed). -/
theorem tsum_integral_cosTransR [Countable ι] (ρ : ℝ) :
    ∑' i, ∫ v in Icc (0 : ℝ) 1, cosTransR (bR.e i) v * cosTransR (bR.e i) (ρ * v)
      = ∫ v in Icc (0 : ℝ) 1, ∫ y in Icc (0 : ℝ) 1, cosKR (v, y) * cosKR (ρ * v, y) := by
  rw [← integral_tsum (fun i ↦ (continuous_term bR i ρ).aestronglyMeasurable)]
  · refine integral_congr_ae (ae_of_all _ fun v ↦ ?_)
    exact (hasSum_cosTransR_mul bR v (ρ * v)).tsum_eq
  · rw [← lintegral_tsum (fun i ↦ (continuous_term bR i ρ).enorm.aemeasurable)]
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono (g := fun _ ↦ ENNReal.ofReal 4)
      (fun v ↦ ?_)) ?_)
    · simp only [Real.enorm_eq_ofReal_abs]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ abs_nonneg _)
        (summable_abs_cosTransR_mul bR v (ρ * v))]
      exact ENNReal.ofReal_le_ofReal (tsum_abs_cosTransR_mul_le bR v (ρ * v))
    · rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-! ### The n-th term of (75) -/

variable (T : Scaling evenPair)

theorem cosTransR_eq (i : ι) (w : ℝ) : cosTransR (bR.e i) w = bR.μ i * phiR bR i w := by
  have hμ : bR.μ i ≠ 0 := prolateBasisOf_lam_ne_zero (complexify bR) i
  rw [phiR]; field_simp

/-- **The n-th term of CC (75)**: `λ_n ⟨ξ_n | ϑ(e^{-t}) η_n⟩ = e^{t/2} ∫₀¹ (C e_n)(v) (C e_n)(e^t v) dv`,
i.e. `λ_n² e^{t/2} ∫₀¹ ξ_n^an(v) ξ_n^an(e^t v) dv`. -/
theorem term_eq (hT : IsPointwise T) (i : ι) (t : ℝ) :
    ((realProlateBasis bR).lam i : ℂ)
        * ⟪(realProlateBasis bR).ξ i, T.θ (-t) ((realProlateBasis bR).η i)⟫_ℂ
      = ((Real.exp (t / 2)
          * ∫ v in Icc (0 : ℝ) 1, cosTransR (bR.e i) v * cosTransR (bR.e i) (Real.exp t * v) : ℝ) : ℂ) := by
  set b := realProlateBasis bR
  have hB : ((((b.η i : evenL2) : L2R)) : ℝ → ℂ) =ᵐ[volume]
      fun w ↦ c2 * (bR.μ i : ℂ) * (phiR bR i w : ℂ) := fourier_ξ_ae_real bR i
  rw [inner_dil hT t (xi_ae bR i) hB, realProlateBasis_lam]
  set G : ℝ → ℝ := (Icc (0 : ℝ) 1).indicator
    (fun x ↦ Real.exp (t / 2) * bR.μ i * (phiR bR i x * phiR bR i (Real.exp t * x)) / 2) with hGdef
  have hpt : ∀ v, conj (xiRep (phiR bR i) v)
      * dil t (fun w ↦ c2 * (bR.μ i : ℂ) * (phiR bR i w : ℂ)) v = ((G |v| : ℝ) : ℂ) := by
    intro v
    unfold xiRep dil
    by_cases h1 : |v| ≤ 1
    · rw [if_pos h1, hGdef, indicator_of_mem (show |v| ∈ Icc (0 : ℝ) 1 from ⟨abs_nonneg v, h1⟩),
        Complex.conj_ofReal]
      have : phiR bR i (Real.exp t * v) = phiR bR i (Real.exp t * |v|) := by
        rw [← phiR_abs bR i (Real.exp t * v), abs_mul, abs_of_pos (Real.exp_pos t)]
      beta_reduce
      rw [this, c2_eq]
      have hs : Real.sqrt 2 ≠ 0 := by positivity
      have h2c : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring
      push_cast
      field_simp
      rw [h2c]
    · rw [if_neg h1, hGdef, indicator_of_notMem (fun h ↦ h1 h.2)]
      simp
  simp_rw [hpt]
  rw [integral_complex_ofReal]
  have hI : ∫ v, G |v| = Real.exp (t / 2) * bR.μ i
      * ∫ x in Icc (0 : ℝ) 1, phiR bR i x * phiR bR i (Real.exp t * x) := by
    rw [integral_comp_abs (f := G), hGdef, setIntegral_indicator measurableSet_Icc]
    have hsub : Ioi (0 : ℝ) ∩ Icc 0 1 = Ioc 0 1 := by
      ext x; simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
      constructor
      · rintro ⟨h0, -, h1⟩; exact ⟨h0, h1⟩
      · rintro ⟨h0, h1⟩; exact ⟨h0, h0.le, h1⟩
    rw [hsub, ← integral_Icc_eq_integral_Ioc, integral_div, integral_const_mul]
    ring
  have hJ : ∫ v in Icc (0 : ℝ) 1, cosTransR (bR.e i) v * cosTransR (bR.e i) (Real.exp t * v)
      = bR.μ i ^ 2 * ∫ x in Icc (0 : ℝ) 1, phiR bR i x * phiR bR i (Real.exp t * x) := by
    simp_rw [cosTransR_eq bR i]
    rw [← integral_const_mul]
    congr 1; funext x; ring
  rw [hI, hJ]
  push_cast
  ring

/-! ### CC Lemma 4.1 / (75) -/

theorem setIntegral_Icc01 (f : ℝ → ℝ) : ∫ x in Icc (0 : ℝ) 1, f x = ∫ x in (0 : ℝ)..1, f x := by
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le zero_le_one]

/-- **CC Lemma 4.1 with (75) (obligation O2 of S7)**: for `ρ = e^t ≥ 1`, the prolate series
`δS(t) = Σ λ(n) ⟨ξ_n | ϑ(ρ⁻¹) η_n⟩` is CC's `δ(ρ)` of (48), i.e. S3's `deltaK t`. -/
theorem δS_eq_deltaK [Countable ι] (hT : IsPointwise T) {t : ℝ} (ht : 0 ≤ t) :
    ProlateBasis.δS (realProlateBasis bR) T t = ((deltaK t : ℝ) : ℂ) := by
  rw [ProlateBasis.δS]
  simp only [ProlateBasis.η] at *
  have h := fun i ↦ term_eq bR T hT i t
  simp only [ArchS6.ProlateBasis.η] at h
  simp only [h]
  rw [← Complex.ofReal_tsum, tsum_mul_left, tsum_integral_cosTransR, deltaK_eq_double ht]
  simp only [setIntegral_Icc01]

/-- O2 in the even form consumed by `thm47_concrete` (`h85`). -/
theorem δS_abs_eq_deltaK [Countable ι] (hT : IsPointwise T) (x : ℝ) :
    ProlateBasis.δS (realProlateBasis bR) T |x| = ((deltaK x : ℝ) : ℂ) := by
  rw [δS_eq_deltaK bR T hT (abs_nonneg x)]
  simp only [deltaK, abs_abs]

/-! ### Plugging O2 into `thm47_concrete` -/

/-- `h85` of `thm47_concrete` from O1 alone: the `δS` integral is S3's `Dfun`. -/
theorem integral_δS_eq_Dfun [Countable ι] (hT : IsPointwise T) (g : ℝ → ℂ) :
    (∫ x, WeilExplicit.autocorr g x * ProlateBasis.δS (realProlateBasis bR) T |x|).re = Dfun g := by
  rw [Dfun]
  congr 2; funext x
  rw [δS_abs_eq_deltaK bR T hT x]

/-- **CC Thm 4.7, concrete, with O2 discharged.**  The remaining hypotheses are O1 in S3's form
(`‖P̂ P ϑ(g)‖²_HS = archW g + Dfun g`, CC (85)), O3 (`T`, `V`, `hcoef`) and O4 (`D`, `σ`, `hτ`). -/
theorem thm47_concrete_O1 {ι : Type*} (bR : EigenBasis CopR ι) (T : Scaling evenPair)
    (hT : IsPointwise T) (D : ArchS8.ProlateDataNat) (σ : ℕ ≃ ι) (hDlam : ∀ n, D.lam n = bR.μ (σ n))
    (hDphi : ∀ n, D.phi n = phiR bR (σ n))
    (hτ : Summable fun i ↦ |(realProlateBasis bR).τ i|)
    (g : ℝ → ℂ) (hf : Integrable (WeilExplicit.autocorr g)) (V : evenL2 →L[ℂ] evenL2)
    (hcoef : ∀ v, ((‖(ContinuousLinearMap.adjoint V) v‖ ^ 2 : ℝ) : ℂ)
      = ∫ x, WeilExplicit.autocorr g x * ⟪v, T.θ x v⟫_ℂ)
    {κ : Type*} (e : HilbertBasis κ ℂ evenL2)
    (h85 : HasSum (fun k ↦ ‖evenPair.hatP (evenPair.P (V (e k)))‖ ^ 2) (archW g + Dfun g)) :
    HasSum (fun k ↦ ‖ArchS6.ProlateBasis.soninProj (S := evenPair) (V (e k))‖ ^ 2)
      (archW g + (D.Eplus (WeilExplicit.autocorr g)).re) := by
  have : Countable ι := σ.symm.injective.countable
  refine thm47_concrete bR T hT D σ hDlam hDphi hτ g hf V hcoef e ?_
  rwa [integral_δS_eq_Dfun bR T hT g]

/-- **CC (83), concrete, with O2 discharged**: `archW g + Re D.Eplus(autocorr g) ≥ 0` given O1, O3, O4. -/
theorem thm47_concrete_O1_nonneg {ι : Type*} (bR : EigenBasis CopR ι) (T : Scaling evenPair)
    (hT : IsPointwise T) (D : ArchS8.ProlateDataNat) (σ : ℕ ≃ ι) (hDlam : ∀ n, D.lam n = bR.μ (σ n))
    (hDphi : ∀ n, D.phi n = phiR bR (σ n))
    (hτ : Summable fun i ↦ |(realProlateBasis bR).τ i|)
    (g : ℝ → ℂ) (hf : Integrable (WeilExplicit.autocorr g)) (V : evenL2 →L[ℂ] evenL2)
    (hcoef : ∀ v, ((‖(ContinuousLinearMap.adjoint V) v‖ ^ 2 : ℝ) : ℂ)
      = ∫ x, WeilExplicit.autocorr g x * ⟪v, T.θ x v⟫_ℂ)
    {κ : Type*} (e : HilbertBasis κ ℂ evenL2)
    (h85 : HasSum (fun k ↦ ‖evenPair.hatP (evenPair.P (V (e k)))‖ ^ 2) (archW g + Dfun g)) :
    0 ≤ archW g + (D.Eplus (WeilExplicit.autocorr g)).re :=
  (thm47_concrete_O1 bR T hT D σ hDlam hDphi hτ g hf V hcoef e h85).nonneg fun _ ↦ sq_nonneg _

end ArchS7b
