import ArchS7_Kappa

/-!
# ArchS7_PFP: `𝓕Λ(P F φ)(w) = ⟨κ_{-2πw}, φ⟩` on a smooth dense class

For `φ` even, `C¹`, compactly supported and vanishing on `[-1,1]`, the Mellin transform of `P F φ`
is computed pointwise.  The proof truncates the (conditionally convergent) Mellin integral at `Y`,
swaps the order on `[1, Y] × (0, ∞)`, substitutes `s = xy`, and lets `Y → ∞` with S3's
`tendsto_integral_Psi` (`∫₀^R s^{z-1} 2cos(2πs) ds → Ψ(z)`) under dominated convergence.

conjecture1_proved = False.
-/

open MeasureTheory Set Filter Topology FourierTransform
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace ArchS7

open ArchS6 ArchS3

set_option linter.unusedSectionVars false

/-! ### Elementary facts -/

theorem ofReal_exp_cpow (u : ℝ) (s : ℂ) : ((Real.exp u : ℝ) : ℂ) ^ s = Complex.exp (u * s) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos u).ne'),
    ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]

theorem norm_fourier_le (f : ℝ → ℂ) (w : ℝ) : ‖𝓕 f w‖ ≤ ∫ v, ‖f v‖ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; funext v
  rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem cexp_add_cexp_neg (a : ℝ) :
    Complex.exp (↑a * Complex.I) + Complex.exp (↑(-a) * Complex.I) = ((2 * Real.cos a : ℝ) : ℂ) := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

theorem norm_Gpart_le {t a : ℝ} (ha : 1 ≤ a) : ‖Gpart t 0 a‖ ≤ 1 + ArchS3.Kt t := by
  have h : Gpart t 0 a = Psi (zt t) - Phi t a := by rw [Phi]; ring
  rw [h]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_Psi_zt]
  have h1 := norm_Phi_le (t := t) (lt_of_lt_of_le one_pos ha)
  have h2 : a ^ (-1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ha (by norm_num)
  have h3 := ArchS3.Kt_nonneg t
  nlinarith

/-! ### The smooth class -/

section Smooth

variable {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
  (hφe : ∀ x, φ (-x) = φ x) (hφ1 : ∀ x, |x| ≤ 1 → φ x = 0)

include hφ hφc in
theorem integrable_phi : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hφc

include hφ hφc in
/-- Decay of `𝓕φ`: `|𝓕φ(y)| ≤ C / |y|`. -/
theorem norm_fourier_phi_le {y : ℝ} (hy : y ≠ 0) :
    ‖𝓕 φ y‖ ≤ (∫ v, ‖deriv φ v‖) / (2 * Real.pi * |y|) := by
  have hd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hdi : Integrable (deriv φ) :=
    (hφ.continuous_deriv le_rfl).integrable_of_hasCompactSupport hφc.deriv
  have h := congrFun (Real.fourier_deriv (integrable_phi hφ hφc) hd hdi) y
  have hb := norm_fourier_le (deriv φ) y
  rw [h, norm_smul] at hb
  have hn : ‖(2 * (Real.pi : ℂ) * Complex.I * y)‖ = 2 * Real.pi * |y| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  rw [hn] at hb
  have hpos : 0 < 2 * Real.pi * |y| := by positivity
  rw [le_div_iff₀ hpos]; linarith

include hφ hφc hφe in
/-- `𝓕φ(y) = ∫_{x>0} 2cos(2πxy) φ(x) dx` for even `φ`. -/
theorem fourier_phi_eq_cos (y : ℝ) :
    𝓕 φ y = ∫ x in Ioi 0, cosD 0 (x * y) * φ x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  set h : ℝ → ℂ := fun v ↦ Complex.exp (↑(-2 * Real.pi * v * y) * Complex.I) • φ v
  have hi : Integrable h := by
    refine Integrable.mono' (integrable_phi hφ hφc).norm (by
      unfold h; exact ((by fun_prop : Continuous fun v : ℝ ↦
        Complex.exp (↑(-2 * Real.pi * v * y) * Complex.I)).smul hφ.continuous).aestronglyMeasurable)
      (Eventually.of_forall fun v ↦ ?_)
    simp only [h, norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]
  rw [← integral_add_compl measurableSet_Ioi hi, compl_Ioi]
  have hn := integral_comp_neg_Ioi (c := (0 : ℝ)) (f := h)
  rw [neg_zero] at hn
  rw [← hn, ← integral_add hi.integrableOn (hi.comp_neg.integrableOn)]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ ?_
  simp only [h, smul_eq_mul, hφe]
  rw [← add_mul, show (-2 * Real.pi * -x * y) = -(-2 * Real.pi * x * y) by ring, cosD,
    show (-2 * Real.pi * x * y) = -(2 * Real.pi * (x * y)) by ring, neg_neg, add_comm,
    cexp_add_cexp_neg]
  push_cast; simp only [neg_zero, zero_mul, Complex.exp_zero, mul_one]

/-! ### The truncated Mellin integral -/

/-- `G(y) = √2 y^{z-1} 𝓕φ(y)`. -/
def Gm (φ : ℝ → ℂ) (t y : ℝ) : ℂ := ((Real.sqrt 2 : ℝ) : ℂ) * ((y : ℝ) : ℂ) ^ (zt t - 1) * 𝓕 φ y

theorem continuousOn_cpow_zt (w : ℂ) : ContinuousOn (fun y : ℝ ↦ ((y : ℝ) : ℂ) ^ w) (Ioi 0) :=
  fun y hy ↦ (ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const
    (Complex.ofReal_mem_slitPlane.2 hy)).continuousWithinAt

include hφ hφc in
theorem continuous_fourier_phi : Continuous (𝓕 φ) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner
    (integrable_phi hφ hφc)

include hφ hφc in
theorem integrableOn_Gm (t : ℝ) : IntegrableOn (Gm φ t) (Ioi 1) := by
  set C := (∫ v, ‖deriv φ v‖) / (2 * Real.pi)
  have hC : 0 ≤ C := by positivity
  have hb := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1) one_pos).const_mul
    (Real.sqrt 2 * C)
  refine hb.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact ((continuousOn_const.mul (continuousOn_cpow_zt _)).mul
      (continuous_fourier_phi hφ hφc).continuousOn).mono (Ioi_subset_Ioi zero_le_one)
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun y hy ↦ ?_)
    have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
    rw [Gm, norm_mul, norm_mul, Complex.norm_real, norm_cpow_zt hy0, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2))]
    have h1 := norm_fourier_phi_le hφ hφc hy0.ne'
    rw [abs_of_pos hy0] at h1
    have h2 : (∫ v, ‖deriv φ v‖) / (2 * Real.pi * y) = C * y⁻¹ := by
      unfold C; field_simp
    rw [h2] at h1
    have h3 : y ^ (-1 / 2 : ℝ) * y⁻¹ = y ^ (-3 / 2 : ℝ) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hy0]; norm_num
    have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hr : 0 ≤ y ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hy0.le _
    calc Real.sqrt 2 * y ^ (-1 / 2 : ℝ) * ‖𝓕 φ y‖ ≤ Real.sqrt 2 * y ^ (-1 / 2 : ℝ) * (C * y⁻¹) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg hs hr)
      _ = Real.sqrt 2 * C * (y ^ (-1 / 2 : ℝ) * y⁻¹) := by ring
      _ = Real.sqrt 2 * C * y ^ (-3 / 2 : ℝ) := by rw [h3]

/-- The inner integral after the substitution `s = xy`. -/
theorem inner_subst (t : ℝ) {x Y : ℝ} (hx : 0 < x) (hY : 1 ≤ Y) :
    ∫ y in (1 : ℝ)..Y, ((y : ℝ) : ℂ) ^ (zt t - 1) * cosD 0 (x * y)
      = mz t x * (Gpart t 0 (x * Y) - Gpart t 0 x) := by
  have hxc : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have e : ∀ y ∈ Set.uIcc (1 : ℝ) Y, ((y : ℝ) : ℂ) ^ (zt t - 1) * cosD 0 (x * y)
      = ((x : ℝ) : ℂ) ^ (-(zt t - 1)) * pD t 0 (x * y) := by
    intro y hy
    have hy0 : 0 ≤ y := by
      rcases Set.mem_uIcc.1 hy with h | h <;> linarith [h.1, h.2]
    unfold pD
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hx.le hy0, ← mul_assoc, ← mul_assoc,
      ← Complex.cpow_add _ _ hxc, neg_add_cancel, Complex.cpow_zero, one_mul]
  rw [intervalIntegral.integral_congr e, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun s ↦ pD t 0 s) hx.ne', mul_one,
    ← Gpart_sub hx.le (by positivity), mz, Complex.real_smul, ← mul_assoc]
  congr 1
  rw [show -(zt t - 1) = -zt t + 1 by ring, Complex.cpow_add _ _ hxc, Complex.cpow_one,
    Complex.ofReal_inv]
  field_simp

include hφ hφc hφe in
/-- The truncated Mellin integral, after Fubini and `s = xy`. -/
theorem integral_Gm_eq (t : ℝ) {Y : ℝ} (hY : 1 ≤ Y) :
    ∫ y in (1 : ℝ)..Y, Gm φ t y
      = ((Real.sqrt 2 : ℝ) : ℂ) * ∫ x in Ioi 0, φ x * (mz t x * (Gpart t 0 (x * Y) - Gpart t 0 x)) := by
  have hφi := integrable_phi hφ hφc
  set F : ℝ → ℝ → ℂ := fun y x ↦ ((y : ℝ) : ℂ) ^ (zt t - 1) * cosD 0 (x * y) * φ x
  have hG : ∀ y, Gm φ t y = ((Real.sqrt 2 : ℝ) : ℂ) * ∫ x in Ioi 0, F y x := by
    intro y
    rw [Gm, fourier_phi_eq_cos hφ hφc hφe, mul_assoc, ← integral_const_mul]
    congr 2; funext x; simp only [F]; ring
  simp_rw [hG]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hY]
  congr 1
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc 1 Y)).prod (volume.restrict (Ioi 0))) := by
    have hB : Integrable (fun z : ℝ × ℝ ↦ (2 : ℝ) * ‖φ z.2‖)
        ((volume.restrict (Ioc 1 Y)).prod (volume.restrict (Ioi 0))) := by
      have := (integrable_const (2 : ℝ) : Integrable (fun _ : ℝ ↦ (2 : ℝ))
        (volume.restrict (Ioc 1 Y))).mul_prod (hφi.norm.integrableOn (s := Ioi 0))
      simpa using this
    rw [Measure.prod_restrict] at hB ⊢
    refine hB.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ (measurableSet_Ioc.prod measurableSet_Ioi)
      intro z hz
      have hz1 : (0 : ℝ) < z.1 := lt_trans one_pos hz.1.1
      refine ContinuousAt.continuousWithinAt ?_
      show ContinuousAt (fun z : ℝ × ℝ ↦ ((z.1 : ℝ) : ℂ) ^ (zt t - 1) * cosD 0 (z.2 * z.1) * φ z.2) z
      refine ContinuousAt.mul (ContinuousAt.mul ?_ ?_) (hφ.continuous.comp continuous_snd).continuousAt
      · exact ContinuousAt.cpow (Complex.continuous_ofReal.comp continuous_fst).continuousAt
          continuousAt_const (Complex.ofReal_mem_slitPlane.2 hz1)
      · exact ((continuous_cosD 0).comp (continuous_snd.mul continuous_fst)).continuousAt
    · refine (ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioi)).2
        (Eventually.of_forall fun z hz ↦ ?_)
      have hz1 : (0 : ℝ) < z.1 := lt_trans one_pos hz.1.1
      simp only [Function.uncurry, F, norm_mul]
      rw [norm_cpow_zt hz1]
      have h1 : z.1 ^ (-1 / 2 : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hz.1.1.le (by norm_num)
      have h2 := norm_cosD_le (le_refl (0 : ℝ)) (mul_nonneg (le_of_lt hz.2) hz1.le)
      have h3 := norm_nonneg (φ z.2)
      have h4 : 0 ≤ z.1 ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hz1.le _
      calc z.1 ^ (-1 / 2 : ℝ) * ‖cosD 0 (z.2 * z.1)‖ * ‖φ z.2‖ ≤ 1 * 2 * ‖φ z.2‖ := by gcongr
        _ = 2 * ‖φ z.2‖ := by ring
  rw [integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  have hx0 : (0 : ℝ) < x := hx
  simp only [F]
  rw [show (fun y : ℝ ↦ ((y : ℝ) : ℂ) ^ (zt t - 1) * cosD 0 (x * y) * φ x)
      = fun y ↦ (((y : ℝ) : ℂ) ^ (zt t - 1) * cosD 0 (x * y)) * φ x from rfl,
    integral_mul_const, ← intervalIntegral.integral_of_le hY, inner_subst t hx0 hY]
  ring

/-- `β(u) = √2 e^{u/2} 𝓕φ(e^u)` for `u > 0`, `0` otherwise: the log-map image of `P F φ`. -/
def betaF (φ : ℝ → ℂ) (u : ℝ) : ℂ :=
  (Ioi 0).indicator (fun u ↦ ((Real.sqrt 2 * Real.exp (u / 2) : ℝ) : ℂ) * 𝓕 φ (Real.exp u)) u

include hφ hφc in
theorem integrable_betaF : Integrable (betaF φ) := by
  set C := (∫ v, ‖deriv φ v‖) / (2 * Real.pi)
  have hC : 0 ≤ C := by positivity
  unfold betaF
  rw [integrable_indicator_iff measurableSet_Ioi]
  have hb := (exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
    (Real.sqrt 2 * C)
  refine hb.mono' ?_ ?_
  · exact ((by fun_prop : Continuous fun u : ℝ ↦ ((Real.sqrt 2 * Real.exp (u / 2) : ℝ) : ℂ)).mul
      ((continuous_fourier_phi hφ hφc).comp Real.continuous_exp)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu ↦ ?_)
    have h1 := norm_fourier_phi_le hφ hφc (Real.exp_pos u).ne'
    rw [abs_of_pos (Real.exp_pos u)] at h1
    have h2 : (∫ v, ‖deriv φ v‖) / (2 * Real.pi * Real.exp u) = C * Real.exp (-u) := by
      unfold C; rw [Real.exp_neg]; field_simp
    rw [h2] at h1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h3 : Real.exp (u / 2) * Real.exp (-u) = Real.exp (-(1 / 2) * u) := by
      rw [← Real.exp_add]; ring_nf
    calc Real.sqrt 2 * Real.exp (u / 2) * ‖𝓕 φ (Real.exp u)‖
        ≤ Real.sqrt 2 * Real.exp (u / 2) * (C * Real.exp (-u)) := by gcongr
      _ = Real.sqrt 2 * C * (Real.exp (u / 2) * Real.exp (-u)) := by ring
      _ = Real.sqrt 2 * C * Real.exp (-(1 / 2) * u) := by rw [h3]

/-- **`𝓕β(w) = ∫₁^∞ √2 y^{z-1} 𝓕φ(y) dy`** with `z = 1/2 - 2πiw`. -/
theorem fourier_betaF (w : ℝ) :
    𝓕 (betaF φ) w = ∫ y in Ioi 1, Gm φ (-2 * Real.pi * w) y := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have e1 : (fun u ↦ Complex.exp (↑(-2 * Real.pi * u * w) * Complex.I) • betaF φ u)
      = (Ioi 0).indicator (fun u ↦ Complex.exp (↑(-2 * Real.pi * u * w) * Complex.I)
          • (((Real.sqrt 2 * Real.exp (u / 2) : ℝ) : ℂ) * 𝓕 φ (Real.exp u))) := by
    funext u; unfold betaF
    by_cases hu : u ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hu, indicator_of_mem hu]
    · rw [indicator_of_notMem hu, indicator_of_notMem hu, smul_zero]
  rw [e1, integral_indicator measurableSet_Ioi]
  have h := integral_comp_exp_Ioi (Gm φ (-2 * Real.pi * w)) 0
  rw [Real.exp_zero] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
  simp only [Gm, smul_eq_mul, Complex.real_smul]
  rw [ofReal_exp_cpow]
  have hx : ((Real.exp u : ℝ) : ℂ) = Complex.exp (u : ℂ) := Complex.ofReal_exp u
  have hy : ((Real.sqrt 2 * Real.exp (u / 2) : ℝ) : ℂ)
      = ((Real.sqrt 2 : ℝ) : ℂ) * Complex.exp ((u : ℂ) / 2) := by
    push_cast; rfl
  rw [hx, hy]
  have hexp : Complex.exp (↑(-2 * Real.pi * u * w) * Complex.I) * Complex.exp ((u : ℂ) / 2)
      = Complex.exp (u : ℂ) * Complex.exp ((u : ℂ) * (zt (-2 * Real.pi * w) - 1)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1; unfold zt; push_cast; ring
  linear_combination (((Real.sqrt 2 : ℝ) : ℂ) * 𝓕 φ (Real.exp u)) * hexp

include hφ hφc hφ1 in
/-- `Y → ∞` in the truncated integral (dominated convergence, S3's `tendsto_integral_Psi`). -/
theorem tendsto_trunc (t : ℝ) :
    Tendsto (fun Y ↦ ∫ x in Ioi 0, φ x * (mz t x * (Gpart t 0 (x * Y) - Gpart t 0 x))) atTop
      (𝓝 (∫ x in Ioi 0, φ x * (mz t x * Phi t x))) := by
  have hφi := integrable_phi hφ hφc
  have hGc : ContinuousOn (Gpart t 0) (Ioi 0) := fun a ha ↦
    (hasDerivAt_Gpart (le_refl 0) ha).continuousAt.continuousWithinAt
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x ↦ ‖φ x‖ * (2 * (1 + ArchS3.Kt t))) ?_ ?_ (hφi.norm.mul_const _).integrableOn ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine hφ.continuous.continuousOn.mul ((continuousOn_cpow_zt _).mul (ContinuousOn.sub ?_ hGc))
    exact hGc.comp (continuous_id.mul continuous_const).continuousOn fun x hx ↦
      show (0 : ℝ) < x * Y from mul_pos hx (by linarith)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx ↦ ?_)
    have hx0 : (0 : ℝ) < x := hx
    by_cases h0 : φ x = 0
    · rw [h0]; simp
    · have hx1 : 1 < x := by
        by_contra h; apply h0; apply hφ1; rw [abs_of_pos hx0]; linarith
      rw [norm_mul, norm_mul, mz, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      have h1 : x ^ (-zt t).re ≤ 1 := by
        refine Real.rpow_le_one_of_one_le_of_nonpos hx1.le ?_
        simp [zt]
      have h2 := norm_Gpart_le (t := t) (show 1 ≤ x * Y by nlinarith)
      have h3 := norm_Gpart_le (t := t) hx1.le
      have h4 : ‖Gpart t 0 (x * Y) - Gpart t 0 x‖ ≤ 2 * (1 + ArchS3.Kt t) :=
        (norm_sub_le _ _).trans (by linarith)
      have h5 : 0 ≤ x ^ (-zt t).re := Real.rpow_nonneg hx0.le _
      calc ‖φ x‖ * (x ^ (-zt t).re * ‖Gpart t 0 (x * Y) - Gpart t 0 x‖)
          ≤ ‖φ x‖ * (1 * (2 * (1 + ArchS3.Kt t))) := by gcongr
        _ = ‖φ x‖ * (2 * (1 + ArchS3.Kt t)) := by ring
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx ↦ ?_)
    have hx0 : (0 : ℝ) < x := hx
    have hlim : Tendsto (fun Y ↦ Gpart t 0 (x * Y)) atTop (𝓝 (Psi (zt t))) := by
      have := (tendsto_integral_Psi t).comp (tendsto_id.const_mul_atTop hx0)
      exact this
    have := ((hlim.sub_const (Gpart t 0 x)).const_mul (mz t x)).const_mul (φ x)
    simpa [Phi] using this

include hφ hφc hφe hφ1 in
/-- `⟨κ_t, φ⟩ = √2 ∫_{x>0} φ(x) x^{-z} Φ_t(x) dx`. -/
theorem inner_kap_phi (hm : MemLp φ 2 volume) (t : ℝ) :
    ⟪kap t, hm.toLp φ⟫_ℂ = ((Real.sqrt 2 : ℝ) : ℂ) * ∫ x in Ioi 0, φ x * (mz t x * Phi t x) := by
  rw [MeasureTheory.L2.inner_def]
  set h : ℝ → ℂ := fun v ↦ conj (kapF t v) * φ v
  have e1 : (fun v ↦ ⟪(kap t : ℝ → ℂ) v, (hm.toLp φ : ℝ → ℂ) v⟫_ℂ) =ᵐ[volume] h := by
    filter_upwards [coeFn_kap t, hm.coeFn_toLp] with v e1 e2
    rw [e1, e2, RCLike.inner_apply']
  have hi : Integrable h := by
    have := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (kap t) (hm.toLp φ)
    exact this.congr e1
  rw [integral_congr_ae e1, integral_even_eq hi (Eventually.of_forall fun v ↦ by
    simp only [h, kapF_neg, hφe])]
  have e2 : ∀ x ∈ Ioi (0 : ℝ), h x = ((1 / Real.sqrt 2 : ℝ) : ℂ) * (φ x * (mz t x * Phi t x)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    simp only [h, kapF]
    by_cases hx1 : 1 < |x|
    · rw [indicator_of_mem (show x ∈ {v : ℝ | 1 < |v|} from hx1), Complex.conj_conj, kapG,
        abs_of_pos hx0]
      ring
    · rw [indicator_of_notMem (show x ∉ {v : ℝ | 1 < |v|} from hx1),
        hφ1 x (le_of_not_gt hx1)]
      simp
  rw [setIntegral_congr_fun measurableSet_Ioi e2, integral_const_mul, ← mul_assoc]
  congr 1
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have h2 : (2 : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul]
    congr 1
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
  exact h2

include hφ hφc hφe hφ1 in
/-- **The pointwise identity on the smooth class**: `𝓕β(w) = ⟨κ_{-2πw}, φ⟩` for every `w`. -/
theorem fourier_betaF_eq_inner (hm : MemLp φ 2 volume) (w : ℝ) :
    𝓕 (betaF φ) w = ⟪kap (-2 * Real.pi * w), hm.toLp φ⟫_ℂ := by
  set t := -2 * Real.pi * w
  rw [fourier_betaF, inner_kap_phi hφ hφc hφe hφ1 hm t]
  have h1 := intervalIntegral_tendsto_integral_Ioi 1 (integrableOn_Gm hφ hφc t) tendsto_id
  have h2 := (tendsto_trunc hφ hφc hφ1 t).const_mul ((Real.sqrt 2 : ℝ) : ℂ)
  have heq : ∀ᶠ Y in atTop, ∫ y in (1 : ℝ)..id Y, Gm φ t y
      = ((Real.sqrt 2 : ℝ) : ℂ) * ∫ x in Ioi 0, φ x * (mz t x * (Gpart t 0 (x * Y) - Gpart t 0 x)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
    exact integral_Gm_eq hφ hφc hφe t hY
  exact tendsto_nhds_unique (h1.congr' heq) h2

end Smooth

end ArchS7
