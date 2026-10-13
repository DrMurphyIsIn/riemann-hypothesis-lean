/-
  ArchS3_Limits -- the limit eps -> 0 of the exact damped identity, and CC Cor 2.3
  (2026-10-11, stage S3 milestones M2c part 2 and M3 of
  telperion/docs/ARCHIMEDEAN_CONCEPTUAL_BLUEPRINT_2026-10-11.md and ARCH_S3_NOTES.md section 2).

  From ArchS3_Quadrant.damped_identity, for every eps > 0,
      N_eps = Re(Psi'_eps conj Psi_eps) + R_eps + D_eps.
  Here we prove, as eps -> 0+:
    * N_eps -> Nnorm t = ∫_1^∞ |Phi_t(a)|^2 da/a           (dominated convergence, M2b bounds);
    * Re(Psi'_eps conj Psi_eps) -> psiR t - log pi            (M2a);
    * R_eps -> 0: J_eps(rho) = 2k/(k^2 + 4pi^2(rho-1)^2) + 2k/(k^2 + 4pi^2(rho+1)^2), k = eps(1+rho),
      and log rho · J_eps(rho) <= (1 + 2 log rho)/rho;
    * D_eps -> deltaHat t: I_eps(rho) -> ccDelta(rho)/sqrt rho with |I_eps(rho)| <= 16 (rho-1)^{-3/4},
      then rho = e^u.
  Hence THE MANIFEST-POSITIVITY IDENTITY  ell t = ∫_1^∞ |Phi_t(a)|^2 da/a  and  CC Cor 2.3: L >= 0.

  No zeros, no RH progress.  conjecture1_proved = False.
-/
import ArchS3_Quadrant

open MeasureTheory Filter Topology Complex Set
open scoped ComplexConjugate

noncomputable section

namespace ArchS3

/-! ## A. The kernel J_eps in closed form. -/

/-- 2cos(2 pi a)e^{-eps a} · 2cos(2 pi rho a)e^{-eps rho a}
      = 2 (cos(2pi(rho-1)a) + cos(2pi(rho+1)a)) e^{-eps(1+rho)a}. -/
lemma cosD_mul_cosD (ε a ρ : ℝ) :
    cosD ε a * cosD ε (ρ * a)
      = ((2 * (Real.cos (2 * Real.pi * (ρ - 1) * a) + Real.cos (2 * Real.pi * (ρ + 1) * a))
          * Real.exp (-(ε * (1 + ρ)) * a) : ℝ) : ℂ) := by
  unfold cosD
  rw [← Complex.ofReal_mul]
  congr 1
  have h1 : Real.exp (-ε * a) * Real.exp (-ε * (ρ * a)) = Real.exp (-(ε * (1 + ρ)) * a) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.cos (2 * Real.pi * a) * Real.cos (2 * Real.pi * (ρ * a))
      = (Real.cos (2 * Real.pi * (ρ - 1) * a) + Real.cos (2 * Real.pi * (ρ + 1) * a)) / 2 := by
    rw [mul_comm, cos_mul_cos_eq]
    rw [show 2 * Real.pi * (ρ * a) + 2 * Real.pi * a = 2 * Real.pi * (ρ + 1) * a by ring,
      show 2 * Real.pi * (ρ * a) - 2 * Real.pi * a = 2 * Real.pi * (ρ - 1) * a by ring]
    ring
  calc 2 * Real.cos (2 * Real.pi * a) * Real.exp (-ε * a)
        * (2 * Real.cos (2 * Real.pi * (ρ * a)) * Real.exp (-ε * (ρ * a)))
      = 4 * (Real.cos (2 * Real.pi * a) * Real.cos (2 * Real.pi * (ρ * a)))
          * (Real.exp (-ε * a) * Real.exp (-ε * (ρ * a))) := by ring
    _ = _ := by rw [h1, h2]; ring

lemma integrableOn_cos_exp {κ ω : ℝ} (hκ : 0 < κ) :
    IntegrableOn (fun a : ℝ => Real.cos (ω * a) * Real.exp (-κ * a)) (Ioi 0) := by
  refine (exp_neg_integrableOn_Ioi 0 hκ).mono' (by fun_prop : Continuous _).aestronglyMeasurable ?_
  refine Eventually.of_forall fun a => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (Real.abs_cos_le_one _)

/-- ∫_0^∞ cos(omega a) e^{-k a} da = k/(k^2 + omega^2). -/
lemma integral_cos_exp {κ ω : ℝ} (hκ : 0 < κ) :
    ∫ a in Ioi (0 : ℝ), Real.cos (ω * a) * Real.exp (-κ * a) = κ / (κ ^ 2 + ω ^ 2) := by
  set c : ℂ := -κ + ω * I
  have hc : c.re < 0 := by simp [c]; linarith
  have hint := integrableOn_exp_mul_complex_Ioi hc 0
  have hre : ∀ a : ℝ, Real.cos (ω * a) * Real.exp (-κ * a) = (cexp (c * a)).re := by
    intro a
    rw [show c * (a : ℂ) = ((-κ * a : ℝ) : ℂ) + ((ω * a : ℝ) : ℂ) * I by simp [c]; ring,
      Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  simp_rw [hre]
  have hI := integral_re hint
  simp only [RCLike.re_to_complex] at hI
  rw [hI, integral_exp_mul_complex_Ioi hc, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hc0 : c ≠ 0 := fun h => by rw [h] at hc; simp at hc
  have hn : Complex.normSq c = κ ^ 2 + ω ^ 2 := by simp [c, Complex.normSq_apply]; ring
  change (-1 / c).re = _
  rw [neg_div, Complex.neg_re, one_div, Complex.inv_re, hn]
  simp [c]
  ring

/-- The closed form of J_eps (as a real function). -/
def jfun (ε ρ : ℝ) : ℝ :=
  2 * (ε * (1 + ρ) / ((ε * (1 + ρ)) ^ 2 + (2 * Real.pi * (ρ - 1)) ^ 2)
    + ε * (1 + ρ) / ((ε * (1 + ρ)) ^ 2 + (2 * Real.pi * (ρ + 1)) ^ 2))

theorem Jd_eq {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) : Jd ε ρ = (jfun ε ρ : ℂ) := by
  have hκ : 0 < ε * (1 + ρ) := by positivity
  unfold Jd
  simp_rw [cosD_mul_cosD]
  rw [integral_complex_ofReal]
  congr 1
  have h1 := integrableOn_cos_exp (ω := 2 * Real.pi * (ρ - 1)) hκ
  have h2 := integrableOn_cos_exp (ω := 2 * Real.pi * (ρ + 1)) hκ
  have e : (fun a : ℝ => 2 * (Real.cos (2 * Real.pi * (ρ - 1) * a) + Real.cos (2 * Real.pi * (ρ + 1) * a))
      * Real.exp (-(ε * (1 + ρ)) * a))
      = fun a => 2 * (Real.cos (2 * Real.pi * (ρ - 1) * a) * Real.exp (-(ε * (1 + ρ)) * a)
          + Real.cos (2 * Real.pi * (ρ + 1) * a) * Real.exp (-(ε * (1 + ρ)) * a)) := by
    funext a; ring
  rw [e, integral_const_mul, integral_add h1 h2, integral_cos_exp hκ, integral_cos_exp hκ, jfun]

lemma jfun_nonneg {ε ρ : ℝ} (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) : 0 ≤ jfun ε ρ := by
  unfold jfun; positivity

/-- log rho · J_eps(rho) <= (1 + 2 log rho)/rho for 0 < eps <= 1, rho > 1. -/
lemma log_mul_jfun_le {ε ρ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hρ : 1 < ρ) :
    Real.log ρ * jfun ε ρ ≤ (1 + 2 * Real.log ρ) / ρ := by
  have hρ0 : 0 < ρ := lt_trans one_pos hρ
  have hlog : 0 ≤ Real.log ρ := Real.log_nonneg hρ.le
  have hpi := Real.pi_gt_three
  set κ := ε * (1 + ρ)
  have hκ : 0 < κ := by positivity
  have hκle : κ ≤ 1 + ρ := by simp only [κ]; nlinarith
  set ωm := 2 * Real.pi * (ρ - 1)
  set ωp := 2 * Real.pi * (ρ + 1)
  have hωm : 0 < ωm := by
    have : 0 < ρ - 1 := by linarith
    simp only [ωm]; positivity
  have hωp : 0 < ωp := by simp only [ωp]; positivity
  -- the (rho + 1) term
  have hTp : κ / (κ ^ 2 + ωp ^ 2) ≤ 1 / (2 * ρ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : ωp ^ 2 ≥ 36 * (ρ + 1) ^ 2 := by
      have h6 : 6 * (ρ + 1) ≤ ωp := by simp only [ωp]; nlinarith
      have := pow_le_pow_left₀ (by positivity) h6 2
      nlinarith
    nlinarith [sq_nonneg κ]
  -- the (rho - 1) term
  have hTm : Real.log ρ * (κ / (κ ^ 2 + ωm ^ 2)) ≤ (1 + Real.log ρ) / (2 * ρ) := by
    rcases le_or_gt ρ 2 with h2 | h2
    · have hl : Real.log ρ ≤ ρ - 1 := Real.log_le_sub_one_of_pos hρ0
      have hAM : 2 * κ * ωm ≤ κ ^ 2 + ωm ^ 2 := by nlinarith [sq_nonneg (κ - ωm)]
      have h1 : Real.log ρ * (κ / (κ ^ 2 + ωm ^ 2)) ≤ (ρ - 1) * (κ / (κ ^ 2 + ωm ^ 2)) :=
        mul_le_mul_of_nonneg_right hl (by positivity)
      have h2' : (ρ - 1) * (κ / (κ ^ 2 + ωm ^ 2)) ≤ 1 / (4 * Real.pi) := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
        have : ωm = 2 * Real.pi * (ρ - 1) := rfl
        nlinarith
      have h3 : 1 / (4 * Real.pi) ≤ (1 + Real.log ρ) / (2 * ρ) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
    · have hfrac : κ / (κ ^ 2 + ωm ^ 2) ≤ 1 / (2 * ρ) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hm : ωm ^ 2 ≥ 36 * (ρ - 1) ^ 2 := by
          have h6 : 6 * (ρ - 1) ≤ ωm := by simp only [ωm]; nlinarith
          have := pow_le_pow_left₀ (by linarith) h6 2
          nlinarith
        have : (ρ - 1) ^ 2 ≥ ρ ^ 2 / 4 := by nlinarith
        nlinarith [sq_nonneg κ]
      calc Real.log ρ * (κ / (κ ^ 2 + ωm ^ 2)) ≤ Real.log ρ * (1 / (2 * ρ)) :=
            mul_le_mul_of_nonneg_left hfrac hlog
        _ ≤ (1 + Real.log ρ) / (2 * ρ) := by
            rw [mul_one_div]; exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have : Real.log ρ * jfun ε ρ
      = 2 * (Real.log ρ * (κ / (κ ^ 2 + ωm ^ 2))) + 2 * (Real.log ρ * (κ / (κ ^ 2 + ωp ^ 2))) := by
    simp only [jfun, κ, ωm, ωp]; ring
  rw [this]
  have h4 : 2 * (Real.log ρ * (κ / (κ ^ 2 + ωp ^ 2))) ≤ Real.log ρ / ρ := by
    have := mul_le_mul_of_nonneg_left hTp hlog
    calc 2 * (Real.log ρ * (κ / (κ ^ 2 + ωp ^ 2))) ≤ 2 * (Real.log ρ * (1 / (2 * ρ))) := by linarith
      _ = Real.log ρ / ρ := by field_simp
  have h5 : 2 * (Real.log ρ * (κ / (κ ^ 2 + ωm ^ 2))) ≤ (1 + Real.log ρ) / ρ := by
    calc 2 * (Real.log ρ * (κ / (κ ^ 2 + ωm ^ 2))) ≤ 2 * ((1 + Real.log ρ) / (2 * ρ)) := by linarith
      _ = (1 + Real.log ρ) / ρ := by field_simp
  calc _ ≤ (1 + Real.log ρ) / ρ + Real.log ρ / ρ := add_le_add h5 h4
    _ = (1 + 2 * Real.log ρ) / ρ := by ring

/-- (1 + 2 log rho) rho^{-3/2} is integrable on (1, ∞). -/
lemma integrableOn_log_rpow : IntegrableOn (fun ρ : ℝ => (1 + 2 * Real.log ρ) * ρ ^ (-3 / 2 : ℝ)) (Ioi 1) := by
  have h1 := integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1) one_pos
  have h2 := integrableOn_Ioi_rpow_of_lt (by norm_num : (-5 / 4 : ℝ) < -1) one_pos
  refine ((h1.add (h2.const_mul 8))).mono' ?_ ?_
  · exact ((continuousOn_const.add (continuousOn_const.mul (Real.continuousOn_log.mono fun x hx =>
      (lt_trans one_pos (show (1 : ℝ) < x from hx)).ne'))).mul
      (continuousOn_id.rpow_const fun x hx => Or.inl (lt_trans one_pos
        (show (1 : ℝ) < x from hx)).ne')).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun ρ hρ => ?_)
    have hρ0 : (0 : ℝ) < ρ := lt_trans one_pos hρ
    have hlog : 0 ≤ Real.log ρ := Real.log_nonneg (le_of_lt hρ)
    have hl := Real.log_le_rpow_div hρ0.le (by norm_num : (0 : ℝ) < 1 / 4)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have e : ρ ^ (1 / 4 : ℝ) * ρ ^ (-3 / 2 : ℝ) = ρ ^ (-5 / 4 : ℝ) := by
      rw [← Real.rpow_add hρ0]; norm_num
    have hp : 0 < ρ ^ (-3 / 2 : ℝ) := by positivity
    simp only [Pi.add_apply]
    calc (1 + 2 * Real.log ρ) * ρ ^ (-3 / 2 : ℝ)
        = ρ ^ (-3 / 2 : ℝ) + 2 * (Real.log ρ * ρ ^ (-3 / 2 : ℝ)) := by ring
      _ ≤ ρ ^ (-3 / 2 : ℝ) + 2 * (ρ ^ (1 / 4 : ℝ) / (1 / 4) * ρ ^ (-3 / 2 : ℝ)) := by gcongr
      _ = ρ ^ (-3 / 2 : ℝ) + 8 * ρ ^ (-5 / 4 : ℝ) := by rw [← e]; ring

lemma norm_rpow_conj_zt {ρ : ℝ} (hρ : 0 < ρ) (t : ℝ) : ‖(ρ : ℂ) ^ (conj (zt t) - 1)‖ = ρ ^ (-1 / 2 : ℝ) := by
  rw [norm_cpow_eq_rpow_re_of_pos hρ]
  congr 1
  simp [zt]; norm_num

/-- R_eps -> 0. -/
theorem tendsto_R (t : ℝ) :
    Tendsto (fun ε => ∫ ρ in Ioi (1 : ℝ), (-(Real.log ρ : ℂ)) * (ρ : ℂ) ^ (conj (zt t) - 1) * Jd ε ρ)
      (𝓝[>] 0) (𝓝 0) := by
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  -- replace Jd by the closed form on (1, ∞)
  have hcongr : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∫ ρ in Ioi (1 : ℝ), (-(Real.log ρ : ℂ)) * (ρ : ℂ) ^ (conj (zt t) - 1) * Jd ε ρ
        = ∫ ρ in Ioi (1 : ℝ), (-(Real.log ρ : ℂ)) * (ρ : ℂ) ^ (conj (zt t) - 1) * (jfun ε ρ : ℂ) := by
    filter_upwards [hev] with ε hε
    refine setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
    rw [Jd_eq hε.1 (lt_trans one_pos hρ)]
  refine Tendsto.congr' (EventuallyEq.symm hcongr) ?_
  have hlim0 : (0 : ℂ) = ∫ ρ in Ioi (1 : ℝ),
      (-(Real.log ρ : ℂ)) * (ρ : ℂ) ^ (conj (zt t) - 1) * (jfun 0 ρ : ℂ) := by
    simp [jfun]
  rw [hlim0]
  have hcont_log : ContinuousOn (fun ρ : ℝ => (Real.log ρ : ℂ)) (Ioi 1) :=
    continuousOn_log_ofReal.mono (Ioi_subset_Ioi zero_le_one)
  have hcont_pow : ContinuousOn (fun ρ : ℝ => (ρ : ℂ) ^ (conj (zt t) - 1)) (Ioi 1) :=
    (continuousOn_ofReal_cpow _).mono (Ioi_subset_Ioi zero_le_one)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun ρ => (1 + 2 * Real.log ρ) * ρ ^ (-3 / 2 : ℝ)) ?_ ?_ integrableOn_log_rpow ?_
  · refine Eventually.of_forall fun ε => ?_
    have hj : ContinuousOn (fun ρ : ℝ => (jfun ε ρ : ℂ)) (Ioi 1) := by
      refine Complex.continuous_ofReal.comp_continuousOn ?_
      unfold jfun
      refine continuousOn_const.mul (ContinuousOn.add ?_ ?_)
      · refine ContinuousOn.div (by fun_prop) (by fun_prop) fun ρ hρ => ?_
        have : 0 < ρ - 1 := by linarith [show (1 : ℝ) < ρ from hρ]
        have : 0 < (2 * Real.pi * (ρ - 1)) ^ 2 := by positivity
        exact ne_of_gt (by nlinarith [sq_nonneg (ε * (1 + ρ))])
      · refine ContinuousOn.div (by fun_prop) (by fun_prop) fun ρ hρ => ?_
        have : 0 < ρ + 1 := by linarith [show (1 : ℝ) < ρ from hρ]
        have : 0 < (2 * Real.pi * (ρ + 1)) ^ 2 := by positivity
        exact ne_of_gt (by nlinarith [sq_nonneg (ε * (1 + ρ))])
    exact (((hcont_log.neg).mul hcont_pow).mul hj).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [hev] with ε hε
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun ρ hρ => ?_)
    have hρ1 : (1 : ℝ) < ρ := hρ
    have hρ0 : (0 : ℝ) < ρ := lt_trans one_pos hρ1
    have hlog : 0 ≤ Real.log ρ := Real.log_nonneg hρ1.le
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hlog, abs_of_nonneg (jfun_nonneg hε.1.le hρ0.le),
      norm_rpow_conj_zt hρ0]
    have hb := log_mul_jfun_le hε.1 hε.2.le hρ1
    have e : (1 + 2 * Real.log ρ) / ρ * ρ ^ (-1 / 2 : ℝ) = (1 + 2 * Real.log ρ) * ρ ^ (-3 / 2 : ℝ) := by
      rw [div_mul_eq_mul_div, mul_div_assoc, show (-3 / 2 : ℝ) = -1 / 2 + (-1) by norm_num,
        Real.rpow_add hρ0, Real.rpow_neg_one, div_eq_mul_inv]
    calc Real.log ρ * ρ ^ (-1 / 2 : ℝ) * jfun ε ρ = Real.log ρ * jfun ε ρ * ρ ^ (-1 / 2 : ℝ) := by ring
      _ ≤ (1 + 2 * Real.log ρ) / ρ * ρ ^ (-1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right hb (by positivity)
      _ = _ := e
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun ρ hρ => ?_)
    have hρ1 : (1 : ℝ) < ρ := hρ
    have hj : Continuous fun ε : ℝ => (jfun ε ρ : ℂ) := by
      refine Complex.continuous_ofReal.comp ?_
      unfold jfun
      have hm : 0 < (2 * Real.pi * (ρ - 1)) ^ 2 := by
        have : 0 < ρ - 1 := by linarith
        positivity
      have hp : 0 < (2 * Real.pi * (ρ + 1)) ^ 2 := by
        have : 0 < ρ + 1 := by linarith
        positivity
      refine continuous_const.mul (Continuous.add ?_ ?_)
      · exact Continuous.div (by fun_prop) (by fun_prop) fun ε =>
          ne_of_gt (by nlinarith [sq_nonneg (ε * (1 + ρ))])
      · exact Continuous.div (by fun_prop) (by fun_prop) fun ε =>
          ne_of_gt (by nlinarith [sq_nonneg (ε * (1 + ρ))])
    exact ((hj.tendsto 0).const_mul _).mono_left nhdsWithin_le_nhds

/-! ## B. The Delta part: the uniform bound on I_eps. -/

/-- |∫_0^1 (-log a) cos(omega a) e^{-k a} da| <= 4 (2/omega)^{3/4}, uniformly in k >= 0. -/
theorem logcos_bound {ω κ : ℝ} (hω : 0 < ω) (hκ : 0 ≤ κ) :
    |∫ a in (0 : ℝ)..1, (-Real.log a) * (Real.cos (ω * a) * Real.exp (-κ * a))|
      ≤ 4 * (2 / ω) ^ (3 / 4 : ℝ) := by
  set f : ℝ → ℝ := fun a => Real.cos (ω * a) * Real.exp (-κ * a)
  have hfc : Continuous f := by fun_prop
  have hf1 : ∀ a, 0 ≤ a → |f a| ≤ 1 := by
    intro a ha
    simp only [f]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_one₀ (Real.abs_cos_le_one _) (Real.exp_pos _).le
      (Real.exp_le_one_iff.mpr (by nlinarith))
  set e : ℝ → ℝ := fun a => ∫ r in (0 : ℝ)..1, f (a * r)
  have he_cont : Continuous e :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun a r => f (a * r)) (hfc.comp (continuous_fst.mul continuous_snd)) 0 1
  have hE : ∀ a, a * e a = ∫ s in (0 : ℝ)..a, f s := by
    intro a
    by_cases ha : a = 0
    · simp [ha]
    · simp only [e]
      rw [intervalIntegral.integral_comp_mul_left (f := f) ha, mul_zero, mul_one, smul_eq_mul,
        ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  -- the primitive trick: ∫_0^1 (-log a) f(a) = ∫_0^1 e(a)
  set H : ℝ → ℝ := fun a => -(a * e a) * Real.log a
  have hHc : ContinuousOn H (Icc 0 1) := by
    have : H = fun a => -e a * (a * Real.log a) := by funext a; simp only [H]; ring
    rw [this]
    exact (he_cont.neg.mul Real.continuous_mul_log).continuousOn
  have hHd : ∀ a ∈ Ioo (0 : ℝ) 1, HasDerivAt H (f a * (-Real.log a) - e a) a := by
    intro a ha
    have h1 : HasDerivAt (fun a => a * e a) (f a) a := by
      rw [show (fun a => a * e a) = fun a => ∫ s in (0 : ℝ)..a, f s from funext hE]
      exact (hfc.integral_hasStrictDerivAt 0 a).hasDerivAt
    have h := h1.neg.mul (Real.hasDerivAt_log ha.1.ne')
    refine h.congr_deriv ?_
    have ha0 : a ≠ 0 := ha.1.ne'
    have : a * e a * a⁻¹ = e a := by field_simp
    simp only [Pi.neg_apply, neg_mul, this]
    ring
  have hlogint : IntervalIntegrable (fun a => (-Real.log a) * f a) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_log'.neg).mul_continuousOn hfc.continuousOn
  have hint : IntervalIntegrable (fun a => f a * (-Real.log a) - e a) volume 0 1 :=
    (hlogint.congr (fun a _ => mul_comm _ _)).sub (he_cont.intervalIntegrable 0 1)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hHc hHd hint
  have hH0 : H 1 - H 0 = 0 := by simp [H]
  rw [hH0, intervalIntegral.integral_sub (hlogint.congr (fun a _ => mul_comm _ _))
    (he_cont.intervalIntegrable 0 1)] at hFTC
  have hswap : ∫ a in (0 : ℝ)..1, (-Real.log a) * f a = ∫ a in (0 : ℝ)..1, e a := by
    have : ∫ a in (0 : ℝ)..1, (-Real.log a) * f a = ∫ a in (0 : ℝ)..1, f a * (-Real.log a) := by
      congr 1; funext a; ring
    linarith
  change |∫ a in (0 : ℝ)..1, (-Real.log a) * f a| ≤ _
  rw [hswap]
  -- |∫_0^x f| <= 2/omega
  have hprim : ∀ x, 0 ≤ x → |∫ s in (0 : ℝ)..x, f s| ≤ 2 / ω := by
    intro x hx
    set c : ℂ := -κ + ω * I
    have hc0 : c ≠ 0 := fun h => by
      have := congrArg Complex.im h; simp [c] at this; linarith
    have hfre : ∀ s : ℝ, f s = (cexp (c * s)).re := by
      intro s
      simp only [f]
      rw [show c * (s : ℂ) = ((-κ * s : ℝ) : ℂ) + ((ω * s : ℝ) : ℂ) * I by simp [c]; ring,
        Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
        Complex.mul_im, Complex.I_re, Complex.I_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      ring
    have hI : ∫ s in (0 : ℝ)..x, f s = ((cexp (c * x) - 1) / c).re := by
      simp_rw [hfre]
      have := Complex.reCLM.intervalIntegral_comp_comm (μ := volume) (a := 0) (b := x)
        (f := fun s : ℝ => cexp (c * s)) ((by fun_prop : Continuous fun s : ℝ => cexp (c * s)).intervalIntegrable 0 x)
      simp only [Complex.reCLM_apply] at this
      rw [this, integral_exp_mul_complex hc0, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [hI]
    have hcn : ω ≤ ‖c‖ := by
      have := Complex.abs_im_le_norm c
      have hci : c.im = ω := by simp [c]
      rw [hci, abs_of_pos hω] at this
      exact this
    have hexp : ‖cexp (c * x)‖ ≤ 1 := by
      rw [Complex.norm_exp]
      exact Real.exp_le_one_iff.mpr (by simp [c, Complex.mul_re]; nlinarith)
    calc |((cexp (c * x) - 1) / c).re| ≤ ‖(cexp (c * x) - 1) / c‖ := Complex.abs_re_le_norm _
      _ = ‖cexp (c * x) - 1‖ / ‖c‖ := norm_div _ _
      _ ≤ 2 / ω := by
          rw [div_le_div_iff₀ (lt_of_lt_of_le hω hcn) hω]
          have : ‖cexp (c * x) - 1‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
          nlinarith [norm_nonneg (cexp (c * x) - 1)]
  -- pointwise bound on e
  have hebound : ∀ x ∈ Ioc (0 : ℝ) 1, ‖e x‖ ≤ (2 / ω) ^ (3 / 4 : ℝ) * x ^ (-3 / 4 : ℝ) := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have he1 : |e x| ≤ 1 := by
      simp only [e]
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := 1)
        (f := fun r => f (x * r)) (fun r hr => by
          rw [Real.norm_eq_abs]
          rw [uIoc_of_le zero_le_one] at hr
          exact hf1 _ (mul_nonneg hx0.le hr.1.le))
      simpa using this
    have he2 : |e x| ≤ 2 / (ω * x) := by
      have h := hprim x hx0.le
      rw [← hE x, abs_mul, abs_of_pos hx0] at h
      rw [div_mul_eq_div_div, le_div_iff₀ hx0]
      linarith
    set X := 2 / (ω * x)
    have hX0 : 0 < X := by positivity
    have hXr : X ^ (3 / 4 : ℝ) = (2 / ω) ^ (3 / 4 : ℝ) * x ^ (-3 / 4 : ℝ) := by
      rw [show X = (2 / ω) * x⁻¹ by simp only [X]; field_simp,
        Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hx0.le, ← Real.rpow_neg hx0.le]
      norm_num
    rw [Real.norm_eq_abs, ← hXr]
    rcases le_or_gt 1 X with h1 | h1
    · exact he1.trans (Real.one_le_rpow h1 (by norm_num))
    · calc |e x| ≤ X := he2
        _ = X ^ (1 : ℝ) := (Real.rpow_one X).symm
        _ ≤ X ^ (3 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hX0 h1.le (by norm_num)
  have hgint : IntervalIntegrable (fun x : ℝ => (2 / ω) ^ (3 / 4 : ℝ) * x ^ (-3 / 4 : ℝ)) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _
  have := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (Eventually.of_forall fun x hx => hebound x hx) hgint
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num)),
    Real.zero_rpow (by norm_num), Real.one_rpow]
  norm_num
  ring

lemma intervalIntegrable_neglog_mul {g : ℝ → ℝ} (hg : Continuous g) :
    IntervalIntegrable (fun a => (-Real.log a) * g a) volume 0 1 :=
  (intervalIntegral.intervalIntegrable_log'.neg).mul_continuousOn hg.continuousOn

/-- I_eps as a real integral. -/
lemma Id_eq_real (ε ρ : ℝ) :
    Id ε ρ = ((∫ a in (0 : ℝ)..1, (-Real.log a)
        * (2 * (Real.cos (2 * Real.pi * (ρ - 1) * a) + Real.cos (2 * Real.pi * (ρ + 1) * a))
          * Real.exp (-(ε * (1 + ρ)) * a)) : ℝ) : ℂ) := by
  unfold Id
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioc fun a _ => ?_
  rw [cosD_mul_cosD]
  push_cast
  ring

/-- |I_eps(rho)| <= 16 (rho - 1)^{-3/4}, uniformly in eps >= 0. -/
theorem norm_Id_le {ε ρ : ℝ} (hε : 0 ≤ ε) (hρ : 1 < ρ) : ‖Id ε ρ‖ ≤ 16 * (ρ - 1) ^ (-3 / 4 : ℝ) := by
  set κ := ε * (1 + ρ)
  have hκ : 0 ≤ κ := by simp only [κ]; nlinarith
  set ωm := 2 * Real.pi * (ρ - 1)
  set ωp := 2 * Real.pi * (ρ + 1)
  have hρ1 : 0 < ρ - 1 := by linarith
  have hωm : 0 < ωm := by simp only [ωm]; positivity
  have hωp : 0 < ωp := by simp only [ωp]; positivity
  have hsplit : ∫ a in (0 : ℝ)..1, (-Real.log a)
        * (2 * (Real.cos (ωm * a) + Real.cos (ωp * a)) * Real.exp (-κ * a))
      = 2 * (∫ a in (0 : ℝ)..1, (-Real.log a) * (Real.cos (ωm * a) * Real.exp (-κ * a)))
        + 2 * (∫ a in (0 : ℝ)..1, (-Real.log a) * (Real.cos (ωp * a) * Real.exp (-κ * a))) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add
        ((intervalIntegrable_neglog_mul (by fun_prop)).const_mul 2)
        ((intervalIntegrable_neglog_mul (by fun_prop)).const_mul 2)]
    congr 1; funext a; ring
  rw [Id_eq_real, Complex.norm_real, Real.norm_eq_abs]
  change |∫ a in (0 : ℝ)..1, (-Real.log a)
      * (2 * (Real.cos (ωm * a) + Real.cos (ωp * a)) * Real.exp (-κ * a))| ≤ _
  rw [hsplit]
  have b1 := logcos_bound hωm hκ
  have b2 := logcos_bound hωp hκ
  have hmono : (2 / ωp) ^ (3 / 4 : ℝ) ≤ (2 / ωm) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity)
      (div_le_div_of_nonneg_left (by norm_num) hωm (by simp only [ωm, ωp]; nlinarith [Real.pi_pos]))
      (by norm_num)
  have hm : (2 / ωm) ^ (3 / 4 : ℝ) ≤ (ρ - 1) ^ (-3 / 4 : ℝ) := by
    rw [show (-3 / 4 : ℝ) = -(3 / 4) by norm_num, Real.rpow_neg hρ1.le, ← Real.inv_rpow hρ1.le]
    refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
    rw [div_le_iff₀ hωm]
    simp only [ωm]
    have := Real.pi_gt_three
    field_simp
    nlinarith
  calc |2 * (∫ a in (0 : ℝ)..1, (-Real.log a) * (Real.cos (ωm * a) * Real.exp (-κ * a)))
        + 2 * (∫ a in (0 : ℝ)..1, (-Real.log a) * (Real.cos (ωp * a) * Real.exp (-κ * a)))|
      ≤ 2 * (4 * (2 / ωm) ^ (3 / 4 : ℝ)) + 2 * (4 * (2 / ωp) ^ (3 / 4 : ℝ)) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;>
        · rw [abs_mul, abs_two]; gcongr
    _ ≤ 16 * (ρ - 1) ^ (-3 / 4 : ℝ) := by nlinarith

/-! ## C. The Delta part: limit and value. -/

lemma integrableOn_neglog_Ioc : IntegrableOn (fun a : ℝ => -Real.log a) (Ioc 0 1) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp intervalIntegral.intervalIntegrable_log'.neg

lemma continuousOn_neglog_ofReal : ContinuousOn (fun a : ℝ => (-(Real.log a : ℂ))) (Ioc 0 1) :=
  (continuousOn_log_ofReal.mono Ioc_subset_Ioi_self).neg

lemma norm_Id_integrand_le {ε ρ a : ℝ} (hε : 0 ≤ ε) (ha : a ∈ Ioc (0 : ℝ) 1) (hρ : 0 ≤ ρ) :
    ‖(-(Real.log a : ℂ)) * (cosD ε a * cosD ε (ρ * a))‖ ≤ 4 * (-Real.log a) := by
  have hl : 0 ≤ -Real.log a := neg_nonneg.mpr (Real.log_nonpos ha.1.le ha.2)
  rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  have h1 := norm_cosD_le (s := a) hε ha.1.le
  have h2 := norm_cosD_le (s := ρ * a) hε (mul_nonneg hρ ha.1.le)
  have := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
  nlinarith

lemma continuous_Id (ε : ℝ) (hε : 0 ≤ ε) : ContinuousOn (fun ρ => Id ε ρ) (Ici 0) := by
  have h : Continuous fun ρ : ℝ => ∫ a in Ioc (0 : ℝ) 1,
      (-(Real.log a : ℂ)) * (cosD ε a * cosD ε (|ρ| * a)) := by
    refine continuous_of_dominated (bound := fun a => 4 * (-Real.log a)) ?_ ?_
      (integrableOn_neglog_Ioc.const_mul 4) ?_
    · intro ρ
      exact (continuousOn_neglog_ofReal.mul ((continuous_cosD ε).continuousOn.mul
        ((continuous_cosD ε).comp (continuous_const.mul continuous_id)).continuousOn)).aestronglyMeasurable
        measurableSet_Ioc
    · intro ρ
      exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun a ha =>
        norm_Id_integrand_le hε ha (abs_nonneg ρ))
    · exact Eventually.of_forall fun a => continuous_const.mul (continuous_const.mul
        ((continuous_cosD ε).comp (continuous_abs.mul continuous_const)))
  refine h.continuousOn.congr fun ρ hρ => ?_
  simp only [Id, abs_of_nonneg (show (0 : ℝ) ≤ ρ from hρ)]

/-- I_eps(rho) -> I_0(rho) as eps -> 0+. -/
lemma tendsto_Id {ρ : ℝ} (hρ : 0 ≤ ρ) : Tendsto (fun ε => Id ε ρ) (𝓝[>] 0) (𝓝 (Id 0 ρ)) := by
  unfold Id
  refine tendsto_integral_filter_of_dominated_convergence (fun a => 4 * (-Real.log a)) ?_ ?_
    (integrableOn_neglog_Ioc.const_mul 4) ?_
  · exact Eventually.of_forall fun ε =>
      (continuousOn_neglog_ofReal.mul ((continuous_cosD ε).continuousOn.mul
        ((continuous_cosD ε).comp (continuous_const.mul continuous_id)).continuousOn)).aestronglyMeasurable
        measurableSet_Ioc
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun a ha =>
      norm_Id_integrand_le (le_of_lt hε) ha hρ)
  · refine Eventually.of_forall fun a => ?_
    have hc : Continuous fun ε : ℝ => (-(Real.log a : ℂ)) * (cosD ε a * cosD ε (ρ * a)) := by
      unfold cosD; fun_prop
    exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- The dominating function 16 (rho - 1)^{-3/4} rho^{-1/2} is integrable on (1, ∞). -/
lemma integrableOn_Id_bound :
    IntegrableOn (fun ρ : ℝ => 16 * (ρ - 1) ^ (-3 / 4 : ℝ) * ρ ^ (-1 / 2 : ℝ)) (Ioi 1) := by
  have hcont : ContinuousOn (fun ρ : ℝ => 16 * (ρ - 1) ^ (-3 / 4 : ℝ) * ρ ^ (-1 / 2 : ℝ)) (Ioi 1) := by
    refine (continuousOn_const.mul ?_).mul ?_
    · exact (continuousOn_id.sub continuousOn_const).rpow_const fun x hx =>
        Or.inl (sub_ne_zero.mpr (ne_of_gt (show (1 : ℝ) < x from hx)))
    · exact continuousOn_id.rpow_const fun x hx => Or.inl (lt_trans one_pos (show (1 : ℝ) < x from hx)).ne'
  rw [← Ioc_union_Ioi_eq_Ioi (show (1 : ℝ) ≤ 2 by norm_num)]
  refine IntegrableOn.union ?_ ?_
  · have h0 : IntervalIntegrable (fun x : ℝ => x ^ (-3 / 4 : ℝ)) volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have h1 := (h0.comp_sub_right 1)
    simp only [zero_add, show (1 : ℝ) + 1 = 2 by norm_num] at h1
    have h2 : IntegrableOn (fun x : ℝ => (x - 1) ^ (-3 / 4 : ℝ)) (Ioc 1 2) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp h1
    refine (h2.const_mul 16).mono' ?_ ?_
    · exact (hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun ρ hρ => ?_)
      have hρ0 : 0 < ρ := lt_trans one_pos hρ.1
      have hp : 0 ≤ (ρ - 1) ^ (-3 / 4 : ℝ) := Real.rpow_nonneg (by linarith [hρ.1]) _
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have : ρ ^ (-1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hρ.1.le (by norm_num)
      nlinarith
  · have h2 := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-5 / 4 : ℝ) < -1) (by norm_num : (0 : ℝ) < 2))
    refine (h2.const_mul 32).mono' ?_ ?_
    · exact (hcont.mono (Ioi_subset_Ioi (by norm_num))).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun ρ hρ => ?_)
      have hρ2 : (2 : ℝ) < ρ := hρ
      have hρ0 : 0 < ρ := by linarith
      have hρ1 : 0 < ρ - 1 := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      -- (rho - 1)^{-3/4} <= (rho/2)^{-3/4} = 2^{3/4} rho^{-3/4} <= 2 rho^{-3/4}
      have h3 : (ρ - 1) ^ (-3 / 4 : ℝ) ≤ (ρ / 2) ^ (-3 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
      have h4 : (ρ / 2) ^ (-3 / 4 : ℝ) = 2 ^ (3 / 4 : ℝ) * ρ ^ (-3 / 4 : ℝ) := by
        rw [Real.div_rpow hρ0.le (by norm_num), show (-3 / 4 : ℝ) = -(3 / 4) by norm_num,
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        field_simp
      have h5 : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 := by
        calc (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2
      have h6 : ρ ^ (-3 / 4 : ℝ) * ρ ^ (-1 / 2 : ℝ) = ρ ^ (-5 / 4 : ℝ) := by
        rw [← Real.rpow_add hρ0]; norm_num
      have hp : 0 ≤ ρ ^ (-3 / 4 : ℝ) := by positivity
      have hq : 0 ≤ ρ ^ (-1 / 2 : ℝ) := by positivity
      calc 16 * (ρ - 1) ^ (-3 / 4 : ℝ) * ρ ^ (-1 / 2 : ℝ)
          ≤ 16 * (2 ^ (3 / 4 : ℝ) * ρ ^ (-3 / 4 : ℝ)) * ρ ^ (-1 / 2 : ℝ) := by
            rw [← h4]; gcongr
        _ ≤ 16 * (2 * ρ ^ (-3 / 4 : ℝ)) * ρ ^ (-1 / 2 : ℝ) := by gcongr
        _ = 32 * (ρ ^ (-3 / 4 : ℝ) * ρ ^ (-1 / 2 : ℝ)) := by ring
        _ = 32 * ρ ^ (-5 / 4 : ℝ) := by rw [h6]

/-- D_eps -> D_0. -/
theorem tendsto_D (t : ℝ) :
    Tendsto (fun ε => ∫ ρ in Ioi (1 : ℝ), (ρ : ℂ) ^ (conj (zt t) - 1) * Id ε ρ) (𝓝[>] 0)
      (𝓝 (∫ ρ in Ioi (1 : ℝ), (ρ : ℂ) ^ (conj (zt t) - 1) * Id 0 ρ)) := by
  have hcpow : ContinuousOn (fun ρ : ℝ => (ρ : ℂ) ^ (conj (zt t) - 1)) (Ioi 1) :=
    (continuousOn_ofReal_cpow _).mono (Ioi_subset_Ioi zero_le_one)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun ρ => 16 * (ρ - 1) ^ (-3 / 4 : ℝ) * ρ ^ (-1 / 2 : ℝ)) ?_ ?_ integrableOn_Id_bound ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hcpow.mul ((continuous_Id ε (le_of_lt hε)).mono fun x hx =>
      le_of_lt (lt_trans one_pos (show (1 : ℝ) < x from hx)))).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun ρ hρ => ?_)
    have hρ0 : (0 : ℝ) < ρ := lt_trans one_pos hρ
    rw [norm_mul, norm_rpow_conj_zt hρ0]
    have := norm_Id_le (le_of_lt (show (0 : ℝ) < ε from hε)) (show (1 : ℝ) < ρ from hρ)
    have hp : 0 ≤ ρ ^ (-1 / 2 : ℝ) := by positivity
    nlinarith
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun ρ hρ =>
      (tendsto_Id (le_of_lt (lt_trans one_pos (show (1 : ℝ) < ρ from hρ)))).const_mul _)

/-- I_0(rho) = ccDelta(rho)/sqrt(rho). -/
lemma Id_zero_eq {ρ : ℝ} (hρ : 0 < ρ) : Id 0 ρ = ((ccDelta ρ / Real.sqrt ρ : ℝ) : ℂ) := by
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have h4 : ccDelta ρ / Real.sqrt ρ = 4 * ∫ t in (0 : ℝ)..1,
      Real.cos (2 * Real.pi * ρ * t) * Real.cos (2 * Real.pi * t) * (-Real.log t) := by
    rw [ccDelta]; field_simp
  rw [h4, intervalIntegral.integral_of_le zero_le_one, ← integral_const_mul, ← integral_complex_ofReal]
  unfold Id
  refine setIntegral_congr_fun measurableSet_Ioc fun a _ => ?_
  unfold cosD
  rw [show 2 * Real.pi * (ρ * a) = 2 * Real.pi * ρ * a by ring]
  simp only [neg_zero, zero_mul, Real.exp_zero, mul_one]
  push_cast
  ring

lemma sqrt_exp (u : ℝ) : Real.sqrt (Real.exp u) = Real.exp (u / 2) := by
  rw [show Real.exp u = Real.exp (u / 2) ^ 2 by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring]
  exact Real.sqrt_sq (Real.exp_pos _).le

/-- THE VALUE: 2 Re ∫_1^∞ rho^{w-1} I_0(rho) d rho = deltaHat t. -/
theorem Dlimit_value (t : ℝ) :
    2 * (∫ ρ in Ioi (1 : ℝ), (ρ : ℂ) ^ (conj (zt t) - 1) * Id 0 ρ).re = deltaHat t := by
  -- substitution rho = e^u
  have hsub := integral_comp_exp_Ioi (fun ρ : ℝ => (ρ : ℂ) ^ (conj (zt t) - 1) * Id 0 ρ) 0
  rw [Real.exp_zero] at hsub
  rw [← hsub]
  have hpt : ∀ u ∈ Ioi (0 : ℝ), Real.exp u • ((Real.exp u : ℂ) ^ (conj (zt t) - 1) * Id 0 (Real.exp u))
      = (deltaK u : ℂ) * cexp (-((t * u : ℝ) : ℂ) * I) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    have hd : ccDelta (Real.exp u) = deltaK u := by rw [deltaK_eq_ccDelta, abs_of_pos hu0]
    rw [Id_zero_eq (Real.exp_pos u), sqrt_exp, hd, Complex.real_smul]
    · have hcp : ((Real.exp u : ℝ) : ℂ) ^ (conj (zt t) - 1) = cexp (u * (conj (zt t) - 1)) := by
        rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos u).ne'), Complex.ofReal_exp,
          Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]
      rw [hcp]
      have hw : conj (zt t) = 1 / 2 - (t : ℂ) * I := by
        apply Complex.ext <;> simp [zt]
      have hE : cexp (u : ℂ) * cexp (u * (conj (zt t) - 1))
          = cexp (-((t * u : ℝ) : ℂ) * I) * cexp ((u : ℂ) / 2) := by
        rw [← Complex.exp_add, ← Complex.exp_add, hw]
        congr 1; push_cast; ring
      have hne : cexp ((u : ℂ) / 2) ≠ 0 := Complex.exp_ne_zero _
      calc ((Real.exp u : ℝ) : ℂ) * (cexp (u * (conj (zt t) - 1)) * ((deltaK u / Real.exp (u / 2) : ℝ) : ℂ))
          = (cexp (u : ℂ) * cexp (u * (conj (zt t) - 1))) * (deltaK u : ℂ) / cexp ((u : ℂ) / 2) := by
            push_cast
            ring
        _ = (deltaK u : ℂ) * cexp (-((t * u : ℝ) : ℂ) * I) := by
            rw [hE]; field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  -- real part
  have hint : IntegrableOn (fun u : ℝ => (deltaK u : ℂ) * cexp (-((t * u : ℝ) : ℂ) * I)) (Ioi 0) := by
    refine (integrable_deltaK.abs.integrableOn).mono' ?_ ?_
    · exact ((Complex.continuous_ofReal.comp continuous_deltaK).mul (by fun_prop)).aestronglyMeasurable
    · refine Eventually.of_forall fun u => ?_
      rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
      simp
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [← hre]
  have hcos : ∀ u : ℝ, ((deltaK u : ℂ) * cexp (-((t * u : ℝ) : ℂ) * I)).re = deltaK u * Real.cos (t * u) := by
    intro u
    rw [Complex.re_ofReal_mul, show -((t * u : ℝ) : ℂ) * I = ((-(t * u) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  simp_rw [hcos]
  -- evenness: ∫_ℝ = 2 ∫_0^∞
  unfold deltaHat
  have hf : Integrable fun u => deltaK u * Real.cos (t * u) := integrable_deltaK_mul_cos t
  have hneg : ∫ u in Iic (0 : ℝ), deltaK u * Real.cos (t * u) = ∫ u in Ioi (0 : ℝ), deltaK u * Real.cos (t * u) := by
    have := integral_comp_neg_Ioi 0 (fun u => deltaK u * Real.cos (t * u))
    rw [neg_zero] at this
    rw [← this]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    simp only [deltaK_neg, mul_neg, Real.cos_neg]
  rw [← integral_add_compl measurableSet_Iic hf, compl_Iic, hneg]
  ring

/-! ## D. Assembly: ell = ∫_1^∞ |Phi_t|^2 da/a. -/

lemma normSq_div_bound {x : ℂ} {K a : ℝ} (ha : 0 < a) (hx : ‖x‖ ≤ K * a ^ (-1 / 2 : ℝ)) :
    ‖x‖ ^ 2 / a ≤ K ^ 2 * a ^ (-2 : ℝ) := by
  have hsq : ‖x‖ ^ 2 ≤ (K * a ^ (-1 / 2 : ℝ)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
  have e : (K * a ^ (-1 / 2 : ℝ)) ^ 2 / a = K ^ 2 * a ^ (-2 : ℝ) := by
    rw [mul_pow, ← Real.rpow_natCast (a ^ (-1 / 2 : ℝ)), ← Real.rpow_mul ha.le,
      show (-2 : ℝ) = (-1 / 2 * ((2 : ℕ) : ℝ)) + (-1) by norm_num, Real.rpow_add ha,
      Real.rpow_neg_one]
    field_simp
  rw [← e]
  exact div_le_div_of_nonneg_right hsq ha.le

/-- N_eps -> Nnorm t. -/
theorem tendsto_N (t : ℝ) :
    Tendsto (fun ε => ∫ a in Ioi (1 : ℝ), ‖PhiE t ε a‖ ^ 2 / a) (𝓝[>] 0) (𝓝 (Nnorm t)) := by
  unfold Nnorm
  refine tendsto_integral_filter_of_dominated_convergence (fun a => Kt t ^ 2 * a ^ (-2 : ℝ)) ?_ ?_
    ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).const_mul _) ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ((((continuousOn_PhiE (t := t) hε).mono (Ioi_subset_Ioi zero_le_one)).norm.pow 2).div
      continuousOn_id fun a ha => (lt_trans one_pos (show (1 : ℝ) < a from ha)).ne').aestronglyMeasurable
      measurableSet_Ioi
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun a ha => ?_)
    have ha0 : (0 : ℝ) < a := lt_trans one_pos ha
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact normSq_div_bound ha0 (norm_PhiE_le hε ha0)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun a ha => ?_)
    exact ((tendsto_PhiE (lt_trans one_pos (show (1 : ℝ) < a from ha))).norm.pow 2).div_const a

theorem tendsto_A (t : ℝ) :
    Tendsto (fun ε => (dPsiE ε (zt t) * conj (PsiE ε (zt t))).re) (𝓝[>] 0)
      (𝓝 (RvMBridge11.psiR t - Real.log Real.pi)) := by
  rw [← re_dPsi_mul_conj_Psi]
  have h := (tendsto_dPsiE (zt t)).mul
    ((Complex.continuous_conj.tendsto (Psi (zt t))).comp (tendsto_PsiE (zt t)))
  exact (Complex.continuous_re.tendsto _).comp h

/-- THE MANIFEST-POSITIVITY IDENTITY (CC Prop 2.2(iii), pointwise in the Mellin variable):
    ell t = psiR t - log pi + deltaHat t = ∫_1^∞ |Phi_t(a)|^2 da/a. -/
theorem ell_eq_Nnorm (t : ℝ) : ell t = Nnorm t := by
  have h1 := tendsto_N t
  have h2 : Tendsto (fun ε => (dPsiE ε (zt t) * conj (PsiE ε (zt t))).re
      + (∫ ρ in Ioi (1 : ℝ), (-(Real.log ρ : ℂ)) * (ρ : ℂ) ^ (conj (zt t) - 1) * Jd ε ρ).re
      + 2 * (∫ ρ in Ioi (1 : ℝ), (ρ : ℂ) ^ (conj (zt t) - 1) * Id ε ρ).re) (𝓝[>] 0)
      (𝓝 ((RvMBridge11.psiR t - Real.log Real.pi) + (0 : ℂ).re
        + 2 * (∫ ρ in Ioi (1 : ℝ), (ρ : ℂ) ^ (conj (zt t) - 1) * Id 0 ρ).re)) := by
    refine ((tendsto_A t).add ((Complex.continuous_re.tendsto _).comp (tendsto_R t))).add ?_
    exact ((Complex.continuous_re.tendsto _).comp (tendsto_D t)).const_mul 2
  have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∫ a in Ioi (1 : ℝ), ‖PhiE t ε a‖ ^ 2 / a
      = (dPsiE ε (zt t) * conj (PsiE ε (zt t))).re
        + (∫ ρ in Ioi (1 : ℝ), (-(Real.log ρ : ℂ)) * (ρ : ℂ) ^ (conj (zt t) - 1) * Jd ε ρ).re
        + 2 * (∫ ρ in Ioi (1 : ℝ), (ρ : ℂ) ^ (conj (zt t) - 1) * Id ε ρ).re := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact damped_identity hε
  have := tendsto_nhds_unique (h1.congr' heq) h2
  rw [Dlimit_value, Complex.zero_re, add_zero] at this
  rw [this, ell]

/-! ## E. M3: CC Corollary 2.3. -/

/-- ell >= 0: CC Cor 2.3 (ii), as a squared norm. -/
theorem ell_nonneg (t : ℝ) : 0 ≤ ell t := by
  rw [ell_eq_Nnorm]; exact Nnorm_nonneg t

/-- L(g * g^*) = (1/2pi) ∫ |g^(r)|^2 ‖A e_r‖^2 dr: the HS norm in the Mellin diagonalisation. -/
theorem Lfun_eq_integral_Nnorm {g : ℝ → ℂ} (hg : WeilExplicit.IsWeilTest g) :
    Lfun g = (1 / (2 * Real.pi)) * ∫ r : ℝ, RvMBridge31.hsq g r * Nnorm r := by
  rw [Lfun_eq_integral_ell hg]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only [ell_eq_Nnorm]

/-- CONNES-CONSANI COROLLARY 2.3 in our conventions: for every test function g of ANY support,
    W_inf(g * g^*) + D(g * g^*) >= 0. -/
theorem cc_cor_2_3 {g : ℝ → ℂ} (hg : WeilExplicit.IsWeilTest g) : 0 ≤ Lfun g :=
  Lfun_nonneg_of_ell_nonneg ell_nonneg hg

/-- The same in u-space: (psiR 0 - log pi)||g||^2 + (1/2)∫∫|Δg|^2 k + <g, K_delta g> >= 0. -/
theorem cc_cor_2_3_dirichlet {g : ℝ → ℂ} (hg : WeilExplicit.IsWeilTest g) :
    0 ≤ (RvMBridge11.psiR 0 - Real.log Real.pi) * RvMBridge31.mass g
      + (1 / 2) * ∫ z : ℝ × ℝ, ‖g z.1 - g z.2‖ ^ 2 * ArchS1.archK (z.1 - z.2) ∂(volume.prod volume)
      + Dfun g := by
  rw [← Lfun_eq_dirichlet hg]; exact cc_cor_2_3 hg

/-- On the pole-free class in the window 2L <= log 2: Re weilForm(g * g^*) + D(g * g^*) >= 0. -/
theorem weilForm_add_Dfun_nonneg {g : ℝ → ℂ} (hg : WeilExplicit.IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) (hL : 2 * L ≤ Real.log 2)
    (h0 : Zeta23.paperFT g (I / 2) = 0) :
    0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re + Dfun g := by
  rw [re_weilForm_eq_archW hg hsupp hL h0]
  exact cc_cor_2_3 hg

end ArchS3
