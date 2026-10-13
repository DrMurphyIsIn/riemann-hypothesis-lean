/-
  ArchS3_Quadrant -- the exact damped identity (2026-10-11, stage S3 milestone M2c, part 1, of
  telperion/docs/ARCHIMEDEAN_CONCEPTUAL_BLUEPRINT_2026-10-11.md and ARCH_S3_NOTES.md section 2).

  Fix t, eps > 0, z = 1/2 + i t, w = conj z = 1 - z, P(a) = a^{z-1} 2cos(2 pi a) e^{-eps a}, Q = conj P,
  Phi_eps(a) = ∫_a^∞ P, Psi_eps = ∫_0^∞ P, Psi'_eps = ∫_0^∞ log · P.  Every integral converges absolutely.

    (A)  N_eps := ∫_1^∞ |Phi_eps|^2 da/a = 2 Re ∫_1^∞ log a P(a) conj Phi_eps(a) da       (IBP, v = log)
    (B)  Psi'_eps conj Psi_eps = U(0,∞) + U_2,   conj U_2 = V                            (quadrant swap)
    (C1) U(0,∞) - V = ∫_1^∞ (-log rho) rho^{w-1} J_eps(rho) d rho                        (s = rho a)
    (C2) U(0,1] = -∫_1^∞ rho^{w-1} I_eps(rho) d rho                                       (s = rho a)
  hence the EXACT DAMPED IDENTITY

    N_eps = Re(Psi'_eps conj Psi_eps) + Re ∫_1^∞ (-log rho) rho^{w-1} J_eps
            + 2 Re ∫_1^∞ rho^{w-1} I_eps,

  J_eps(rho) = ∫_0^∞ C_eps(a) C_eps(rho a) da,  I_eps(rho) = ∫_0^1 (-log a) C_eps(a) C_eps(rho a) da.

  No zeros, no RH progress.  conjecture1_proved = False.
-/
import ArchS3_Phi

open MeasureTheory Filter Topology Complex Set
open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace ArchS3

/-! ## A. Conjugates, bounds, derivative of Phi_eps. -/

lemma conj_cosD (ε s : ℝ) : conj (cosD ε s) = cosD ε s := Complex.conj_ofReal _

lemma zt_add_conj (t : ℝ) : zt t + conj (zt t) = 1 := by
  apply Complex.ext <;> simp [zt]; norm_num

/-- Q = conj P. -/
def Qd (t ε s : ℝ) : ℂ := conj (pD t ε s)

lemma conj_cpow_ofReal {s : ℝ} (hs : 0 ≤ s) (n : ℂ) : conj ((s : ℂ) ^ n) = (s : ℂ) ^ (conj n) := by
  rw [cpow_conj _ _ (by rw [arg_ofReal_of_nonneg hs]; exact Real.pi_pos.ne), Complex.conj_ofReal]

lemma Qd_eq {t ε s : ℝ} (hs : 0 ≤ s) : Qd t ε s = (s : ℂ) ^ (conj (zt t) - 1) * cosD ε s := by
  unfold Qd pD
  rw [map_mul, conj_cosD, conj_cpow_ofReal hs, map_sub, map_one]

lemma norm_cosD_le_exp {ε s : ℝ} : ‖cosD ε s‖ ≤ 2 * Real.exp (-ε * s) := by
  unfold cosD
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_two, abs_of_pos (Real.exp_pos _)]
  have h1 := Real.abs_cos_le_one (2 * Real.pi * s)
  nlinarith [Real.exp_pos (-ε * s)]

lemma norm_pD_le_exp {t ε s : ℝ} (hs : 0 < s) :
    ‖pD t ε s‖ ≤ 2 * s ^ (-1 / 2 : ℝ) * Real.exp (-ε * s) := by
  unfold pD
  rw [norm_mul, norm_cpow_zt hs]
  have := norm_cosD_le_exp (ε := ε) (s := s)
  calc s ^ (-1 / 2 : ℝ) * ‖cosD ε s‖ ≤ s ^ (-1 / 2 : ℝ) * (2 * Real.exp (-ε * s)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

lemma norm_Qd {t ε s : ℝ} : ‖Qd t ε s‖ = ‖pD t ε s‖ := by unfold Qd; exact Complex.norm_conj _

lemma hasDerivAt_PhiE {t ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    HasDerivAt (PhiE t ε) (-pD t ε a) a := by
  have h := (hasDerivAt_const a (PsiE ε (zt t))).sub (hasDerivAt_Gpart (t := t) hε.le ha)
  rw [zero_sub] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ha] with b hb
  exact PhiE_eq hε hb

lemma continuousOn_PhiE {t ε : ℝ} (hε : 0 < ε) : ContinuousOn (PhiE t ε) (Ioi 0) :=
  fun _ ha => (hasDerivAt_PhiE hε ha).continuousAt.continuousWithinAt

/-- Phi_eps is bounded on (0, ∞). -/
lemma norm_PhiE_le_M {t ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    ‖PhiE t ε a‖ ≤ ‖PsiE ε (zt t)‖ + 4 + Kt t := by
  rcases le_or_gt a 1 with h1 | h1
  · rw [PhiE_eq hε ha]
    have hG := norm_Gpart_le (t := t) hε.le ha.le
    have hs : Real.sqrt a ≤ 1 := Real.sqrt_le_one.mpr h1
    have := norm_sub_le (PsiE ε (zt t)) (Gpart t ε a)
    nlinarith [Kt_nonneg t]
  · have h := norm_PhiE_le (t := t) hε ha
    have hr : a ^ (-1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1.le (by norm_num)
    have := mul_le_mul_of_nonneg_left hr (Kt_nonneg t)
    nlinarith [norm_nonneg (PsiE ε (zt t))]

/-! ## B. Step (A): integration by parts against log. -/

lemma log_div_le_one {a : ℝ} (ha : 1 ≤ a) : Real.log a / a ≤ 1 := by
  have h0 : 0 < a := by linarith
  rw [div_le_one h0]
  exact (Real.log_le_sub_one_of_pos h0).trans (by linarith)

/-- (A) N_eps = 2 Re ∫_1^∞ log a · P(a) · conj Phi_eps(a) da. -/
theorem stepA {t ε : ℝ} (hε : 0 < ε) :
    ∫ a in Ioi (1 : ℝ), ‖PhiE t ε a‖ ^ 2 / a
      = 2 * (∫ a in Ioi (1 : ℝ), (Real.log a : ℂ) * pD t ε a * conj (PhiE t ε a)).re := by
  set K := Kt t
  set u : ℝ → ℝ := fun a => ‖PhiE t ε a‖ ^ 2
  set u' : ℝ → ℝ := fun a => 2 * ⟪PhiE t ε a, -pD t ε a⟫_ℝ
  have hu : ∀ a ∈ Ioi (1 : ℝ), HasDerivAt u (u' a) a := fun a ha =>
    (hasDerivAt_PhiE (t := t) hε (lt_trans zero_lt_one ha)).norm_sq
  have hv : ∀ a ∈ Ioi (1 : ℝ), HasDerivAt Real.log (a⁻¹) a := fun a ha =>
    Real.hasDerivAt_log (lt_trans zero_lt_one ha).ne'
  have hPhiK : ∀ a, 0 < a → ‖PhiE t ε a‖ ≤ K * a ^ (-1 / 2 : ℝ) := fun a ha => norm_PhiE_le hε ha
  -- pointwise bounds
  have hb1 : ∀ a ∈ Ioi (1 : ℝ), ‖u a * a⁻¹‖ ≤ K ^ 2 * a ^ (-2 : ℝ) := by
    intro a ha
    have ha0 : (0 : ℝ) < a := lt_trans zero_lt_one ha
    have hsq : ‖PhiE t ε a‖ ^ 2 ≤ (K * a ^ (-1 / 2 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hPhiK a ha0) 2
    have e : (K * a ^ (-1 / 2 : ℝ)) ^ 2 * a⁻¹ = K ^ 2 * a ^ (-2 : ℝ) := by
      rw [mul_pow, ← Real.rpow_natCast (a ^ (-1 / 2 : ℝ)), ← Real.rpow_mul ha0.le,
        show (-2 : ℝ) = (-1 / 2 * ((2 : ℕ) : ℝ)) + (-1) by norm_num, Real.rpow_add ha0,
        Real.rpow_neg_one]
      ring
    rw [Real.norm_eq_abs, abs_of_nonneg (by simp only [u]; positivity), ← e]
    exact mul_le_mul_of_nonneg_right hsq (by positivity)
  have hb2 : ∀ a ∈ Ioi (1 : ℝ), ‖(Real.log a : ℂ) * pD t ε a * conj (PhiE t ε a)‖
      ≤ 2 * K * Real.exp (-ε * a) := by
    intro a ha
    have ha0 : (0 : ℝ) < a := lt_trans zero_lt_one ha
    have hlog : 0 ≤ Real.log a := Real.log_nonneg ha.le
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
    have hP := norm_pD_le_exp (t := t) (ε := ε) ha0
    have hF := hPhiK a ha0
    have hprod : a ^ (-1 / 2 : ℝ) * a ^ (-1 / 2 : ℝ) = a⁻¹ := by
      rw [← Real.rpow_add ha0]; norm_num; exact Real.rpow_neg_one a
    have hld := log_div_le_one ha.le
    have hK := Kt_nonneg t
    calc Real.log a * ‖pD t ε a‖ * ‖PhiE t ε a‖
        ≤ Real.log a * (2 * a ^ (-1 / 2 : ℝ) * Real.exp (-ε * a)) * (K * a ^ (-1 / 2 : ℝ)) := by
          gcongr
      _ = 2 * K * Real.exp (-ε * a) * (Real.log a * (a ^ (-1 / 2 : ℝ) * a ^ (-1 / 2 : ℝ))) := by ring
      _ = 2 * K * Real.exp (-ε * a) * (Real.log a / a) := by rw [hprod, div_eq_mul_inv]
      _ ≤ 2 * K * Real.exp (-ε * a) * 1 := by gcongr
      _ = _ := by ring
  have hcP : ContinuousOn (PhiE t ε) (Ioi 1) := (continuousOn_PhiE hε).mono (Ioi_subset_Ioi zero_le_one)
  have hcp : ContinuousOn (pD t ε) (Ioi 1) := (continuousOn_pD t ε).mono (Ioi_subset_Ioi zero_le_one)
  have hcl : ContinuousOn Real.log (Ioi 1) :=
    Real.continuousOn_log.mono fun a ha => (lt_trans zero_lt_one ha).ne'
  have hf_int : IntegrableOn (fun a : ℝ => (Real.log a : ℂ) * pD t ε a * conj (PhiE t ε a)) (Ioi 1) := by
    refine ((exp_neg_integrableOn_Ioi 1 hε).const_mul (2 * K)).mono' ?_ ?_
    · exact (((Complex.continuous_ofReal.comp_continuousOn hcl).mul hcp).mul
        (Complex.continuous_conj.comp_continuousOn hcP)).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun a ha => ?_)
      have := hb2 a ha
      simpa [neg_mul] using this
  have huv' : IntegrableOn (u * fun a => a⁻¹) (Ioi 1) := by
    refine ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).const_mul (K ^ 2)).mono'
      ?_ ?_
    · exact ((hcP.norm.pow 2).mul (continuousOn_inv₀.mono fun a ha =>
        (lt_trans zero_lt_one ha).ne')).aestronglyMeasurable measurableSet_Ioi
    · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun a ha => hb1 a ha)
  -- u' * log = -2 Re (log · P · conj Phi)
  have hu'v_eq : ∀ a, u' a * Real.log a
      = -(2 * ((Real.log a : ℂ) * pD t ε a * conj (PhiE t ε a)).re) := by
    intro a
    simp only [u', Complex.inner, inner_neg_right]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, add_zero, Complex.conj_re, Complex.conj_im]
    ring
  have hu'v : IntegrableOn (u' * Real.log) (Ioi 1) := by
    have h0 : IntegrableOn (fun a : ℝ => -(2 * ((Real.log a : ℂ) * pD t ε a * conj (PhiE t ε a)).re))
        (Ioi 1) := (hf_int.re.const_mul 2).neg
    refine h0.congr_fun (fun a _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply]
    rw [hu'v_eq]
  have h_zero : Tendsto (u * Real.log) (𝓝[>] 1) (𝓝 0) := by
    have hc : ContinuousAt (fun a => u a * Real.log a) 1 := by
      have h1 : ContinuousAt (PhiE t ε) 1 := (hasDerivAt_PhiE (t := t) hε one_pos).continuousAt
      exact (h1.norm.pow 2).mul (Real.continuousAt_log one_ne_zero)
    have := hc.tendsto
    rw [Real.log_one, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h_infty : Tendsto (u * Real.log) atTop (𝓝 0) := by
    have hlim : Tendsto (fun a : ℝ => K ^ 2 * (Real.log a ^ 1 / (1 * a + 0))) atTop (𝓝 (K ^ 2 * 0)) :=
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).const_mul _
    rw [mul_zero] at hlim
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop 1] with a ha
    have ha0 : (0 : ℝ) < a := lt_trans zero_lt_one ha
    have := hb1 a ha
    have hlog : 0 ≤ Real.log a := Real.log_nonneg ha.le
    rw [Pi.mul_apply, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by simp only [u]; positivity) hlog)]
    have e : K ^ 2 * a ^ (-2 : ℝ) * a = K ^ 2 * a⁻¹ := by
      rw [mul_assoc, ← Real.rpow_add_one ha0.ne', show (-2 : ℝ) + 1 = -1 by norm_num,
        Real.rpow_neg_one]
    have hua : u a ≤ K ^ 2 * a⁻¹ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by simp only [u]; positivity)] at this
      have := mul_le_mul_of_nonneg_right this ha0.le
      rwa [mul_assoc, inv_mul_cancel₀ ha0.ne', mul_one, e] at this
    calc u a * Real.log a ≤ K ^ 2 * a⁻¹ * Real.log a := mul_le_mul_of_nonneg_right hua hlog
      _ = K ^ 2 * (Real.log a ^ 1 / (1 * a + 0)) := by ring
  have hIBP := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h_zero h_infty
  have hL : ∫ a in Ioi (1 : ℝ), ‖PhiE t ε a‖ ^ 2 / a = ∫ a in Ioi (1 : ℝ), u a * a⁻¹ := by
    refine setIntegral_congr_fun measurableSet_Ioi fun a _ => ?_
    simp only [u, div_eq_mul_inv]
  rw [hL, hIBP, sub_zero, zero_sub]
  have hR : ∫ a in Ioi (1 : ℝ), u' a * Real.log a
      = -(2 * ∫ a in Ioi (1 : ℝ), ((Real.log a : ℂ) * pD t ε a * conj (PhiE t ε a)).re) := by
    rw [← integral_const_mul, ← integral_neg]
    exact setIntegral_congr_fun measurableSet_Ioi fun a _ => hu'v_eq a
  rw [hR, neg_neg]
  congr 1
  exact integral_re hf_int

/-! ## C. Integrability toolkit on (0, ∞). -/

lemma integrable_conj' {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {f : α → ℂ}
    (hf : Integrable f μ) : Integrable (fun x => conj (f x)) μ :=
  hf.mono (Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    (Eventually.of_forall fun x => by simp)

lemma integrableOn_Qd {t ε : ℝ} (hε : 0 < ε) : IntegrableOn (Qd t ε) (Ioi 0) :=
  integrable_conj' (integrableOn_pD hε)

lemma integrableOn_logpD {t ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun a : ℝ => (Real.log a : ℂ) * pD t ε a) (Ioi 0) :=
  (integrableOn_log_cosD hε (z := zt t) (by rw [zt_re]; norm_num)).congr_fun
    (fun s _ => by simp only [pD]; ring) measurableSet_Ioi

lemma integrableOn_logQd {t ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun s : ℝ => (Real.log s : ℂ) * Qd t ε s) (Ioi 0) :=
  IntegrableOn.congr_fun (integrable_conj' (integrableOn_logpD (t := t) hε))
    (fun s _ => by simp [Qd, map_mul, Complex.conj_ofReal]) measurableSet_Ioi

lemma continuousOn_Qd (t ε : ℝ) : ContinuousOn (Qd t ε) (Ioi 0) :=
  Complex.continuous_conj.comp_continuousOn (continuousOn_pD t ε)

/-- The kernel identity behind the substitution s = rho a:
P(a) · a · Q(a rho) = rho^{w-1} C(a) C(rho a), because a^{z-1} a^{w-1} a = a^{z+w-1} = 1. -/
lemma kernel_eq {t ε a ρ : ℝ} (ha : 0 < a) (hρ : 0 < ρ) :
    pD t ε a * ((a : ℂ) * Qd t ε (a * ρ))
      = (ρ : ℂ) ^ (conj (zt t) - 1) * (cosD ε a * cosD ε (ρ * a)) := by
  rw [Qd_eq (by positivity), pD, Complex.ofReal_mul, mul_cpow_ofReal_nonneg ha.le hρ.le, mul_comm ρ a]
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have hz : (a : ℂ) ^ (zt t - 1) * (a : ℂ) ^ (conj (zt t) - 1) * (a : ℂ) = 1 := by
    rw [← cpow_add _ _ ha0, show zt t - 1 + (conj (zt t) - 1) = -1 by
      linear_combination zt_add_conj t, cpow_neg_one]
    field_simp
  calc (a : ℂ) ^ (zt t - 1) * cosD ε a
        * ((a : ℂ) * ((a : ℂ) ^ (conj (zt t) - 1) * (ρ : ℂ) ^ (conj (zt t) - 1) * cosD ε (a * ρ)))
      = ((a : ℂ) ^ (zt t - 1) * (a : ℂ) ^ (conj (zt t) - 1) * (a : ℂ))
          * ((ρ : ℂ) ^ (conj (zt t) - 1) * (cosD ε a * cosD ε (a * ρ))) := by ring
    _ = _ := by rw [hz, one_mul]

/-! ## D. The generic substitution-and-swap lemma. -/

/-- ∫_{a ∈ A} P(a) ∫_{s > a} h(a,s) Q(s) ds da
      = ∫_{rho > 1} rho^{w-1} ∫_{a ∈ A} h(a, a rho) C(a) C(rho a) da d rho. -/
theorem subst_swap {t ε : ℝ} {A : Set ℝ} (hA : MeasurableSet A) (hA0 : A ⊆ Ioi 0) (h : ℝ → ℝ → ℂ)
    (hc : ContinuousOn (fun p : ℝ × ℝ => h p.1 (p.1 * p.2)) (Ioi 0 ×ˢ Ioi 1))
    (hin : ∀ a ∈ A, IntegrableOn (fun s => h a s * Qd t ε s) (Ioi a))
    (B : ℝ → ℝ) (hB : IntegrableOn B A)
    (hbound : ∀ a ∈ A, ‖pD t ε a‖ * ∫ s in Ioi a, ‖h a s * Qd t ε s‖ ≤ B a) :
    ∫ a in A, pD t ε a * ∫ s in Ioi a, h a s * Qd t ε s
      = ∫ ρ in Ioi (1 : ℝ), (ρ : ℂ) ^ (conj (zt t) - 1)
          * ∫ a in A, h a (a * ρ) * (cosD ε a * cosD ε (ρ * a)) := by
  set w := conj (zt t)
  set Fk : ℝ → ℝ → ℂ := fun a ρ => (ρ : ℂ) ^ (w - 1) * (h a (a * ρ) * (cosD ε a * cosD ε (ρ * a)))
  -- the substitution, pointwise in a
  have hcv : ∀ a, 0 < a → ∀ g : ℝ → ℂ, ∫ s in Ioi a, g s = (a : ℂ) * ∫ x in Ioi (1 : ℝ), g (a * x) := by
    intro a ha g
    have := integral_comp_mul_left_Ioi g 1 ha
    rw [mul_one] at this
    rw [this, Complex.real_smul, ← mul_assoc, ofReal_inv, mul_inv_cancel₀ (ofReal_ne_zero.mpr ha.ne'),
      one_mul]
  have hcvR : ∀ a, 0 < a → ∀ g : ℝ → ℝ, ∫ s in Ioi a, g s = a * ∫ x in Ioi (1 : ℝ), g (a * x) := by
    intro a ha g
    have := integral_comp_mul_left_Ioi g 1 ha
    rw [mul_one] at this
    rw [this, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
  have hFk : ∀ a, 0 < a → ∀ ρ, 0 < ρ → Fk a ρ = pD t ε a * ((a : ℂ) * (h a (a * ρ) * Qd t ε (a * ρ))) := by
    intro a ha ρ hρ
    have := kernel_eq (t := t) (ε := ε) ha hρ
    simp only [Fk]
    calc (ρ : ℂ) ^ (w - 1) * (h a (a * ρ) * (cosD ε a * cosD ε (ρ * a)))
        = h a (a * ρ) * ((ρ : ℂ) ^ (w - 1) * (cosD ε a * cosD ε (ρ * a))) := by ring
      _ = h a (a * ρ) * (pD t ε a * ((a : ℂ) * Qd t ε (a * ρ))) := by rw [this]
      _ = _ := by ring
  have hsub : ∀ a ∈ A, pD t ε a * ∫ s in Ioi a, h a s * Qd t ε s = ∫ ρ in Ioi (1 : ℝ), Fk a ρ := by
    intro a haA
    have ha : 0 < a := hA0 haA
    rw [hcv a ha, ← mul_assoc, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
    rw [hFk a ha ρ (lt_trans one_pos hρ)]
    ring
  rw [setIntegral_congr_fun hA hsub]
  -- integrability of Fk on A × (1, ∞)
  have hcont : ContinuousOn (Function.uncurry Fk) (A ×ˢ Ioi 1) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (p.2 : ℂ) ^ (w - 1)) (Ioi 0 ×ˢ Ioi 1) := fun p hp =>
      ((continuousAt_ofReal_cpow_const p.2 (w - 1)
        (Or.inr (lt_trans one_pos hp.2).ne')).comp continuous_snd.continuousAt).continuousWithinAt
    have h2 : Continuous fun p : ℝ × ℝ => cosD ε p.1 * cosD ε (p.2 * p.1) :=
      ((continuous_cosD ε).comp continuous_fst).mul ((continuous_cosD ε).comp
        (continuous_snd.mul continuous_fst))
    exact ((h1.mul (hc.mul h2.continuousOn)).mono (prod_mono hA0 subset_rfl))
  have hmeas : AEStronglyMeasurable (Function.uncurry Fk)
      ((volume.restrict A).prod (volume.restrict (Ioi (1 : ℝ)))) := by
    rw [Measure.prod_restrict]
    exact hcont.aestronglyMeasurable (hA.prod measurableSet_Ioi)
  have hnorm : ∀ a ∈ A, ∫ ρ in Ioi (1 : ℝ), ‖Fk a ρ‖ = ‖pD t ε a‖ * ∫ s in Ioi a, ‖h a s * Qd t ε s‖ := by
    intro a haA
    have ha : 0 < a := hA0 haA
    rw [hcvR a ha (fun s => ‖h a s * Qd t ε s‖), ← mul_assoc, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
    rw [hFk a ha ρ (lt_trans one_pos hρ), norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ha]
    ring
  have hint : Integrable (Function.uncurry Fk)
      ((volume.restrict A).prod (volume.restrict (Ioi (1 : ℝ)))) := by
    rw [integrable_prod_iff hmeas]
    constructor
    · refine (ae_restrict_iff' hA).mpr (Eventually.of_forall fun a haA => ?_)
      have ha : 0 < a := hA0 haA
      have h1 : IntegrableOn (fun x => h a (a * x) * Qd t ε (a * x)) (Ioi 1) := by
        have := (integrableOn_Ioi_comp_mul_left_iff (fun s => h a s * Qd t ε s) 1 ha).mpr
        rw [mul_one] at this
        exact this (hin a haA)
      refine IntegrableOn.congr_fun (h1.const_mul (pD t ε a * (a : ℂ))) (fun ρ hρ => ?_) measurableSet_Ioi
      show pD t ε a * (a : ℂ) * (h a (a * ρ) * Qd t ε (a * ρ)) = Fk a ρ
      rw [hFk a ha ρ (lt_trans one_pos hρ)]
      ring
    · refine hB.mono' hmeas.norm.integral_prod_right' ?_
      refine (ae_restrict_iff' hA).mpr (Eventually.of_forall fun a haA => ?_)
      simp only [Function.uncurry_apply_pair]
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), hnorm a haA]
      exact hbound a haA
  rw [integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioi fun ρ _ => ?_
  simp only [Fk]
  rw [integral_const_mul]

/-! ## E. Steps (C1), (C2): the two substitutions. -/

/-- J_eps(rho) = ∫_0^∞ C_eps(a) C_eps(rho a) da. -/
def Jd (ε ρ : ℝ) : ℂ := ∫ a in Ioi (0 : ℝ), cosD ε a * cosD ε (ρ * a)

/-- I_eps(rho) = ∫_0^1 (-log a) C_eps(a) C_eps(rho a) da. -/
def Id (ε ρ : ℝ) : ℂ := ∫ a in Ioc (0 : ℝ) 1, (-(Real.log a : ℂ)) * (cosD ε a * cosD ε (ρ * a))

lemma setIntegral_norm_le_Ioi {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0)) {a : ℝ} (ha : 0 ≤ a) :
    ∫ s in Ioi a, ‖f s‖ ≤ ∫ s in Ioi 0, ‖f s‖ :=
  setIntegral_mono_set hf.norm (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall (Ioi_subset_Ioi ha))

/-- (C1) ∫_0^∞ P(a) ∫_a^∞ (log a - log s) Q(s) ds da = ∫_1^∞ (-log rho) rho^{w-1} J_eps(rho) d rho. -/
theorem stepC1 {t ε : ℝ} (hε : 0 < ε) :
    ∫ a in Ioi (0 : ℝ), pD t ε a * ∫ s in Ioi a, ((Real.log a : ℂ) - Real.log s) * Qd t ε s
      = ∫ ρ in Ioi (1 : ℝ), (-(Real.log ρ : ℂ)) * (ρ : ℂ) ^ (conj (zt t) - 1) * Jd ε ρ := by
  set C1 := ∫ s in Ioi (0 : ℝ), ‖Qd t ε s‖
  set C2 := ∫ s in Ioi (0 : ℝ), ‖(Real.log s : ℂ) * Qd t ε s‖
  have hQ := integrableOn_Qd (t := t) hε
  have hlQ := integrableOn_logQd (t := t) hε
  have hin : ∀ a ∈ Ioi (0 : ℝ),
      IntegrableOn (fun s => ((Real.log a : ℂ) - Real.log s) * Qd t ε s) (Ioi a) := by
    intro a ha
    refine IntegrableOn.congr_fun (IntegrableOn.mono_set ((hQ.const_mul (Real.log a : ℂ)).sub hlQ)
      (Ioi_subset_Ioi (le_of_lt ha))) (fun s _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]; ring
  have hB : IntegrableOn (fun a => ‖(Real.log a : ℂ) * pD t ε a‖ * C1 + ‖pD t ε a‖ * C2) (Ioi 0) :=
    ((integrableOn_logpD hε).norm.mul_const C1).add ((integrableOn_pD hε).norm.mul_const C2)
  have hc : ContinuousOn (fun p : ℝ × ℝ => ((Real.log p.1 : ℂ) - Real.log (p.1 * p.2)))
      (Ioi 0 ×ˢ Ioi 1) := by
    intro p hp
    have h1 : p.1 ≠ 0 := (show (0 : ℝ) < p.1 from hp.1).ne'
    have h2 : p.1 * p.2 ≠ 0 := mul_ne_zero h1 (lt_trans one_pos (show (1 : ℝ) < p.2 from hp.2)).ne'
    have hm : ContinuousAt (fun q : ℝ × ℝ => q.1 * q.2) p := (continuous_fst.mul continuous_snd).continuousAt
    have hl1 : ContinuousAt (fun q : ℝ × ℝ => ((Real.log q.1 : ℝ) : ℂ)) p :=
      ContinuousAt.comp (g := fun x : ℝ => (x : ℂ)) Complex.continuous_ofReal.continuousAt
        (ContinuousAt.comp (g := Real.log) (Real.continuousAt_log h1) continuous_fst.continuousAt)
    have hl2 : ContinuousAt (fun q : ℝ × ℝ => ((Real.log (q.1 * q.2) : ℝ) : ℂ)) p :=
      ContinuousAt.comp (g := fun x : ℝ => (x : ℂ)) Complex.continuous_ofReal.continuousAt
        (ContinuousAt.comp (g := Real.log) (Real.continuousAt_log h2) hm)
    exact (hl1.sub hl2).continuousWithinAt
  have hbound : ∀ a ∈ Ioi (0 : ℝ), ‖pD t ε a‖
      * ∫ s in Ioi a, ‖((Real.log a : ℂ) - Real.log s) * Qd t ε s‖
      ≤ ‖(Real.log a : ℂ) * pD t ε a‖ * C1 + ‖pD t ε a‖ * C2 := by
    intro a ha
    have ha0 : (0 : ℝ) ≤ a := le_of_lt ha
    have hle : ∫ s in Ioi a, ‖((Real.log a : ℂ) - Real.log s) * Qd t ε s‖
        ≤ (‖(Real.log a : ℂ)‖ * ∫ s in Ioi a, ‖Qd t ε s‖)
          + ∫ s in Ioi a, ‖(Real.log s : ℂ) * Qd t ε s‖ := by
      rw [← integral_const_mul, ← integral_add
        (IntegrableOn.mono_set (hQ.norm.const_mul _) (Ioi_subset_Ioi ha0))
        (IntegrableOn.mono_set hlQ.norm (Ioi_subset_Ioi ha0))]
      refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
        (IntegrableOn.mono_set ((hQ.norm.const_mul _).add hlQ.norm) (Ioi_subset_Ioi ha0)) ?_
      refine Eventually.of_forall fun s => ?_
      simp only
      rw [sub_mul, ← norm_mul]
      exact norm_sub_le _ _
    have h1 := setIntegral_norm_le_Ioi hQ ha0
    have h2 := setIntegral_norm_le_Ioi hlQ ha0
    have hP := norm_nonneg (pD t ε a)
    have hl := norm_nonneg (Real.log a : ℂ)
    calc ‖pD t ε a‖ * ∫ s in Ioi a, ‖((Real.log a : ℂ) - Real.log s) * Qd t ε s‖
        ≤ ‖pD t ε a‖ * (‖(Real.log a : ℂ)‖ * C1 + C2) :=
          mul_le_mul_of_nonneg_left (hle.trans (add_le_add (mul_le_mul_of_nonneg_left h1 hl) h2)) hP
      _ = ‖(Real.log a : ℂ) * pD t ε a‖ * C1 + ‖pD t ε a‖ * C2 := by rw [norm_mul]; ring
  rw [subst_swap measurableSet_Ioi subset_rfl (fun a s => ((Real.log a : ℂ) - Real.log s)) hc hin _ hB
    hbound]
  refine setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
  have hρ0 : (0 : ℝ) < ρ := lt_trans one_pos hρ
  have : ∫ a in Ioi (0 : ℝ), ((Real.log a : ℂ) - Real.log (a * ρ)) * (cosD ε a * cosD ε (ρ * a))
      = ∫ a in Ioi (0 : ℝ), (-(Real.log ρ : ℂ)) * (cosD ε a * cosD ε (ρ * a)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun a ha => ?_
    rw [Real.log_mul (show (0 : ℝ) < a from ha).ne' hρ0.ne']
    push_cast; ring
  rw [this, integral_const_mul, Jd]
  ring

/-- (C2) ∫_0^1 P(a) ∫_a^∞ log a Q(s) ds da = -∫_1^∞ rho^{w-1} I_eps(rho) d rho. -/
theorem stepC2 {t ε : ℝ} (hε : 0 < ε) :
    ∫ a in Ioc (0 : ℝ) 1, pD t ε a * ∫ s in Ioi a, (Real.log a : ℂ) * Qd t ε s
      = -∫ ρ in Ioi (1 : ℝ), (ρ : ℂ) ^ (conj (zt t) - 1) * Id ε ρ := by
  set C1 := ∫ s in Ioi (0 : ℝ), ‖Qd t ε s‖
  have hQ := integrableOn_Qd (t := t) hε
  have hin : ∀ a ∈ Ioc (0 : ℝ) 1, IntegrableOn (fun s => (Real.log a : ℂ) * Qd t ε s) (Ioi a) :=
    fun a ha => IntegrableOn.mono_set (hQ.const_mul _) (Ioi_subset_Ioi ha.1.le)
  have hB : IntegrableOn (fun a => ‖(Real.log a : ℂ) * pD t ε a‖ * C1) (Ioc 0 1) :=
    IntegrableOn.mono_set ((integrableOn_logpD (t := t) hε).norm.mul_const C1) Ioc_subset_Ioi_self
  have hc : ContinuousOn (fun p : ℝ × ℝ => (Real.log p.1 : ℂ)) (Ioi 0 ×ˢ Ioi 1) := by
    intro p hp
    exact (Complex.continuous_ofReal.continuousAt.comp ((Real.continuousAt_log
      (show (0 : ℝ) < p.1 from hp.1).ne').comp continuous_fst.continuousAt)).continuousWithinAt
  have hbound : ∀ a ∈ Ioc (0 : ℝ) 1, ‖pD t ε a‖ * ∫ s in Ioi a, ‖(Real.log a : ℂ) * Qd t ε s‖
      ≤ ‖(Real.log a : ℂ) * pD t ε a‖ * C1 := by
    intro a ha
    simp only [norm_mul]
    rw [integral_const_mul]
    have h1 := setIntegral_norm_le_Ioi hQ ha.1.le
    have := mul_le_mul_of_nonneg_left h1 (mul_nonneg (norm_nonneg (pD t ε a)) (norm_nonneg
      (Real.log a : ℂ)))
    nlinarith
  rw [subst_swap measurableSet_Ioc Ioc_subset_Ioi_self (fun a _ => (Real.log a : ℂ)) hc hin _ hB hbound,
    ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun ρ _ => ?_
  simp only [Id]
  rw [← mul_neg, ← integral_neg]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun a _ => ?_
  ring

/-! ## F. Step (B): the quadrant symmetry. -/

/-- U(A) = ∫_{a ∈ A} log a · P(a) · conj Phi_eps(a) da. -/
def Uint (t ε : ℝ) (A : Set ℝ) : ℂ := ∫ a in A, (Real.log a : ℂ) * pD t ε a * conj (PhiE t ε a)

lemma conj_PhiE {t ε a : ℝ} : conj (PhiE t ε a) = ∫ s in Ioi a, Qd t ε s := by
  rw [PhiE, ← integral_conj]; rfl

lemma U_integrand_eq {t ε a : ℝ} :
    (Real.log a : ℂ) * pD t ε a * conj (PhiE t ε a) = pD t ε a * ∫ s in Ioi a, (Real.log a : ℂ) * Qd t ε s := by
  rw [conj_PhiE, integral_const_mul]; ring

lemma continuousOn_log_ofReal : ContinuousOn (fun a : ℝ => (Real.log a : ℂ)) (Ioi 0) :=
  Complex.continuous_ofReal.comp_continuousOn (Real.continuousOn_log.mono fun a ha =>
    (show (0 : ℝ) < a from ha).ne')

lemma integrableOn_U {t ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun a : ℝ => (Real.log a : ℂ) * pD t ε a * conj (PhiE t ε a)) (Ioi 0) := by
  set M := ‖PsiE ε (zt t)‖ + 4 + Kt t
  refine ((integrableOn_logpD (t := t) hε).norm.mul_const M).mono' ?_ ?_
  · exact ((continuousOn_log_ofReal.mul (continuousOn_pD t ε)).mul
      (Complex.continuous_conj.comp_continuousOn (continuousOn_PhiE hε))).aestronglyMeasurable
      measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun a ha => ?_)
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (norm_PhiE_le_M hε ha) (norm_nonneg _)

lemma integrableOn_U2 {t ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun a : ℝ => (Real.log a : ℂ) * pD t ε a * conj (Gpart t ε a)) (Ioi 0) := by
  set M := ‖PsiE ε (zt t)‖ + (‖PsiE ε (zt t)‖ + 4 + Kt t)
  refine ((integrableOn_logpD (t := t) hε).norm.mul_const M).mono' ?_ ?_
  · refine ((continuousOn_log_ofReal.mul (continuousOn_pD t ε)).mul
      (Complex.continuous_conj.comp_continuousOn ?_)).aestronglyMeasurable measurableSet_Ioi
    exact fun a ha => (hasDerivAt_Gpart (t := t) hε.le ha).continuousAt.continuousWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun a ha => ?_)
    rw [norm_mul, Complex.norm_conj]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hG : Gpart t ε a = PsiE ε (zt t) - PhiE t ε a := by rw [PhiE_eq hε ha]; ring
    rw [hG]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_PhiE_le_M hε ha))

/-- (B) 2 Re U(0,∞) = Re(Psi'_eps conj Psi_eps) + Re ∫_0^∞ P(a) ∫_a^∞ (log a - log s) Q(s) ds da. -/
theorem stepB {t ε : ℝ} (hε : 0 < ε) :
    2 * (Uint t ε (Ioi 0)).re
      = (dPsiE ε (zt t) * conj (PsiE ε (zt t))).re
        + (∫ a in Ioi (0 : ℝ), pD t ε a * ∫ s in Ioi a, ((Real.log a : ℂ) - Real.log s) * Qd t ε s).re := by
  have hz : 0 < (zt t).re := by rw [zt_re]; norm_num
  set U0 := Uint t ε (Ioi 0)
  set U2 := ∫ a in Ioi (0 : ℝ), (Real.log a : ℂ) * pD t ε a * conj (Gpart t ε a)
  set V := ∫ a in Ioi (0 : ℝ), pD t ε a * ∫ s in Ioi a, (Real.log s : ℂ) * Qd t ε s
  have hQ := integrableOn_Qd (t := t) hε
  have hlQ := integrableOn_logQd (t := t) hε
  -- (B1) Psi' conj Psi = U0 + U2
  have hb2 : dPsiE ε (zt t) = ∫ a in Ioi (0 : ℝ), (Real.log a : ℂ) * pD t ε a := by
    rw [← integral_log_cosD hε hz]
    refine setIntegral_congr_fun measurableSet_Ioi fun a _ => ?_
    simp only [pD]; ring
  have hB1 : dPsiE ε (zt t) * conj (PsiE ε (zt t)) = U0 + U2 := by
    rw [hb2, ← integral_mul_const, show U0 + U2 = _ from
      (integral_add (integrableOn_U (t := t) hε) (integrableOn_U2 (t := t) hε)).symm]
    refine setIntegral_congr_fun measurableSet_Ioi fun a ha => ?_
    rw [← PhiE_add_Gpart hε ha, map_add]
    ring
  -- (B2) conj U2 = V, by Fubini on {0 < s <= a}
  set μ := volume.restrict (Ioi (0 : ℝ))
  set F : ℝ × ℝ → ℂ := {p : ℝ × ℝ | p.2 ≤ p.1}.indicator
    (fun p => (Real.log p.1 : ℂ) * pD t ε p.1 * Qd t ε p.2)
  have hFint : Integrable F (μ.prod μ) :=
    ((integrableOn_logpD (t := t) hε).mul_prod hQ).indicator (measurableSet_le measurable_snd measurable_fst)
  have hrow : ∀ a ∈ Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), F (a, s)
      = (Real.log a : ℂ) * pD t ε a * conj (Gpart t ε a) := by
    intro a ha
    have e : (fun s => F (a, s)) = (Iic a).indicator (fun s => (Real.log a : ℂ) * pD t ε a * Qd t ε s) := by
      funext s; simp only [F, Set.indicator, Set.mem_ofPred_eq, Set.mem_Iic]
    rw [e, setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic, integral_const_mul, Gpart,
      intervalIntegral.integral_of_le (le_of_lt ha), ← integral_conj]
    rfl
  have hcol : ∀ s ∈ Ioi (0 : ℝ), ∫ a in Ioi (0 : ℝ), F (a, s)
      = (∫ a in Ioi s, (Real.log a : ℂ) * pD t ε a) * Qd t ε s := by
    intro s hs
    have e : (fun a => F (a, s)) = (Ici s).indicator (fun a => (Real.log a : ℂ) * pD t ε a * Qd t ε s) := by
      funext a; simp only [F, Set.indicator, Set.mem_ofPred_eq, Set.mem_Ici]
    rw [e, setIntegral_indicator measurableSet_Ici,
      inter_eq_right.mpr (Ici_subset_Ioi.mpr hs), integral_Ici_eq_integral_Ioi, integral_mul_const]
  have hswap := integral_integral_swap (μ := μ) (ν := μ) (f := fun a s => F (a, s)) hFint
  have hU2 : U2 = ∫ s in Ioi (0 : ℝ), (∫ a in Ioi s, (Real.log a : ℂ) * pD t ε a) * Qd t ε s := by
    have h1 : U2 = ∫ a in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), F (a, s) :=
      setIntegral_congr_fun measurableSet_Ioi fun a ha => (hrow a ha).symm
    rw [h1, hswap]
    exact setIntegral_congr_fun measurableSet_Ioi fun s hs => hcol s hs
  have hconjcol : ∀ s, conj ((∫ a in Ioi s, (Real.log a : ℂ) * pD t ε a) * Qd t ε s)
      = pD t ε s * ∫ a in Ioi s, (Real.log a : ℂ) * Qd t ε a := by
    intro s
    rw [map_mul, ← integral_conj]
    simp only [Qd, map_mul, Complex.conj_ofReal, Complex.conj_conj]
    ring
  have hB2 : conj U2 = V := by
    rw [hU2, ← integral_conj]
    exact setIntegral_congr_fun measurableSet_Ioi fun s _ => hconjcol s
  have hVint : IntegrableOn (fun a => pD t ε a * ∫ s in Ioi a, (Real.log s : ℂ) * Qd t ε s) (Ioi 0) := by
    have h1 := integrable_conj' hFint.integral_prod_right
    refine IntegrableOn.congr_fun h1 (fun s hs => ?_) measurableSet_Ioi
    rw [hcol s hs, hconjcol]
  -- (B3) U0 - V
  have hB3 : U0 - V
      = ∫ a in Ioi (0 : ℝ), pD t ε a * ∫ s in Ioi a, ((Real.log a : ℂ) - Real.log s) * Qd t ε s := by
    rw [show U0 - V = _ from (integral_sub (integrableOn_U (t := t) hε) hVint).symm]
    refine setIntegral_congr_fun measurableSet_Ioi fun a ha => ?_
    have ha0 : (0 : ℝ) ≤ a := le_of_lt ha
    rw [U_integrand_eq, ← mul_sub, ← integral_sub (IntegrableOn.mono_set (hQ.const_mul _)
      (Ioi_subset_Ioi ha0)) (IntegrableOn.mono_set hlQ (Ioi_subset_Ioi ha0))]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    ring
  rw [← hB3, hB1]
  have hre : U2.re = V.re := by rw [← hB2, Complex.conj_re]
  simp only [Complex.add_re, Complex.sub_re]
  linarith

/-! ## G. THE EXACT DAMPED IDENTITY. -/

/-- For every eps > 0:
∫_1^∞ |Phi_eps|^2 da/a = Re(Psi'_eps conj Psi_eps) + Re ∫_1^∞ (-log rho) rho^{w-1} J_eps
                          + 2 Re ∫_1^∞ rho^{w-1} I_eps. -/
theorem damped_identity {t ε : ℝ} (hε : 0 < ε) :
    ∫ a in Ioi (1 : ℝ), ‖PhiE t ε a‖ ^ 2 / a
      = (dPsiE ε (zt t) * conj (PsiE ε (zt t))).re
        + (∫ ρ in Ioi (1 : ℝ), (-(Real.log ρ : ℂ)) * (ρ : ℂ) ^ (conj (zt t) - 1) * Jd ε ρ).re
        + 2 * (∫ ρ in Ioi (1 : ℝ), (ρ : ℂ) ^ (conj (zt t) - 1) * Id ε ρ).re := by
  have hU := integrableOn_U (t := t) hε
  have hsplit : Uint t ε (Ioi 0) = Uint t ε (Ioc 0 1) + Uint t ε (Ioi 1) := by
    unfold Uint
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hU.mono_set Ioc_subset_Ioi_self) (hU.mono_set (Ioi_subset_Ioi zero_le_one))]
  have hC2 : Uint t ε (Ioc 0 1) = -∫ ρ in Ioi (1 : ℝ), (ρ : ℂ) ^ (conj (zt t) - 1) * Id ε ρ := by
    rw [← stepC2 hε]
    exact setIntegral_congr_fun measurableSet_Ioc fun a _ => U_integrand_eq
  have hA := stepA (t := t) hε
  have hB := stepB (t := t) hε
  rw [stepC1 hε] at hB
  rw [hA]
  change 2 * (Uint t ε (Ioi 1)).re = _
  have : (Uint t ε (Ioi 1)).re = (Uint t ε (Ioi 0)).re - (Uint t ε (Ioc 0 1)).re := by
    rw [hsplit, Complex.add_re]; ring
  rw [this, hC2, Complex.neg_re]
  linarith

end ArchS3
