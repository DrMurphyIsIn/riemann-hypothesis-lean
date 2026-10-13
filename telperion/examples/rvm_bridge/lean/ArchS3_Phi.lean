/-
  ArchS3_Phi -- the vector A e_t (2026-10-11, stage S3 milestone M2b of
  telperion/docs/ARCHIMEDEAN_CONCEPTUAL_BLUEPRINT_2026-10-11.md).

  For z = z_t = 1/2 + i t and a > 0:

    Phi_t(a) := Psi(z) - ∫_0^a s^{z-1} 2cos(2 pi s) ds  =  lim_{R -> ∞} ∫_a^R s^{z-1} 2cos(2 pi s) ds,

  i.e. Phi_t(a) = 2 ∫_a^∞ s^{-1/2 + i t} cos(2 pi s) ds as an improper integral; Phi_t(1/λ) λ^{it} is
  CC's A = (1 - P) u P applied to the generalised eigenvector λ^{it} of the scaling action.
  Proved here:
    * the damped tails PhiE eps a = ∫_a^∞ s^{z-1} 2cos(2 pi s) e^{-eps s} ds satisfy, uniformly in eps > 0,
          |PhiE eps a| <= K_t a^{-1/2},   K_t = (2 + 2|z_t - 1|)/pi      (one integration by parts);
    * |∫_0^a s^{z-1} 2cos(2 pi s) e^{-eps s} ds| <= 4 sqrt a;
    * PhiE eps a -> Phi_t(a) as eps -> 0+, hence |Phi_t(a)| <= K_t a^{-1/2};
    * the improper-integral identities (Psi and Phi_t as lim_R ∫^R);
    * a |-> |Phi_t(a)|^2 / a is integrable on (1, ∞).

  No zeros, no RH progress.  conjecture1_proved = False.
-/
import ArchS3_Mellin

open MeasureTheory Filter Topology Complex Set
open scoped ComplexConjugate

noncomputable section

namespace ArchS3

/-! ## A. The integrand and its pieces. -/

/-- s^{z_t - 1} · 2cos(2 pi s) e^{-eps s}  (eps = 0: undamped). -/
def pD (t ε s : ℝ) : ℂ := (s : ℂ) ^ (zt t - 1) * cosD ε s

/-- The damped tail ∫_a^∞ pD. -/
def PhiE (t ε a : ℝ) : ℂ := ∫ s in Ioi a, pD t ε s

/-- The head ∫_0^a pD. -/
def Gpart (t ε a : ℝ) : ℂ := ∫ s in (0 : ℝ)..a, pD t ε s

/-- Phi_t(a) = Psi(z_t) - ∫_0^a s^{z_t - 1} 2cos(2 pi s) ds. -/
def Phi (t a : ℝ) : ℂ := Psi (zt t) - Gpart t 0 a

/-- K_t = (2 + 2 |z_t - 1|)/pi. -/
def Kt (t : ℝ) : ℝ := (2 + 2 * ‖zt t - 1‖) / Real.pi

lemma Kt_nonneg (t : ℝ) : 0 ≤ Kt t := by unfold Kt; positivity

lemma zt_sub_one_re (t : ℝ) : (zt t - 1).re = -1 / 2 := by simp [zt]; norm_num

lemma norm_cosD_le {ε s : ℝ} (hε : 0 ≤ ε) (hs : 0 ≤ s) : ‖cosD ε s‖ ≤ 2 := by
  unfold cosD
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_two, abs_of_pos (Real.exp_pos _)]
  have h1 := Real.abs_cos_le_one (2 * Real.pi * s)
  have h2 : Real.exp (-ε * s) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h3 : 0 ≤ |Real.cos (2 * Real.pi * s)| := abs_nonneg _
  nlinarith [Real.exp_pos (-ε * s)]

lemma norm_cpow_zt {t s : ℝ} (hs : 0 < s) : ‖(s : ℂ) ^ (zt t - 1)‖ = s ^ (-1 / 2 : ℝ) := by
  rw [norm_cpow_eq_rpow_re_of_pos hs, zt_sub_one_re]

lemma norm_pD_le {t ε s : ℝ} (hε : 0 ≤ ε) (hs : 0 < s) : ‖pD t ε s‖ ≤ 2 * s ^ (-1 / 2 : ℝ) := by
  unfold pD
  rw [norm_mul, norm_cpow_zt hs, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_cosD_le hε hs.le) (by positivity)

lemma continuous_cosD (ε : ℝ) : Continuous (cosD ε) := by unfold cosD; fun_prop

lemma continuousOn_pD (t ε : ℝ) : ContinuousOn (pD t ε) (Ioi 0) :=
  (continuousOn_ofReal_cpow _).mul (continuous_cosD ε).continuousOn

lemma intervalIntegrable_pD {t ε a : ℝ} (hε : 0 ≤ ε) (ha : 0 ≤ a) :
    IntervalIntegrable (pD t ε) volume 0 a := by
  have hb : IntervalIntegrable (fun s : ℝ => 2 * s ^ (-1 / 2 : ℝ)) volume 0 a :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul 2
  refine hb.mono_fun' ?_ ?_
  · rw [uIoc_of_le ha]
    exact ((continuousOn_pD t ε).mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
  · rw [uIoc_of_le ha]
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun s hs => ?_)
    exact norm_pD_le hε hs.1

/-- |∫_0^a pD| <= 4 sqrt a. -/
lemma norm_Gpart_le {t ε a : ℝ} (hε : 0 ≤ ε) (ha : 0 ≤ a) : ‖Gpart t ε a‖ ≤ 4 * Real.sqrt a := by
  unfold Gpart
  have hb : IntervalIntegrable (fun s : ℝ => 2 * s ^ (-1 / 2 : ℝ)) volume 0 a :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul 2
  refine (intervalIntegral.norm_integral_le_of_norm_le ha ?_ hb).trans (le_of_eq ?_)
  · exact Eventually.of_forall fun s hs => norm_pD_le hε hs.1
  · rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num)),
      Real.sqrt_eq_rpow, Real.zero_rpow (by norm_num)]
    norm_num
    ring

lemma integrableOn_pD {t ε : ℝ} (hε : 0 < ε) : IntegrableOn (pD t ε) (Ioi 0) := by
  have h := integrableOn_cosD hε (z := zt t) (by rw [zt_re]; norm_num)
  exact h

lemma PhiE_add_Gpart {t ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    PhiE t ε a + Gpart t ε a = PsiE ε (zt t) := by
  have hI := integral_cosD hε (z := zt t) (by rw [zt_re]; norm_num)
  have hint := integrableOn_pD (t := t) hε
  rw [← hI]
  change PhiE t ε a + Gpart t ε a = ∫ s in Ioi 0, pD t ε s
  rw [← Ioc_union_Ioi_eq_Ioi ha.le, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi ha.le)),
    PhiE, Gpart, intervalIntegral.integral_of_le ha.le]
  ring

lemma PhiE_eq {t ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    PhiE t ε a = PsiE ε (zt t) - Gpart t ε a := by
  rw [← PhiE_add_Gpart hε ha]; ring

/-! ## B. The uniform tail bound |PhiE eps a| <= K_t a^{-1/2} (one integration by parts). -/

lemma cosD_split (ε s : ℝ) :
    cosD ε s = ((2 * Real.cos (2 * Real.pi * s) : ℝ) : ℂ) * cexp (-((ε : ℂ) * s)) := by
  unfold cosD
  rw [show -((ε : ℂ) * s) = ((-ε * s : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp]
  push_cast; ring

/-- THE TAIL BOUND: |∫_a^∞ s^{z_t-1} 2cos(2 pi s) e^{-eps s} ds| <= K_t a^{-1/2}, uniformly in eps > 0. -/
theorem norm_PhiE_le {t ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    ‖PhiE t ε a‖ ≤ Kt t * a ^ (-1 / 2 : ℝ) := by
  set z := zt t
  set w := ‖z - 1‖
  -- u s = s^{z-1} e^{-eps s}, v s = sin(2 pi s)/pi
  set u : ℝ → ℂ := fun s => (s : ℂ) ^ (z - 1) * cexp (-((ε : ℂ) * s))
  set u' : ℝ → ℂ := fun s =>
    ((z - 1) * (s : ℂ) ^ (z - 1 - 1) - ε * (s : ℂ) ^ (z - 1)) * cexp (-((ε : ℂ) * s))
  set v : ℝ → ℂ := fun s => ((Real.sin (2 * Real.pi * s) / Real.pi : ℝ) : ℂ)
  set v' : ℝ → ℂ := fun s => ((2 * Real.cos (2 * Real.pi * s) : ℝ) : ℂ)
  have hu : ∀ s ∈ Ioi a, HasDerivAt u (u' s) s := by
    intro s hs
    have hs0 : (0 : ℝ) < s := ha.trans hs
    have hslit : ((s : ℝ) : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hs0
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (z - 1)) ((z - 1) * (s : ℂ) ^ (z - 1 - 1)) s := by
      have := ((hasDerivAt_id (s : ℂ)).cpow_const (c := z - 1) hslit).comp_ofReal
      simpa using this
    have h2 : HasDerivAt (fun y : ℝ => cexp (-((ε : ℂ) * y))) (cexp (-((ε : ℂ) * s)) * (-(ε : ℂ))) s := by
      have := ((((hasDerivAt_id (s : ℂ)).const_mul (ε : ℂ)).neg).cexp).comp_ofReal
      simpa using this
    refine (h1.mul h2).congr_deriv ?_
    simp only [u']
    ring
  have hv : ∀ s ∈ Ioi a, HasDerivAt v (v' s) s := by
    intro s _
    have h := ((((hasDerivAt_id s).const_mul (2 * Real.pi)).sin).div_const Real.pi).ofReal_comp
    refine h.congr_deriv ?_
    simp only [v', id, mul_one]
    push_cast
    field_simp
  have hpD : ∀ s, u s * v' s = pD t ε s := by
    intro s; simp only [u, v', pD, cosD_split]; ring
  have hnu : ∀ s, 0 < s → ‖u s‖ ≤ s ^ (-1 / 2 : ℝ) := by
    intro s hs
    simp only [u]
    rw [norm_mul, norm_cpow_zt hs, Complex.norm_exp]
    have : (-((ε : ℂ) * (s : ℂ))).re = -(ε * s) := by simp [Complex.mul_re]
    rw [this]
    exact mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by nlinarith))
  have hnv : ∀ s, ‖v s‖ ≤ 1 / Real.pi := by
    intro s
    simp only [v]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos Real.pi_pos]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) Real.pi_pos.le
  -- the bound on u' v
  set B : ℝ → ℝ := fun s => (w * s ^ (-3 / 2 : ℝ) + ε * a ^ (-1 / 2 : ℝ) * Real.exp (-ε * s)) / Real.pi
  have hnu'v : ∀ s ∈ Ioi a, ‖u' s * v s‖ ≤ B s := by
    intro s hs
    have hs0 : (0 : ℝ) < s := ha.trans hs
    have has : a ≤ s := le_of_lt hs
    rw [norm_mul]
    have hu'n : ‖u' s‖ ≤ w * s ^ (-3 / 2 : ℝ) + ε * a ^ (-1 / 2 : ℝ) * Real.exp (-ε * s) := by
      simp only [u']
      rw [norm_mul, Complex.norm_exp]
      have hre : (-((ε : ℂ) * (s : ℂ))).re = -ε * s := by simp [Complex.mul_re]
      rw [hre]
      have hA : ‖(z - 1) * (s : ℂ) ^ (z - 1 - 1)‖ = w * s ^ (-3 / 2 : ℝ) := by
        rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hs0]
        congr 2
        simp [z, zt]; norm_num
      have hB : ‖(ε : ℂ) * (s : ℂ) ^ (z - 1)‖ = ε * s ^ (-1 / 2 : ℝ) := by
        rw [norm_mul, norm_cpow_zt hs0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
      have hsa : s ^ (-1 / 2 : ℝ) ≤ a ^ (-1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos ha has (by norm_num)
      have hexp1 : Real.exp (-ε * s) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      calc ‖(z - 1) * (s : ℂ) ^ (z - 1 - 1) - ↑ε * (s : ℂ) ^ (z - 1)‖ * Real.exp (-ε * s)
          ≤ (w * s ^ (-3 / 2 : ℝ) + ε * s ^ (-1 / 2 : ℝ)) * Real.exp (-ε * s) := by
            gcongr
            rw [← hA, ← hB]; exact norm_sub_le _ _
        _ ≤ w * s ^ (-3 / 2 : ℝ) + ε * a ^ (-1 / 2 : ℝ) * Real.exp (-ε * s) := by
            have h3 : 0 ≤ w * s ^ (-3 / 2 : ℝ) := by positivity
            have h4 : 0 ≤ Real.exp (-ε * s) := (Real.exp_pos _).le
            nlinarith [mul_le_mul_of_nonneg_left hsa hε.le]
    calc ‖u' s‖ * ‖v s‖ ≤ (w * s ^ (-3 / 2 : ℝ) + ε * a ^ (-1 / 2 : ℝ) * Real.exp (-ε * s))
          * (1 / Real.pi) := mul_le_mul hu'n (hnv s) (norm_nonneg _) (by positivity)
      _ = B s := by simp only [B]; ring
  have hBint : IntegrableOn B (Ioi a) := by
    have h1 := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1) ha).const_mul w
    have h2 := (exp_neg_integrableOn_Ioi a hε).const_mul (ε * a ^ (-1 / 2 : ℝ))
    exact (h1.add h2).div_const _
  have hcu' : ContinuousOn u' (Ioi 0) := by
    have hc : Continuous fun s : ℝ => cexp (-((ε : ℂ) * s)) := by fun_prop
    exact ((continuousOn_const.mul (continuousOn_ofReal_cpow _)).sub
      (continuousOn_const.mul (continuousOn_ofReal_cpow _))).mul hc.continuousOn
  have hcv : Continuous v := by simp only [v]; fun_prop
  have hu'v_int : IntegrableOn (u' * v) (Ioi a) := by
    refine hBint.mono' ?_ ?_
    · exact ((hcu'.mono (Ioi_subset_Ioi ha.le)).mul hcv.continuousOn).aestronglyMeasurable
        measurableSet_Ioi
    · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => hnu'v s hs)
  have huv'_int : IntegrableOn (u * v') (Ioi a) := by
    refine ((integrableOn_pD (t := t) hε).mono_set (Ioi_subset_Ioi ha.le)).congr_fun
      (fun s _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply]; exact (hpD s).symm
  have hcu_a : ContinuousAt u a := by
    have h1 : ContinuousAt (fun y : ℝ => (y : ℂ) ^ (z - 1)) a :=
      continuousAt_ofReal_cpow_const a _ (Or.inr ha.ne')
    exact h1.mul (by fun_prop)
  have h_zero : Tendsto (u * v) (𝓝[>] a) (𝓝 (u a * v a)) :=
    ((hcu_a.mul hcv.continuousAt).tendsto).mono_left nhdsWithin_le_nhds
  have h_infty : Tendsto (u * v) atTop (𝓝 0) := by
    have hlim : Tendsto (fun s : ℝ => s ^ (-(1 / 2 : ℝ)) / Real.pi) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).div_const Real.pi
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop 0] with s hs
    rw [Pi.mul_apply, norm_mul, show (-(1 / 2 : ℝ)) = -1 / 2 by norm_num, div_eq_mul_one_div]
    exact mul_le_mul (hnu s hs) (hnv s) (norm_nonneg _) (by positivity)
  have hIBP := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv'_int hu'v_int h_zero h_infty
  have hPhi : PhiE t ε a = -(u a * v a) - ∫ s in Ioi a, u' s * v s := by
    rw [PhiE, ← zero_sub, ← hIBP]
    exact setIntegral_congr_fun measurableSet_Ioi fun s _ => (hpD s).symm
  -- the integral of B
  have hIB : ∫ s in Ioi a, B s
      = (w * (2 * a ^ (-1 / 2 : ℝ)) + a ^ (-1 / 2 : ℝ) * Real.exp (-(ε * a))) / Real.pi := by
    have h1 := integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1) ha
    have h2 := exp_neg_integrableOn_Ioi a hε
    simp only [B]
    rw [integral_div, integral_add (h1.const_mul w) (h2.const_mul _), integral_const_mul,
      integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) ha]
    have hE : ∫ s in Ioi a, Real.exp (-ε * s) = ε⁻¹ * Real.exp (-(ε * a)) := by
      have := integral_comp_mul_left_Ioi (fun x => Real.exp (-x)) a hε
      simp only [smul_eq_mul, integral_exp_neg_Ioi] at this
      rw [← this]
      exact setIntegral_congr_fun measurableSet_Ioi fun s _ => by simp only [neg_mul]
    rw [hE]
    congr 1
    have hε0 : ε ≠ 0 := hε.ne'
    norm_num
    field_simp
  have hnI : ‖∫ s in Ioi a, u' s * v s‖ ≤ ∫ s in Ioi a, B s :=
    norm_integral_le_of_norm_le hBint
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hnu'v))
  have hua : ‖u a * v a‖ ≤ a ^ (-1 / 2 : ℝ) / Real.pi := by
    rw [norm_mul, div_eq_mul_one_div]
    exact mul_le_mul (hnu a ha) (hnv a) (norm_nonneg _) (by positivity)
  have hexp : Real.exp (-(ε * a)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hapos : 0 < a ^ (-1 / 2 : ℝ) := by positivity
  calc ‖PhiE t ε a‖ ≤ ‖u a * v a‖ + ‖∫ s in Ioi a, u' s * v s‖ := by
        rw [hPhi]; exact (norm_sub_le _ _).trans (by rw [norm_neg])
    _ ≤ a ^ (-1 / 2 : ℝ) / Real.pi
          + (w * (2 * a ^ (-1 / 2 : ℝ)) + a ^ (-1 / 2 : ℝ) * Real.exp (-(ε * a))) / Real.pi := by
        rw [← hIB]; exact add_le_add hua hnI
    _ ≤ Kt t * a ^ (-1 / 2 : ℝ) := by
        unfold Kt
        rw [← add_div, div_mul_eq_mul_div]
        apply div_le_div_of_nonneg_right _ Real.pi_pos.le
        nlinarith [mul_le_mul_of_nonneg_left hexp hapos.le]

/-! ## C. The limit eps -> 0 and the undamped Phi_t. -/

lemma tendsto_Gpart {t a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun ε => Gpart t ε a) (𝓝[>] 0) (𝓝 (Gpart t 0 a)) := by
  unfold Gpart
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun s : ℝ => 2 * s ^ (-1 / 2 : ℝ)) ?_ ?_
    ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul 2) ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (intervalIntegrable_pD (t := t) (le_of_lt hε) ha).def'.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine Eventually.of_forall fun s hs => ?_
    rw [uIoc_of_le ha] at hs
    exact norm_pD_le (le_of_lt hε) hs.1
  · refine Eventually.of_forall fun s _ => ?_
    have hc : Continuous fun ε : ℝ => pD t ε s := by
      unfold pD cosD; fun_prop
    exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- PhiE eps a -> Phi_t(a) as eps -> 0+. -/
theorem tendsto_PhiE {t a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε => PhiE t ε a) (𝓝[>] 0) (𝓝 (Phi t a)) := by
  have h := (tendsto_PsiE (zt t)).sub (tendsto_Gpart (t := t) ha.le)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (PhiE_eq hε ha).symm

/-- THE BOUND |Phi_t(a)| <= K_t a^{-1/2}. -/
theorem norm_Phi_le {t a : ℝ} (ha : 0 < a) : ‖Phi t a‖ ≤ Kt t * a ^ (-1 / 2 : ℝ) := by
  refine le_of_tendsto (tendsto_PhiE ha).norm ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact norm_PhiE_le hε ha

lemma Gpart_sub {t a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Gpart t 0 b - Gpart t 0 a = ∫ s in a..b, pD t 0 s := by
  unfold Gpart
  exact intervalIntegral.integral_interval_sub_left (intervalIntegrable_pD le_rfl hb)
    (intervalIntegrable_pD le_rfl ha)

/-- Psi(z_t) = lim_{R -> ∞} ∫_0^R s^{z_t - 1} 2cos(2 pi s) ds: Psi is the improper Mellin integral of
2 cos(2 pi s) on the critical line. -/
theorem tendsto_integral_Psi (t : ℝ) :
    Tendsto (fun R => ∫ s in (0 : ℝ)..R, pD t 0 s) atTop (𝓝 (Psi (zt t))) := by
  have hK : Tendsto (fun R : ℝ => Kt t * R ^ (-1 / 2 : ℝ)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (Kt t)
    rw [mul_zero] at this
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num]
    exact this
  have hPhi0 : Tendsto (fun R => Phi t R) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hK
    filter_upwards [eventually_gt_atTop 0] with R hR
    exact norm_Phi_le hR
  have h := (tendsto_const_nhds (x := Psi (zt t))).sub hPhi0
  rw [sub_zero] at h
  refine h.congr' (Eventually.of_forall fun R => ?_)
  simp [Phi, Gpart]

/-- Phi_t(a) = lim_{R -> ∞} ∫_a^R s^{z_t - 1} 2cos(2 pi s) ds  (the improper integral A e_t). -/
theorem tendsto_integral_Phi {t a : ℝ} (ha : 0 < a) :
    Tendsto (fun R => ∫ s in a..R, pD t 0 s) atTop (𝓝 (Phi t a)) := by
  have h := (tendsto_integral_Psi t).sub_const (Gpart t 0 a)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with R hR
  rw [← Gpart_sub ha.le hR]; rfl

lemma hasDerivAt_Gpart {t ε a : ℝ} (hε : 0 ≤ ε) (ha : 0 < a) :
    HasDerivAt (Gpart t ε) (pD t ε a) a := by
  unfold Gpart
  exact intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_pD hε ha.le)
    ((continuousOn_pD t ε).stronglyMeasurableAtFilter isOpen_Ioi a ha)
    ((continuousOn_pD t ε).continuousAt (Ioi_mem_nhds ha))

lemma continuousOn_Phi (t : ℝ) : ContinuousOn (Phi t) (Ioi 0) := fun _ ha =>
  (continuousAt_const.sub (hasDerivAt_Gpart (t := t) le_rfl ha).continuousAt).continuousWithinAt

/-- a |-> |Phi_t(a)|^2 / a is integrable on (1, ∞). -/
theorem integrableOn_normSq_Phi (t : ℝ) :
    IntegrableOn (fun a => ‖Phi t a‖ ^ 2 / a) (Ioi 1) := by
  have hb := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).const_mul (Kt t ^ 2)
  refine hb.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact (((continuousOn_Phi t).mono (Ioi_subset_Ioi zero_le_one)).norm.pow 2).div continuousOn_id
      fun a ha => (lt_trans zero_lt_one ha).ne'
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun a ha => ?_)
    have ha0 : (0 : ℝ) < a := lt_trans zero_lt_one ha
    have hb := norm_Phi_le (t := t) ha0
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hsq : ‖Phi t a‖ ^ 2 ≤ (Kt t * a ^ (-1 / 2 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    have e : (Kt t * a ^ (-1 / 2 : ℝ)) ^ 2 / a = Kt t ^ 2 * a ^ (-2 : ℝ) := by
      rw [mul_pow, ← Real.rpow_natCast (a ^ (-1 / 2 : ℝ)), ← Real.rpow_mul ha0.le,
        show (-2 : ℝ) = (-1 / 2 * ((2 : ℕ) : ℝ)) + (-1) by norm_num, Real.rpow_add ha0,
        Real.rpow_neg_one]
      field_simp
    rw [← e]
    exact div_le_div_of_nonneg_right hsq ha0.le

/-- N(t) = ∫_1^∞ |Phi_t(a)|^2 da / a = ‖A e_t‖^2. -/
def Nnorm (t : ℝ) : ℝ := ∫ a in Ioi (1 : ℝ), ‖Phi t a‖ ^ 2 / a

lemma Nnorm_nonneg (t : ℝ) : 0 ≤ Nnorm t :=
  setIntegral_nonneg measurableSet_Ioi fun a ha => by
    have : (0 : ℝ) < a := lt_trans zero_lt_one ha
    positivity

end ArchS3
