/-
  ArchS4_Rung -- stage S4' of the archimedean conceptual blueprint (2026-10-11): the "delta rung",
  a pipeline test of CC Corollary 3.8 (the crude L¹/sup route, no matrix, no prolates).

  CLOSED FORM (kappaD_eq): the 1/4·deltaE terms cancel in kappaD = -deltaE''(|x|) + deltaE(|x|)/4:
      kappaD x = 2 e^{y/2} [4π e^y (S₁(α) + S₁(β)) + 4π² e^{2y} (C₂(α) + C₂(β))],  y = |x|,
  with α = 2π(1+e^y), β = 2π(e^y - 1), S₁ = Sm 1, C₂ = Cm 2 (square moments, ArchS4_Delta).
  Checked against mpmath to 20 digits (kappaD 0 = 8.39172...).  |S₁| ≤ 1/4 and |C₂| ≤ 1/9 give
      |kappaD x| ≤ 35  for |x| ≤ 1/40                                            (abs_kappaD_le)
  CC Cor 3.8 then gives D∘Q ≤ 0: |autocorr h| ≤ ‖h‖² (Cauchy-Schwarz) and autocorr h vanishes
  off [-2L, 2L], so for L ≤ 1/80
      Re D(autocorr g) ≤ -2‖h‖² + 4L·35·‖h‖² ≤ 0                                  (DQ_nonpos)
  for every g = h' - h/2 with tsupport h ⊆ [-L, L], hence for every pole-free window test
  (DQ_nonpos_poleFree).  With CC Corollary 2.3 (stage S3, NOT proved here; an explicit
  hypothesis hCC) this gives Weil positivity on the pole-free window L ≤ 1/80
  (weil_nonneg_of_CC_cor23).
  The window 1/80 is far below the proved L ≤ 1/10 and below CC's own 0.0488 (which integrates
  |kappa| numerically instead of using a sup bound).  This is a PIPELINE TEST only.
  conjecture1_proved = False.  Nothing here is RH progress.
-/
import ArchS4_Jump

open Zeta23 MeasureTheory Set Complex
open scoped ComplexConjugate

noncomputable section

namespace ArchS4
open WeilExplicit RvMBridge31

/-! ## A. Moment bounds. -/

lemma integral_sq_pow (k : ℕ) : ∫ p, (p.1 * p.2) ^ k ∂sq = 1 / ((k : ℝ) + 1) ^ 2 := by
  unfold sq
  simp_rw [mul_pow]
  rw [integral_prod_mul (fun s : ℝ => s ^ k) (fun r : ℝ => r ^ k)]
  have h1 : ∫ s in Icc (0 : ℝ) 1, s ^ k = 1 / ((k : ℝ) + 1) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one, integral_pow]
    simp
  rw [h1, div_mul_div_comm, one_mul, pow_two]

lemma abs_mom_le {φ : ℝ → ℝ} (hb : ∀ y, |φ y| ≤ 1) (k : ℕ) (a : ℝ) :
    |mom φ k a| ≤ 1 / ((k : ℝ) + 1) ^ 2 := by
  rw [← integral_sq_pow k, ← Real.norm_eq_abs]
  unfold mom
  refine norm_integral_le_of_norm_le ?_ ?_
  · exact Integrable.of_bound ((continuous_fst.mul continuous_snd).pow k).aestronglyMeasurable 1
      (by
        filter_upwards [ae_sq] with p hp
        rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg hp.1]
        exact pow_le_one₀ hp.1 hp.2)
  · filter_upwards [ae_sq] with p hp
    rw [norm_mul, norm_pow, Real.norm_of_nonneg hp.1]
    exact mul_le_of_le_one_right (pow_nonneg hp.1 _) (by rw [Real.norm_eq_abs]; exact hb _)

lemma abs_Sm_one (a : ℝ) : |Sm 1 a| ≤ 1 / 4 := by
  have := abs_mom_le Real.abs_sin_le_one 1 a
  norm_num at this
  exact this

lemma abs_Cm_two (a : ℝ) : |Cm 2 a| ≤ 1 / 9 := by
  have := abs_mom_le Real.abs_cos_le_one 2 a
  norm_num at this
  exact this

/-! ## B. The closed form of kappaD. -/

/-- α(x) = 2π(1 + e^x), β(x) = 2π(e^x - 1). -/
def alphaE (x : ℝ) : ℝ := 2 * Real.pi * (1 + Real.exp x)
def betaE (x : ℝ) : ℝ := 2 * Real.pi * (Real.exp x - 1)

/-- F = S∘α + S∘β, so deltaE = 2 e^{x/2} F. -/
def FE (x : ℝ) : ℝ := ccS (alphaE x) + ccS (betaE x)
def FE1 (x : ℝ) : ℝ := -(2 * Real.pi * Real.exp x) * (Sm 1 (alphaE x) + Sm 1 (betaE x))
def FE2 (x : ℝ) : ℝ := -(2 * Real.pi * Real.exp x) * (Sm 1 (alphaE x) + Sm 1 (betaE x))
  - (2 * Real.pi * Real.exp x) ^ 2 * (Cm 2 (alphaE x) + Cm 2 (betaE x))

lemma hasDerivAt_alphaE (x : ℝ) : HasDerivAt alphaE (2 * Real.pi * Real.exp x) x := by
  unfold alphaE
  simpa using ((Real.hasDerivAt_exp x).const_add 1).const_mul (2 * Real.pi)

lemma hasDerivAt_betaE (x : ℝ) : HasDerivAt betaE (2 * Real.pi * Real.exp x) x := by
  unfold betaE
  simpa using ((Real.hasDerivAt_exp x).sub_const 1).const_mul (2 * Real.pi)

lemma hasDerivAt_FE (x : ℝ) : HasDerivAt FE (FE1 x) x := by
  have h := ((hasDerivAt_ccS _).comp x (hasDerivAt_alphaE x)).add
    ((hasDerivAt_ccS _).comp x (hasDerivAt_betaE x))
  refine h.congr_deriv ?_
  unfold FE1; ring

lemma hasDerivAt_FE1 (x : ℝ) : HasDerivAt FE1 (FE2 x) x := by
  have hc : HasDerivAt (fun x => -(2 * Real.pi * Real.exp x)) (-(2 * Real.pi * Real.exp x)) x :=
    ((Real.hasDerivAt_exp x).const_mul (2 * Real.pi)).neg
  have hS := ((hasDerivAt_Sm 1 _).comp x (hasDerivAt_alphaE x)).add
    ((hasDerivAt_Sm 1 _).comp x (hasDerivAt_betaE x))
  refine (hc.mul hS).congr_deriv ?_
  simp only [Pi.add_apply, Function.comp_apply]
  unfold FE2; ring

lemma deltaE_eq_FE : deltaE = fun x => 2 * Real.exp (x / 2) * FE x := rfl

lemma hasDerivAt_expHalfR (x : ℝ) :
    HasDerivAt (fun x => Real.exp (x / 2)) (Real.exp (x / 2) / 2) x := by
  have := (Real.hasDerivAt_exp (x / 2)).comp x ((hasDerivAt_id x).div_const 2)
  refine this.congr_deriv ?_
  ring

lemma deriv_deltaE_eq :
    deriv deltaE = fun x => Real.exp (x / 2) * FE x + 2 * Real.exp (x / 2) * FE1 x := by
  funext x
  rw [deltaE_eq_FE]
  have h : HasDerivAt (fun x => 2 * Real.exp (x / 2) * FE x)
      (2 * (Real.exp (x / 2) / 2) * FE x + 2 * Real.exp (x / 2) * FE1 x) x :=
    ((hasDerivAt_expHalfR x).const_mul 2).mul (hasDerivAt_FE x)
  rw [h.deriv]
  ring

lemma deriv_deriv_deltaE (x : ℝ) :
    deriv (deriv deltaE) x = Real.exp (x / 2) * (FE x / 2 + 2 * FE1 x + 2 * FE2 x) := by
  rw [deriv_deltaE_eq]
  have h : HasDerivAt (fun x => Real.exp (x / 2) * FE x + 2 * Real.exp (x / 2) * FE1 x)
      (Real.exp (x / 2) / 2 * FE x + Real.exp (x / 2) * FE1 x +
        (2 * (Real.exp (x / 2) / 2) * FE1 x + 2 * Real.exp (x / 2) * FE2 x)) x :=
    ((hasDerivAt_expHalfR x).mul (hasDerivAt_FE x)).add
      (((hasDerivAt_expHalfR x).const_mul 2).mul (hasDerivAt_FE1 x))
  rw [h.deriv]
  ring

/-- **Closed form of the jump kernel**: kappaD x = -2 e^{|x|/2} (F₁ + F₂)(|x|). -/
theorem kappaD_eq (x : ℝ) :
    kappaD x = -2 * Real.exp (|x| / 2) * (FE1 |x| + FE2 |x|) := by
  unfold kappaD
  rw [deriv_deriv_deltaE, deltaE_eq_FE]
  ring

/-! ## C. A crude sup bound on kappaD near 0. -/

lemma exp_le_of_small {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1 / 40) : Real.exp y ≤ 21 / 20 := by
  have := Real.exp_bound' h0 (by linarith) (n := 1) one_pos
  norm_num at this
  linarith

theorem abs_kappaD_le {x : ℝ} (hx : |x| ≤ 1 / 40) : |kappaD x| ≤ 35 := by
  rw [kappaD_eq]
  set y := |x| with hy
  have hy0 : 0 ≤ y := abs_nonneg x
  set e := Real.exp y with he
  have he1 : 1 ≤ e := Real.one_le_exp hy0
  have he2 : e ≤ 21 / 20 := exp_le_of_small hy0 hx
  have hh : Real.exp (y / 2) ≤ e := Real.exp_le_exp.2 (by linarith)
  have hh0 : 0 ≤ Real.exp (y / 2) := (Real.exp_pos _).le
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have b1 := abs_Sm_one (alphaE y)
  have b2 := abs_Sm_one (betaE y)
  have b3 := abs_Cm_two (alphaE y)
  have b4 := abs_Cm_two (betaE y)
  have hsum : |FE1 y + FE2 y| ≤ 2 * Real.pi * e + 8 / 9 * Real.pi ^ 2 * e ^ 2 := by
    have hrw : FE1 y + FE2 y = -(2 * (2 * Real.pi * e)) * (Sm 1 (alphaE y) + Sm 1 (betaE y))
        - (2 * Real.pi * e) ^ 2 * (Cm 2 (alphaE y) + Cm 2 (betaE y)) := by
      unfold FE1 FE2; rw [← he]; ring
    rw [hrw]
    have p1 : 0 ≤ 2 * Real.pi * e := by positivity
    calc |-(2 * (2 * Real.pi * e)) * (Sm 1 (alphaE y) + Sm 1 (betaE y))
          - (2 * Real.pi * e) ^ 2 * (Cm 2 (alphaE y) + Cm 2 (betaE y))|
        ≤ |-(2 * (2 * Real.pi * e)) * (Sm 1 (alphaE y) + Sm 1 (betaE y))|
          + |(2 * Real.pi * e) ^ 2 * (Cm 2 (alphaE y) + Cm 2 (betaE y))| := abs_sub _ _
      _ = 2 * (2 * Real.pi * e) * |Sm 1 (alphaE y) + Sm 1 (betaE y)|
          + (2 * Real.pi * e) ^ 2 * |Cm 2 (alphaE y) + Cm 2 (betaE y)| := by
          rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (2 * Real.pi * e)),
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * Real.pi * e) ^ 2)]
      _ ≤ 2 * (2 * Real.pi * e) * (1 / 4 + 1 / 4) + (2 * Real.pi * e) ^ 2 * (1 / 9 + 1 / 9) := by
          gcongr
          · exact (abs_add_le _ _).trans (add_le_add b1 b2)
          · exact (abs_add_le _ _).trans (add_le_add b3 b4)
      _ = 2 * Real.pi * e + 8 / 9 * Real.pi ^ 2 * e ^ 2 := by ring
  calc |-2 * Real.exp (y / 2) * (FE1 y + FE2 y)|
      = 2 * Real.exp (y / 2) * |FE1 y + FE2 y| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hh0]; norm_num
    _ ≤ 2 * e * (2 * Real.pi * e + 8 / 9 * Real.pi ^ 2 * e ^ 2) := by gcongr
    _ ≤ 2 * (21 / 20) * (2 * 3.15 * (21 / 20) + 8 / 9 * 3.15 ^ 2 * (21 / 20) ^ 2) := by
        gcongr
    _ ≤ 35 := by norm_num

/-! ## D. Cauchy-Schwarz and support of the autocorrelation. -/

lemma integrable_normSq_test {h : ℝ → ℂ} (hh : IsWeilTest h) :
    Integrable fun v => ‖h v‖ ^ 2 := by
  have hc : Continuous fun v => ‖h v‖ ^ 2 := hh.1.continuous.norm.pow 2
  have hs : HasCompactSupport ((fun z : ℂ => ‖z‖ ^ 2) ∘ h) := hh.2.comp_left (by norm_num)
  exact hc.integrable_of_hasCompactSupport hs

theorem norm_autocorr_le {h : ℝ → ℂ} (hh : IsWeilTest h) (u : ℝ) : ‖autocorr h u‖ ≤ mass h := by
  have i1 := integrable_normSq_test hh
  have i2 : Integrable fun v => ‖h (v - u)‖ ^ 2 := i1.comp_sub_right u
  unfold autocorr
  calc ‖∫ v, h v * conj (h (v - u))‖
      ≤ ∫ v, (‖h v‖ ^ 2 + ‖h (v - u)‖ ^ 2) / 2 := by
        refine norm_integral_le_of_norm_le ((i1.add i2).div_const 2)
          (Filter.Eventually.of_forall fun v => ?_)
        rw [norm_mul, Complex.norm_conj]
        nlinarith [sq_nonneg (‖h v‖ - ‖h (v - u)‖)]
    _ = mass h := by
        rw [integral_div, integral_add i1 i2,
          integral_sub_right_eq_self (fun v => ‖h v‖ ^ 2) u]
        unfold mass; ring

theorem autocorr_eq_zero_of_far {h : ℝ → ℂ} {L : ℝ} (hsupp : tsupport h ⊆ Icc (-L) L) {u : ℝ}
    (hu : 2 * L < |u|) : autocorr h u = 0 := by
  unfold autocorr
  have : (fun v => h v * conj (h (v - u))) = fun _ => 0 := by
    funext v
    by_cases hv : v ∈ Icc (-L) L
    · have : v - u ∉ Icc (-L) L := by
        intro hm
        have h1 := hv.1; have h2 := hv.2; have h3 := hm.1; have h4 := hm.2
        rcases le_or_gt 0 u with h5 | h5
        · rw [abs_of_nonneg h5] at hu; linarith
        · rw [abs_of_neg h5] at hu; linarith
      rw [zero_of_not_mem hsupp this]; simp
    · rw [zero_of_not_mem hsupp hv]; simp
  rw [this, integral_zero]

/-! ## E. CC Corollary 3.8 (crude): D∘Q ≤ 0 on a small window. -/

/-- CC's D in our variable: D(f) = ∫ f(u) delta(e^{|u|}) du. -/
def Dfun (f : ℝ → ℂ) : ℂ := ∫ u, f u * (deltaE |u| : ℂ)

/-- **D∘Q ≤ 0** for every g = h' - h/2 with tsupport h ⊆ [-L, L], 0 ≤ L ≤ 1/80. -/
theorem DQ_nonpos {g h : ℝ → ℂ} (hh : IsWeilTest h) (hgh : ∀ u, g u = deriv h u - h u / 2)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : L ≤ 1 / 80) (hsupp : tsupport h ⊆ Icc (-L) L) :
    (Dfun (autocorr g)).re ≤ 0 := by
  unfold Dfun
  rw [jump_lemma hh hgh]
  set m := mass h with hm
  have hm0 : 0 ≤ m := integral_nonneg fun u => by positivity
  set c : ℝ := m * 35 with hc
  have hbound : ‖∫ u, autocorr h u * (kappaD u : ℂ)‖
      ≤ ∫ u, (Icc (-(2 * L)) (2 * L)).indicator (fun _ => c) u := by
    refine norm_integral_le_of_norm_le
      ((continuous_const.integrableOn_Icc (μ := volume)).integrable_indicator measurableSet_Icc)
      (Filter.Eventually.of_forall fun u => ?_)
    by_cases hu : u ∈ Icc (-(2 * L)) (2 * L)
    · rw [Set.indicator_of_mem hu, norm_mul, Complex.norm_real, Real.norm_eq_abs, hc]
      have hu' : |u| ≤ 1 / 40 := by rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
      exact mul_le_mul (norm_autocorr_le hh u) (abs_kappaD_le hu') (abs_nonneg _) hm0
    · rw [Set.indicator_of_notMem hu]
      have hfar : 2 * L < |u| := by
        simp only [mem_Icc, not_and_or, not_le] at hu
        rcases hu with hu | hu
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      rw [autocorr_eq_zero_of_far hsupp hfar]; simp
  have hint : ∫ u, (Icc (-(2 * L)) (2 * L)).indicator (fun _ => c) u = 4 * L * c := by
    rw [integral_indicator_const c measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith),
      smul_eq_mul]
    ring
  have hre := Complex.re_le_norm (∫ u, autocorr h u * (kappaD u : ℂ))
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  norm_num
  nlinarith [hbound, hint, hre]

/-- **D∘Q ≤ 0 on the pole-free window** L ≤ 1/80 (via the S2 lift). -/
theorem DQ_nonpos_poleFree {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : L ≤ 1 / 80) (hsupp : tsupport g ⊆ Icc (-L) L) (h0 : paperFT g (I / 2) = 0) :
    (Dfun (autocorr g)).re ≤ 0 :=
  DQ_nonpos (ArchS2.isWeilTest_qLift hg hsupp h0) (ArchS2.qLift_rel hg L) hL0 hL
    (ArchS2.tsupport_qLift hg hsupp h0)

/-- **The delta rung (CC (57)), conditional on CC Corollary 2.3.**  If W∞ + D ≥ 0 on autocorr g
    (stage S3's target, taken here as the explicit hypothesis hCC, with archSide = W∞ on the
    pole-free class), then Weil positivity holds on the pole-free window L ≤ 1/80. -/
theorem weil_nonneg_of_CC_cor23 {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : L ≤ 1 / 80) (hsupp : tsupport g ⊆ Icc (-L) L) (h0 : paperFT g (I / 2) = 0)
    (hCC : 0 ≤ (archSide (autocorr g)).re + (Dfun (autocorr g)).re) :
    0 ≤ (weilForm (autocorr g)).re := by
  have hlog : 2 * L ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  rw [weilForm_autocorr_eq_archSide hg hsupp hlog]
  linarith [DQ_nonpos_poleFree hg hL0 hL hsupp h0]

end ArchS4
