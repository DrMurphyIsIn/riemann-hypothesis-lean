/-
  E6Bridge21 -- Obligation 2 of E6Bridge18: real-axis decay of (log xi)'' (2026-09-21).

  THE TARGET.  RvMBridge18.XiLogDerivDerivDecay :
      Tendsto (fun sigma : R => deriv (logDeriv xi) (sigma : C)) atTop (nhds 0).

  THE ARGUMENT (pure asymptotics; nothing here bears on RH; conjecture1_proved = False).
  On the open half-plane Re s > 1 the four hypotheses of logDeriv_xi_eq (E6Bridge18) and
  logDeriv_completedZeta (Zeta23.WeilEF) hold, and Lambda = Gamma_R * zeta with both factors
  nonvanishing, so

      logDeriv xi s = s^{-1} + (s-1)^{-1} + (-(log pi)/2 + (1/2) psi(s/2)) - L(Lambda)(s)

  (Zeta23.RvM.logDeriv_Gammaℝ for the Gamma_R factor, LSeries_vonMangoldt_eq_deriv_riemannZeta_div
  for zeta'/zeta = -L(Lambda)).  Differentiating this identity termwise on the open set gives

      deriv (logDeriv xi) sigma = -1/sigma^2 - 1/(sigma-1)^2 + (1/4) psi'(sigma/2) + L(log * Lambda)(sigma)

  (deriv_logDeriv_xi_real, with the last term written as deriv (logDeriv riemannZeta) sigma).
  Each piece tends to 0:
    * the rational terms trivially;
    * psi'(x) = Sum_{n >= 0} 1/(x+n)^2 <= 1/(x - 1/2) for real x >= 1 (norm_deriv_digamma_real_le).
      Zeta23.Stirling.hasSum_trigamma gives the series off the integers; it is extended across the
      positive integers by continuity of both sides (hasSum_trigamma_of_re_pos), the series side by
      continuousOn_tsum with the uniform majorant 1/(n+1/2)^2 on Re w >= 1/2;
    * L(log * Lambda)(sigma) = Sum_n log n * Lambda(n) n^{-sigma} -> 0 by Tannery/dominated convergence
      against the sigma = 2 terms (zeta_logDeriv_deriv_tendsto_zero).

  DELIVERED.  xi_logDeriv_deriv_decay : RvMBridge18.XiLogDerivDerivDecay, kernel-clean
  (axioms [propext, Classical.choice, Quot.sound]); no named obligation remains on this side.

  2026-09-22: the COMPLEX-argument forms norm_term_le_of_two_le_re (‖term f s n‖ <= ‖term f 2 n‖ for
  Re s >= 2) and deriv_logDeriv_xi_of_one_lt_re (the termwise derivative on Re s > 1), which
  E6Bridge22 had re-proved, now live here (they need this module's digamma / LSeries machinery, so
  they cannot go in the prelude RvMBridgeXi); the real-axis forms below are their corollaries at
  s = sigma, statements unchanged.  Nothing about RH.  conjecture1_proved = False.
-/
import E6Bridge18
import RvMBridgeXi
import Zeta23.Analytic.Stirling
import Zeta23.RvM.GammaSide
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Dirichlet

open Zeta23 Complex Filter Topology
open scoped LSeries.notation ArithmeticFunction

noncomputable section

namespace RvMBridge21
open RvMBridge18

/-! ## A. The digamma function on the right half-plane. -/

lemma ne_neg_nat_of_re_pos {z : ℂ} (hz : 0 < z.re) : ∀ m : ℕ, z ≠ -(m : ℂ) := by
  intro m h
  have := congrArg Complex.re h
  simp only [Complex.neg_re, Complex.natCast_re] at this
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

lemma isOpen_re_pos : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re

lemma analyticAt_Gamma_of_re_pos {z : ℂ} (hz : 0 < z.re) : AnalyticAt ℂ Complex.Gamma z := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [isOpen_re_pos.mem_nhds hz] with w hw
  exact Complex.differentiableAt_Gamma w (ne_neg_nat_of_re_pos hw)

/-- psi is analytic on Re z > 0 (Gamma is analytic and nonvanishing there). -/
lemma analyticAt_digamma_of_re_pos {z : ℂ} (hz : 0 < z.re) : AnalyticAt ℂ Complex.digamma z := by
  have hΓ := analyticAt_Gamma_of_re_pos hz
  have hne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero (ne_neg_nat_of_re_pos hz)
  refine (hΓ.deriv.div hΓ hne).congr ?_
  filter_upwards with w
  rw [Complex.digamma_def, logDeriv_apply]
  rfl

lemma continuousAt_deriv_digamma {z : ℂ} (hz : 0 < z.re) :
    ContinuousAt (deriv Complex.digamma) z :=
  (analyticAt_digamma_of_re_pos hz).deriv.continuousAt

/-! ## B. The trigamma series on Re z > 1/2, including the positive integers. -/

/-- The trigamma term. -/
def trigTerm (w : ℂ) (n : ℕ) : ℂ := 1 / (w + n) ^ 2

lemma norm_trigTerm_le {w : ℂ} (hw : 1 / 2 ≤ w.re) (n : ℕ) :
    ‖trigTerm w n‖ ≤ 1 / ((n : ℝ) + 1 / 2) ^ 2 := by
  unfold trigTerm
  rw [norm_div, norm_one, norm_pow]
  have hre : (n : ℝ) + 1 / 2 ≤ ‖w + n‖ := by
    have h1 : (w + n).re ≤ ‖w + n‖ := Complex.re_le_norm _
    rw [Complex.add_re, Complex.natCast_re] at h1
    linarith
  have hpos : (0 : ℝ) < (n : ℝ) + 1 / 2 := by positivity
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hpos.le hre 2)

lemma summable_trigBound : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1 / 2) ^ 2) := by
  have h1 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have h2 := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa [add_comm] using h2
  refine (h1.mul_left 4).of_nonneg_of_le (fun n => by positivity) fun n => ?_
  have hpos : (0 : ℝ) < (n : ℝ) + 1 / 2 := by positivity
  rw [← mul_div_assoc, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg ((n : ℝ) + 1), sq_nonneg ((n : ℝ))]

lemma continuousOn_trigSum :
    ContinuousOn (fun w : ℂ => ∑' n : ℕ, trigTerm w n) {w : ℂ | 1 / 2 < w.re} := by
  refine continuousOn_tsum (fun n => ?_) summable_trigBound fun n w hw => norm_trigTerm_le (le_of_lt hw) n
  intro w hw
  have hne : w + n ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [Complex.add_re, Complex.natCast_re, Complex.zero_re] at this
    have hw' : 1 / 2 < w.re := hw
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  unfold trigTerm
  exact ((continuousAt_const.div ((continuous_id.add continuous_const).continuousAt.pow 2)
    (pow_ne_zero 2 hne))).continuousWithinAt

lemma summable_trigTerm {w : ℂ} (hw : 1 / 2 ≤ w.re) : Summable (trigTerm w) :=
  Summable.of_norm_bounded summable_trigBound (norm_trigTerm_le hw)

/-- An integer within distance < 1/2 of the integer z is z itself. -/
lemma eq_of_intCast_near {k j : ℤ} (h : ‖(j : ℂ) - (k : ℂ)‖ < 1 / 2) : (j : ℂ) = (k : ℂ) := by
  have h1 : ‖((j - k : ℤ) : ℂ)‖ < 1 / 2 := by push_cast; exact h
  rw [Complex.norm_intCast] at h1
  have h2 : |j - k| < (1 : ℤ) := by
    have h3 : |((j - k : ℤ) : ℝ)| < 1 := by linarith
    exact_mod_cast h3
  have h4 : j - k = 0 := Int.abs_lt_one_iff.mp h2
  have : j = k := by omega
  rw [this]

/-- **The trigamma series on Re z > 1/2**: psi'(z) = Sum_{n >= 0} 1/(z+n)^2.  Zeta23 gives it off
the integers (Stirling.hasSum_trigamma); at a positive integer both sides are continuous and the
identity holds on the punctured neighbourhood. -/
theorem hasSum_trigamma_of_re_pos {z : ℂ} (hz : 1 / 2 < z.re) :
    HasSum (fun n : ℕ => 1 / (z + n) ^ 2) (deriv Complex.digamma z) := by
  by_cases hzI : z ∈ Complex.integerComplement
  · exact Zeta23.Stirling.hasSum_trigamma hzI
  · -- z is an integer; compare the two continuous sides on the punctured neighbourhood
    obtain ⟨k, hk⟩ : ∃ n : ℤ, (n : ℂ) = z := by
      by_contra hne
      exact hzI hne
    have hsum : Summable (trigTerm z) := summable_trigTerm (le_of_lt hz)
    suffices hEq : (∑' n : ℕ, trigTerm z n) = deriv Complex.digamma z by
      have := hsum.hasSum
      rw [hEq] at this
      exact this
    -- both sides are continuous at z and agree on the punctured neighbourhood (the prelude's atom)
    have hopen : IsOpen {w : ℂ | 1 / 2 < w.re} := isOpen_lt continuous_const continuous_re
    refine RvMBridgeXi.eq_of_continuousAt_of_eventually_ne
      (continuousOn_trigSum.continuousAt (hopen.mem_nhds hz)) (continuousAt_deriv_digamma (by linarith)) ?_
    have hball : Metric.ball z (1 / 2) ∈ 𝓝 z := Metric.ball_mem_nhds z (by norm_num)
    filter_upwards [hball] with w hwb hwne
    have hwI : w ∈ Complex.integerComplement := by
      rintro ⟨j, hj⟩
      apply hwne
      rw [← hj, ← hk]
      refine eq_of_intCast_near ?_
      rw [Metric.mem_ball, dist_eq_norm] at hwb
      rw [hj, hk]
      exact hwb
    exact (Zeta23.Stirling.hasSum_trigamma hwI).tsum_eq

/-! ## C. The trigamma bound on the real ray: psi'(x) <= 1/(x - 1/2) for x >= 1. -/

lemma sum_range_inv_sq_le {x : ℝ} (hx : 1 ≤ x) (N : ℕ) :
    ∑ i ∈ Finset.range N, 1 / (x + i) ^ 2 ≤ 1 / (x - 1 / 2) - 1 / (x + N - 1 / 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have ha : 1 ≤ x + N := by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith
    set a : ℝ := x + N with ha_def
    have hstep : 1 / a ^ 2 ≤ 1 / (a - 1 / 2) - 1 / (a + 1 / 2) := by
      have hne1 : a - 1 / 2 ≠ 0 := by linarith
      have hne2 : a + 1 / 2 ≠ 0 := by linarith
      have hprod : 0 < (a - 1 / 2) * (a + 1 / 2) := by nlinarith
      rw [div_sub_div _ _ hne1 hne2, div_le_div_iff₀ (by positivity) hprod]
      nlinarith
    have hN : x + ((N + 1 : ℕ) : ℝ) - 1 / 2 = a + 1 / 2 := by
      push_cast; ring
    rw [hN]
    linarith

lemma summable_inv_sq_real {x : ℝ} (hx : 1 ≤ x) : Summable (fun n : ℕ => 1 / (x + n) ^ 2) := by
  refine summable_of_sum_range_le (c := 1 / (x - 1 / 2))
    (fun n => div_nonneg zero_le_one (sq_nonneg _)) fun N => ?_
  refine (sum_range_inv_sq_le hx N).trans ?_
  have : 0 ≤ 1 / (x + N - 1 / 2) := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    exact div_nonneg zero_le_one (by linarith)
  linarith

lemma tsum_inv_sq_real_le {x : ℝ} (hx : 1 ≤ x) : ∑' n : ℕ, 1 / (x + n) ^ 2 ≤ 1 / (x - 1 / 2) := by
  refine Real.tsum_le_of_sum_range_le (fun n => div_nonneg zero_le_one (sq_nonneg _)) fun N => ?_
  refine (sum_range_inv_sq_le hx N).trans ?_
  have : 0 ≤ 1 / (x + N - 1 / 2) := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    exact div_nonneg zero_le_one (by linarith)
  linarith

lemma norm_trigTerm_real (x : ℝ) (n : ℕ) : ‖(1 : ℂ) / ((x : ℂ) + n) ^ 2‖ = 1 / (x + n) ^ 2 := by
  rw [norm_div, norm_one, norm_pow]
  rw [show (x : ℂ) + n = ((x + n : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real, Real.norm_eq_abs,
    sq_abs]

/-- **The trigamma bound on the real ray.** -/
theorem norm_deriv_digamma_real_le {x : ℝ} (hx : 1 ≤ x) :
    ‖deriv Complex.digamma (x : ℂ)‖ ≤ 1 / (x - 1 / 2) := by
  have hre : 1 / 2 < (x : ℂ).re := by rw [Complex.ofReal_re]; linarith
  rw [← (hasSum_trigamma_of_re_pos hre).tsum_eq]
  have hn : Summable (fun n : ℕ => ‖(1 : ℂ) / ((x : ℂ) + n) ^ 2‖) := by
    simp_rw [norm_trigTerm_real]
    exact summable_inv_sq_real hx
  refine (norm_tsum_le_tsum_norm hn).trans ?_
  simp_rw [norm_trigTerm_real]
  exact tsum_inv_sq_real_le hx

/-- Stage lemma: psi'(sigma/2) -> 0 as sigma -> +infinity along the real axis. -/
theorem digamma_deriv_tendsto_zero :
    Tendsto (fun σ : ℝ => deriv Complex.digamma ((σ : ℂ) / 2)) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun σ : ℝ => 1 / (σ / 2 - 1 / 2)) ?_ ?_
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with σ hσ
    rw [show (σ : ℂ) / 2 = ((σ / 2 : ℝ) : ℂ) by push_cast; rfl]
    exact norm_deriv_digamma_real_le (by linarith)
  · refine tendsto_const_nhds.div_atTop ?_
    exact tendsto_atTop_add_const_right atTop (-(1 / 2)) (tendsto_id.atTop_div_const two_pos)

/-! ## D. The zeta side: (zeta'/zeta)' = L(log * Lambda) on Re s > 1, and it decays. -/

lemma abscissa_vonMangoldt_le_one : LSeries.abscissaOfAbsConv ↗Λ ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hy)

lemma abscissa_vonMangoldt_lt {s : ℂ} (hs : 1 < s.re) : LSeries.abscissaOfAbsConv ↗Λ < s.re :=
  abscissa_vonMangoldt_le_one.trans_lt (by exact_mod_cast hs)

lemma isOpen_one_lt_re : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const continuous_re

/-- zeta'/zeta = -L(Lambda) on Re s > 1. -/
lemma logDeriv_zeta_eq {s : ℂ} (hs : 1 < s.re) : logDeriv riemannZeta s = -LSeries ↗Λ s := by
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, logDeriv_apply, neg_div,
    neg_neg]

/-- (zeta'/zeta)'(s) = L(log * Lambda)(s) on Re s > 1. -/
theorem deriv_logDeriv_zeta_eq {s : ℂ} (hs : 1 < s.re) :
    deriv (logDeriv riemannZeta) s = LSeries (LSeries.logMul ↗Λ) s := by
  have hev : logDeriv riemannZeta =ᶠ[𝓝 s] fun z => -LSeries ↗Λ z := by
    filter_upwards [isOpen_one_lt_re.mem_nhds hs] with z hz
    exact logDeriv_zeta_eq hz
  have h4 : HasDerivAt (fun z : ℂ => -LSeries ↗Λ z) (-(-LSeries (LSeries.logMul ↗Λ) s)) s :=
    (LSeries_hasDerivAt (abscissa_vonMangoldt_lt hs)).neg
  rw [hev.deriv_eq, h4.deriv, neg_neg]

lemma term_logMul_one (f : ℕ → ℂ) (s : ℂ) : LSeries.term (LSeries.logMul f) s 1 = 0 := by
  rw [LSeries.term_of_ne_zero one_ne_zero]
  simp [LSeries.logMul]

lemma term_tendsto_zero (f : ℕ → ℂ) (n : ℕ) :
    Tendsto (fun σ : ℝ => LSeries.term (LSeries.logMul f) (σ : ℂ) n) atTop (𝓝 0) := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simp only [LSeries.term_zero]; exact tendsto_const_nhds
    · simp only [term_logMul_one]; exact tendsto_const_nhds
  · have hn0 : n ≠ 0 := by omega
    refine squeeze_zero_norm' (a := fun σ : ℝ => ‖LSeries.logMul f n‖ / (n : ℝ) ^ σ) ?_ ?_
    · filter_upwards with σ
      rw [LSeries.norm_term_eq, if_neg hn0, Complex.ofReal_re]
    · refine tendsto_const_nhds.div_atTop ?_
      exact tendsto_rpow_atTop_of_base_gt_one (n : ℝ) (by exact_mod_cast hn)

/-- ‖term f s n‖ ≤ ‖term f 2 n‖ for Re s ≥ 2 (complex argument). -/
lemma norm_term_le_of_two_le_re (f : ℕ → ℂ) {s : ℂ} (hs : 2 ≤ s.re) (n : ℕ) :
    ‖LSeries.term f s n‖ ≤ ‖LSeries.term f (2 : ℂ) n‖ := by
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, if_neg hn]
    have h2 : ((2 : ℂ)).re = (2 : ℝ) := by simp
    rw [h2]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
      (Real.rpow_le_rpow_of_exponent_le hn1 hs)

/-- The real-axis form: ‖term f σ n‖ ≤ ‖term f 2 n‖ for real σ ≥ 2. -/
lemma norm_term_le_of_two_le (f : ℕ → ℂ) {σ : ℝ} (hσ : 2 ≤ σ) (n : ℕ) :
    ‖LSeries.term f (σ : ℂ) n‖ ≤ ‖LSeries.term f (2 : ℂ) n‖ :=
  norm_term_le_of_two_le_re f (by rw [Complex.ofReal_re]; exact hσ) n

/-- Stage lemma: (zeta'/zeta)'(sigma) -> 0 as sigma -> +infinity (Tannery against the sigma = 2
terms of the Dirichlet series of L(log * Lambda)). -/
theorem zeta_logDeriv_deriv_tendsto_zero :
    Tendsto (fun σ : ℝ => deriv (logDeriv riemannZeta) (σ : ℂ)) atTop (𝓝 0) := by
  have hL : Tendsto (fun σ : ℝ => LSeries (LSeries.logMul ↗Λ) (σ : ℂ)) atTop (𝓝 0) := by
    have h0 : (0 : ℂ) = ∑' n : ℕ, (0 : ℂ) := tsum_zero.symm
    rw [h0]
    have hsum : Summable (fun n : ℕ => ‖LSeries.term (LSeries.logMul ↗Λ) (2 : ℂ) n‖) := by
      refine summable_norm_iff.mpr ?_
      exact LSeriesSummable_logMul_of_lt_re (abscissa_vonMangoldt_lt (by simp))
    refine tendsto_tsum_of_dominated_convergence hsum (fun n => term_tendsto_zero _ n) ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with σ hσ n
    exact norm_term_le_of_two_le _ hσ n
  refine hL.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with σ hσ
  rw [deriv_logDeriv_zeta_eq (by rw [Complex.ofReal_re]; linarith)]

/-! ## E. The termwise formula for deriv (logDeriv xi) on the real ray. -/

/-- On Re s > 1: logDeriv xi = s^{-1} + (s-1)^{-1} + Gamma_R'/Gamma_R + zeta'/zeta, with the
last two in closed form. -/
lemma logDeriv_xi_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    logDeriv xi s = s⁻¹ + (s - 1)⁻¹
      + (-(Real.log Real.pi : ℂ) / 2 + (1 / 2 : ℂ) * Complex.digamma (s / 2)) + (-LSeries ↗Λ s) := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hs; linarith
  have hs1 : s ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hs; linarith
  have hre : 0 < s.re := by linarith
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hΛ : completedRiemannZeta s ≠ 0 := by
    have h := riemannZeta_def_of_ne_zero hs0
    intro h0
    rw [h0, zero_div] at h
    exact hζ h
  rw [logDeriv_xi_eq hs0 hs1 hΛ, Zeta23.WeilEF.logDeriv_completedZeta s hs1 hζ hre,
    Zeta23.RvM.logDeriv_Gammaℝ hre, logDeriv_zeta_eq hs, one_div, one_div]
  ring

/-- **Stage lemma (the termwise derivative), complex argument.**  On Re s > 1,
deriv (logDeriv xi) s = -1/s^2 - 1/(s-1)^2 + (1/4) psi'(s/2) + (zeta'/zeta)'(s). -/
theorem deriv_logDeriv_xi_of_one_lt_re {s : ℂ} (hre : 1 < s.re) :
    deriv (logDeriv xi) s = -1 / s ^ 2 - 1 / (s - 1) ^ 2
      + (1 / 4 : ℂ) * deriv Complex.digamma (s / 2) + deriv (logDeriv riemannZeta) s := by
  have hev : logDeriv xi =ᶠ[𝓝 s] fun z => z⁻¹ + (z - 1)⁻¹
      + (-(Real.log Real.pi : ℂ) / 2 + (1 / 2 : ℂ) * Complex.digamma (z / 2)) + (-LSeries ↗Λ z) := by
    filter_upwards [isOpen_one_lt_re.mem_nhds hre] with z hz
    exact logDeriv_xi_eq_of_one_lt_re hz
  have hs0 : s ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hre; linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at this; linarith
  have h1 : HasDerivAt (fun z : ℂ => z⁻¹) (-1 / s ^ 2) s :=
    (hasDerivAt_inv hs0).congr_deriv (by ring)
  have h2 : HasDerivAt (fun z : ℂ => (z - 1)⁻¹) (-1 / (s - 1) ^ 2) s :=
    ((hasDerivAt_inv hs1).comp s ((hasDerivAt_id' s).sub_const 1)).congr_deriv (by ring)
  have hψ : HasDerivAt (fun z : ℂ => Complex.digamma (z / 2))
      (deriv Complex.digamma (s / 2) * (1 / 2)) s := by
    have hd : DifferentiableAt ℂ Complex.digamma (s / 2) := by
      refine (analyticAt_digamma_of_re_pos ?_).differentiableAt
      rw [Complex.div_re]
      simp only [Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_ofNat]
      linarith
    have hin : HasDerivAt (fun z : ℂ => z / 2) (1 / 2) s := by
      simpa using (hasDerivAt_id s).div_const 2
    exact hd.hasDerivAt.comp s hin
  have h3 : HasDerivAt (fun z : ℂ => -(Real.log Real.pi : ℂ) / 2 + (1 / 2 : ℂ) * Complex.digamma (z / 2))
      ((1 / 2 : ℂ) * (deriv Complex.digamma (s / 2) * (1 / 2))) s :=
    (hψ.const_mul (1 / 2 : ℂ)).const_add _
  have h4 : HasDerivAt (fun z : ℂ => -LSeries ↗Λ z) (-(-LSeries (LSeries.logMul ↗Λ) s)) s :=
    (LSeries_hasDerivAt (abscissa_vonMangoldt_lt hre)).neg
  have hall : HasDerivAt (fun z : ℂ => z⁻¹ + (z - 1)⁻¹
      + (-(Real.log Real.pi : ℂ) / 2 + (1 / 2 : ℂ) * Complex.digamma (z / 2)) + (-LSeries ↗Λ z))
      (-1 / s ^ 2 + -1 / (s - 1) ^ 2
        + (1 / 2 : ℂ) * (deriv Complex.digamma (s / 2) * (1 / 2))
        + -(-LSeries (LSeries.logMul ↗Λ) s)) s :=
    ((h1.add h2).add h3).add h4
  rw [hev.deriv_eq, hall.deriv, deriv_logDeriv_zeta_eq hre]
  ring

/-- **Stage lemma (the termwise derivative), real axis.**  For real sigma >= 2,
deriv (logDeriv xi)(sigma) = -1/sigma^2 - 1/(sigma-1)^2 + (1/4) psi'(sigma/2) + (zeta'/zeta)'(sigma):
the complex form at s = sigma. -/
theorem deriv_logDeriv_xi_real {σ : ℝ} (hσ : 2 ≤ σ) :
    deriv (logDeriv xi) (σ : ℂ) = -1 / (σ : ℂ) ^ 2 - 1 / ((σ : ℂ) - 1) ^ 2
      + (1 / 4 : ℂ) * deriv Complex.digamma ((σ : ℂ) / 2)
      + deriv (logDeriv riemannZeta) (σ : ℂ) :=
  deriv_logDeriv_xi_of_one_lt_re (by rw [Complex.ofReal_re]; linarith)

/-! ## F. Assembly: Obligation 2 of E6Bridge18. -/

lemma tendsto_neg_inv_sq : Tendsto (fun σ : ℝ => -1 / (σ : ℂ) ^ 2) atTop (𝓝 0) := by
  have h : Tendsto (fun σ : ℝ => (-1 : ℝ) / σ ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
  have h' := (Complex.continuous_ofReal.tendsto 0).comp h
  rw [Complex.ofReal_zero] at h'
  refine h'.congr' ?_
  filter_upwards with σ
  simp [Function.comp]

lemma tendsto_inv_sub_one_sq : Tendsto (fun σ : ℝ => 1 / ((σ : ℂ) - 1) ^ 2) atTop (𝓝 0) := by
  have h : Tendsto (fun σ : ℝ => (1 : ℝ) / (σ - 1) ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_right atTop (-1) tendsto_id))
  have h' := (Complex.continuous_ofReal.tendsto 0).comp h
  rw [Complex.ofReal_zero] at h'
  refine h'.congr' ?_
  filter_upwards with σ
  simp [Function.comp, sub_eq_add_neg]

/-- **Obligation 2 of E6Bridge18, discharged.**  deriv (logDeriv xi)(sigma) -> 0 as sigma -> +infinity
along the real axis. -/
theorem xi_logDeriv_deriv_decay : RvMBridge18.XiLogDerivDerivDecay := by
  unfold RvMBridge18.XiLogDerivDerivDecay
  have h := ((tendsto_neg_inv_sq.sub tendsto_inv_sub_one_sq).add
    (digamma_deriv_tendsto_zero.const_mul (1 / 4 : ℂ))).add zeta_logDeriv_deriv_tendsto_zero
  simp only [sub_zero, mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with σ hσ
  rw [deriv_logDeriv_xi_real hσ]

/-- The interface identity of E6Bridge18 now rests on XiDiffRegular alone. -/
theorem xi_logDeriv_deriv_eq_of_regular (h1 : RvMBridge18.XiDiffRegular) :
    RvMBridge18.XiLogDerivDerivEq :=
  RvMBridge18.xi_logDeriv_deriv_eq_of h1 xi_logDeriv_deriv_decay

end RvMBridge21
