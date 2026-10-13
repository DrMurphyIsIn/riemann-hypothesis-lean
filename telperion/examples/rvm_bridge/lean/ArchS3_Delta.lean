/-
  ArchS3_Delta -- the trace-remainder kernel delta and the functional L = W_inf + D
  (2026-10-11, stage S3 milestone M1 of telperion/docs/ARCHIMEDEAN_CONCEPTUAL_BLUEPRINT_2026-10-11.md).

  Connes-Consani (arXiv 2006.13771) (48): for rho >= 1,
      delta(rho) = 4 rho^{1/2} ∫_0^1 cos(2 pi rho t) cos(2 pi t) (-log t) dt.
  In the additive variable the kernel is delta(e^{|u|}) (even by construction, CC Prop 2.2(ii)).

  Proved here:
    * ∫_0^1 cos(c t)(-log t) dt = ∫_0^1 sinc(c t) dt  (= Si(c)/c; CC's "one can check" before (49));
    * the closed form (49) in sinc form; |Si| <= 4; the decay |delta(e^{|u|})| <= 8 e^{-|u|/2};
    * continuity, evenness, integrability of the kernel; delta(1) = 2 (Si(4 pi)/(4 pi) + 1);
    * the Parseval pairing D(g * g^*) = (1/2pi) ∫ |g^|^2 delta^ (generalising E6Bridge32.pairing);
    * the functional L = W_inf + D in Fourier form (1/2pi) ∫ |g^|^2 ell, ell = psiR - log pi + delta^,
      in u-space form via S1, and its link to archSide.

  No zeros, no RH progress.  conjecture1_proved = False.
-/
import ArchS1_Identity

open MeasureTheory Filter Topology Complex
open scoped ComplexConjugate

noncomputable section

namespace ArchS3

open WeilExplicit Zeta23 RvMBridge11 RvMBridge31 RvMBridge32 ArchS1

/-! ## A. The sinc form of CC's log integral. -/

lemma mul_sinc_eq {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    t * Real.sinc (c * t) = Real.sin (c * t) / c := by
  by_cases ht : t = 0
  · simp [ht]
  · rw [Real.sinc_of_ne_zero (mul_ne_zero hc ht)]
    field_simp

/-- d/dt (t sinc(c t)) = cos(c t): t sinc(c t) is the primitive ∫_0^t cos(c s) ds. -/
lemma hasDerivAt_mul_sinc (c t : ℝ) :
    HasDerivAt (fun s => s * Real.sinc (c * s)) (Real.cos (c * t)) t := by
  by_cases hc : c = 0
  · subst hc
    have e : (fun s : ℝ => s * Real.sinc (0 * s)) = fun s => s := by
      funext s; simp
    rw [e]
    exact (hasDerivAt_id' t).congr_deriv (by simp)
  · have e : (fun s : ℝ => s * Real.sinc (c * s)) = fun s => Real.sin (c * s) / c :=
      funext (mul_sinc_eq hc)
    rw [e]
    have h := (((hasDerivAt_id t).const_mul c).sin).div_const c
    refine h.congr_deriv ?_
    simp only [id, mul_one]
    field_simp

lemma continuous_mul_sinc (c : ℝ) : Continuous fun s : ℝ => s * Real.sinc (c * s) :=
  continuous_id.mul (Real.continuous_sinc.comp (continuous_const.mul continuous_id))

lemma intervalIntegrable_cos_mul_neg_log (c a b : ℝ) :
    IntervalIntegrable (fun t => Real.cos (c * t) * (-Real.log t)) volume a b := by
  have hl : IntervalIntegrable (fun t => -Real.log t) volume a b :=
    (intervalIntegral.intervalIntegrable_log').neg
  exact hl.continuousOn_mul (by fun_prop)

lemma intervalIntegrable_sinc_mul (c a b : ℝ) :
    IntervalIntegrable (fun t => Real.sinc (c * t)) volume a b :=
  (Real.continuous_sinc.comp (continuous_const.mul continuous_id)).intervalIntegrable a b

/-- CC's log integral in sinc form: ∫_0^1 cos(c t)(-log t) dt = ∫_0^1 sinc(c t) dt (= Si(c)/c). -/
theorem integral_cos_mul_neg_log (c : ℝ) :
    ∫ t in (0 : ℝ)..1, Real.cos (c * t) * (-Real.log t) = ∫ t in (0 : ℝ)..1, Real.sinc (c * t) := by
  -- H(t) = -(t sinc(ct)) log t = -sinc(ct) (t log t), continuous on [0,1], H(0) = H(1) = 0.
  set H : ℝ → ℝ := fun t => -(t * Real.sinc (c * t)) * Real.log t with hH
  have hHc : ContinuousOn H (Set.Icc 0 1) := by
    have e : H = fun t => -Real.sinc (c * t) * (t * Real.log t) := by
      funext t; simp only [hH]; ring
    rw [e]
    exact ((Real.continuous_sinc.comp (continuous_const.mul continuous_id)).neg.mul
      Real.continuous_mul_log).continuousOn
  have hHd : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt H (Real.cos (c * t) * (-Real.log t) - Real.sinc (c * t)) t := by
    intro t ht
    have ht0 : t ≠ 0 := ht.1.ne'
    have h := ((hasDerivAt_mul_sinc c t).neg).mul (Real.hasDerivAt_log ht0)
    refine h.congr_deriv ?_
    have : t * Real.sinc (c * t) * t⁻¹ = Real.sinc (c * t) := by field_simp
    simp only [Pi.neg_apply, neg_mul, this]
    ring
  have hint : IntervalIntegrable
      (fun t => Real.cos (c * t) * (-Real.log t) - Real.sinc (c * t)) volume 0 1 :=
    (intervalIntegrable_cos_mul_neg_log c 0 1).sub (intervalIntegrable_sinc_mul c 0 1)
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hHc hHd hint
  have h0 : H 1 - H 0 = 0 := by simp [hH]
  rw [h0, intervalIntegral.integral_sub (intervalIntegrable_cos_mul_neg_log c 0 1)
    (intervalIntegrable_sinc_mul c 0 1)] at hF
  linarith

/-! ## B. The kernel delta: CC (48) and its closed form (49). -/

/-- sincInt c = ∫_0^1 sinc(c t) dt = Si(c)/c (and = 1 at c = 0). -/
def sincInt (c : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, Real.sinc (c * t)

/-- CC (48): delta(rho) = 4 rho^{1/2} ∫_0^1 cos(2 pi rho t) cos(2 pi t) (-log t) dt (for rho >= 1). -/
def ccDelta (ρ : ℝ) : ℝ :=
  4 * Real.sqrt ρ * ∫ t in (0 : ℝ)..1,
    Real.cos (2 * Real.pi * ρ * t) * Real.cos (2 * Real.pi * t) * (-Real.log t)

/-- The additive-variable kernel delta(e^{|u|}), written in the closed form (49). -/
def deltaK (u : ℝ) : ℝ :=
  2 * Real.exp (|u| / 2) * (sincInt (2 * Real.pi * (Real.exp |u| + 1))
    + sincInt (2 * Real.pi * (Real.exp |u| - 1)))

lemma cos_mul_cos_eq (A B : ℝ) :
    Real.cos A * Real.cos B = (Real.cos (A + B) + Real.cos (A - B)) / 2 := by
  rw [Real.cos_add, Real.cos_sub]; ring

/-- CC (49) in sinc form: delta(rho) = 2 rho^{1/2} (Si(2pi(rho+1))/(2pi(rho+1)) + Si(2pi(rho-1))/(2pi(rho-1))). -/
theorem ccDelta_eq (ρ : ℝ) :
    ccDelta ρ = 2 * Real.sqrt ρ * (sincInt (2 * Real.pi * (ρ + 1)) + sincInt (2 * Real.pi * (ρ - 1))) := by
  unfold ccDelta sincInt
  have e : (fun t : ℝ => Real.cos (2 * Real.pi * ρ * t) * Real.cos (2 * Real.pi * t) * (-Real.log t))
      = fun t => (1 / 2) * (Real.cos (2 * Real.pi * (ρ + 1) * t) * (-Real.log t)
          + Real.cos (2 * Real.pi * (ρ - 1) * t) * (-Real.log t)) := by
    funext t
    rw [cos_mul_cos_eq, show 2 * Real.pi * ρ * t + 2 * Real.pi * t = 2 * Real.pi * (ρ + 1) * t by ring,
      show 2 * Real.pi * ρ * t - 2 * Real.pi * t = 2 * Real.pi * (ρ - 1) * t by ring]
    ring
  rw [e, intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    (intervalIntegrable_cos_mul_neg_log _ 0 1) (intervalIntegrable_cos_mul_neg_log _ 0 1),
    integral_cos_mul_neg_log, integral_cos_mul_neg_log]
  ring

lemma sqrt_exp_abs (u : ℝ) : Real.sqrt (Real.exp |u|) = Real.exp (|u| / 2) := by
  rw [show Real.exp |u| = Real.exp (|u| / 2) ^ 2 by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring]
  exact Real.sqrt_sq (Real.exp_pos _).le

/-- The kernel is CC's delta at e^{|u|} >= 1, via (48). -/
theorem deltaK_eq_ccDelta (u : ℝ) : deltaK u = ccDelta (Real.exp |u|) := by
  rw [ccDelta_eq, sqrt_exp_abs]; rfl

lemma deltaK_neg (u : ℝ) : deltaK (-u) = deltaK u := by simp [deltaK]

lemma sincInt_zero : sincInt 0 = 1 := by simp [sincInt]

lemma sincInt_neg (c : ℝ) : sincInt (-c) = sincInt c := by
  unfold sincInt
  congr 1; funext t
  rw [neg_mul, Real.sinc_neg]

/-- delta(1) = 2 (Si(4 pi)/(4 pi) + 1)  (CC (50), constant term). -/
lemma deltaK_zero : deltaK 0 = 2 * (sincInt (4 * Real.pi) + 1) := by
  simp only [deltaK, abs_zero, zero_div, Real.exp_zero, mul_one, sub_self, mul_zero, sincInt_zero]
  ring_nf

lemma continuous_sincInt : Continuous sincInt := by
  unfold sincInt
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun c t => Real.sinc (c * t)) (Real.continuous_sinc.comp (continuous_fst.mul continuous_snd)) 0 1

lemma continuous_deltaK : Continuous deltaK := by
  unfold deltaK
  have h1 : Continuous fun u : ℝ => Real.exp |u| := by fun_prop
  exact (continuous_const.mul (by fun_prop)).mul
    ((continuous_sincInt.comp (continuous_const.mul (h1.add continuous_const))).add
      (continuous_sincInt.comp (continuous_const.mul (h1.sub continuous_const))))

/-! ## C. Si is bounded, so delta decays like e^{-|u|/2}. -/

lemma abs_sincInt_le_one (c : ℝ) : |sincInt c| ≤ 1 := by
  unfold sincInt
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := 1) (f := fun t => Real.sinc (c * t)) (fun t _ => by
      rw [Real.norm_eq_abs]; exact Real.abs_sinc_le_one _)
  simpa using h

/-- c · sincInt c = ∫_0^c sinc = Si(c). -/
lemma mul_sincInt (c : ℝ) : c * sincInt c = ∫ s in (0 : ℝ)..c, Real.sinc s := by
  by_cases hc : c = 0
  · simp [hc]
  · unfold sincInt
    rw [intervalIntegral.integral_comp_mul_left (fun s => Real.sinc s) hc, mul_zero, mul_one,
      smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-- ∫_1^c sin s / s = cos 1 - cos c / c - ∫_1^c cos s / s^2 (integration by parts). -/
lemma integral_sin_div_eq {c : ℝ} (hc : 1 ≤ c) :
    ∫ s in (1 : ℝ)..c, Real.sin s / s
      = Real.cos 1 - Real.cos c / c - ∫ s in (1 : ℝ)..c, Real.cos s / s ^ 2 := by
  have hpos : ∀ s ∈ Set.uIcc (1 : ℝ) c, 0 < s := by
    intro s hs
    rw [Set.uIcc_of_le hc] at hs
    linarith [hs.1]
  have hcont1 : ContinuousOn (fun s : ℝ => Real.sin s / s) (Set.uIcc 1 c) :=
    Real.continuous_sin.continuousOn.div continuousOn_id fun s hs => (hpos s hs).ne'
  have hcont2 : ContinuousOn (fun s : ℝ => Real.cos s / s ^ 2) (Set.uIcc 1 c) :=
    Real.continuous_cos.continuousOn.div (continuousOn_id.pow 2) fun s hs =>
      pow_ne_zero 2 (hpos s hs).ne'
  -- F(s) = -cos s / s has F' = sin s / s + cos s / s^2.
  have hderiv : ∀ s ∈ Set.uIcc (1 : ℝ) c,
      HasDerivAt (fun s => -Real.cos s / s) (Real.sin s / s + Real.cos s / s ^ 2) s := by
    intro s hs
    have hs0 := (hpos s hs).ne'
    have h := ((Real.hasDerivAt_cos s).neg).div (hasDerivAt_id s) hs0
    refine h.congr_deriv ?_
    simp only [id, Pi.neg_apply]
    field_simp
    ring
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((hcont1.add hcont2).intervalIntegrable)
  rw [intervalIntegral.integral_add hcont1.intervalIntegrable hcont2.intervalIntegrable] at hF
  linear_combination hF

lemma abs_integral_cos_div_sq_le {c : ℝ} (hc : 1 ≤ c) :
    |∫ s in (1 : ℝ)..c, Real.cos s / s ^ 2| ≤ 1 := by
  have hpos : ∀ s ∈ Set.uIcc (1 : ℝ) c, 0 < s := by
    intro s hs
    rw [Set.uIcc_of_le hc] at hs
    linarith [hs.1]
  have hi2 : IntervalIntegrable (fun s : ℝ => 1 / s ^ 2) volume 1 c :=
    (continuousOn_const.div (continuousOn_id.pow 2) fun s hs =>
      pow_ne_zero 2 (hpos s hs).ne').intervalIntegrable
  have hmono : |∫ s in (1 : ℝ)..c, Real.cos s / s ^ 2| ≤ ∫ s in (1 : ℝ)..c, 1 / s ^ 2 := by
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le hc ?_ hi2
    filter_upwards with s hs
    have hs0 : 0 < s := by linarith [hs.1]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hs0 2)]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one s) (pow_pos hs0 2).le
  -- ∫_1^c 1/s^2 = 1 - 1/c <= 1.
  have hderiv : ∀ s ∈ Set.uIcc (1 : ℝ) c, HasDerivAt (fun s : ℝ => -s⁻¹) (1 / s ^ 2) s := by
    intro s hs
    have h := (hasDerivAt_inv (hpos s hs).ne').neg
    refine h.congr_deriv ?_
    field_simp
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hi2
  have hc0 : 0 < c := by linarith
  have : -c⁻¹ - -(1 : ℝ)⁻¹ ≤ 1 := by
    have := inv_pos.mpr hc0
    norm_num
    linarith
  linarith

/-- |Si(c)| <= 4 for c >= 0. -/
lemma abs_Si_le {c : ℝ} (hc : 0 ≤ c) : |∫ s in (0 : ℝ)..c, Real.sinc s| ≤ 4 := by
  rcases le_or_gt c 1 with h1 | h1
  · have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := c)
      (C := 1) (f := Real.sinc) (fun t _ => by rw [Real.norm_eq_abs]; exact Real.abs_sinc_le_one _)
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hc] at h
    linarith
  · have hsplit : ∫ s in (0 : ℝ)..c, Real.sinc s
        = (∫ s in (0 : ℝ)..1, Real.sinc s) + ∫ s in (1 : ℝ)..c, Real.sinc s :=
      (intervalIntegral.integral_add_adjacent_intervals (Real.continuous_sinc.intervalIntegrable 0 1)
        (Real.continuous_sinc.intervalIntegrable 1 c)).symm
    have hA : |∫ s in (0 : ℝ)..1, Real.sinc s| ≤ 1 := by
      have := abs_sincInt_le_one 1
      simpa [sincInt] using this
    have hB : ∫ s in (1 : ℝ)..c, Real.sinc s = ∫ s in (1 : ℝ)..c, Real.sin s / s := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [Set.uIcc_of_le h1.le] at hs
      have : s ≠ 0 := by linarith [hs.1]
      exact Real.sinc_of_ne_zero this
    rw [hsplit, hB, integral_sin_div_eq h1.le]
    have hC := abs_integral_cos_div_sq_le h1.le
    have hc0 : 0 < c := by linarith
    have hcos : |Real.cos c / c| ≤ 1 := by
      rw [abs_div, abs_of_pos hc0, div_le_one hc0]
      linarith [Real.abs_cos_le_one c]
    have hcos1 := Real.abs_cos_le_one 1
    calc |(∫ s in (0 : ℝ)..1, Real.sinc s)
            + (Real.cos 1 - Real.cos c / c - ∫ s in (1 : ℝ)..c, Real.cos s / s ^ 2)|
        ≤ |∫ s in (0 : ℝ)..1, Real.sinc s| + (|Real.cos 1| + |Real.cos c / c|
            + |∫ s in (1 : ℝ)..c, Real.cos s / s ^ 2|) := by
          refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
          refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
          exact abs_sub _ _
      _ ≤ 4 := by linarith

/-- |sincInt c| <= 4/|c|. -/
lemma abs_sincInt_le_div {c : ℝ} (hc : c ≠ 0) : |sincInt c| ≤ 4 / |c| := by
  have key : ∀ c : ℝ, 0 < c → |sincInt c| ≤ 4 / c := by
    intro c hc
    have h := abs_Si_le hc.le
    rw [← mul_sincInt, abs_mul, abs_of_pos hc] at h
    rw [le_div_iff₀ hc]
    linarith
  rcases lt_or_gt_of_ne hc with h | h
  · have := key (-c) (by linarith)
    rw [sincInt_neg] at this
    rw [abs_of_neg h]
    exact this
  · rw [abs_of_pos h]
    exact key c h

/-- THE DECAY BOUND: |delta(e^{|u|})| <= 8 e^{-|u|/2}  (CC: delta(rho) = rho^{-1/2} + O(rho^{-3/2})). -/
theorem abs_deltaK_le (u : ℝ) : |deltaK u| ≤ 8 * Real.exp (-(1 / 2) * |u|) := by
  set E := Real.exp |u| with hE
  set s := Real.exp (|u| / 2) with hs
  have hE1 : 1 ≤ E := Real.one_le_exp (abs_nonneg u)
  have hs0 : 0 < s := Real.exp_pos _
  have hss : s * s = E := by rw [hs, hE, ← Real.exp_add]; congr 1; ring
  have hinv : Real.exp (-(1 / 2) * |u|) = s⁻¹ := by
    rw [hs, ← Real.exp_neg]; congr 1; ring
  rw [hinv]
  -- Reduce to E (|A| + |B|) <= 4.
  set A := sincInt (2 * Real.pi * (E + 1))
  set B := sincInt (2 * Real.pi * (E - 1))
  have hsum : E * (|A| + |B|) ≤ 4 := by
    have hpi := Real.pi_gt_three
    rcases le_or_gt E 2 with h2 | h2
    · have := abs_sincInt_le_one (2 * Real.pi * (E + 1))
      have := abs_sincInt_le_one (2 * Real.pi * (E - 1))
      nlinarith [abs_nonneg A, abs_nonneg B]
    · have hA : |A| ≤ 4 / (2 * Real.pi * (E + 1)) := by
        have hd : 0 < 2 * Real.pi * (E + 1) := by positivity
        have h := abs_sincInt_le_div hd.ne'
        rw [abs_of_pos hd] at h
        exact h
      have hB : |B| ≤ 4 / (2 * Real.pi * (E - 1)) := by
        have hpos : 0 < 2 * Real.pi * (E - 1) := by
          have : 0 < E - 1 := by linarith
          positivity
        have h := abs_sincInt_le_div hpos.ne'
        rw [abs_of_pos hpos] at h
        exact h
      have hA' : E * |A| ≤ 1 := by
        have hd : 0 < 2 * Real.pi * (E + 1) := by positivity
        calc E * |A| ≤ E * (4 / (2 * Real.pi * (E + 1))) :=
              mul_le_mul_of_nonneg_left hA (by linarith)
          _ ≤ 1 := by
            rw [mul_div_assoc', div_le_one hd]
            nlinarith
      have hB' : E * |B| ≤ 3 := by
        have hd : 0 < 2 * Real.pi * (E - 1) := by
          have : 0 < E - 1 := by linarith
          positivity
        calc E * |B| ≤ E * (4 / (2 * Real.pi * (E - 1))) :=
              mul_le_mul_of_nonneg_left hB (by linarith)
          _ ≤ 3 := by
            rw [mul_div_assoc', div_le_iff₀ hd]
            nlinarith
      nlinarith
  have hdef : deltaK u = 2 * s * (A + B) := rfl
  rw [hdef, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hs0]
  have hAB := abs_add_le A B
  have hE0 : 0 ≤ E := by linarith
  have key : 2 * s * |A + B| * s ≤ 8 := by
    calc 2 * s * |A + B| * s = 2 * (s * s) * |A + B| := by ring
      _ ≤ 2 * (s * s) * (|A| + |B|) :=
          mul_le_mul_of_nonneg_left hAB (by positivity)
      _ = 2 * (E * (|A| + |B|)) := by rw [hss]; ring
      _ ≤ 8 := by linarith
  rw [← div_eq_mul_inv, le_div_iff₀ hs0]
  exact key

lemma integrable_deltaK : Integrable deltaK := by
  refine ((integrable_expK (b := 1 / 2) (by norm_num)).const_mul 8).mono'
    continuous_deltaK.aestronglyMeasurable ?_
  filter_upwards with u
  rw [Real.norm_eq_abs]
  have h := abs_deltaK_le u
  unfold expK
  convert h using 2

/-! ## D. The Fourier transform delta^ and the Parseval pairing. -/

/-- delta^(r) = ∫ delta(e^{|u|}) cos(r u) du  (CC: delta^(t) = ∫ delta(rho) rho^{-it} d*rho). -/
def deltaHat (r : ℝ) : ℝ := ∫ u : ℝ, deltaK u * Real.cos (r * u)

def deltaL1 : ℝ := ∫ u : ℝ, |deltaK u|

lemma integrable_deltaK_mul_cos (r : ℝ) : Integrable fun u => deltaK u * Real.cos (r * u) := by
  refine integrable_deltaK.mul_bdd (c := 1) (by fun_prop) ?_
  filter_upwards with u
  rw [Real.norm_eq_abs]
  exact Real.abs_cos_le_one _

lemma integrable_deltaK_mul_sin (r : ℝ) : Integrable fun u => deltaK u * Real.sin (r * u) := by
  refine integrable_deltaK.mul_bdd (c := 1) (by fun_prop) ?_
  filter_upwards with u
  rw [Real.norm_eq_abs]
  exact Real.abs_sin_le_one _

lemma abs_deltaHat_le (r : ℝ) : |deltaHat r| ≤ deltaL1 := by
  unfold deltaHat deltaL1
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ => norm_nonneg _) integrable_deltaK.abs ?_)
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

lemma continuous_deltaHat : Continuous deltaHat := by
  unfold deltaHat
  refine continuous_of_dominated (bound := fun u => |deltaK u|) ?_ ?_ integrable_deltaK.abs ?_
  · intro r
    exact (continuous_deltaK.mul (by fun_prop)).aestronglyMeasurable
  · intro r
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  · filter_upwards with u
    exact continuous_const.mul (by fun_prop)

/-- The sine transform of the even kernel vanishes. -/
lemma integral_deltaK_mul_sin (r : ℝ) : ∫ u : ℝ, deltaK u * Real.sin (r * u) = 0 := by
  have h := integral_neg_eq_self (fun u : ℝ => deltaK u * Real.sin (r * u)) volume
  simp only [deltaK_neg, mul_neg, Real.sin_neg, integral_neg] at h
  linarith

lemma integral_deltaK_cexp (r : ℝ) :
    ∫ u : ℝ, (deltaK u : ℂ) * cexp (-I * r * u) = (deltaHat r : ℂ) := by
  have e : (fun u : ℝ => (deltaK u : ℂ) * cexp (-I * r * u))
      = fun u => ((deltaK u * Real.cos (r * u) : ℝ) : ℂ) - I * ((deltaK u * Real.sin (r * u) : ℝ) : ℂ) := by
    funext u
    rw [show -I * (r : ℂ) * (u : ℂ) = ((-(r * u) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  rw [e, integral_sub, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal,
    integral_deltaK_mul_sin]
  · simp [deltaHat]
  · exact (integrable_deltaK_mul_cos r).ofReal
  · exact ((integrable_deltaK_mul_sin r).ofReal).const_mul I

lemma integrable_pairing_integrand_delta {g : ℝ → ℂ} (hg : IsWeilTest g) :
    Integrable (Function.uncurry fun (u r : ℝ) =>
      (hsq g r : ℂ) * cexp (-I * r * u) * (deltaK u : ℂ)) (volume.prod volume) := by
  have hprod : Integrable (fun z : ℝ × ℝ => |deltaK z.1| * hsq g z.2) (volume.prod volume) :=
    (integrable_deltaK.abs).mul_prod (integrable_hsq hg)
  refine hprod.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    have h1 : Continuous fun z : ℝ × ℝ => (hsq g z.2 : ℂ) :=
      Complex.continuous_ofReal.comp ((continuous_hsq hg).comp continuous_snd)
    have h2 : Continuous fun z : ℝ × ℝ => (deltaK z.1 : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_deltaK.comp continuous_fst)
    have h3 : Continuous fun z : ℝ × ℝ => cexp (-I * (z.2 : ℂ) * (z.1 : ℂ)) := by fun_prop
    exact (h1.mul h3).mul h2
  · filter_upwards with z
    show ‖(hsq g z.2 : ℂ) * cexp (-I * (z.2 : ℂ) * (z.1 : ℂ)) * (deltaK z.1 : ℂ)‖
      ≤ |deltaK z.1| * hsq g z.2
    rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_exp, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    apply le_of_eq
    rw [show (-I * (z.2 : ℂ) * (z.1 : ℂ)).re = 0 by
        simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
        ring,
      Real.exp_zero, mul_one, abs_of_nonneg (hsq_nonneg g _), mul_comm]

/-- THE D-PAIRING: ∫ (g * g^*)(u) delta(e^{|u|}) du = (1/2pi) ∫ |g^|^2 delta^. -/
theorem pairing_deltaK {g : ℝ → ℂ} (hg : IsWeilTest g) :
    ∫ u : ℝ, autocorr g u * (deltaK u : ℂ)
      = (1 / (2 * (Real.pi : ℂ))) * ((∫ r : ℝ, hsq g r * deltaHat r : ℝ) : ℂ) := by
  have hF := integrable_pairing_integrand_delta hg
  calc ∫ u : ℝ, autocorr g u * (deltaK u : ℂ)
      = ∫ u : ℝ, (1 / (2 * (Real.pi : ℂ)))
          * ∫ r : ℝ, (hsq g r : ℂ) * cexp (-I * r * u) * (deltaK u : ℂ) := by
        congr 1
        funext u
        rw [autocorr_inversion hg u, mul_assoc, ← integral_mul_const]
    _ = (1 / (2 * (Real.pi : ℂ)))
          * ∫ u : ℝ, ∫ r : ℝ, (hsq g r : ℂ) * cexp (-I * r * u) * (deltaK u : ℂ) := by
        rw [integral_const_mul]
    _ = (1 / (2 * (Real.pi : ℂ)))
          * ∫ r : ℝ, ∫ u : ℝ, (hsq g r : ℂ) * cexp (-I * r * u) * (deltaK u : ℂ) := by
        rw [integral_integral_swap hF]
    _ = (1 / (2 * (Real.pi : ℂ))) * ∫ r : ℝ, (hsq g r : ℂ) * (deltaHat r : ℂ) := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
        simp only
        rw [← integral_deltaK_cexp r, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        simp only
        ring
    _ = (1 / (2 * (Real.pi : ℂ))) * ((∫ r : ℝ, hsq g r * deltaHat r : ℝ) : ℂ) := by
        rw [← integral_complex_ofReal]
        push_cast
        rfl

/-! ## E. The functional L = W_inf + D. -/

/-- W_inf(g * g^*) = (1/2pi) ∫ |g^|^2 (psiR - log pi)  (CC (52): 2 theta' = psiR - log pi). -/
def archW (g : ℝ → ℂ) : ℝ := (1 / (2 * Real.pi)) * ∫ r : ℝ, hsq g r * (psiR r - Real.log Real.pi)

/-- D(g * g^*) = Re ∫ (g * g^*)(u) delta(e^{|u|}) du = <g, K_delta g>. -/
def Dfun (g : ℝ → ℂ) : ℝ := (∫ u : ℝ, autocorr g u * (deltaK u : ℂ)).re

/-- CC's functional L = W_inf + D (Cor 2.3). -/
def Lfun (g : ℝ → ℂ) : ℝ := archW g + Dfun g

/-- CC's ell(t) = 2 theta'(t) + delta^(t) in our conventions. -/
def ell (r : ℝ) : ℝ := psiR r - Real.log Real.pi + deltaHat r

lemma integrable_hsq_mul_deltaHat {g : ℝ → ℂ} (hg : IsWeilTest g) :
    Integrable fun r => hsq g r * deltaHat r := by
  refine (integrable_hsq hg).mul_bdd (c := deltaL1) continuous_deltaHat.aestronglyMeasurable ?_
  filter_upwards with r
  rw [Real.norm_eq_abs]
  exact abs_deltaHat_le r

lemma Dfun_eq {g : ℝ → ℂ} (hg : IsWeilTest g) :
    Dfun g = (1 / (2 * Real.pi)) * ∫ r : ℝ, hsq g r * deltaHat r := by
  unfold Dfun
  rw [pairing_deltaK hg]
  rw [show (1 / (2 * (Real.pi : ℂ))) * ((∫ r : ℝ, hsq g r * deltaHat r : ℝ) : ℂ)
      = (((1 / (2 * Real.pi)) * ∫ r : ℝ, hsq g r * deltaHat r : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_re]

/-- (S3-a) THE FOURIER FORM: L(g * g^*) = (1/2pi) ∫ |g^|^2 ell. -/
theorem Lfun_eq_integral_ell {g : ℝ → ℂ} (hg : IsWeilTest g) :
    Lfun g = (1 / (2 * Real.pi)) * ∫ r : ℝ, hsq g r * ell r := by
  unfold Lfun archW
  rw [Dfun_eq hg, ← mul_add, ← integral_add]
  · congr 1
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [ell]
    ring
  · have h1 := integrable_hsq_mul_psiR hg
    have h2 := (integrable_hsq hg).mul_const (Real.log Real.pi)
    refine (h1.sub h2).congr (Eventually.of_forall fun r => ?_)
    simp only [Pi.sub_apply]
    ring
  · exact integrable_hsq_mul_deltaHat hg

/-- W_inf in u-space via S1: archW = (psiR 0 - log pi) ||g||^2 + (1/2) ∫∫ |Δg|^2 k. -/
theorem archW_eq_dirichlet {g : ℝ → ℂ} (hg : IsWeilTest g) :
    archW g = (psiR 0 - Real.log Real.pi) * mass g
      + (1 / 2) * ∫ z : ℝ × ℝ, ‖g z.1 - g z.2‖ ^ 2 * archK (z.1 - z.2) ∂(volume.prod volume) := by
  unfold archW
  have hsplit : ∫ r : ℝ, hsq g r * (psiR r - Real.log Real.pi)
      = (∫ r : ℝ, hsq g r * psiR r) - Real.log Real.pi * ∫ r : ℝ, hsq g r := by
    rw [← integral_const_mul, ← integral_sub (integrable_hsq_mul_psiR hg)
      ((integrable_hsq hg).const_mul _)]
    congr 1; funext r; ring
  have hA := arch_integral_dirichlet hg
  rw [hsplit, integral_hsq hg, mul_sub, hA]
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp
  ring

/-- (S3-b) THE u-SPACE FORM: L = (psiR 0 - log pi) ||g||^2 + (1/2) ∫∫ |Δg|^2 k + D. -/
theorem Lfun_eq_dirichlet {g : ℝ → ℂ} (hg : IsWeilTest g) :
    Lfun g = (psiR 0 - Real.log Real.pi) * mass g
      + (1 / 2) * ∫ z : ℝ × ℝ, ‖g z.1 - g z.2‖ ^ 2 * archK (z.1 - z.2) ∂(volume.prod volume)
      + Dfun g := by
  unfold Lfun
  rw [archW_eq_dirichlet hg]

/-- (S3-c) W_inf is the archimedean side minus the pole terms. -/
theorem re_archSide_eq_poles_add_archW {g : ℝ → ℂ} (hg : IsWeilTest g) :
    (archSide (autocorr g)).re
      = (weilKernel (autocorr g) 0 + weilKernel (autocorr g) 1).re + archW g := by
  rw [archSide_autocorr_dirichlet_identity hg, archW_eq_dirichlet hg]
  ring

/-- On the pole-free class in the window, the Weil form is W_inf. -/
theorem re_weilForm_eq_archW {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) (hL : 2 * L ≤ Real.log 2) (h0 : paperFT g (I / 2) = 0) :
    (weilForm (autocorr g)).re = archW g := by
  rw [weilForm_autocorr_eq_archSide hg hsupp hL, re_archSide_eq_poles_add_archW hg]
  obtain ⟨hz, ho⟩ := poles_vanish hg h0
  rw [hz, ho]
  simp

/-- The reduction: pointwise ell >= 0 gives L >= 0 on every test function (CC Cor 2.3 (ii) => (i)). -/
theorem Lfun_nonneg_of_ell_nonneg (hell : ∀ r, 0 ≤ ell r) {g : ℝ → ℂ} (hg : IsWeilTest g) :
    0 ≤ Lfun g := by
  rw [Lfun_eq_integral_ell hg]
  exact mul_nonneg (by positivity) (integral_nonneg fun r => mul_nonneg (hsq_nonneg g r) (hell r))

end ArchS3
