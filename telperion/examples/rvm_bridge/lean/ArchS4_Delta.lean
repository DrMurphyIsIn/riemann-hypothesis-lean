/-
  ArchS4_Delta -- stage S4 of the archimedean conceptual blueprint (2026-10-11), part 1:
  Connes-Consani's trace remainder delta (arXiv:2006.13771, (48)-(50)) in the additive variable,
  with no sine integral and no distribution theory.

  CC (48): for rho >= 1, delta(rho) = 4 rho^{1/2} ∫_0^1 cos(2π rho t) cos(2π t) (-log t) dt
         = 2 rho^{1/2} [S(2π(1+rho)) + S(2π(rho-1))],   S(a) = ∫_0^1 cos(a t)(-log t) dt = Si(a)/a.
  Writing -log t = ∫_t^1 ds/s turns S into an integral over the unit square:
      ccS a = ∫∫_{[0,1]^2} cos(a s r) ds dr                     (ccS, below),
  a finite-measure integral of a smooth function with bounded derivatives, so ccS is C^∞.
  The additive kernel is deltaE x = 2 e^{x/2} (ccS(2π(1+e^x)) + ccS(2π(e^x-1))) (smooth on ℝ);
  CC's D_+ kernel is delta(e^{|x|}) = deltaE |x|.

  PROVED (all statements below; axioms [propext, Classical.choice, Quot.sound]):
    contDiff_ccS, contDiff_deltaE          : smoothness
    ccS_zero                               : ccS 0 = 1
    ccS_add_mul_deriv                      : ccS a + a ccS'(a) = ∫_0^1 cos(a s) ds = sinc a
    deltaE_zero                            : deltaE 0 = 2 (ccS(4π) + 1)            (CC (50))
    deriv_deltaE_zero                      : deltaE'(0) = 1   (the jump: delta' goes -1 -> +1)
  conjecture1_proved = False.  Nothing here is RH progress.
-/
import Mathlib

open MeasureTheory Set Real

noncomputable section

namespace ArchS4

/-! ## A. The unit-square measure and moment integrals. -/

/-- Lebesgue measure on the unit square [0,1] × [0,1]. -/
def sq : Measure (ℝ × ℝ) :=
  (volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))

instance isFiniteMeasure_restrict_unit : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
  isFiniteMeasure_restrict.mpr (by simp)

instance isFiniteMeasure_sq : IsFiniteMeasure sq := by
  unfold sq; infer_instance

lemma ae_sq : ∀ᵐ p ∂sq, p.1 * p.2 ∈ Icc (0 : ℝ) 1 := by
  have hm := ae_restrict_mem (μ := (volume : Measure ℝ).prod (volume : Measure ℝ))
    (measurableSet_Icc.prod measurableSet_Icc :
      MeasurableSet (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
  unfold sq
  rw [Measure.prod_restrict]
  filter_upwards [hm] with p hp
  rcases hp with ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  exact ⟨mul_nonneg h1 h3, mul_le_one₀ h2 h3 h4⟩

/-- The moment integral ∫∫_{[0,1]^2} t^k φ(a t) with t = s r. -/
def mom (φ : ℝ → ℝ) (k : ℕ) (a : ℝ) : ℝ := ∫ p, (p.1 * p.2) ^ k * φ (a * (p.1 * p.2)) ∂sq

lemma continuous_momIntegrand {φ : ℝ → ℝ} (hφ : Continuous φ) (k : ℕ) (a : ℝ) :
    Continuous fun p : ℝ × ℝ => (p.1 * p.2) ^ k * φ (a * (p.1 * p.2)) :=
  ((continuous_fst.mul continuous_snd).pow k).mul
    (hφ.comp (continuous_const.mul (continuous_fst.mul continuous_snd)))

lemma norm_momIntegrand_le {φ : ℝ → ℝ} (hb : ∀ y, |φ y| ≤ 1) (k : ℕ) (a : ℝ) :
    ∀ᵐ p ∂sq, ‖(p.1 * p.2) ^ k * φ (a * (p.1 * p.2))‖ ≤ 1 := by
  filter_upwards [ae_sq] with p hp
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hp.1]
  exact mul_le_one₀ (pow_le_one₀ hp.1 hp.2) (abs_nonneg _) (hb _)

lemma integrable_momIntegrand {φ : ℝ → ℝ} (hφ : Continuous φ) (hb : ∀ y, |φ y| ≤ 1)
    (k : ℕ) (a : ℝ) :
    Integrable (fun p : ℝ × ℝ => (p.1 * p.2) ^ k * φ (a * (p.1 * p.2))) sq :=
  Integrable.of_bound (continuous_momIntegrand hφ k a).aestronglyMeasurable 1
    (norm_momIntegrand_le hb k a)

/-- Differentiation under the square integral: (d/da) mom φ k = mom φ' (k+1). -/
lemma hasDerivAt_mom {φ φ' : ℝ → ℝ} (hd : ∀ y, HasDerivAt φ (φ' y) y) (hφ : Continuous φ)
    (hφ' : Continuous φ') (hb : ∀ y, |φ y| ≤ 1) (hb' : ∀ y, |φ' y| ≤ 1) (k : ℕ) (a : ℝ) :
    HasDerivAt (mom φ k) (mom φ' (k + 1) a) a := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := sq) (x₀ := a)
    (F := fun x (p : ℝ × ℝ) => (p.1 * p.2) ^ k * φ (x * (p.1 * p.2)))
    (F' := fun x (p : ℝ × ℝ) => (p.1 * p.2) ^ (k + 1) * φ' (x * (p.1 * p.2)))
    (bound := fun _ => 1) (s := univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun x => (continuous_momIntegrand hφ k x).aestronglyMeasurable)
    (integrable_momIntegrand hφ hb k a)
    (continuous_momIntegrand hφ' (k + 1) a).aestronglyMeasurable
    (by
      filter_upwards [ae_sq] with p hp
      intro x _
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hp.1]
      exact mul_le_one₀ (pow_le_one₀ hp.1 hp.2) (abs_nonneg _) (hb' _))
    (integrable_const 1)
    (Filter.Eventually.of_forall fun p x _ => by
      have h1 := ((hd (x * (p.1 * p.2))).comp x
        ((hasDerivAt_id x).mul_const (p.1 * p.2))).const_mul ((p.1 * p.2) ^ k)
      refine h1.congr_deriv ?_
      simp only [one_mul]
      ring)
  exact key.2

lemma mom_neg (φ : ℝ → ℝ) (k : ℕ) (a : ℝ) : mom (fun y => -φ y) k a = -mom φ k a := by
  unfold mom
  rw [← integral_neg]
  congr 1
  funext p
  ring

/-! ## B. The cosine and sine moments; smoothness. -/

/-- Cm k a = ∫∫ t^k cos(a t), Sm k a = ∫∫ t^k sin(a t)  (t = s r on the unit square). -/
def Cm (k : ℕ) (a : ℝ) : ℝ := mom Real.cos k a
def Sm (k : ℕ) (a : ℝ) : ℝ := mom Real.sin k a

lemma hasDerivAt_Cm (k : ℕ) (a : ℝ) : HasDerivAt (Cm k) (-Sm (k + 1) a) a := by
  have h := hasDerivAt_mom (φ := Real.cos) (φ' := fun y => -Real.sin y)
    (fun y => Real.hasDerivAt_cos y) Real.continuous_cos Real.continuous_sin.neg
    Real.abs_cos_le_one (fun y => by rw [abs_neg]; exact Real.abs_sin_le_one y) k a
  rw [mom_neg] at h
  exact h

lemma hasDerivAt_Sm (k : ℕ) (a : ℝ) : HasDerivAt (Sm k) (Cm (k + 1) a) a :=
  hasDerivAt_mom (fun y => Real.hasDerivAt_sin y) Real.continuous_sin Real.continuous_cos
    Real.abs_sin_le_one Real.abs_cos_le_one k a

lemma deriv_Cm (k : ℕ) : deriv (Cm k) = fun a => -Sm (k + 1) a :=
  funext fun a => (hasDerivAt_Cm k a).deriv

lemma deriv_Sm (k : ℕ) : deriv (Sm k) = Cm (k + 1) :=
  funext fun a => (hasDerivAt_Sm k a).deriv

lemma contDiff_moments (n : ℕ) : ∀ k, ContDiff ℝ n (Cm k) ∧ ContDiff ℝ n (Sm k) := by
  induction n with
  | zero =>
    intro k
    exact ⟨contDiff_zero.2 (continuous_iff_continuousAt.2 fun a => (hasDerivAt_Cm k a).continuousAt),
      contDiff_zero.2 (continuous_iff_continuousAt.2 fun a => (hasDerivAt_Sm k a).continuousAt)⟩
  | succ n ih =>
    intro k
    rw [Nat.cast_succ]
    refine ⟨contDiff_succ_iff_deriv.2 ⟨fun a => (hasDerivAt_Cm k a).differentiableAt,
      fun h => by simp at h, ?_⟩, contDiff_succ_iff_deriv.2
        ⟨fun a => (hasDerivAt_Sm k a).differentiableAt, fun h => by simp at h, ?_⟩⟩
    · rw [deriv_Cm]; exact (ih (k + 1)).2.neg
    · rw [deriv_Sm]; exact (ih (k + 1)).1

lemma contDiff_Cm (k : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Cm k) :=
  contDiff_infty.2 fun n => (contDiff_moments n k).1

/-- CC's S(a) = Si(a)/a = ∫_0^1 cos(a t)(-log t) dt, as the square integral ∫∫ cos(a s r). -/
def ccS (a : ℝ) : ℝ := Cm 0 a

lemma contDiff_ccS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ccS := contDiff_Cm 0

lemma hasDerivAt_ccS (a : ℝ) : HasDerivAt ccS (-Sm 1 a) a := hasDerivAt_Cm 0 a

lemma sq_univ : sq.real univ = 1 := by
  unfold sq
  rw [Measure.real, ← Set.univ_prod_univ, Measure.prod_prod]
  simp

theorem ccS_zero : ccS 0 = 1 := by
  unfold ccS Cm mom
  simp [sq_univ]

lemma Sm_one_zero : Sm 1 0 = 0 := by
  unfold Sm mom
  simp

/-! ## C. The derivative identity ccS a + a ccS'(a) = ∫_0^1 cos(a s) ds. -/

lemma inner_ftc (a x : ℝ) :
    ∫ y in Icc (0 : ℝ) 1, (Real.cos (a * (x * y)) - a * ((x * y) * Real.sin (a * (x * y))))
      = Real.cos (a * x) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have hF : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun y => y * Real.cos (a * (x * y)))
        (Real.cos (a * (x * y)) - a * ((x * y) * Real.sin (a * (x * y)))) y := by
    intro y _
    have h1 : HasDerivAt (fun y => a * (x * y)) (a * x) y := by
      simpa using ((hasDerivAt_id y).const_mul x).const_mul a
    refine ((hasDerivAt_id y).mul (Real.hasDerivAt_cos _ |>.comp y h1)).congr_deriv ?_
    simp only [id_eq, Function.comp_apply]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF]
  · simp
  · exact (by fun_prop : Continuous fun y : ℝ =>
      Real.cos (a * (x * y)) - a * ((x * y) * Real.sin (a * (x * y)))).intervalIntegrable _ _

theorem ccS_add_mul_deriv (a : ℝ) :
    ccS a + a * deriv ccS a = ∫ s in (0 : ℝ)..1, Real.cos (a * s) := by
  rw [(hasDerivAt_ccS a).deriv]
  have hint : Integrable (fun p : ℝ × ℝ => Real.cos (a * (p.1 * p.2))
      - a * ((p.1 * p.2) * Real.sin (a * (p.1 * p.2)))) sq := by
    have h1 := integrable_momIntegrand Real.continuous_cos Real.abs_cos_le_one 0 a
    have h2 := (integrable_momIntegrand Real.continuous_sin Real.abs_sin_le_one 1 a).const_mul a
    refine (h1.sub h2).congr (Filter.Eventually.of_forall fun p => ?_)
    simp
  have hsplit : ccS a + a * -Sm 1 a = ∫ p, (Real.cos (a * (p.1 * p.2))
      - a * ((p.1 * p.2) * Real.sin (a * (p.1 * p.2)))) ∂sq := by
    unfold ccS Cm Sm mom
    rw [integral_sub, integral_const_mul]
    · simp only [pow_zero, one_mul, pow_one]; ring
    · simpa using integrable_momIntegrand Real.continuous_cos Real.abs_cos_le_one 0 a
    · simpa using (integrable_momIntegrand Real.continuous_sin Real.abs_sin_le_one 1 a).const_mul a
  rw [hsplit]
  unfold sq
  rw [integral_prod _ (by simpa [sq] using hint)]
  simp only
  simp_rw [inner_ftc a]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]

theorem integral_cos_mul_eq_sinc (a : ℝ) : ∫ s in (0 : ℝ)..1, Real.cos (a * s) = Real.sinc a := by
  by_cases ha : a = 0
  · subst ha; simp
  · rw [intervalIntegral.integral_comp_mul_left (fun s => Real.cos s) ha, integral_cos,
      Real.sinc_of_ne_zero ha]
    simp [div_eq_inv_mul]

lemma integral_cos_four_pi : ∫ s in (0 : ℝ)..1, Real.cos (4 * π * s) = 0 := by
  rw [integral_cos_mul_eq_sinc, Real.sinc_of_ne_zero (by positivity)]
  have : Real.sin (4 * π) = 0 := by
    have := Real.sin_nat_mul_pi 4
    simpa using this
  simp [this]

/-! ## D. The additive kernel deltaE and the jump. -/

/-- deltaE x = 2 e^{x/2} (S(2π(1+e^x)) + S(2π(e^x-1))): for x ≥ 0 this is CC's delta(e^x) (49);
    it is smooth on all of ℝ, and delta(e^{|x|}) = deltaE |x|. -/
def deltaE (x : ℝ) : ℝ :=
  2 * Real.exp (x / 2) * (ccS (2 * π * (1 + Real.exp x)) + ccS (2 * π * (Real.exp x - 1)))

theorem contDiff_deltaE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) deltaE := by
  unfold deltaE
  have he : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Real.exp := Real.contDiff_exp
  refine (contDiff_const.mul (he.comp (contDiff_id.div_const 2))).mul
    ((contDiff_ccS.comp (contDiff_const.mul (contDiff_const.add he))).add
      (contDiff_ccS.comp (contDiff_const.mul (he.sub contDiff_const))))

theorem deltaE_zero : deltaE 0 = 2 * (ccS (4 * π) + 1) := by
  unfold deltaE
  simp only [Real.exp_zero, zero_div]
  rw [show (2 * π * (1 + 1) : ℝ) = 4 * π by ring, show (2 * π * (1 - 1) : ℝ) = 0 by ring, ccS_zero]
  ring

/-- An explicit derivative of deltaE. -/
lemma hasDerivAt_deltaE (x : ℝ) :
    HasDerivAt deltaE
      (Real.exp (x / 2) * (ccS (2 * π * (1 + Real.exp x)) + ccS (2 * π * (Real.exp x - 1)))
        + 2 * Real.exp (x / 2) * ((-Sm 1 (2 * π * (1 + Real.exp x))) * (2 * π * Real.exp x)
          + (-Sm 1 (2 * π * (Real.exp x - 1))) * (2 * π * Real.exp x))) x := by
  have hE : HasDerivAt (fun x => 2 * Real.exp (x / 2)) (Real.exp (x / 2)) x := by
    have := ((Real.hasDerivAt_exp (x / 2)).comp x ((hasDerivAt_id x).div_const 2)).const_mul 2
    refine this.congr_deriv ?_
    ring
  have hα : HasDerivAt (fun x => 2 * π * (1 + Real.exp x)) (2 * π * Real.exp x) x := by
    simpa using ((Real.hasDerivAt_exp x).const_add 1).const_mul (2 * π)
  have hβ : HasDerivAt (fun x => 2 * π * (Real.exp x - 1)) (2 * π * Real.exp x) x := by
    simpa using ((Real.hasDerivAt_exp x).sub_const 1).const_mul (2 * π)
  have hS := ((hasDerivAt_ccS _).comp x hα).add ((hasDerivAt_ccS _).comp x hβ)
  exact hE.mul hS

/-- **The jump.**  deltaE'(0) = 1, so x ↦ delta(e^{|x|}) has slopes -1 and +1 at 0 (CC (50)). -/
theorem deriv_deltaE_zero : deriv deltaE 0 = 1 := by
  rw [(hasDerivAt_deltaE 0).deriv]
  have hk := ccS_add_mul_deriv (4 * π)
  rw [(hasDerivAt_ccS _).deriv, integral_cos_four_pi] at hk
  simp only [Real.exp_zero, zero_div, mul_one]
  have h0 : (2 * π * (1 - 1) : ℝ) = 0 := by ring
  have h4 : (2 * π * (1 + 1) : ℝ) = 4 * π := by ring
  rw [h0, h4, ccS_zero, Sm_one_zero]
  linear_combination hk

end ArchS4
