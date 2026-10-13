import Mathlib

/-!
# ArchS6_Sobolev: a one-dimensional Sobolev bound

`sq_le_sobolev`: for `f` differentiable on `ℝ` with continuous derivative and `a < b`, every
`x ∈ [a, b]` satisfies `f(x)² ≤ (∫_a^b f²)/(b - a) + 2 ∫_a^b (f² + f'²)`.

Proof: `f(x)² - f(t)² = ∫_t^x 2ff'` and `2|ff'| ≤ f² + f'²`, then average over `t ∈ [a, b]`.
No square roots and no Cauchy-Schwarz.  This is what turns the pointwise Bessel inequality for the
prolates into the sup bounds `M n`, `N n` of S8's `ProlateData`.

conjecture1_proved = False.
-/

open MeasureTheory Set intervalIntegral

noncomputable section

namespace ArchS6

theorem sq_le_sobolev {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Continuous f') {x : ℝ} (hx : x ∈ Icc a b) :
    f x ^ 2 ≤ (∫ t in a..b, f t ^ 2) / (b - a) + 2 * ∫ t in a..b, (f t ^ 2 + f' t ^ 2) := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x ↦ (hf x).continuousAt
  have hf2 : Continuous fun t ↦ f t ^ 2 := hfc.pow 2
  set g' : ℝ → ℝ := fun t ↦ f' t * f t + f t * f' t with hg'
  have hg'c : Continuous g' := (hf'.mul hfc).add (hfc.mul hf')
  have hgd : ∀ t, HasDerivAt (fun t ↦ f t ^ 2) (g' t) t := fun t ↦ by
    exact ((hf t).mul (hf t)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s ↦ sq (f s))
  set I := ∫ t in a..b, (f t ^ 2 + f' t ^ 2)
  -- `|∫_a^y g'| ≤ I` for `y ∈ [a, b]`
  have hbound : ∀ y ∈ Icc a b, |∫ t in a..y, g' t| ≤ I := by
    intro y hy
    have h1 := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := g') hy.1
    have h2 : ∫ t in a..y, |g' t| ≤ ∫ t in a..b, |g' t| := by
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hg'c.abs.intervalIntegrable (μ := volume) a y) (hg'c.abs.intervalIntegrable (μ := volume) y b)
      have hnn : 0 ≤ ∫ t in y..b, |g' t| :=
        intervalIntegral.integral_nonneg hy.2 fun _ _ ↦ abs_nonneg _
      linarith
    have h3 : ∫ t in a..b, |g' t| ≤ I := by
      refine intervalIntegral.integral_mono_on hab.le (hg'c.abs.intervalIntegrable a b)
        (((hfc.pow 2).add (hf'.pow 2)).intervalIntegrable a b) fun t _ ↦ ?_
      simp only [hg']
      have : |f' t * f t + f t * f' t| = 2 * |f t| * |f' t| := by
        rw [show f' t * f t + f t * f' t = 2 * (f t * f' t) by ring, abs_mul, abs_mul,
          abs_two]; ring
      rw [this]
      nlinarith [sq_abs (f t), sq_abs (f' t), sq_nonneg (|f t| - |f' t|)]
    linarith
  -- FTC: `f y² = f a² + ∫_a^y g'`
  have hftc : ∀ y, f y ^ 2 = f a ^ 2 + ∫ t in a..y, g' t := fun y ↦ by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hgd t)
      (hg'c.intervalIntegrable a y)]; ring
  -- `f x² ≤ f t² + 2I` for all `t ∈ [a, b]`
  have hpt : ∀ t ∈ Icc a b, f x ^ 2 ≤ f t ^ 2 + 2 * I := by
    intro t ht
    have e1 := hftc x
    have e2 := hftc t
    have b1 := (abs_le.1 (hbound x hx)).2
    have b2 := (abs_le.1 (hbound t ht)).1
    linarith
  -- average over `t`
  have havg : ∫ _ in a..b, f x ^ 2 ≤ ∫ t in a..b, (f t ^ 2 + 2 * I) :=
    intervalIntegral.integral_mono_on hab.le intervalIntegrable_const
      (((hfc.pow 2).add continuous_const).intervalIntegrable a b) hpt
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add
    (hf2.intervalIntegrable a b) intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul] at havg
  have hba : 0 < b - a := by linarith
  rw [div_add' _ _ _ hba.ne', le_div_iff₀ hba]
  nlinarith

end ArchS6
