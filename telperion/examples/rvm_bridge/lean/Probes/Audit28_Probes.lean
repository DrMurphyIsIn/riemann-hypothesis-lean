/- Audit probes for E6Bridge28 (auditor-forward, 2026-09-21). -/
import E6Bridge28
open Zeta23 Complex RvMBridge15 RvMBridge15.BombieriLagarias RvMBridge28
open scoped ComplexConjugate

/- 1. Closed-form rung 5 re-composed from the pieces (expected SUCCESS). -/
example : 0 ≤ (archSide 5 + finiteSide 5).re := by
  rw [← RvMBridge27.liValue 5 (by norm_num)]
  exact liLimit_re_nonneg_of_termwise 5 fun _ h => liKernel_five_re_nonneg h
#print axioms liLimit_re_nonneg_of_line_below
#print axioms archSide_add_finiteSide_five_re_nonneg

/- 2. The involution is 1 - conj, definitionally; on-line points are its fixed points
   (expected SUCCESS). -/
example (ρ : ℂ) : Zeta23.reflect ρ = 1 - conj ρ := rfl
example (ρ : ℂ) (hre : ρ.re = 1 / 2) : (1 : ℂ) - conj ρ = ρ :=
  Complex.ext (by simp [hre]; norm_num) (by simp)

/- 3. Regrouping arithmetic: HasSum f a and HasSum (f ∘ e) a give HasSum (f + f ∘ e) (2a);
   nonneg pair terms give 0 ≤ a (expected SUCCESS, abstract). -/
example (f : ℂ → ℝ) (a : ℝ) (e : ℂ ≃ ℂ) (h : HasSum f a) (hp : ∀ ρ, 0 ≤ f ρ + f (e ρ)) : 0 ≤ a := by
  have h2 : HasSum (fun ρ => f (e ρ)) a := e.hasSum_iff.mpr h
  have h3 : HasSum (fun ρ => f ρ + f (e ρ)) (2 * a) := by rw [two_mul]; exact h.add h2
  have : 0 ≤ 2 * a := by rw [← h3.tsum_eq]; exact tsum_nonneg hp
  linarith

/- 4. Threshold arithmetic of Theorem D (expected SUCCESS). -/
example (T : ℝ) (N : ℕ) (hN : (N : ℝ) ≤ 3 * Real.pi * T / 2) (ρ : ℂ) (hT : T < |ρ.im|) :
    (N : ℝ) ≤ 3 * Real.pi * |ρ.im| / 2 := by nlinarith [Real.pi_pos]

/- 5. Box algebra: the two constraints give Box 2 and Box 1 (expected SUCCESS). -/
example (σ t : ℝ) (h1 : 4 * σ ^ 2 ≤ (σ - 1) ^ 2 + t ^ 2) (h2 : 4 * (1 - σ) ^ 2 ≤ σ ^ 2 + t ^ 2) :
    (σ - 1 / 2) ^ 2 ≤ t ^ 2 / 3 - 1 / 4 ∧ 3 / 4 ≤ t ^ 2 :=
  ⟨by nlinarith, by nlinarith [sq_nonneg (σ - 1 / 2)]⟩

/- 6. Rung-4 auxiliary: t² ≥ 3/4 gives t² ≤ 6 (t² - 1/4)² (expected SUCCESS). -/
example (x : ℝ) (h : 3 / 4 ≤ x) : x ≤ 6 * (x - 1 / 4) ^ 2 := by nlinarith

/- 7. Rung 2 unpaired: A = β² - β + γ² ≥ 0 suffices: 1 - (A² - γ²)/P² ≥ 0 with P = β² + γ²
   (expected SUCCESS, abstract). -/
example (β γ : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hA : 0 ≤ β ^ 2 - β + γ ^ 2) :
    (β ^ 2 - β + γ ^ 2) ^ 2 - γ ^ 2 ≤ (β ^ 2 + γ ^ 2) ^ 2 := by
  nlinarith [mul_nonneg hβ.le hA, sq_nonneg γ]

/- 8. Consumption of the ladder node at N = 3 with T = 1 (expected SUCCESS). -/
example (hline : ∀ ρ, IsNontrivialZero ρ → |ρ.im| ≤ 1 → ρ.re = 1 / 2) : 0 ≤ (liLimit 3).re :=
  liLimit_re_nonneg_of_line_below 1 le_rfl hline 3 (by nlinarith [Real.pi_gt_three])

/- 9. EXPECTED FAIL: Theorem D at T = 1/2. -/
example (hline : ∀ ρ, IsNontrivialZero ρ → |ρ.im| ≤ 1 / 2 → ρ.re = 1 / 2) : 0 ≤ (liLimit 1).re :=
  liLimit_re_nonneg_of_line_below (1 / 2) (by norm_num) hline 1 (by nlinarith [Real.pi_gt_three])

/- 10. EXPECTED FAIL: closed form needs 0 < N. -/
example (hline : ∀ ρ, IsNontrivialZero ρ → |ρ.im| ≤ 1 → ρ.re = 1 / 2) :
    0 ≤ (archSide 0 + finiteSide 0).re :=
  archSide_add_finiteSide_re_nonneg_of_line_below 1 le_rfl hline 0 (by norm_num) (by positivity)

/- 11. EXPECTED FAIL: the rung-5 termwise lemma does not give rung 6. -/
example : 0 ≤ (liLimit 6).re :=
  liLimit_re_nonneg_of_termwise 6 fun _ hρ => liKernel_five_re_nonneg hρ
