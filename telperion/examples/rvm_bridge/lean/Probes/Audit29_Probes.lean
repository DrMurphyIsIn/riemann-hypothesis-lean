/- Audit probes for E6Bridge29 (auditor-forward, 2026-09-22). -/
import E6Bridge29
open Zeta23 Complex RvMBridge15 RvMBridge15.BombieriLagarias RvMBridge28 RvMBridge29

#print axioms liLimit_re_nonneg_of_line_below_sharp

/- 1. The three-case split re-composed abstractly: |a| ≤ |b| and |a| + |b| ≤ 2π give
   cosh a cos b ≤ 1 (expected SUCCESS). -/
example (a b : ℝ) (hab : |a| ≤ |b|) (hsum : |a| + |b| ≤ 2 * Real.pi) : Real.cosh a * Real.cos b ≤ 1 := by
  rcases le_or_gt |b| (Real.pi / 2) with h1 | h1
  · exact cosh_mul_cos_le_one_of_abs_le hab h1
  rcases le_or_gt |b| (3 * Real.pi / 2) with h2 | h2
  · have hcos : Real.cos b ≤ 0 := by
      rw [← Real.cos_abs]; exact Real.cos_nonpos_of_pi_div_two_le_of_le h1.le (by linarith)
    nlinarith [Real.cosh_pos a]
  · exact cosh_mul_cos_le_one_window h2 (by linarith [abs_nonneg a]) (by linarith)

/- 2. The deficit d = 2π - |b| lies in [0, π/2) on the window (expected SUCCESS). -/
example (b : ℝ) (h1 : 3 * Real.pi / 2 < |b|) (h2 : |b| ≤ 2 * Real.pi) :
    0 ≤ 2 * Real.pi - |b| ∧ 2 * Real.pi - |b| < Real.pi / 2 := ⟨by linarith, by linarith⟩

/- 3. Lemma B'' algebra: (2g + 1)(g - 1/2) ≤ 2g² for g > 1/2, i.e. 1/g + 1/(2g²) ≤ 1/(g - 1/2)
   (expected SUCCESS, abstract). -/
example (g : ℝ) (hg : 1 / 2 < g) : (2 * g + 1) * (g - 1 / 2) ≤ 2 * g ^ 2 := by nlinarith

/- 4. The window lemma at its edge a = 0, b = 2π (equality case; expected SUCCESS). -/
example : Real.cosh 0 * Real.cos (2 * Real.pi) ≤ 1 :=
  cosh_mul_cos_le_one_window (a := 0) (b := 2 * Real.pi)
    (by rw [abs_of_pos (by positivity)]; linarith [Real.pi_pos])
    (by rw [abs_of_pos (by positivity)])
    (by rw [abs_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]; linarith)

/- 5. The sharp rate dominates the E6Bridge28 rate for T ≥ 2: 3πT/2 ≤ 2π(T - 1/2)
   (expected SUCCESS). -/
example (T : ℝ) (hT : 2 ≤ T) : 3 * Real.pi * T / 2 ≤ 2 * Real.pi * (T - 1 / 2) := by
  nlinarith [Real.pi_pos]

/- 6. Consumption at T = 3, N = 15 (5π > 15; expected SUCCESS). -/
example (hline : ∀ ρ, IsNontrivialZero ρ → |ρ.im| ≤ 3 → ρ.re = 1 / 2) : 0 ≤ (liLimit 15).re :=
  liLimit_re_nonneg_of_line_below_sharp 3 (by norm_num) hline 15 (by nlinarith [Real.pi_gt_three])

/- 7. Threshold arithmetic of Theorem D'' (expected SUCCESS). -/
example (T : ℝ) (N : ℕ) (hN : (N : ℝ) ≤ 2 * Real.pi * (T - 1 / 2)) (ρ : ℂ) (hT : T < |ρ.im|) :
    (N : ℝ) ≤ 2 * Real.pi * (|ρ.im| - 1 / 2) := by nlinarith [Real.pi_pos]

/- 8. EXPECTED FAIL: N = 16 at T = 3 is beyond the sharp rate (5π < 16). -/
example (hline : ∀ ρ, IsNontrivialZero ρ → |ρ.im| ≤ 3 → ρ.re = 1 / 2) : 0 ≤ (liLimit 16).re :=
  liLimit_re_nonneg_of_line_below_sharp 3 (by norm_num) hline 16
    (by nlinarith [Real.pi_gt_three, Real.pi_lt_four])

/- 9. EXPECTED FAIL: T = 1/2. -/
example (hline : ∀ ρ, IsNontrivialZero ρ → |ρ.im| ≤ 1 / 2 → ρ.re = 1 / 2) : 0 ≤ (liLimit 0).re :=
  liLimit_re_nonneg_of_line_below_sharp (1 / 2) (by norm_num) hline 0 (by simp)

/- 10. EXPECTED FAIL: the window lemma refuses |b| ≤ 3π/2 (its own hypothesis is strict). -/
example : Real.cosh 0 * Real.cos Real.pi ≤ 1 :=
  cosh_mul_cos_le_one_window (a := 0) (b := Real.pi)
    (by rw [abs_of_pos Real.pi_pos]; linarith [Real.pi_pos])
    (by rw [abs_of_pos Real.pi_pos]; linarith [Real.pi_pos]) (by simp)
