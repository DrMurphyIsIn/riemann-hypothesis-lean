/-
  E6Bridge29 -- THE SHARPENED EXCHANGE RATE of the Li ladder (2026-09-21; Li face brief,
  section 5, after the numerics: the true termwise threshold is |Im rho| = N/(2 pi) + 1/2 + o(1)).

  E6Bridge28 proved Theorem C (termwise nonnegativity of the pair term for
  N <= 3 pi |Im rho| / 2) by splitting b = N theta into |b| <= pi/2 (Lemma A) and
  pi/2 <= |b| <= 3 pi/2 (cos b <= 0).  This module adds the last window:

    * Lemma A'' (window): 3 pi/2 < |b| <= 2 pi and |a| <= 2 pi - |b| give cosh a cos b <= 1
      (d = 2 pi - |b| in [0, pi/2), cos b = cos d, Lemma A applied to (a, d));
    * Lemma B'': |theta| + |log r| <= 1/|gamma| + 1/(2 gamma^2) <= 1/(|gamma| - 1/2) for
      |gamma| >= 1 (E6Bridge28's bounds, then (2g + 1)(g - 1/2) <= 2 g^2);
    * Theorem C'' (pair_re_nonneg_of_far_sharp): |Im rho| >= 1 and
      N <= 2 pi (|Im rho| - 1/2) give a nonnegative pair term (three cases on |b|: Lemma A,
      cos b <= 0, and the window with |a| + |b| <= N/(|Im rho| - 1/2) <= 2 pi);
    * Theorem D'' (liLimit_re_nonneg_of_line_below_sharp): zeros on the line up to height
      T >= 1 give 0 <= Re (liLimit N) for every N <= 2 pi (T - 1/2), and the closed form
      0 <= Re (archSide N + finiteSide N) (E6Bridge27's liValue, N >= 1).

  NOTHING here proves anything about RH: the theorems consume zero localisation (a hypothesis)
  and produce sign information about finitely many Li coefficients.
  conjecture1_proved = False.
-/
import E6Bridge28

open Zeta23 Complex Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace RvMBridge29
open RvMBridge15 RvMBridge15.BombieriLagarias RvMBridge28

/-! ## A. Lemma A'': the window 3 pi/2 < |b| <= 2 pi. -/

/-- **Lemma A''.**  If 3 pi/2 < |b| <= 2 pi and |a| <= 2 pi - |b| then cosh a cos b <= 1. -/
theorem cosh_mul_cos_le_one_window {a b : ℝ} (hb1 : 3 * Real.pi / 2 < |b|) (hb2 : |b| ≤ 2 * Real.pi)
    (ha : |a| ≤ 2 * Real.pi - |b|) : Real.cosh a * Real.cos b ≤ 1 := by
  set d := 2 * Real.pi - |b| with hd
  have hd0 : 0 ≤ d := by linarith
  have hd1 : d < Real.pi / 2 := by linarith
  have hcos : Real.cos b = Real.cos d := by
    rw [← Real.cos_abs, hd, Real.cos_two_pi_sub]
  rw [hcos]
  have hda : |a| ≤ |d| := by rw [abs_of_nonneg hd0]; exact ha
  exact cosh_mul_cos_le_one_of_abs_le hda (by rw [abs_of_nonneg hd0]; exact hd1.le)

/-! ## B. Lemma B'': the combined angle-plus-log bound. -/

/-- 1/g + 1/(2 g^2) <= 1/(g - 1/2) for g > 1/2. -/
lemma inv_add_inv_two_sq_le {g : ℝ} (hg : 1 / 2 < g) :
    1 / g + 1 / (2 * g ^ 2) ≤ 1 / (g - 1 / 2) := by
  have hg0 : 0 < g := by linarith
  have hg1 : 0 < g - 1 / 2 := by linarith
  rw [div_add_div _ _ hg0.ne' (by positivity), div_le_div_iff₀ (by positivity) hg1]
  nlinarith [hg0]

/-- **Lemma B''.**  |theta| + |log r| <= 1/|gamma| + 1/(2 gamma^2) on the strip, |gamma| >= 1. -/
theorem abs_arg_add_abs_log_le {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hγ : 1 ≤ |ρ.im|) :
    |arg (wOf ρ)| + |Real.log ‖wOf ρ‖| ≤ 1 / |ρ.im| + 1 / (2 * ρ.im ^ 2) := by
  have hγ0 : ρ.im ≠ 0 := fun h => by rw [h, abs_zero] at hγ; linarith
  exact add_le_add (abs_arg_wOf_le h0 h1 hγ) (abs_log_norm_wOf_le h0 h1 hγ0)

/-- The combined bound in the sharp form: |theta| + |log r| <= 1/(|gamma| - 1/2). -/
theorem abs_arg_add_abs_log_le_sharp {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hγ : 1 ≤ |ρ.im|) :
    |arg (wOf ρ)| + |Real.log ‖wOf ρ‖| ≤ 1 / (|ρ.im| - 1 / 2) := by
  refine (abs_arg_add_abs_log_le h0 h1 hγ).trans ?_
  rw [← sq_abs ρ.im]
  exact inv_add_inv_two_sq_le (by linarith)

/-! ## C. Theorem C'': the sharp termwise threshold. -/

/-- **Theorem C''.**  For a strip point with |Im rho| >= 1 and N <= 2 pi (|Im rho| - 1/2), the
pair term is nonnegative, whether or not rho is on the line. -/
theorem pair_re_nonneg_of_far_sharp {N : ℕ} {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hγ : 1 ≤ |ρ.im|) (hN : (N : ℝ) ≤ 2 * Real.pi * (|ρ.im| - 1 / 2)) :
    0 ≤ (liKernel N ρ).re + (liKernel N (1 - conj ρ)).re := by
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at h0; simp at h0
  have hρ1 : ρ ≠ 1 := fun h => by rw [h] at h1; simp at h1
  have hγ0 : ρ.im ≠ 0 := fun h => by rw [h, abs_zero] at hγ; linarith
  have hg : 0 < |ρ.im| - 1 / 2 := by linarith
  have hw : 0 < ‖wOf ρ‖ := norm_pos_iff.mpr (wOf_ne_zero hρ0 hρ1)
  rw [pair_re_eq hρ0 hρ1, pow_add_inv_pow_eq_cosh hw]
  set a := (N : ℝ) * Real.log ‖wOf ρ‖ with ha
  set b := (N : ℝ) * arg (wOf ρ) with hb
  have hab : |a| ≤ |b| := by
    rw [ha, hb, abs_mul, abs_mul, Nat.abs_cast]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    calc |Real.log ‖wOf ρ‖| ≤ 1 / (2 * ρ.im ^ 2) := abs_log_norm_wOf_le h0 h1 hγ0
      _ ≤ 1 / (2 * |ρ.im|) := by
          apply one_div_le_one_div_of_le (by positivity)
          rw [← sq_abs]
          nlinarith
      _ ≤ |arg (wOf ρ)| := le_abs_arg_wOf h0 h1 hγ
  -- the combined bound: |a| + |b| <= N/(|gamma| - 1/2) <= 2 pi
  have hsum : |a| + |b| ≤ 2 * Real.pi := by
    rw [ha, hb, abs_mul, abs_mul, Nat.abs_cast, ← mul_add]
    calc (N : ℝ) * (|Real.log ‖wOf ρ‖| + |arg (wOf ρ)|)
        ≤ (N : ℝ) * (1 / (|ρ.im| - 1 / 2)) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          rw [add_comm]
          exact abs_arg_add_abs_log_le_sharp h0 h1 hγ
      _ ≤ (2 * Real.pi * (|ρ.im| - 1 / 2)) * (1 / (|ρ.im| - 1 / 2)) :=
          mul_le_mul_of_nonneg_right hN (by positivity)
      _ = 2 * Real.pi := by rw [mul_one_div, mul_div_cancel_right₀ _ hg.ne']
  by_cases hsmall : |b| ≤ Real.pi / 2
  · have := cosh_mul_cos_le_one_of_abs_le hab hsmall
    linarith
  · have hsmall := not_le.mp hsmall
    by_cases hmid : |b| ≤ 3 * Real.pi / 2
    · have hcos : Real.cos b ≤ 0 := by
        rw [← Real.cos_abs]
        exact Real.cos_nonpos_of_pi_div_two_le_of_le hsmall.le (by linarith)
      have := mul_nonpos_of_nonneg_of_nonpos (Real.cosh_pos a).le hcos
      linarith
    · have hmid := not_le.mp hmid
      have := cosh_mul_cos_le_one_window (a := a) hmid (by linarith [abs_nonneg a]) (by linarith)
      linarith

/-- **Theorem D'', termwise.** -/
theorem pair_re_nonneg_of_line_below_sharp {T : ℝ} (hT : 1 ≤ T)
    (hline : ∀ ρ, IsNontrivialZero ρ → |ρ.im| ≤ T → ρ.re = 1 / 2) {N : ℕ}
    (hN : (N : ℝ) ≤ 2 * Real.pi * (T - 1 / 2)) {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    0 ≤ (liKernel N ρ).re + (liKernel N (1 - conj ρ)).re := by
  by_cases hT' : |ρ.im| ≤ T
  · exact pair_re_nonneg_of_on_line (hline ρ hρ hT')
  · have hT' := not_le.mp hT'
    refine pair_re_nonneg_of_far_sharp hρ.2.1 hρ.2.2 (hT.trans hT'.le) (hN.trans ?_)
    have := Real.pi_pos
    nlinarith

/-- **Theorem D'' (the sharpened Li ladder).**  If every nontrivial zero with |Im rho| <= T
(T >= 1) has real part 1/2, then Re (liLimit N) >= 0 for every N <= 2 pi (T - 1/2). -/
theorem liLimit_re_nonneg_of_line_below_sharp (T : ℝ) (hT : 1 ≤ T)
    (hline : ∀ ρ, IsNontrivialZero ρ → |ρ.im| ≤ T → ρ.re = 1 / 2) (N : ℕ)
    (hN : (N : ℝ) ≤ 2 * Real.pi * (T - 1 / 2)) : 0 ≤ (liLimit N).re :=
  liLimit_re_nonneg_of_pairs fun _ hρ => pair_re_nonneg_of_line_below_sharp hT hline hN hρ

/-- The closed form: 0 <= Re (archSide N + finiteSide N) for N <= 2 pi (T - 1/2), N >= 1. -/
theorem archSide_add_finiteSide_re_nonneg_of_line_below_sharp (T : ℝ) (hT : 1 ≤ T)
    (hline : ∀ ρ, IsNontrivialZero ρ → |ρ.im| ≤ T → ρ.re = 1 / 2) (N : ℕ) (hN0 : 0 < N)
    (hN : (N : ℝ) ≤ 2 * Real.pi * (T - 1 / 2)) : 0 ≤ (archSide N + finiteSide N).re := by
  have h : liLimit N = archSide N + finiteSide N := RvMBridge27.liValue N hN0
  rw [← h]
  exact liLimit_re_nonneg_of_line_below_sharp T hT hline N hN

end RvMBridge29
