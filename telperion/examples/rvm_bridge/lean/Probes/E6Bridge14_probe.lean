/-
  Probes for E6Bridge14 (2026-09-21): axiom audit of the effective Gaussian dominance theorem
  and its lemmas; the threshold is >= 1; a NUMERIC instantiation y0 = 1/10, xmin = 1/5, N = 20,
  D = 2, B = 1 with the threshold pinned to [297, 300] by kernel-checked bounds
  (its value is 50 log 400 = 299.57...); the spacing floor is load-bearing (the threshold is
  unbounded as xmin -> 0).
  Run: cd telperion/examples/rvm_bridge/lean && lake env lean Probes/E6Bridge14_probe.lean
-/
import E6Bridge14

open RvMBridge14

/-! ### Axiom audit. -/
#print axioms RvMBridge14.effective_gaussian_dominance
#print axioms RvMBridge14.offline_zeros_small_or_margin
#print axioms RvMBridge14.effectiveThreshold_unbounded_of_small_spacing
#print axioms RvMBridge14.effectiveThreshold_mono_B
#print axioms RvMBridge14.le_exp_of_log_le
#print axioms RvMBridge14.tsum_winSet_eq_sum
#print axioms RvMBridge14.re_term_centre
#print axioms RvMBridge14.norm_term_le_competitor
#print axioms RvMBridge14.re_window_sum_le
#print axioms RvMBridge14.windowCount_le_Ncount

#check @RvMBridge14.effective_gaussian_dominance
#check @RvMBridge14.offline_zeros_small_or_margin

/-! ### The threshold is positive (>= 1) for every parameter choice. -/
example (y0 xmin : ℝ) (N : ℕ) (B D : ℝ) : 1 ≤ effectiveThreshold y0 xmin N B D :=
  one_le_effectiveThreshold y0 xmin N B D

/-! ### Numeric instantiation: y0 = 1/10, xmin = 1/5, N = 20, D = 2, B = 1.
The two log terms are  log 34000 / (2/25) = 130.4...  and  log 400 / (1/50) = 299.57...,
so the threshold is 50 log 400 = 299.57...; we pin it to [297, 300]. -/

lemma exp_six_lt : Real.exp 6 < 403.5 := by
  have h : Real.exp 1 ^ 6 = Real.exp 6 := by
    rw [Real.exp_one_pow]
    norm_num
  rw [← h]
  calc Real.exp 1 ^ 6 < 2.7182818286 ^ 6 :=
        pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
    _ < 403.5 := by norm_num

lemma exp_six_gt : 400 < Real.exp 6 := by
  have h : Real.exp 1 ^ 6 = Real.exp 6 := by
    rw [Real.exp_one_pow]
    norm_num
  rw [← h]
  calc (400 : ℝ) < 2.7182818283 ^ 6 := by norm_num
    _ < Real.exp 1 ^ 6 :=
        pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)

lemma exp_twentyfour_gt : 34000 < Real.exp 24 := by
  have h : Real.exp 1 ^ 24 = Real.exp 24 := by
    rw [Real.exp_one_pow]
    norm_num
  rw [← h]
  calc (34000 : ℝ) < 2.7182818283 ^ 24 := by norm_num
    _ < Real.exp 1 ^ 24 :=
        pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)

theorem threshold_example_le : effectiveThreshold (1 / 10) (1 / 5) 20 1 2 ≤ 300 := by
  unfold effectiveThreshold
  have hQ1 : (4 * ((20 : ℕ) : ℝ) * ((2 : ℝ) ^ 2 + 1 / 4) / (1 / 10 : ℝ) ^ 2) = 34000 := by
    norm_num
  have hQ2 : (4 * (1 : ℝ) / (1 / 10 : ℝ) ^ 2) = 400 := by norm_num
  rw [hQ1, hQ2, max_eq_right (by norm_num : (1 : ℝ) ≤ 34000),
    max_eq_right (by norm_num : (1 : ℝ) ≤ 400)]
  have hl1 : Real.log 34000 ≤ 24 :=
    (Real.log_le_iff_le_exp (by norm_num)).mpr exp_twentyfour_gt.le
  have hl2 : Real.log 400 ≤ 6 :=
    (Real.log_le_iff_le_exp (by norm_num)).mpr exp_six_gt.le
  refine max_le (by norm_num) (max_le ?_ ?_)
  · rw [div_le_iff₀ (by norm_num)]
    linarith
  · rw [div_le_iff₀ (by norm_num)]
    linarith

theorem threshold_example_ge : 297 ≤ effectiveThreshold (1 / 10) (1 / 5) 20 1 2 := by
  unfold effectiveThreshold
  have hQ2 : (4 * (1 : ℝ) / (1 / 10 : ℝ) ^ 2) = 400 := by norm_num
  rw [hQ2, max_eq_right (by norm_num : (1 : ℝ) ≤ 400)]
  -- log 400 >= 5.94 since exp 5.94 = exp 6 / exp 0.06 <= 403.5 / 1.06 < 400
  have hexp : Real.exp 5.94 ≤ 400 := by
    have h1 : Real.exp 5.94 = Real.exp 6 / Real.exp 0.06 := by
      rw [← Real.exp_sub]
      norm_num
    have h2 : (1.06 : ℝ) ≤ Real.exp 0.06 := by
      have := Real.add_one_le_exp (0.06 : ℝ)
      linarith
    rw [h1, div_le_iff₀ (Real.exp_pos _)]
    nlinarith [exp_six_lt]
  have hl : (5.94 : ℝ) ≤ Real.log 400 := (Real.le_log_iff_exp_le (by norm_num)).mpr hexp
  refine le_trans ?_ (le_max_right _ _)
  refine le_trans ?_ (le_max_right _ _)
  rw [le_div_iff₀ (by norm_num)]
  linarith

/-! ### The spacing floor is load-bearing: with y0 = 1/10, N = 20, D = 2 (any B) the threshold
exceeds 10^6 for some positive xmin. -/
example (B : ℝ) : ∃ xmin : ℝ, 0 < xmin ∧ (10 ^ 6 : ℝ) ≤ effectiveThreshold (1 / 10) xmin 20 B 2 :=
  effectiveThreshold_unbounded_of_small_spacing (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) B _
