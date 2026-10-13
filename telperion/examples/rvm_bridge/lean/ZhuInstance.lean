/-
  ZhuInstance -- the proved tail constants at Zhu's certified instance L = 4/5, T# = 200, N = 200
  (rvm_bridge island, 2026-09-23).

  `legendreLocalization_L08_T200` / `legendreLocalizationOdd_L08_T200`: the eq. (13) tail data hold
  with the closed-form constants epsDfun / epsBfun of ZhuTail; `eps_sum_lt_betaStar_L08_T200`: their
  sum is below beta*(4/5, 200) >= 1/2 (the constants are below 1e-90; the kernel evaluates
  801!! and 803!! by `decide`).  Also `betaStar_L08_T200_ge_half` and `combMass_L08_le`, the
  finite part re-derived from its definition: A_L = sqrt2 log 2 + (2/sqrt3) log 3 + log 2
  (n = 2, 3, 4; n = 5 is excluded because exp(8/5) < 5).  Numbers proved, never trusted.
  Nothing about zeros.  No `sorry`.  conjecture1_proved = False.
-/
import ZhuTail

open scoped Nat

noncomputable section

namespace RvMBridgeZhu
open WeilWindow

/-! ### A. Elementary numeric bounds. -/

lemma hcut_L08_T200 : Real.exp 1 * (4 / 5) * 200 / 2 ≤ 2 * ((200 : ℕ) : ℝ) := by
  have := Real.exp_one_lt_d9
  push_cast
  linarith

lemma log_three_le : Real.log 3 ≤ 109862 / 100000 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 12)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

lemma exp_four_fifths_le : Real.exp (4 / 5) ≤ 222556 / 100000 := by
  have h := Real.exp_bound (x := 4 / 5) (by rw [abs_of_pos (by norm_num)]; norm_num) (n := 10) (by norm_num)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 4 / 5)] at h
  have h2 := (abs_le.mp h).2
  have hS : ∑ m ∈ Finset.range 10, (4 / 5 : ℝ) ^ m / (m.factorial : ℝ) ≤ 222555 / 100000 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have hb : (4 / 5 : ℝ) ^ 10 * (((10 : ℕ).succ : ℝ) / (((10 : ℕ).factorial : ℝ) * (10 : ℕ))) ≤ 1 / 100000 := by
    simp only [Nat.factorial, Nat.succ_eq_add_one]
    norm_num
  linarith

lemma exp_eight_fifths_lt_five : Real.exp (8 / 5) < 5 := by
  have h := exp_four_fifths_le
  have e : Real.exp (8 / 5) = Real.exp (4 / 5) * Real.exp (4 / 5) := by
    rw [← Real.exp_add]; norm_num
  have hp := Real.exp_pos (4 / 5)
  rw [e]
  nlinarith

lemma log_five_ge : 8 / 5 ≤ Real.log 5 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  exact exp_eight_fifths_lt_five.le

lemma sqrt_two_ge : (14142 / 10000 : ℝ) ≤ Real.sqrt 2 := by
  rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num

lemma sqrt_three_ge : (173205 / 100000 : ℝ) ≤ Real.sqrt 3 := by
  rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num

lemma sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-! ### B. The comb mass at L = 4/5, re-derived: n = 2, 3, 4 only. -/

lemma ite_le_of_nonneg {c : Prop} [Decidable c] {a : ℝ} (ha : 0 ≤ a) : (if c then a else 0) ≤ a := by
  split_ifs <;> linarith

theorem combMass_L08_le : combMass (4 / 5) ≤ 2943 / 1000 := by
  unfold combMass
  have hvan : ∀ n : ℕ, n ∉ Finset.range 6 →
      (if Real.log n < 2 * (4 / 5) then 2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n else 0) = 0 := by
    intro n hn
    rw [if_neg]
    intro hlt
    have hn' : 6 ≤ n := by simpa [Finset.mem_range] using hn
    have h5 : Real.log 5 ≤ Real.log n :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 5 ≤ n))
    linarith [log_five_ge]
  rw [tsum_eq_sum (s := Finset.range 6) hvan]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have hΛ0 : ArithmeticFunction.vonMangoldt 0 = 0 := by simp
  have hΛ1 : ArithmeticFunction.vonMangoldt 1 = 0 := ArithmeticFunction.vonMangoldt_apply_one
  have hΛ2 : ArithmeticFunction.vonMangoldt 2 = Real.log 2 :=
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  have hΛ3 : ArithmeticFunction.vonMangoldt 3 = Real.log 3 :=
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three
  have hΛ4 : ArithmeticFunction.vonMangoldt 4 = Real.log 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), hΛ2]
  have h5 : (if Real.log ((5 : ℕ) : ℝ) < 2 * (4 / 5) then
      2 * ArithmeticFunction.vonMangoldt 5 / Real.sqrt ((5 : ℕ) : ℝ) else 0) = 0 := by
    rw [if_neg]
    push_cast
    linarith [log_five_ge]
  rw [h5]
  have hl2 := Real.log_two_lt_d9.le
  have hl3 := log_three_le
  have hs2 := sqrt_two_ge
  have hs3 := sqrt_three_ge
  have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog3_nn : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have t2 : 2 * Real.log 2 / Real.sqrt 2 ≤ 9803 / 10000 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have t3 : 2 * Real.log 3 / Real.sqrt 3 ≤ 12687 / 10000 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have t4 : 2 * Real.log 2 / Real.sqrt 4 ≤ 6931472 / 10000000 := by
    rw [sqrt_four]; linarith
  have e0 := ite_le_of_nonneg (c := Real.log ((0 : ℕ) : ℝ) < 2 * (4 / 5))
    (a := 2 * ArithmeticFunction.vonMangoldt 0 / Real.sqrt ((0 : ℕ) : ℝ)) (by rw [hΛ0]; simp)
  have e1 := ite_le_of_nonneg (c := Real.log ((1 : ℕ) : ℝ) < 2 * (4 / 5))
    (a := 2 * ArithmeticFunction.vonMangoldt 1 / Real.sqrt ((1 : ℕ) : ℝ)) (by rw [hΛ1]; simp)
  have e2 := ite_le_of_nonneg (c := Real.log ((2 : ℕ) : ℝ) < 2 * (4 / 5))
    (a := 2 * ArithmeticFunction.vonMangoldt 2 / Real.sqrt ((2 : ℕ) : ℝ)) (by rw [hΛ2]; positivity)
  have e3 := ite_le_of_nonneg (c := Real.log ((3 : ℕ) : ℝ) < 2 * (4 / 5))
    (a := 2 * ArithmeticFunction.vonMangoldt 3 / Real.sqrt ((3 : ℕ) : ℝ)) (by rw [hΛ3]; positivity)
  have e4 := ite_le_of_nonneg (c := Real.log ((4 : ℕ) : ℝ) < 2 * (4 / 5))
    (a := 2 * ArithmeticFunction.vonMangoldt 4 / Real.sqrt ((4 : ℕ) : ℝ)) (by rw [hΛ4]; positivity)
  rw [hΛ0, hΛ1, hΛ2, hΛ3, hΛ4] at *
  push_cast at *
  simp only [mul_zero, zero_div] at e0 e1
  linarith

/-! ### C. beta* at the instance. -/

theorem betaStar_L08_T200_ge_half : (1 / 2 : ℝ) ≤ betaStar (4 / 5) 200 := by
  unfold betaStar
  have hA := combMass_L08_le
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have h1 : Real.log (2000 / 63) ≤ Real.log (200 / (2 * Real.pi)) := by
    apply Real.log_le_log (by norm_num)
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have h2 : Real.log (2000 / 63) = 5 * Real.log 2 + Real.log (125 / 126) := by
    rw [show (2000 / 63 : ℝ) = 2 ^ 5 * (125 / 126) by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast; ring
  have h3 : 1 - (125 / 126 : ℝ)⁻¹ ≤ Real.log (125 / 126) := Real.one_sub_inv_le_log_of_pos (by norm_num)
  have hl2 := Real.log_two_gt_d9
  norm_num at h3
  linarith

theorem betaStar_L08_T200_le_five : betaStar (4 / 5) 200 ≤ 5 := by
  unfold betaStar
  have hA := combMass_nonneg (4 / 5)
  have hpi := Real.pi_gt_three
  have h1 : Real.log (200 / (2 * Real.pi)) ≤ Real.log 64 := by
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have h2 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; push_cast; ring
  have hl2 := Real.log_two_lt_d9
  linarith

/-! ### D. The tail constants at the instance. -/

lemma symbolSup_L08_T200_le : symbolSup (4 / 5) 200 ≤ 19 := by
  unfold symbolSup
  have hA := combMass_L08_le
  have hb1 := betaStar_L08_T200_ge_half
  have hb2 := betaStar_L08_T200_le_five
  have habs : |betaStar (4 / 5) 200| ≤ 5 := abs_le.mpr ⟨by linarith, hb2⟩
  have hlog100 : Real.log (200 / 2) ≤ 7 * Real.log 2 := by
    rw [show (200 / 2 : ℝ) = 100 by norm_num,
      show (7 : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ 7) by rw [Real.log_pow]; push_cast; ring]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have hlogpi : Real.log Real.pi ≤ 2 * Real.log 2 := by
    rw [show (2 : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ 2) by rw [Real.log_pow]; push_cast; ring]
    exact Real.log_le_log Real.pi_pos (by nlinarith [Real.pi_lt_d2])
  have hl2 := Real.log_two_lt_d9
  norm_num
  linarith

lemma cosh_two_fifths_le : Real.cosh (4 / 5 / 2) ≤ 2 := by
  rw [Real.cosh_eq]
  have h1 : Real.exp (4 / 5 / 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
  have h2 : Real.exp (-(4 / 5 / 2)) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by norm_num)
  rw [Real.exp_zero] at h2
  have := Real.exp_one_lt_d9
  linarith

lemma entryConst_L08_T200_le : entryConst (4 / 5) 200 ≤ 1300 := by
  unfold entryConst
  have hS := symbolSup_L08_T200_le
  have hS0 : 0 ≤ symbolSup (4 / 5) 200 :=
    (abs_nonneg _).trans (abs_weilSymbol_sub_betaStar_le (L := 4 / 5) (T := 200) (by norm_num) le_rfl (by norm_num))
  have hc := cosh_two_fifths_le
  have hc0 := (Real.cosh_pos (4 / 5 / 2)).le
  have hpi := Real.pi_gt_three
  have h1 : 200 * symbolSup (4 / 5) 200 / Real.pi ≤ 200 * 19 / 3 := by
    rw [div_le_div_iff₀ Real.pi_pos (by norm_num)]; nlinarith
  nlinarith

lemma entryConst_nonneg_L08 : 0 ≤ entryConst (4 / 5) 200 := by
  unfold entryConst
  have hS0 : 0 ≤ symbolSup (4 / 5) 200 :=
    (abs_nonneg _).trans (abs_weilSymbol_sub_betaStar_le (L := 4 / 5) (T := 200) (by norm_num) le_rfl (by norm_num))
  positivity

set_option maxRecDepth 100000 in
/-- The kernel evaluates `801!!`: `160^400 · 10^103 ≤ 801!!`. -/
lemma pow_le_doubleFactorial_801 : (160 : ℕ) ^ 400 * 10 ^ 103 ≤ (801 : ℕ)‼ := by
  decide

set_option maxRecDepth 100000 in
/-- The kernel evaluates `803!!`: `160^401 · 10^103 ≤ 803!!`. -/
lemma pow_le_doubleFactorial_803 : (160 : ℕ) ^ 401 * 10 ^ 103 ≤ (803 : ℕ)‼ := by
  decide

lemma real_pow_le_doubleFactorial_801 : (160 : ℝ) ^ 400 * 10 ^ 103 ≤ (((801 : ℕ)‼ : ℕ) : ℝ) := by
  have := (Nat.cast_le (α := ℝ)).mpr pow_le_doubleFactorial_801
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_ofNat] at this
  exact this

lemma real_pow_le_doubleFactorial_803 : (160 : ℝ) ^ 401 * 10 ^ 103 ≤ (((803 : ℕ)‼ : ℕ) : ℝ) := by
  have := (Nat.cast_le (α := ℝ)).mpr pow_le_doubleFactorial_803
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_ofNat] at this
  exact this

lemma tailMajorant_L08_T200_le : tailMajorant (4 / 5) 200 200 ≤ 1 / 10 ^ 100 := by
  unfold tailMajorant
  have hs : Real.sqrt (4 / 5) ≤ 1 := by rw [Real.sqrt_le_iff]; norm_num
  have e1 : (200 * (4 / 5) : ℝ) ^ (2 * 200) = (160 : ℝ) ^ 400 := by norm_num
  have e2 : (2 * (2 * 200) + 1 : ℕ) = 801 := by norm_num
  rw [e1, e2]
  have hpos : (0 : ℝ) < (((801 : ℕ)‼ : ℕ) : ℝ) := by exact_mod_cast Nat.doubleFactorial_pos _
  have hkey : (160 : ℝ) ^ 400 / (((801 : ℕ)‼ : ℕ) : ℝ) ≤ 1 / 10 ^ 103 := by
    rw [div_le_div_iff₀ hpos (by positivity), one_mul]
    exact real_pow_le_doubleFactorial_801
  have h0 : (0 : ℝ) ≤ (160 : ℝ) ^ 400 / (((801 : ℕ)‼ : ℕ) : ℝ) := by positivity
  push_cast
  calc 2 * Real.sqrt (4 / 5) * (200 + 1) * ((160 : ℝ) ^ 400 / (((801 : ℕ)‼ : ℕ) : ℝ))
      ≤ 2 * 1 * (200 + 1) * (1 / 10 ^ 103) := by gcongr
    _ ≤ 1 / 10 ^ 100 := by norm_num

lemma tailMajorantOdd_L08_T200_le : tailMajorantOdd (4 / 5) 200 200 ≤ 1 / 10 ^ 100 := by
  unfold tailMajorantOdd
  have hs : Real.sqrt (4 / 5) ≤ 1 := by rw [Real.sqrt_le_iff]; norm_num
  have e1 : (200 * (4 / 5) : ℝ) ^ (2 * 200 + 1) = (160 : ℝ) ^ 401 := by norm_num
  have e2 : (2 * (2 * 200 + 1) + 1 : ℕ) = 803 := by norm_num
  rw [e1, e2]
  have hpos : (0 : ℝ) < (((803 : ℕ)‼ : ℕ) : ℝ) := by exact_mod_cast Nat.doubleFactorial_pos _
  have hkey : (160 : ℝ) ^ 401 / (((803 : ℕ)‼ : ℕ) : ℝ) ≤ 1 / 10 ^ 103 := by
    rw [div_le_div_iff₀ hpos (by positivity), one_mul]
    exact real_pow_le_doubleFactorial_803
  have h0 : (0 : ℝ) ≤ (160 : ℝ) ^ 401 / (((803 : ℕ)‼ : ℕ) : ℝ) := by positivity
  push_cast
  calc 2 * Real.sqrt (4 / 5) * (200 + 2) * ((160 : ℝ) ^ 401 / (((803 : ℕ)‼ : ℕ) : ℝ))
      ≤ 2 * 1 * (200 + 2) * (1 / 10 ^ 103) := by gcongr
    _ ≤ 1 / 10 ^ 100 := by norm_num

/-! ### E. The instance theorems. -/

/-- **The eq. (13) tail data at Zhu's certified instance, even sector, PROVED.** -/
theorem legendreLocalization_L08_T200 :
    LegendreLocalization (4 / 5) 200 200 (epsDfun (4 / 5) 200 200) (epsBfun (4 / 5) 200 200) :=
  legendreLocalization_of_cut (by norm_num) (by norm_num) (by norm_num) hcut_L08_T200

/-- **The eq. (13) tail data at Zhu's certified instance, odd sector, PROVED.** -/
theorem legendreLocalizationOdd_L08_T200 :
    LegendreLocalizationOdd (4 / 5) 200 200 (epsDfunOdd (4 / 5) 200 200) (epsBfunOdd (4 / 5) 200 200) :=
  legendreLocalizationOdd_of_cut (by norm_num) (by norm_num) (by norm_num) hcut_L08_T200

/-- The four proved tail constants sum to less than `10^-90`. -/
theorem eps_sum_L08_T200_le :
    epsDfun (4 / 5) 200 200 + epsBfun (4 / 5) 200 200 + epsDfunOdd (4 / 5) 200 200 + epsBfunOdd (4 / 5) 200 200
      ≤ 1 / 10 ^ 90 := by
  unfold epsDfun epsBfun epsDfunOdd epsBfunOdd
  have hK := entryConst_L08_T200_le
  have hK0 := entryConst_nonneg_L08
  have hb := tailMajorant_L08_T200_le
  have hb0 := tailMajorant_nonneg (L := 4 / 5) (T := 200) (by norm_num) (by norm_num) 200
  have hbo := tailMajorantOdd_L08_T200_le
  have hbo0 := tailMajorantOdd_nonneg (L := 4 / 5) (T := 200) (by norm_num) (by norm_num) 200
  have hb2 : tailMajorant (4 / 5) 200 200 ^ 2 ≤ (1 / 10 ^ 100) ^ 2 := by gcongr
  have hbo2 : tailMajorantOdd (4 / 5) 200 200 ^ 2 ≤ (1 / 10 ^ 100) ^ 2 := by gcongr
  push_cast
  have h1 : (10 / 7 : ℝ) * entryConst (4 / 5) 200 * tailMajorant (4 / 5) 200 200 ^ 2
      ≤ (10 / 7) * 1300 * (1 / 10 ^ 100) ^ 2 := by gcongr
  have h2 : (10 / 7 + 200 : ℝ) * entryConst (4 / 5) 200 * ((1 + 2 * (4 / 5)) / 2) * tailMajorant (4 / 5) 200 200
      ≤ (10 / 7 + 200) * 1300 * ((1 + 2 * (4 / 5)) / 2) * (1 / 10 ^ 100) := by gcongr
  have h3 : (10 / 7 : ℝ) * entryConst (4 / 5) 200 * tailMajorantOdd (4 / 5) 200 200 ^ 2
      ≤ (10 / 7) * 1300 * (1 / 10 ^ 100) ^ 2 := by gcongr
  have h4 : (10 / 7 + 200 : ℝ) * entryConst (4 / 5) 200 * ((1 + 2 * (4 / 5)) / 2) * tailMajorantOdd (4 / 5) 200 200
      ≤ (10 / 7 + 200) * 1300 * ((1 + 2 * (4 / 5)) / 2) * (1 / 10 ^ 100) := by gcongr
  have c1 : (10 / 7 : ℝ) * 1300 * (1 / 10 ^ 100) ^ 2 ≤ 1 / 10 ^ 195 := by norm_num
  have c2 : (10 / 7 + 200 : ℝ) * 1300 * ((1 + 2 * (4 / 5)) / 2) * (1 / 10 ^ 100) ≤ 1 / 10 ^ 93 := by norm_num
  have c3 : (1 / 10 ^ 195 : ℝ) + 1 / 10 ^ 93 + 1 / 10 ^ 195 + 1 / 10 ^ 93 ≤ 1 / 10 ^ 90 := by norm_num
  linarith

/-- **The closing arithmetic at the instance**: the proved tail constants are below `β*`. -/
theorem eps_sum_lt_betaStar_L08_T200 :
    epsDfun (4 / 5) 200 200 + epsBfun (4 / 5) 200 200 + epsDfunOdd (4 / 5) 200 200 + epsBfunOdd (4 / 5) 200 200
      < betaStar (4 / 5) 200 := by
  have h := eps_sum_L08_T200_le
  have hb := betaStar_L08_T200_ge_half
  have : (1 : ℝ) / 10 ^ 90 < 1 / 2 := by norm_num
  linarith

end RvMBridgeZhu

end
