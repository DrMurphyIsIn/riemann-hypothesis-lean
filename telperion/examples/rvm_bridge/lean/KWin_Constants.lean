/-
  KWin_Constants -- the real constants of the prime-free window certificate at 2L = log 2
  (rvm_bridge island, 2026-09-24).

  conjecture1_proved = False.  A finite-window Weil positivity statement is NOT RH (PR #604: the
  1.3e-3 full-class margin at this window is zero content; not Connes-Consani, whose theorem is
  for the pole-free class).

  PROVED HERE:
    * gamma_le: Euler's constant gamma <= H_16 - 4 * 0.6931471803 - 1/32 + 1/3072 (= gamma +
      1.3e-7).  The island's 0.58112 is off by 3.9e-3, larger than the whole margin, so this
      sharper bound is mandatory.  Route: a_n = H_n - log n - 1/(2n) + 1/(12 n^2) is antitone for
      n >= 16 (log(1 + 1/n) against its degree-6 Taylor floor; the difference is
      (2n^4 - 3n^3 - 67n^2 - 122n - 50) / (60 n^6 (n-1) (n+1)^2) >= 0) and tends to gamma
      (Real.tendsto_harmonic_sub_log), so gamma <= a_16.
    * log_pi_le: log pi <= 1.1447298859 (pi_lt_d20 and the exp Taylor floor, kernel-checked).
    * combMass_L0 / weilSymbol_L0: on the window 2L = log 2 the prime comb is EMPTY
      (Lambda(0) = Lambda(1) = 0), so Psi_L0(t) = Re psi(1/4 + it/2) - log pi.
    * beta0_le_betaStar: 1107/1000 <= beta*(log 2 / 2, 20) = log(10/pi) - 1/20.
    * abs_Psi_sub_beta0_le: |Psi(t) - beta0| <= 6.485 on [0, 20].
    * cosh_half_ell_le: cosh(l/2) <= 1.02, l = 26/75; L0_lt_ell: log 2 / 2 < 26/75.
  No `sorry`.
-/
import ZhuTail
import KWin_Data

open Real Finset Filter Topology

noncomputable section

namespace KWin
open RvMBridge11 RvMBridge30 RvMBridgeZhu WeilWindow

/-- The window half-width `L0 = log 2 / 2` (the edge `2 L0 = log 2` of the prime-free window). -/
def L0 : ℝ := Real.log 2 / 2

/-- The Weil symbol on the prime-free window: `Psi(t) = Re psi(1/4 + it/2) - log pi`. -/
def Psi (t : ℝ) : ℝ := psiR t - Real.log Real.pi

/-! ## A. pi. -/

theorem pi_gt_Q : ((piLoQ : ℚ) : ℝ) < Real.pi := by
  have h := Real.pi_gt_d20
  have e : ((piLoQ : ℚ) : ℝ) = 3.14159265358979323846 := by unfold piLoQ; norm_num
  rw [e]; exact h

theorem pi_lt_Q : Real.pi < ((piHiQ : ℚ) : ℝ) := by
  have h := Real.pi_lt_d20
  have e : ((piHiQ : ℚ) : ℝ) = 3.14159265358979323847 := by unfold piHiQ; norm_num
  rw [e]; exact h

/-! ## B. Euler's constant. -/

/-- `a n = H_n - log n - 1/(2n) + 1/(12 n^2)`. -/
def emA (n : ℕ) : ℝ := (harmonic n : ℝ) - Real.log n - 1 / (2 * n) + 1 / (12 * (n : ℝ) ^ 2)

lemma em_poly {n : ℝ} (hn : 16 ≤ n) :
    1 / (2 * (n + 1)) + 1 / (2 * n) - 1 / (12 * n ^ 2) + 1 / (12 * (n + 1) ^ 2)
      ≤ 1 / n - 1 / (2 * n ^ 2) + 1 / (3 * n ^ 3) - 1 / (4 * n ^ 4) + 1 / (5 * n ^ 5)
        - 1 / (6 * n ^ 6) - (1 / n) ^ 7 / (1 - 1 / n) := by
  have hn0 : n ≠ 0 := by positivity
  have hn1 : n - 1 ≠ 0 := by
    have : 0 < n - 1 := by linarith
    exact this.ne'
  have hn2 : n + 1 ≠ 0 := by positivity
  rw [← sub_nonneg]
  have h1 : 1 - 1 / n = (n - 1) / n := by field_simp
  have key : (1 / n - 1 / (2 * n ^ 2) + 1 / (3 * n ^ 3) - 1 / (4 * n ^ 4) + 1 / (5 * n ^ 5)
        - 1 / (6 * n ^ 6) - (1 / n) ^ 7 / (1 - 1 / n))
      - (1 / (2 * (n + 1)) + 1 / (2 * n) - 1 / (12 * n ^ 2) + 1 / (12 * (n + 1) ^ 2))
      = (2 * n ^ 4 - 3 * n ^ 3 - 67 * n ^ 2 - 122 * n - 50)
        / (60 * n ^ 6 * (n - 1) * (n + 1) ^ 2) := by
    rw [h1]
    field_simp
    ring
  rw [key]
  apply div_nonneg
  · have hm : 0 ≤ n - 16 := by linarith
    have e : 2 * n ^ 4 - 3 * n ^ 3 - 67 * n ^ 2 - 122 * n - 50
        = 2 * (n - 16) ^ 4 + 125 * (n - 16) ^ 3 + 2861 * (n - 16) ^ 2 + 28198 * (n - 16) + 99630 := by
      ring
    rw [e]
    positivity
  · have : 0 < n - 1 := by linarith
    positivity

/-- `log (1 + x) >= x - x^2/2 + ... - x^6/6 - x^7/(1-x)` for `0 < x < 1`. -/
lemma log_one_add_ge {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4 + x ^ 5 / 5 - x ^ 6 / 6 - x ^ 7 / (1 - x)
      ≤ Real.log (1 + x) := by
  have habs : |(-x)| < 1 := by rw [abs_neg, abs_of_pos hx0]; exact hx1
  have h := Real.abs_log_sub_add_sum_range_le habs 6
  have e1 : (∑ i ∈ range 6, (-x) ^ (i + 1) / ((i : ℝ) + 1))
      = -x + x ^ 2 / 2 - x ^ 3 / 3 + x ^ 4 / 4 - x ^ 5 / 5 + x ^ 6 / 6 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    ring
  rw [e1, abs_neg, abs_of_pos hx0, sub_neg_eq_add] at h
  have h2 := (abs_le.mp h).1
  linarith

lemma emA_succ_le {n : ℕ} (hn : 16 ≤ n) : emA (n + 1) ≤ emA n := by
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hx0 : (0 : ℝ) < 1 / n := by positivity
  have hx1 : (1 : ℝ) / n < 1 := by rw [div_lt_one hn0]; linarith
  have hlog := log_one_add_ge hx0 hx1
  have hpoly := em_poly hnR
  have hl : Real.log ((n : ℝ) + 1) - Real.log n = Real.log (1 + 1 / n) := by
    rw [← Real.log_div (by positivity) hn0.ne']
    congr 1
    field_simp
  have hH : (harmonic (n + 1) : ℝ) = (harmonic n : ℝ) + 1 / ((n : ℝ) + 1) := by
    rw [harmonic_succ]
    push_cast
    ring
  unfold emA
  push_cast
  rw [hH]
  have e2 : (1 / (n : ℝ)) ^ 2 / 2 = 1 / (2 * (n : ℝ) ^ 2) := by field_simp
  have e3 : (1 / (n : ℝ)) ^ 3 / 3 = 1 / (3 * (n : ℝ) ^ 3) := by field_simp
  have e4 : (1 / (n : ℝ)) ^ 4 / 4 = 1 / (4 * (n : ℝ) ^ 4) := by field_simp
  have e5 : (1 / (n : ℝ)) ^ 5 / 5 = 1 / (5 * (n : ℝ) ^ 5) := by field_simp
  have e6 : (1 / (n : ℝ)) ^ 6 / 6 = 1 / (6 * (n : ℝ) ^ 6) := by field_simp
  rw [e2, e3, e4, e5, e6] at hlog
  have e7 : 1 / ((n : ℝ) + 1) - 1 / (2 * ((n : ℝ) + 1)) = 1 / (2 * ((n : ℝ) + 1)) := by
    field_simp
    ring
  nlinarith [hl, hlog, hpoly, e7]

lemma tendsto_emA : Tendsto emA atTop (𝓝 Real.eulerMascheroniConstant) := by
  have h1 := Real.tendsto_harmonic_sub_log
  have h2 : Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ))) atTop (𝓝 0) := by
    have := tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : ℝ)
    refine this.congr fun n => ?_
    rw [div_div]
  have h3 : Tendsto (fun n : ℕ => 1 / (12 * (n : ℝ) ^ 2)) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_
      tendsto_one_div_atTop_nhds_zero_nat
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h4 := (h1.sub h2).add h3
  simp only [sub_zero, add_zero] at h4
  refine h4.congr fun n => ?_
  unfold emA
  ring

/-- **A1.** `gamma <= H_16 - 4 * 0.6931471803 - 1/32 + 1/3072`. -/
theorem gamma_le : Real.eulerMascheroniConstant ≤ ((gammaUpQ : ℚ) : ℝ) := by
  have hanti : Antitone (fun m : ℕ => emA (m + 16)) :=
    antitone_nat_of_succ_le fun m => by
      have := emA_succ_le (n := m + 16) (by omega)
      simpa [add_assoc, add_comm 1 16, add_left_comm] using this
  have hlim : Tendsto (fun m : ℕ => emA (m + 16)) atTop (𝓝 Real.eulerMascheroniConstant) :=
    tendsto_emA.comp (tendsto_add_atTop_nat 16)
  have h16 : Real.eulerMascheroniConstant ≤ emA 16 := by
    have := hanti.le_of_tendsto hlim 0
    simpa using this
  refine h16.trans ?_
  unfold emA gammaUpQ
  have hlog16 : Real.log ((16 : ℕ) : ℝ) = 4 * Real.log 2 := by
    rw [show ((16 : ℕ) : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hl2 := Real.log_two_gt_d9
  have hH : (harmonic 16 : ℝ) = ((∑ k ∈ range 16, (1 : ℚ) / (k + 1) : ℚ) : ℝ) := by
    unfold harmonic
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  rw [hlog16, hH]
  push_cast
  norm_num at hl2 ⊢
  linarith

/-! ## C. log pi. -/

/-- **A2.** `log pi <= 1.1447298859`. -/
theorem log_pi_le : Real.log Real.pi ≤ ((logPiUpQ : ℚ) : ℝ) := by
  rw [Real.log_le_iff_le_exp Real.pi_pos]
  have h2 : (piHiQ : ℚ) ≤ ∑ i ∈ range 30, logPiUpQ ^ i / (i.factorial : ℚ) := by decide +kernel
  have h2' : ((piHiQ : ℚ) : ℝ) ≤ ∑ i ∈ range 30, ((logPiUpQ : ℚ) : ℝ) ^ i / (i.factorial : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr h2
    push_cast at this
    exact this
  have h3 := Real.sum_le_exp_of_nonneg (x := ((logPiUpQ : ℚ) : ℝ)) (by unfold logPiUpQ; norm_num) 30
  linarith [pi_lt_Q]

theorem one_le_log_pi : 1 ≤ Real.log Real.pi := by
  rw [Real.le_log_iff_exp_le Real.pi_pos]
  have := Real.exp_one_lt_d9
  have := Real.pi_gt_three
  linarith

/-! ## D. The prime comb is empty on the window. -/

lemma comb_term_eq_zero (n : ℕ) (hn : Real.log n < 2 * L0) :
    ArithmeticFunction.vonMangoldt n = 0 := by
  have h2 : 2 * L0 = Real.log 2 := by unfold L0; ring
  rw [h2] at hn
  have hn2 : n < 2 := by
    by_contra hc
    have hc' : 2 ≤ n := not_lt.mp hc
    have : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hc')
    linarith
  interval_cases n <;> simp

/-- **A4.** `combMass (log 2 / 2) = 0`. -/
theorem combMass_L0 : combMass L0 = 0 := by
  unfold combMass
  convert tsum_zero with n
  split_ifs with h
  · rw [comb_term_eq_zero n h]; simp
  · rfl

/-- **A5.** On the window the Weil symbol is `Psi`. -/
theorem weilSymbol_L0 (t : ℝ) : weilSymbol L0 t = Psi t := by
  unfold weilSymbol Psi
  have h0 : (∑' n : ℕ, if Real.log n < 2 * L0 then
      2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * Real.cos (t * Real.log n) else 0) = 0 := by
    convert tsum_zero with n
    split_ifs with h
    · rw [comb_term_eq_zero n h]; simp
    · rfl
  rw [h0, sub_zero]
  rfl

/-! ## E. beta*. -/

/-- **A3.** `beta0 = 1107/1000 <= beta*(log 2 / 2, 20) = log(10/pi) - 1/20`. -/
theorem beta0_le_betaStar : ((beta0Q : ℚ) : ℝ) ≤ betaStar L0 20 := by
  unfold betaStar
  rw [combMass_L0]
  have hlog : (1157 / 1000 : ℝ) ≤ Real.log (20 / (2 * Real.pi)) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have e1 : Real.exp (1157 / 1000) = Real.exp (1157 / 2000) ^ 2 := by
      rw [← Real.exp_nat_mul]; norm_num
    have e2 := Real.exp_bound' (x := 1157 / 2000) (by norm_num) (by norm_num) (n := 10) (by norm_num)
    have hq : ((∑ m ∈ range 10, (1157 / 2000 : ℚ) ^ m / (m.factorial : ℚ))
        + (1157 / 2000 : ℚ) ^ 10 * (10 + 1) / ((Nat.factorial 10 : ℚ) * 10)) ^ 2 * piHiQ ≤ 10 := by
      decide +kernel
    have hq' : ((∑ m ∈ range 10, (1157 / 2000 : ℝ) ^ m / (m.factorial : ℝ))
        + (1157 / 2000 : ℝ) ^ 10 * (10 + 1) / ((Nat.factorial 10 : ℝ) * 10)) ^ 2
          * ((piHiQ : ℚ) : ℝ) ≤ 10 := by
      have := (Rat.cast_le (K := ℝ)).mpr hq
      push_cast at this
      exact this
    have hpos : 0 ≤ Real.exp (1157 / 2000) := (Real.exp_pos _).le
    have hsq : Real.exp (1157 / 2000) ^ 2 ≤ ((∑ m ∈ range 10, (1157 / 2000 : ℝ) ^ m / (m.factorial : ℝ))
        + (1157 / 2000 : ℝ) ^ 10 * (10 + 1) / ((Nat.factorial 10 : ℝ) * 10)) ^ 2 :=
      pow_le_pow_left₀ hpos e2 2
    have hpi := pi_lt_Q
    have hpi0 := Real.pi_pos
    rw [e1, show (20 : ℝ) / (2 * Real.pi) = 10 / Real.pi by field_simp; ring,
      le_div_iff₀ hpi0]
    nlinarith
  unfold beta0Q
  push_cast
  linarith

/-! ## F. The symbol is bounded on [0, 20]. -/

lemma log_ten_le : Real.log 10 ≤ 231 / 100 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.sum_le_exp_of_nonneg (x := 231 / 100) (by norm_num) 20
  have hq : (10 : ℚ) ≤ ∑ i ∈ range 20, (231 / 100 : ℚ) ^ i / (i.factorial : ℚ) := by decide +kernel
  have hq' : (10 : ℝ) ≤ ∑ i ∈ range 20, (231 / 100 : ℝ) ^ i / (i.factorial : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at this
    exact this
  linarith

/-- **A7.** `|Psi(t) - beta0| <= 6.485` for `0 <= t <= 20`. -/
theorem abs_Psi_sub_beta0_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 20) :
    |Psi t - ((beta0Q : ℚ) : ℝ)| ≤ ((S0Q : ℚ) : ℝ) := by
  have hlow : psiR 0 ≤ psiR t := psiR_mono le_rfl (by rw [abs_of_nonneg h0]; exact h0)
  have hup : psiR t ≤ psiR 20 := psiR_mono h0 (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 20)]; exact h1)
  have hfl := psiR_floor_0
  have hst := psiR_le_stirling (t := 20) (by norm_num)
  have h10 : Real.log ((20 : ℝ) / 2) = Real.log 10 := by norm_num
  rw [h10] at hst
  have hl10 := log_ten_le
  have hlp := log_pi_le
  have hlp1 := one_le_log_pi
  unfold Psi
  unfold beta0Q S0Q logPiUpQ at *
  push_cast at *
  rw [abs_le]
  constructor <;> nlinarith

/-! ## G. Miscellaneous. -/

/-- **A6.** `log 2 / 2 < 26/75`. -/
theorem L0_lt_ell : L0 < ((ellQ : ℚ) : ℝ) := by
  unfold L0 ellQ
  have := Real.log_two_lt_d9
  push_cast
  norm_num at this ⊢
  linarith

theorem L0_pos : 0 < L0 := by
  unfold L0
  have := Real.log_two_gt_d9
  norm_num at this ⊢
  linarith

theorem cosh_half_ell_le : Real.cosh (((ellQ : ℚ) : ℝ) / 2) ≤ ((CpQ : ℚ) : ℝ) := by
  have h := Real.cosh_le_exp_half_sq (((ellQ : ℚ) : ℝ) / 2)
  have hx : (((ellQ : ℚ) : ℝ) / 2) ^ 2 / 2 = 169 / 11250 := by unfold ellQ; push_cast; norm_num
  rw [hx] at h
  have e2 := Real.exp_bound' (x := 169 / 11250) (by norm_num) (by norm_num) (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at e2
  unfold CpQ
  push_cast
  norm_num at e2 ⊢
  linarith

end KWin

end
