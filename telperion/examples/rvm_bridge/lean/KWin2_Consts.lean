/-
  KWin2_Consts -- shared real constants of the KWin2 window certificates (rvm_bridge island,
  2026-09-24).

  conjecture1_proved = False.  (Finite-window Weil positivity is not RH; not Connes-Consani; cf.
  PR #604.)

  PROVED HERE:
    * log2_near_S: |log 2 - S| <= 2^-60, S = sum_{i < 60} 2^-(i+1)/(i+1) (the kernel-evaluated
      partial sum), from Mathlib's `Real.abs_log_sub_add_sum_range_le` at x = 1/2;
    * sqrt2_bounds: two 20-digit rationals squeeze sqrt 2 (their squares are kernel-checked);
    * gamma_le32: Euler's constant gamma <= a_32 = H_32 - log 32 - 1/64 + 1/12288 (rounded up at
      10^-20), i.e. gamma + 8e-9.  KWin's gamma_le stops at a_16 (gamma + 1.3e-7), which is larger
      than the margin of the certificates past L = 2/5, so the sharper bound is needed there.  Same
      route as KWin (a_n antitone for n >= 16, a_n -> gamma), log 2 from log2_near_S.
  No `sorry`.
-/
import KWin_Constants

open Real Finset Filter Topology

noncomputable section

namespace KWin2
open KWin (emA emA_succ_le tendsto_emA ceilR le_ceilR)

/-! ## A. log 2. -/

/-- The partial sum of `log 2 = sum_{i >= 1} 2^-i / i` (60 terms). -/
def log2S : ℚ := ∑ i ∈ range 60, (1 / 2 : ℚ) ^ (i + 1) / ((i : ℚ) + 1)

theorem log2S_ge : (1 / 2) ^ 60 ≤ log2S := by decide +kernel

lemma log2_near_S : |Real.log 2 - ((log2S : ℚ) : ℝ)| ≤ (1 / 2) ^ 60 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 / 2 : ℝ)) (by norm_num) 60
  have e : Real.log (1 - 1 / 2) = -Real.log 2 := by
    rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.log_inv]
  rw [e] at h
  have hS : ((log2S : ℚ) : ℝ) = ∑ i ∈ range 60, (1 / 2 : ℝ) ^ (i + 1) / ((i : ℝ) + 1) := by
    unfold log2S; push_cast; rfl
  rw [← hS] at h
  have hr : |(1 / 2 : ℝ)| ^ (60 + 1) / (1 - |(1 / 2 : ℝ)|) = (1 / 2) ^ 60 := by norm_num
  rw [hr] at h
  rw [abs_sub_comm]
  have e2 : ((log2S : ℚ) : ℝ) + -Real.log 2 = ((log2S : ℚ) : ℝ) - Real.log 2 := by ring
  rwa [e2] at h

/-! ## B. sqrt 2. -/

/-- `sqrt 2` squeezed by two 20-digit rationals. -/
def sq2lo : ℚ := 14142135623730950488 / 10 ^ 19
def sq2hi : ℚ := 14142135623730950489 / 10 ^ 19

theorem sq2lo_sq : sq2lo ^ 2 ≤ 2 := by decide +kernel
theorem sq2hi_sq : 2 ≤ sq2hi ^ 2 := by decide +kernel
theorem sq2lo_pos : 0 < sq2lo := by decide +kernel
theorem sq2hi_nonneg : 0 ≤ sq2hi := by decide +kernel

lemma sqrt2_bounds : ((sq2lo : ℚ) : ℝ) ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ ((sq2hi : ℚ) : ℝ) := by
  have hhi0 : (0 : ℝ) ≤ ((sq2hi : ℚ) : ℝ) := by exact_mod_cast sq2hi_nonneg
  constructor
  · apply Real.le_sqrt_of_sq_le
    have := (Rat.cast_le (K := ℝ)).mpr sq2lo_sq
    push_cast at this
    exact this
  · rw [Real.sqrt_le_left hhi0]
    have := (Rat.cast_le (K := ℝ)).mpr sq2hi_sq
    push_cast at this
    exact this

/-! ## C. Euler's constant at n = 32. -/

/-- `H_32`. -/
def H32 : ℚ := ∑ k ∈ range 32, (1 : ℚ) / (k + 1)

/-- `a_32 = H_32 - log 32 - 1/64 + 1/12288`, with `log 32 >= 5 (S - 2^-60)`, rounded up. -/
def gamUp32 : ℚ := ceilR (H32 - 5 * (log2S - (1 / 2) ^ 60) - 1 / 64 + 1 / 12288) 20

/-- **`gamma <= gamUp32`** (= gamma + 8e-9). -/
theorem gamma_le32 : Real.eulerMascheroniConstant ≤ ((gamUp32 : ℚ) : ℝ) := by
  have hanti : Antitone (fun m : ℕ => emA (m + 16)) :=
    antitone_nat_of_succ_le fun m => by
      have := emA_succ_le (n := m + 16) (by omega)
      simpa [add_assoc, add_comm 1 16, add_left_comm] using this
  have hlim : Tendsto (fun m : ℕ => emA (m + 16)) atTop (𝓝 Real.eulerMascheroniConstant) :=
    tendsto_emA.comp (tendsto_add_atTop_nat 16)
  have h32 : Real.eulerMascheroniConstant ≤ emA 32 := by
    have := hanti.le_of_tendsto hlim 16
    simpa using this
  refine h32.trans ?_
  have hc := le_ceilR (H32 - 5 * (log2S - (1 / 2) ^ 60) - 1 / 64 + 1 / 12288) 20
  have hc' : (((H32 - 5 * (log2S - (1 / 2) ^ 60) - 1 / 64 + 1 / 12288 : ℚ)) : ℝ)
      ≤ ((gamUp32 : ℚ) : ℝ) := by exact_mod_cast hc
  refine le_trans ?_ hc'
  unfold emA
  have hlog32 : Real.log ((32 : ℕ) : ℝ) = 5 * Real.log 2 := by
    rw [show ((32 : ℕ) : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
  have hl2 := (abs_le.mp log2_near_S).1
  have hH : (harmonic 32 : ℝ) = ((H32 : ℚ) : ℝ) := by
    unfold harmonic H32
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hlog32, hH]
  push_cast
  norm_num
  linarith

end KWin2

end
