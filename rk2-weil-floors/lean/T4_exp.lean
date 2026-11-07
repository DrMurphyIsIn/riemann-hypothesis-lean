import Mathlib

/-! RK-2 C: Telperion exp_enclosure (unmodified) for e^{L^2/8}, L in {1, 1.45, 1.493945, 2, 2.25, 2.4}: the pole factor
of K_2 in the Zhu (13) coupling eps_C.  Demonstration of the one chain scalar with an existing emitter shape; eps_C as a
whole stays ARB.  conjecture1_proved = False. -/

namespace RK2.T4

theorem exp_L1 : ((283287113266706579 / 250000000000000000) : ℝ) ≤ Real.exp (1 / 8) ∧ Real.exp (1 / 8) ≤ ((1133148453066826317 / 1000000000000000000) : ℝ) := by
  have hx : |((1 / 8) : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  have hb := Real.exp_bound hx (n := 12) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb
  rw [abs_le] at hb
  obtain ⟨h1, h2⟩ := hb
  constructor
  · norm_num [Nat.factorial] at h1 ⊢; linarith
  · norm_num [Nat.factorial] at h2 ⊢; linarith

theorem exp_L145 : ((650291418403293211 / 500000000000000000) : ℝ) ≤ Real.exp (841 / 3200) ∧ Real.exp (841 / 3200) ≤ ((1300582836806586423 / 1000000000000000000) : ℝ) := by
  have hx : |((841 / 3200) : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  have hb := Real.exp_bound hx (n := 14) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb
  rw [abs_le] at hb
  obtain ⟨h1, h2⟩ := hb
  constructor
  · norm_num [Nat.factorial] at h1 ⊢; linarith
  · norm_num [Nat.factorial] at h2 ⊢; linarith

theorem exp_L1494 : ((1321786139445115961 / 1000000000000000000) : ℝ) ≤ Real.exp (89274866521 / 320000000000) ∧ Real.exp (89274866521 / 320000000000) ≤ ((660893069722557981 / 500000000000000000) : ℝ) := by
  have hx : |((89274866521 / 320000000000) : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  have hb := Real.exp_bound hx (n := 14) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb
  rw [abs_le] at hb
  obtain ⟨h1, h2⟩ := hb
  constructor
  · norm_num [Nat.factorial] at h1 ⊢; linarith
  · norm_num [Nat.factorial] at h2 ⊢; linarith

theorem exp_L2 : ((824360635350064073 / 500000000000000000) : ℝ) ≤ Real.exp (1 / 2) ∧ Real.exp (1 / 2) ≤ ((1648721270700128147 / 1000000000000000000) : ℝ) := by
  have hx : |((1 / 2) : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  have hb := Real.exp_bound hx (n := 17) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb
  rw [abs_le] at hb
  obtain ⟨h1, h2⟩ := hb
  constructor
  · norm_num [Nat.factorial] at h1 ⊢; linarith
  · norm_num [Nat.factorial] at h2 ⊢; linarith

theorem exp_L225 : ((1882898792081916797 / 1000000000000000000) : ℝ) ≤ Real.exp (81 / 128) ∧ Real.exp (81 / 128) ≤ ((941449396040958399 / 500000000000000000) : ℝ) := by
  have hx : |((81 / 128) : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  have hb := Real.exp_bound hx (n := 18) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb
  rw [abs_le] at hb
  obtain ⟨h1, h2⟩ := hb
  constructor
  · norm_num [Nat.factorial] at h1 ⊢; linarith
  · norm_num [Nat.factorial] at h2 ⊢; linarith

theorem exp_L24 : ((1027216605321943871 / 500000000000000000) : ℝ) ≤ Real.exp (18 / 25) ∧ Real.exp (18 / 25) ≤ ((2054433210643887743 / 1000000000000000000) : ℝ) := by
  have hx : |((18 / 25) : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  have hb := Real.exp_bound hx (n := 18) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb
  rw [abs_le] at hb
  obtain ⟨h1, h2⟩ := hb
  constructor
  · norm_num [Nat.factorial] at h1 ⊢; linarith
  · norm_num [Nat.factorial] at h2 ⊢; linarith

end RK2.T4
