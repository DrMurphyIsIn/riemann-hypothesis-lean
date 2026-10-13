/- telperion 0.1.6 | family OfflineDiscsInstances | input-hash 84e0fedfd1b01edb
   15 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib
import OfflineDiscs

namespace OfflineDiscsInstances

/-- Isolation instance `offline_discs_online_pair`: 2 explicitly given point(s) of the open
    critical strip, with the rational radius `r = (1 / 50)`.  Certified separation
    `min dist² = 741321/15625` and strip margin `min (re, 1 - re) = 1/2`,
    both strictly beating `(2r)² = 1/625` resp. `r`.
    conjecture1_proved = False — the points are INPUT, not a claim about ζ. -/
noncomputable def offline_discs_online_pair_p0 : ℂ := ⟨((1 / 2)), ((7067 / 500))⟩
noncomputable def offline_discs_online_pair_p1 : ℂ := ⟨((1 / 2)), ((10511 / 500))⟩

noncomputable def offline_discs_online_pair_S : Finset ℂ := {offline_discs_online_pair_p0, offline_discs_online_pair_p1}

/-- Pair (0,1): `(2·(1 / 50))² < dist²`, so the closed discs are disjoint. -/
theorem offline_discs_online_pair_pair_0_1 :
    Disjoint (Metric.closedBall offline_discs_online_pair_p0 (((1 / 50)) : ℝ))
      (Metric.closedBall offline_discs_online_pair_p1 (((1 / 50)) : ℝ)) := by
  apply Metric.closedBall_disjoint_closedBall
  rw [Complex.dist_eq, Complex.norm_def, Real.lt_sqrt (by norm_num)]
  simp only [offline_discs_online_pair_p0, offline_discs_online_pair_p1, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im]
  norm_num

/-- Point 0: the closed disc of radius `(1 / 50)` about `offline_discs_online_pair_p0`
    (real part `(1 / 2)`) stays inside the OPEN strip. -/
theorem offline_discs_online_pair_strip_0 :
    Metric.closedBall offline_discs_online_pair_p0 (((1 / 50)) : ℝ) ⊆ {s : ℂ | 0 < s.re ∧ s.re < 1} := by
  intro s hs
  have hd : dist s offline_discs_online_pair_p0 ≤ (((1 / 50)) : ℝ) := Metric.mem_closedBall.mp hs
  have hre := abs_le.mp (Quasicrystal.abs_re_sub_le_dist s offline_discs_online_pair_p0)
  have hz : (offline_discs_online_pair_p0).re = (((1 / 2)) : ℝ) := by
    simp only [offline_discs_online_pair_p0]
  rw [hz] at hre
  exact ⟨by linarith [hre.1], by linarith [hre.2]⟩

/-- Point 1: the closed disc of radius `(1 / 50)` about `offline_discs_online_pair_p1`
    (real part `(1 / 2)`) stays inside the OPEN strip. -/
theorem offline_discs_online_pair_strip_1 :
    Metric.closedBall offline_discs_online_pair_p1 (((1 / 50)) : ℝ) ⊆ {s : ℂ | 0 < s.re ∧ s.re < 1} := by
  intro s hs
  have hd : dist s offline_discs_online_pair_p1 ≤ (((1 / 50)) : ℝ) := Metric.mem_closedBall.mp hs
  have hre := abs_le.mp (Quasicrystal.abs_re_sub_le_dist s offline_discs_online_pair_p1)
  have hz : (offline_discs_online_pair_p1).re = (((1 / 2)) : ℝ) := by
    simp only [offline_discs_online_pair_p1]
  rw [hz] at hre
  exact ⟨by linarith [hre.1], by linarith [hre.2]⟩

/-- **Isolation instance** (offline_discs_online_pair): the concrete witness for the registry node
    `MM_offline_disjoint_discs` at these 2 point(s) — radius `r = (1 / 50)` makes the
    closed discs pairwise disjoint and keeps each inside the open critical strip.
    conjecture1_proved = False. -/
theorem offline_discs_online_pair :
    ∃ r : ℝ, 0 < r ∧
      (∀ z ∈ offline_discs_online_pair_S, ∀ w ∈ offline_discs_online_pair_S, z ≠ w →
        Disjoint (Metric.closedBall z r) (Metric.closedBall w r)) ∧
      (∀ z ∈ offline_discs_online_pair_S, Metric.closedBall z r ⊆ {s : ℂ | 0 < s.re ∧ s.re < 1}) := by
  refine ⟨(((1 / 50)) : ℝ), by norm_num, ?_, ?_⟩
  · intro z hz w hw hzw
    simp only [offline_discs_online_pair_S, Finset.mem_insert, Finset.mem_singleton] at hz hw
    rcases hz with rfl | rfl <;> rcases hw with rfl | rfl <;>
      first
        | exact absurd rfl hzw
        | exact offline_discs_online_pair_pair_0_1
        | exact offline_discs_online_pair_pair_0_1.symm
  · intro z hz
    simp only [offline_discs_online_pair_S, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact offline_discs_online_pair_strip_0
    · exact offline_discs_online_pair_strip_1

example : ∃ r : ℝ, 0 < r ∧
      (∀ z ∈ offline_discs_online_pair_S, ∀ w ∈ offline_discs_online_pair_S, z ≠ w →
        Disjoint (Metric.closedBall z r) (Metric.closedBall w r)) ∧
      (∀ z ∈ offline_discs_online_pair_S, Metric.closedBall z r ⊆ {s : ℂ | 0 < s.re ∧ s.re < 1}) := offline_discs_online_pair

/-- Isolation instance `offline_discs_offline_bank`: 4 explicitly given point(s) of the open
    critical strip, with the rational radius `r = (1 / 50)`.  Certified separation
    `min dist² = 1/25` and strip margin `min (re, 1 - re) = 2/5`,
    both strictly beating `(2r)² = 1/625` resp. `r`.
    conjecture1_proved = False — the points are INPUT, not a claim about ζ. -/
noncomputable def offline_discs_offline_bank_p0 : ℂ := ⟨((1 / 2)), ((7067 / 500))⟩
noncomputable def offline_discs_offline_bank_p1 : ℂ := ⟨((1 / 2)), ((10511 / 500))⟩
noncomputable def offline_discs_offline_bank_p2 : ℂ := ⟨((2 / 5)), ((2501 / 100))⟩
noncomputable def offline_discs_offline_bank_p3 : ℂ := ⟨((3 / 5)), ((2501 / 100))⟩

noncomputable def offline_discs_offline_bank_S : Finset ℂ := {offline_discs_offline_bank_p0, offline_discs_offline_bank_p1, offline_discs_offline_bank_p2, offline_discs_offline_bank_p3}

/-- Pair (0,1): `(2·(1 / 50))² < dist²`, so the closed discs are disjoint. -/
theorem offline_discs_offline_bank_pair_0_1 :
    Disjoint (Metric.closedBall offline_discs_offline_bank_p0 (((1 / 50)) : ℝ))
      (Metric.closedBall offline_discs_offline_bank_p1 (((1 / 50)) : ℝ)) := by
  apply Metric.closedBall_disjoint_closedBall
  rw [Complex.dist_eq, Complex.norm_def, Real.lt_sqrt (by norm_num)]
  simp only [offline_discs_offline_bank_p0, offline_discs_offline_bank_p1, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im]
  norm_num

/-- Pair (0,2): `(2·(1 / 50))² < dist²`, so the closed discs are disjoint. -/
theorem offline_discs_offline_bank_pair_0_2 :
    Disjoint (Metric.closedBall offline_discs_offline_bank_p0 (((1 / 50)) : ℝ))
      (Metric.closedBall offline_discs_offline_bank_p2 (((1 / 50)) : ℝ)) := by
  apply Metric.closedBall_disjoint_closedBall
  rw [Complex.dist_eq, Complex.norm_def, Real.lt_sqrt (by norm_num)]
  simp only [offline_discs_offline_bank_p0, offline_discs_offline_bank_p2, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im]
  norm_num

/-- Pair (0,3): `(2·(1 / 50))² < dist²`, so the closed discs are disjoint. -/
theorem offline_discs_offline_bank_pair_0_3 :
    Disjoint (Metric.closedBall offline_discs_offline_bank_p0 (((1 / 50)) : ℝ))
      (Metric.closedBall offline_discs_offline_bank_p3 (((1 / 50)) : ℝ)) := by
  apply Metric.closedBall_disjoint_closedBall
  rw [Complex.dist_eq, Complex.norm_def, Real.lt_sqrt (by norm_num)]
  simp only [offline_discs_offline_bank_p0, offline_discs_offline_bank_p3, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im]
  norm_num

/-- Pair (1,2): `(2·(1 / 50))² < dist²`, so the closed discs are disjoint. -/
theorem offline_discs_offline_bank_pair_1_2 :
    Disjoint (Metric.closedBall offline_discs_offline_bank_p1 (((1 / 50)) : ℝ))
      (Metric.closedBall offline_discs_offline_bank_p2 (((1 / 50)) : ℝ)) := by
  apply Metric.closedBall_disjoint_closedBall
  rw [Complex.dist_eq, Complex.norm_def, Real.lt_sqrt (by norm_num)]
  simp only [offline_discs_offline_bank_p1, offline_discs_offline_bank_p2, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im]
  norm_num

/-- Pair (1,3): `(2·(1 / 50))² < dist²`, so the closed discs are disjoint. -/
theorem offline_discs_offline_bank_pair_1_3 :
    Disjoint (Metric.closedBall offline_discs_offline_bank_p1 (((1 / 50)) : ℝ))
      (Metric.closedBall offline_discs_offline_bank_p3 (((1 / 50)) : ℝ)) := by
  apply Metric.closedBall_disjoint_closedBall
  rw [Complex.dist_eq, Complex.norm_def, Real.lt_sqrt (by norm_num)]
  simp only [offline_discs_offline_bank_p1, offline_discs_offline_bank_p3, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im]
  norm_num

/-- Pair (2,3): `(2·(1 / 50))² < dist²`, so the closed discs are disjoint. -/
theorem offline_discs_offline_bank_pair_2_3 :
    Disjoint (Metric.closedBall offline_discs_offline_bank_p2 (((1 / 50)) : ℝ))
      (Metric.closedBall offline_discs_offline_bank_p3 (((1 / 50)) : ℝ)) := by
  apply Metric.closedBall_disjoint_closedBall
  rw [Complex.dist_eq, Complex.norm_def, Real.lt_sqrt (by norm_num)]
  simp only [offline_discs_offline_bank_p2, offline_discs_offline_bank_p3, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im]
  norm_num

/-- Point 0: the closed disc of radius `(1 / 50)` about `offline_discs_offline_bank_p0`
    (real part `(1 / 2)`) stays inside the OPEN strip. -/
theorem offline_discs_offline_bank_strip_0 :
    Metric.closedBall offline_discs_offline_bank_p0 (((1 / 50)) : ℝ) ⊆ {s : ℂ | 0 < s.re ∧ s.re < 1} := by
  intro s hs
  have hd : dist s offline_discs_offline_bank_p0 ≤ (((1 / 50)) : ℝ) := Metric.mem_closedBall.mp hs
  have hre := abs_le.mp (Quasicrystal.abs_re_sub_le_dist s offline_discs_offline_bank_p0)
  have hz : (offline_discs_offline_bank_p0).re = (((1 / 2)) : ℝ) := by
    simp only [offline_discs_offline_bank_p0]
  rw [hz] at hre
  exact ⟨by linarith [hre.1], by linarith [hre.2]⟩

/-- Point 1: the closed disc of radius `(1 / 50)` about `offline_discs_offline_bank_p1`
    (real part `(1 / 2)`) stays inside the OPEN strip. -/
theorem offline_discs_offline_bank_strip_1 :
    Metric.closedBall offline_discs_offline_bank_p1 (((1 / 50)) : ℝ) ⊆ {s : ℂ | 0 < s.re ∧ s.re < 1} := by
  intro s hs
  have hd : dist s offline_discs_offline_bank_p1 ≤ (((1 / 50)) : ℝ) := Metric.mem_closedBall.mp hs
  have hre := abs_le.mp (Quasicrystal.abs_re_sub_le_dist s offline_discs_offline_bank_p1)
  have hz : (offline_discs_offline_bank_p1).re = (((1 / 2)) : ℝ) := by
    simp only [offline_discs_offline_bank_p1]
  rw [hz] at hre
  exact ⟨by linarith [hre.1], by linarith [hre.2]⟩

/-- Point 2: the closed disc of radius `(1 / 50)` about `offline_discs_offline_bank_p2`
    (real part `(2 / 5)`) stays inside the OPEN strip. -/
theorem offline_discs_offline_bank_strip_2 :
    Metric.closedBall offline_discs_offline_bank_p2 (((1 / 50)) : ℝ) ⊆ {s : ℂ | 0 < s.re ∧ s.re < 1} := by
  intro s hs
  have hd : dist s offline_discs_offline_bank_p2 ≤ (((1 / 50)) : ℝ) := Metric.mem_closedBall.mp hs
  have hre := abs_le.mp (Quasicrystal.abs_re_sub_le_dist s offline_discs_offline_bank_p2)
  have hz : (offline_discs_offline_bank_p2).re = (((2 / 5)) : ℝ) := by
    simp only [offline_discs_offline_bank_p2]
  rw [hz] at hre
  exact ⟨by linarith [hre.1], by linarith [hre.2]⟩

/-- Point 3: the closed disc of radius `(1 / 50)` about `offline_discs_offline_bank_p3`
    (real part `(3 / 5)`) stays inside the OPEN strip. -/
theorem offline_discs_offline_bank_strip_3 :
    Metric.closedBall offline_discs_offline_bank_p3 (((1 / 50)) : ℝ) ⊆ {s : ℂ | 0 < s.re ∧ s.re < 1} := by
  intro s hs
  have hd : dist s offline_discs_offline_bank_p3 ≤ (((1 / 50)) : ℝ) := Metric.mem_closedBall.mp hs
  have hre := abs_le.mp (Quasicrystal.abs_re_sub_le_dist s offline_discs_offline_bank_p3)
  have hz : (offline_discs_offline_bank_p3).re = (((3 / 5)) : ℝ) := by
    simp only [offline_discs_offline_bank_p3]
  rw [hz] at hre
  exact ⟨by linarith [hre.1], by linarith [hre.2]⟩

/-- **Isolation instance** (offline_discs_offline_bank): the concrete witness for the registry node
    `MM_offline_disjoint_discs` at these 4 point(s) — radius `r = (1 / 50)` makes the
    closed discs pairwise disjoint and keeps each inside the open critical strip.
    conjecture1_proved = False. -/
theorem offline_discs_offline_bank :
    ∃ r : ℝ, 0 < r ∧
      (∀ z ∈ offline_discs_offline_bank_S, ∀ w ∈ offline_discs_offline_bank_S, z ≠ w →
        Disjoint (Metric.closedBall z r) (Metric.closedBall w r)) ∧
      (∀ z ∈ offline_discs_offline_bank_S, Metric.closedBall z r ⊆ {s : ℂ | 0 < s.re ∧ s.re < 1}) := by
  refine ⟨(((1 / 50)) : ℝ), by norm_num, ?_, ?_⟩
  · intro z hz w hw hzw
    simp only [offline_discs_offline_bank_S, Finset.mem_insert, Finset.mem_singleton] at hz hw
    rcases hz with rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hzw
        | exact offline_discs_offline_bank_pair_0_1
        | exact offline_discs_offline_bank_pair_0_1.symm
        | exact offline_discs_offline_bank_pair_0_2
        | exact offline_discs_offline_bank_pair_0_2.symm
        | exact offline_discs_offline_bank_pair_0_3
        | exact offline_discs_offline_bank_pair_0_3.symm
        | exact offline_discs_offline_bank_pair_1_2
        | exact offline_discs_offline_bank_pair_1_2.symm
        | exact offline_discs_offline_bank_pair_1_3
        | exact offline_discs_offline_bank_pair_1_3.symm
        | exact offline_discs_offline_bank_pair_2_3
        | exact offline_discs_offline_bank_pair_2_3.symm
  · intro z hz
    simp only [offline_discs_offline_bank_S, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact offline_discs_offline_bank_strip_0
    · exact offline_discs_offline_bank_strip_1
    · exact offline_discs_offline_bank_strip_2
    · exact offline_discs_offline_bank_strip_3

example : ∃ r : ℝ, 0 < r ∧
      (∀ z ∈ offline_discs_offline_bank_S, ∀ w ∈ offline_discs_offline_bank_S, z ≠ w →
        Disjoint (Metric.closedBall z r) (Metric.closedBall w r)) ∧
      (∀ z ∈ offline_discs_offline_bank_S, Metric.closedBall z r ⊆ {s : ℂ | 0 < s.re ∧ s.re < 1}) := offline_discs_offline_bank

end OfflineDiscsInstances
