/-  OfflineDiscs.lean -- PROGRAM MIRRORMERE E4b isolation lemma (QC_RECURRENCE section 4.3).

    Registry node: MM_offline_disjoint_discs (telperion/missions/mirrormere).
    Statement is mirrored VERBATIM from
      telperion/missions/mirrormere/lean/Statements/MM_offline_disjoint_discs.lean
    (node sha256 bac57ccef7c3f828) into this island's namespace.

    Content: finitely many distinct points of the open critical strip
    {0 < re < 1} admit a single positive radius r whose closed discs are
    pairwise disjoint and each contained in the strip.  Pure Mathlib metric
    topology; no MMDefs vocabulary is involved.

    This is the geometric substrate for counting off-line zeros by disjoint
    recurrence-deficit discs (the Rouche-template leg of E5).  It says NOTHING
    about where zeta's zeros are; it is a lemma about finite sets of points.

    conjecture1_proved = False (NOT a proof of RH).
-/
import Mathlib

namespace Quasicrystal

/-- Any finite set of positive reals has a positive common lower bound.
    (Finset induction; the empty set gets the default bound 1.) -/
theorem exists_pos_lower_bound_of_finset (T : Finset ℝ) (hT : ∀ x ∈ T, 0 < x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ T, ε ≤ x := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert a T _ ih =>
    obtain ⟨ε, hε, hle⟩ := ih (fun x hx => hT x (Finset.mem_insert_of_mem hx))
    refine ⟨min ε a, lt_min hε (hT a (Finset.mem_insert_self a T)), ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hle x hx)

/-- The real part is 1-Lipschitz: |s.re - z.re| <= dist s z. -/
theorem abs_re_sub_le_dist (s z : ℂ) : |s.re - z.re| ≤ dist s z := by
  have h := Complex.abs_re_le_norm (s - z)
  rw [Complex.sub_re] at h
  rwa [dist_eq_norm]

/-- MM_offline_disjoint_discs (VERBATIM statement of the registry node):
    finitely many points strictly inside the open critical strip admit a common
    positive radius whose closed discs are pairwise disjoint (for distinct
    centres) and each contained in the strip. -/
theorem offline_disjoint_discs (S : Finset ℂ)
    (hstrip : ∀ z ∈ S, 0 < z.re ∧ z.re < 1) :
    ∃ r : ℝ, 0 < r ∧
      (∀ z ∈ S, ∀ w ∈ S, z ≠ w → Disjoint (Metric.closedBall z r) (Metric.closedBall w r)) ∧
      (∀ z ∈ S, Metric.closedBall z r ⊆ {s : ℂ | 0 < s.re ∧ s.re < 1}) := by
  classical
  -- separation scale: a positive lower bound on all pairwise distances
  obtain ⟨ε₁, hε₁, h₁⟩ := exists_pos_lower_bound_of_finset
    ((S.offDiag).image (fun p => dist p.1 p.2)) (by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      exact dist_pos.mpr (Finset.mem_offDiag.mp hp).2.2)
  -- strip margin: a positive lower bound on all distances to the strip boundary
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_pos_lower_bound_of_finset
    (S.image (fun z => min z.re (1 - z.re))) (by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      exact lt_min (hstrip z hz).1 (by linarith [(hstrip z hz).2]))
  refine ⟨min (ε₁ / 3) (ε₂ / 2), lt_min (by positivity) (by positivity), ?_, ?_⟩
  · -- pairwise disjointness: r + r <= 2 ε₁ / 3 < ε₁ <= dist z w
    intro z hz w hw hzw
    apply Metric.closedBall_disjoint_closedBall
    have hd : ε₁ ≤ dist z w :=
      h₁ _ (Finset.mem_image.mpr ⟨(z, w), Finset.mem_offDiag.mpr ⟨hz, hw, hzw⟩, rfl⟩)
    have hm := min_le_left (ε₁ / 3) (ε₂ / 2)
    linarith
  · -- strip containment: |s.re - z.re| <= r <= ε₂ / 2 < min z.re (1 - z.re)
    intro z hz s hs
    have hd : dist s z ≤ min (ε₁ / 3) (ε₂ / 2) := Metric.mem_closedBall.mp hs
    have hm : ε₂ ≤ min z.re (1 - z.re) := h₂ _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
    have hre := abs_le.mp (abs_re_sub_le_dist s z)
    have hmr := min_le_right (ε₁ / 3) (ε₂ / 2)
    have hz1 := min_le_left z.re (1 - z.re)
    have hz2 := min_le_right z.re (1 - z.re)
    constructor <;> linarith [hre.1, hre.2]

end Quasicrystal

-- conjecture1_proved = False
