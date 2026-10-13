import ArchS6_Real

/-!
# ArchS6_Enum: an orthonormal basis of `L²([0,1]; ℝ)` is indexed by a copy of `ℕ`

* `countable_of_orthonormal`: an orthonormal family in the separable space `L²([0,1]; ℝ)` has a
  countable index type (disjoint balls of radius `1/2`).
* `infinite_of_complete`: a complete orthonormal family there has an infinite index type (otherwise
  `L²([0,1])` would be finite-dimensional, but the indicators of the disjoint intervals
  `(1/(n+2), 1/(n+1))` are infinitely many nonzero pairwise orthogonal vectors).
* `exists_equiv_nat`: hence every `EigenBasis CopR ι` admits an enumeration `σ : ℕ ≃ ι`.

conjecture1_proved = False.
-/

open MeasureTheory Set
open scoped InnerProductSpace ENNReal

noncomputable section

namespace ArchS6

open ArchS5

set_option linter.unusedSectionVars false

theorem separableSpace_L2IR : TopologicalSpace.SeparableSpace (L2IR 0 1) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  infer_instance

/-- An orthonormal family in `L²([0,1]; ℝ)` is countable. -/
theorem countable_of_orthonormal {ι : Type*} {e : ι → L2IR 0 1} (he : Orthonormal ℝ e) :
    Countable ι := by
  have := separableSpace_L2IR
  refine Pairwise.countable_of_isOpen_disjoint (s := fun i ↦ Metric.ball (e i) (1 / 2)) ?_
    (fun _ ↦ Metric.isOpen_ball) (fun i ↦ ⟨e i, Metric.mem_ball_self (by norm_num)⟩)
  intro i j hij
  rw [Function.onFun, Set.disjoint_left]
  intro z hzi hzj
  have hd : ‖e i - e j‖ ^ 2 = 2 := by
    rw [norm_sub_sq_real, he.1 i, he.1 j, he.2 hij]; norm_num
  have h1 : ‖e i - e j‖ < 1 := by
    rw [Metric.mem_ball, dist_eq_norm] at hzi hzj
    calc ‖e i - e j‖ = ‖(z - e j) - (z - e i)‖ := by congr 1; abel
      _ ≤ ‖z - e j‖ + ‖z - e i‖ := norm_sub_le _ _
      _ < 1 := by linarith
  nlinarith [norm_nonneg (e i - e j)]

/-- The intervals `(1/(n+2), 1/(n+1)) ⊂ [0,1]`. -/
def bumpSet (n : ℕ) : Set ℝ := Ioo (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))

theorem bumpSet_subset (n : ℕ) : bumpSet n ⊆ Icc 0 1 := by
  intro x hx
  have h1 : 0 < 1 / ((n : ℝ) + 2) := by positivity
  have h2 : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem bumpSet_lt (n : ℕ) : 1 / ((n : ℝ) + 2) < 1 / ((n : ℝ) + 1) :=
  one_div_lt_one_div_of_lt (by positivity) (by linarith)

theorem disjoint_bumpSet {n m : ℕ} (h : n < m) : Disjoint (bumpSet n) (bumpSet m) := by
  rw [Set.disjoint_left]
  intro x hn hm
  have : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 2) := by
    apply one_div_le_one_div_of_le (by positivity)
    have : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
    linarith
  linarith [hn.1, hm.2]

/-- The indicator of `bumpSet n` in `L²([0,1]; ℝ)`. -/
def bump (n : ℕ) : L2IR 0 1 :=
  indicatorConstLp 2 (measurableSet_Ioo : MeasurableSet (bumpSet n)) (measure_ne_top _ _) (1 : ℝ)

theorem volI_bumpSet_pos (n : ℕ) : 0 < (volI 0 1).real (bumpSet n) := by
  rw [Measure.real]
  show 0 < ((volume.restrict (Icc (0 : ℝ) 1)) (Ioo (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1)))).toReal
  rw [Measure.restrict_apply measurableSet_Ioo,
    Set.inter_eq_left.2 (show Ioo (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1)) ⊆ Icc 0 1 from bumpSet_subset n), Real.volume_Ioo,
    ENNReal.toReal_ofReal (by linarith [bumpSet_lt n])]
  linarith [bumpSet_lt n]

theorem bump_ne_zero (n : ℕ) : bump n ≠ 0 := by
  intro h
  have := congrArg norm h
  rw [bump, norm_indicatorConstLp (by norm_num) (by simp), norm_zero, norm_one, one_mul] at this
  have hpow : 0 < (volI 0 1).real (bumpSet n) ^ (1 / (2 : ℝ≥0∞).toReal) :=
    Real.rpow_pos_of_pos (volI_bumpSet_pos n) _
  exact absurd this (ne_of_gt hpow)

theorem inner_bump {n m : ℕ} (h : n ≠ m) : ⟪bump n, bump m⟫_ℝ = 0 := by
  rw [bump, bump, MeasureTheory.L2.inner_indicatorConstLp_indicatorConstLp]
  have hd : bumpSet n ∩ bumpSet m = ∅ := by
    rcases lt_or_gt_of_ne h with h' | h'
    · exact Set.disjoint_iff_inter_eq_empty.1 (disjoint_bumpSet h')
    · rw [Set.inter_comm]; exact Set.disjoint_iff_inter_eq_empty.1 (disjoint_bumpSet h')
  simp only [bumpSet] at hd
  rw [hd]; simp

/-- A complete orthonormal family in `L²([0,1]; ℝ)` has an infinite index type. -/
theorem infinite_of_complete {ι : Type*} {e : ι → L2IR 0 1} (he : Orthonormal ℝ e)
    (hc : ∀ x, (∀ i, ⟪e i, x⟫_ℝ = 0) → x = 0) : Infinite ι := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  have := Fintype.ofFinite ι
  -- `L²([0,1])` is spanned by the `e i`
  have hspan : ∀ x : L2IR 0 1, x ∈ Submodule.span ℝ (Set.range e) := by
    intro x
    have hx : x - ∑ i, ⟪e i, x⟫_ℝ • e i = 0 := by
      apply hc
      intro j
      rw [inner_sub_right, he.inner_right_fintype, sub_self]
    rw [sub_eq_zero.1 hx]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have htop : (⊤ : Submodule ℝ (L2IR 0 1)) = Submodule.span ℝ (Set.range e) :=
    (eq_top_iff.2 fun x _ ↦ hspan x).symm
  have : Module.Finite ℝ (L2IR 0 1) :=
    Module.Finite.of_fg_top (htop ▸ Submodule.fg_span (Set.finite_range e))
  have hli : LinearIndependent ℝ bump :=
    linearIndependent_of_ne_zero_of_inner_eq_zero bump_ne_zero fun n m h ↦ inner_bump h
  have := hli.finite
  exact _root_.not_finite ℕ

/-- **Enumeration**: every real eigenbasis of `C_ℝ` is indexed by a copy of `ℕ`. -/
theorem exists_equiv_nat {ι : Type*} (bR : EigenBasis CopR ι) : Nonempty (ℕ ≃ ι) := by
  have := countable_of_orthonormal bR.orthonormal
  have := infinite_of_complete bR.orthonormal bR.complete
  exact nonempty_equiv_of_countable

end ArchS6
