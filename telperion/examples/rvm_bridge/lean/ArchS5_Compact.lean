import ArchS5_Adjoint

/-!
# ArchS5_Compact: integral operators with `L²` kernels are compact (stage S5)

On finite measure spaces, every `T_K` with `K ∈ L²(μ ⊗ ν)` is a compact operator.

Proof: the set of kernels `K` with `T_K` compact is closed (it is the preimage of the closed set of
compact operators under the continuous map `K ↦ T_K`, `ArchS5_KernelOp.intOpL`) and is a subspace.
For a measurable rectangle `A ×ˢ B` the operator of `c·1_{A×B}` is the rank-one map
`f ↦ (∫_B f) • c·1_A` (`intOp_indicator_rect`).  A Dynkin (π-λ) argument on the π-system of
rectangles (`MeasurableSpace.induction_on_inter`) extends compactness to the kernel `c·1_S` of every
measurable `S ⊆ α × β`; then `Lp.induction` extends it to all of `L²`.

conjecture1_proved = False.
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal InnerProductSpace symmDiff

noncomputable section

namespace ArchS5

set_option linter.unusedSectionVars false

variable {𝕜 : Type*} [RCLike 𝕜]
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-! ### Rectangles give rank-one operators -/

/-- The operator of the rectangle kernel `c·1_{A×B}` is `f ↦ (∫_B f) • c·1_A`. -/
theorem intOp_indicator_rect {A : Set α} {B : Set β} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (c : 𝕜) (f : Lp 𝕜 2 ν) :
    intOp (indicatorConstLp 2 (hA.prod hB) (measure_ne_top (μ.prod ν) _) c) f =
      (∫ y in B, f y ∂ν) • indicatorConstLp 2 hA (measure_ne_top μ A) c := by
  rw [intOp_apply_eq_iff]
  have hK := kernelApply_congr_left (f := ⇑f)
    (indicatorConstLp_coeFn (p := 2) (μ := μ.prod ν) (hs := hA.prod hB)
      (hμs := measure_ne_top (μ.prod ν) _) (c := c))
  filter_upwards [Lp.coeFn_smul (∫ y in B, f y ∂ν) (indicatorConstLp 2 hA (measure_ne_top μ A) c),
    indicatorConstLp_coeFn (p := 2) (μ := μ) (hs := hA) (hμs := measure_ne_top μ A) (c := c), hK]
    with x h1 h2 h3
  rw [h1, Pi.smul_apply, h2, smul_eq_mul]
  change _ = kernelApply ν _ f x
  rw [h3, kernelApply]
  by_cases hx : x ∈ A
  · have : ∀ y, (A ×ˢ B).indicator (fun _ ↦ c) (x, y) * f y = B.indicator (fun y ↦ c * f y) y := by
      intro y; by_cases hy : y ∈ B <;> simp [Set.indicator, hx, hy]
    simp only [this, integral_indicator hB, integral_const_mul, Set.indicator_of_mem hx]
    ring
  · simp [Set.indicator, hx]

/-- Rank-one maps `f ↦ φ f • v` are compact. -/
theorem isCompactOperator_rankOne {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (φ : E →L[𝕜] 𝕜) (v : F) :
    IsCompactOperator (fun f ↦ φ f • v) :=
  (isCompactOperator_of_locallyCompactSpace_dom φ).clm_comp
    (ContinuousLinearMap.toSpanSingleton 𝕜 v)

theorem isCompactOperator_intOp_rect {A : Set α} {B : Set β} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (c : 𝕜) :
    IsCompactOperator (intOp (indicatorConstLp 2 (hA.prod hB) (measure_ne_top (μ.prod ν) _) c)) := by
  have h := isCompactOperator_rankOne
    (innerSL 𝕜 (indicatorConstLp 2 hB (measure_ne_top ν B) (1 : 𝕜)))
    (indicatorConstLp 2 hA (measure_ne_top μ A) c)
  have heq : ⇑(intOp (indicatorConstLp 2 (hA.prod hB) (measure_ne_top (μ.prod ν) _) c)) =
      fun f ↦ (innerSL 𝕜 (indicatorConstLp 2 hB (measure_ne_top ν B) (1 : 𝕜))) f •
        indicatorConstLp 2 hA (measure_ne_top μ A) c := by
    funext f
    rw [intOp_indicator_rect hA hB c f, innerSL_apply_apply, L2.inner_indicatorConstLp_one]
  rw [heq]; exact h

/-! ### Dynkin argument -/

theorem indicatorConstLp_compl_eq {γ : Type*} [MeasurableSpace γ] {m : Measure γ}
    [IsFiniteMeasure m] {S : Set γ} (hS : MeasurableSet S) (c : 𝕜) :
    indicatorConstLp 2 hS.compl (measure_ne_top m _) c =
      indicatorConstLp 2 MeasurableSet.univ (measure_ne_top m _) c -
        indicatorConstLp 2 hS (measure_ne_top m _) c := by
  ext1
  filter_upwards [indicatorConstLp_coeFn (p := 2) (μ := m) (hs := hS.compl)
      (hμs := measure_ne_top m _) (c := c),
    indicatorConstLp_coeFn (p := 2) (μ := m) (hs := MeasurableSet.univ)
      (hμs := measure_ne_top m _) (c := c),
    indicatorConstLp_coeFn (p := 2) (μ := m) (hs := hS) (hμs := measure_ne_top m _) (c := c),
    Lp.coeFn_sub (indicatorConstLp 2 MeasurableSet.univ (measure_ne_top m _) c)
      (indicatorConstLp 2 hS (measure_ne_top m _) c)] with x h1 h2 h3 h4
  rw [h4, Pi.sub_apply, h1, h2, h3]
  by_cases hx : x ∈ S <;> simp [Set.indicator, hx]

/-- Compactness of `T_K` for the kernel `c·1_S`, `S` any measurable subset of `α × β`. -/
theorem isCompactOperator_intOp_indicator (c : 𝕜) :
    ∀ (S : Set (α × β)) (hS : MeasurableSet S),
      IsCompactOperator (intOp (indicatorConstLp 2 hS (measure_ne_top (μ.prod ν) S) c)) := by
  intro S hS
  induction S, hS using MeasurableSpace.induction_on_inter generateFrom_prod.symm
    isPiSystem_prod with
  | empty =>
    have : indicatorConstLp 2 MeasurableSet.empty (measure_ne_top (μ.prod ν) ∅) c = 0 :=
      indicatorConstLp_empty
    rw [this, intOp_zero]
    exact isCompactOperator_zero
  | basic t ht =>
    obtain ⟨A, hA, B, hB, rfl⟩ := ht
    exact isCompactOperator_intOp_rect hA hB c
  | compl t htm ih =>
    rw [indicatorConstLp_compl_eq htm c, intOp_sub]
    have hU : IsCompactOperator (intOp (indicatorConstLp 2 MeasurableSet.univ
        (measure_ne_top (μ.prod ν) Set.univ) c)) := by
      have := isCompactOperator_intOp_rect (μ := μ) (ν := ν) MeasurableSet.univ
        MeasurableSet.univ c
      simp only [Set.univ_prod_univ] at this
      exact this
    exact hU.sub ih
  | iUnion f hdisj hfm ih =>
    have hacc : ∀ n, MeasurableSet (accumulate f n) := fun n ↦ by
      rw [accumulate_def]; exact MeasurableSet.iUnion fun i ↦ MeasurableSet.iUnion fun _ ↦ hfm i
    -- compactness for the partial unions
    have hpart : ∀ n, IsCompactOperator
        (intOp (indicatorConstLp 2 (hacc n) (measure_ne_top (μ.prod ν) _) c)) := by
      intro n
      induction n with
      | zero =>
        have h0 : accumulate f 0 = f 0 := accumulate_zero_nat f
        have : indicatorConstLp 2 (hacc 0) (measure_ne_top (μ.prod ν) _) c =
            indicatorConstLp 2 (hfm 0) (measure_ne_top (μ.prod ν) _) c := by
          simp only [h0]
        rw [this]; exact ih 0
      | succ n ihn =>
        have hs : accumulate f (n + 1) = accumulate f n ∪ f (n + 1) := accumulate_succ f n
        have : indicatorConstLp 2 (hacc (n + 1)) (measure_ne_top (μ.prod ν) _) c =
            indicatorConstLp 2 (hacc n) (measure_ne_top (μ.prod ν) _) c +
              indicatorConstLp 2 (hfm (n + 1)) (measure_ne_top (μ.prod ν) _) c := by
          rw [← indicatorConstLp_disjoint_union (hacc n) (hfm (n + 1))
            (measure_ne_top (μ.prod ν) _) (measure_ne_top (μ.prod ν) _)
            (disjoint_accumulate hdisj (Nat.lt_succ_self n)) c]
          simp only [hs]
        rw [this, intOp_add]
        exact ihn.add (ih (n + 1))
    -- convergence of the partial unions in `L²`
    have hmeas : Tendsto (fun n ↦ (μ.prod ν) (accumulate f n ∆ ⋃ i, f i)) atTop (𝓝 0) := by
      have hsub : ∀ n, accumulate f n ⊆ ⋃ i, f i := fun n ↦ by
        rw [← iUnion_accumulate]; exact subset_iUnion (accumulate f) n
      have heq : ∀ n, (μ.prod ν) (accumulate f n ∆ ⋃ i, f i) =
          (μ.prod ν) (⋃ i, f i) - (μ.prod ν) (accumulate f n) := fun n ↦ by
        rw [symmDiff_of_le (hsub n), measure_sdiff (hsub n) (hacc n).nullMeasurableSet
          (measure_ne_top _ _)]
      simp_rw [heq]
      have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (μ.prod ν) (⋃ i, f i)))
        (tendsto_measure_iUnion_accumulate (μ := μ.prod ν) (f := f))
        (Or.inl (measure_ne_top _ _))
      simpa only [tsub_self] using this
    have hlim := tendsto_indicatorConstLp_set (p := 2) (c := c) (hs := MeasurableSet.iUnion hfm)
      (hμs := measure_ne_top (μ.prod ν) _) (ht := hacc) (hμt := fun n ↦ measure_ne_top _ _)
      ENNReal.ofNat_ne_top hmeas
    exact isCompactOperator_of_tendsto ((continuous_intOp).tendsto _ |>.comp hlim)
      (Eventually.of_forall hpart)

/-- **Compactness**: on finite measure spaces, an integral operator with an `L²` kernel is
compact. -/
theorem isCompactOperator_intOp (K : Lp 𝕜 2 (μ.prod ν)) : IsCompactOperator (intOp K) := by
  refine Lp.induction (p := 2) ENNReal.ofNat_ne_top
    (fun K : Lp 𝕜 2 (μ.prod ν) ↦ IsCompactOperator (intOp K)) ?_ ?_ ?_ K
  · intro c S hS _
    exact isCompactOperator_intOp_indicator c S hS
  · intro f g hf hg _ hf' hg'
    rw [intOp_add]; exact hf'.add hg'
  · have hc : IsClosed {T : Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 μ | IsCompactOperator T} :=
      isClosed_setOfPred_isCompactOperator
    exact hc.preimage continuous_intOp

end ArchS5
