import Mathlib

/-!
# ArchS5_Rayleigh: the top of the spectrum via the Rayleigh quotient (stage S5)

For a bounded operator `T` on a real or complex inner product space `E`,

    topEig T := ⨆ x ≠ 0, re ⟪T x, x⟫ / ‖x‖²       (the Mathlib `rayleighQuotient` supremum).

* `topEig_eq_iSup_sphere` : `topEig T = ⨆ ‖x‖ = 1, re ⟪T x, x⟫`;
* `re_inner_le_topEig_mul` / `topEig_le_of_forall` / `le_topEig_of` : the variational bounds;
* `abs_topEig_sub_le` : **Weyl perturbation** `|topEig A - topEig B| ≤ ‖A - B‖` (no compactness or
  self-adjointness needed for the variational quantity);
* `norm_sq_apply_le_of_nonneg` : `‖S x‖² ≤ ‖S‖ re ⟪S x, x⟫` for symmetric `S ≥ 0`
  (generalised Cauchy-Schwarz);
* `exists_eigenvector_topEig` : for `T` symmetric and **compact** with `0 < topEig T`, the supremum
  is attained at a unit eigenvector: `T v = topEig T • v`.  (Mathlib only has the
  finite-dimensional version, `hasEigenvalue_iSup_of_finiteDimensional`.)

conjecture1_proved = False.
-/

open Filter Set Metric RCLike Topology
open scoped InnerProductSpace

noncomputable section

namespace ArchS5

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-! ### Two order lemmas for real suprema and infima -/

/-- Suprema of uniformly close bounded families are close (empty index allowed: both are `0`). -/
theorem abs_iSup_sub_iSup_le {ι : Sort*} {f g : ι → ℝ} {c : ℝ} (hf : BddAbove (range f))
    (hg : BddAbove (range g)) (h : ∀ i, |f i - g i| ≤ c) (hc : 0 ≤ c) :
    |(⨆ i, f i) - ⨆ i, g i| ≤ c := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [hc]
  rw [abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add]
    exact ciSup_le fun i ↦ by
      have := (abs_sub_le_iff.1 (h i)).1
      linarith [le_ciSup hg i]
  · rw [sub_le_iff_le_add]
    exact ciSup_le fun i ↦ by
      have := (abs_sub_le_iff.1 (h i)).2
      linarith [le_ciSup hf i]

/-- Infima of uniformly close bounded families are close (empty index allowed: both are `0`). -/
theorem abs_iInf_sub_iInf_le {ι : Sort*} {f g : ι → ℝ} {c : ℝ} (hf : BddBelow (range f))
    (hg : BddBelow (range g)) (h : ∀ i, |f i - g i| ≤ c) (hc : 0 ≤ c) :
    |(⨅ i, f i) - ⨅ i, g i| ≤ c := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [hc]
  have h1 : (⨅ i, f i) - c ≤ ⨅ i, g i := le_ciInf fun i ↦ by
    have := (abs_sub_le_iff.1 (h i)).1
    linarith [ciInf_le hf i]
  have h2 : (⨅ i, g i) - c ≤ ⨅ i, f i := le_ciInf fun i ↦ by
    have := (abs_sub_le_iff.1 (h i)).2
    linarith [ciInf_le hg i]
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-! ### The top of the numerical range -/

/-- The supremum of the Rayleigh quotient, `sup_{x ≠ 0} re ⟪T x, x⟫ / ‖x‖²` (`0` if `E = 0`).
For compact self-adjoint `T` with a positive value it is the largest eigenvalue
(`exists_eigenvector_topEig`). -/
def topEig (T : E →L[𝕜] E) : ℝ := ⨆ x : { x : E // x ≠ 0 }, T.rayleighQuotient x

theorem bddAbove_rayleighQuotient (T : E →L[𝕜] E) {ι : Sort*} (v : ι → E) :
    BddAbove (range fun i ↦ T.rayleighQuotient (v i)) :=
  ⟨‖T‖, by rintro _ ⟨i, rfl⟩; exact (le_abs_self _).trans (T.rayleighQuotient_le_norm _)⟩

theorem bddBelow_rayleighQuotient (T : E →L[𝕜] E) {ι : Sort*} (v : ι → E) :
    BddBelow (range fun i ↦ T.rayleighQuotient (v i)) :=
  ⟨-‖T‖, by rintro _ ⟨i, rfl⟩; exact neg_le_of_abs_le (T.rayleighQuotient_le_norm _)⟩

theorem rayleighQuotient_le_topEig (T : E →L[𝕜] E) {x : E} (hx : x ≠ 0) :
    T.rayleighQuotient x ≤ topEig T :=
  le_ciSup (f := fun x : { x : E // x ≠ 0 } ↦ T.rayleighQuotient x)
    (bddAbove_rayleighQuotient T _) ⟨x, hx⟩

/-- The variational upper bound `re ⟪T x, x⟫ ≤ topEig T · ‖x‖²`. -/
theorem re_inner_le_topEig_mul (T : E →L[𝕜] E) (x : E) :
    re ⟪T x, x⟫ ≤ topEig T * ‖x‖ ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hpos : 0 < ‖x‖ ^ 2 := by positivity
  have := rayleighQuotient_le_topEig T hx
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf,
    div_le_iff₀ hpos] at this
  exact this

theorem le_topEig_of (T : E →L[𝕜] E) {x : E} (hx : x ≠ 0) {c : ℝ}
    (h : c * ‖x‖ ^ 2 ≤ re ⟪T x, x⟫) : c ≤ topEig T := by
  refine le_trans ?_ (rayleighQuotient_le_topEig T hx)
  have hpos : 0 < ‖x‖ ^ 2 := by positivity
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf, le_div_iff₀ hpos]
  exact h

/-- Upper bound for `topEig` from a quadratic-form bound (on a nonzero space). -/
theorem topEig_le_of_forall [Nontrivial E] (T : E →L[𝕜] E) {c : ℝ}
    (h : ∀ x, re ⟪T x, x⟫ ≤ c * ‖x‖ ^ 2) : topEig T ≤ c := by
  have : Nonempty { x : E // x ≠ 0 } := let ⟨x, hx⟩ := exists_ne (0 : E); ⟨⟨x, hx⟩⟩
  refine ciSup_le fun x ↦ ?_
  have hpos : 0 < ‖(x : E)‖ ^ 2 := by have := x.2; positivity
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf, div_le_iff₀ hpos]
  exact h x

/-- Upper bound for `topEig` from a quadratic-form bound with a nonnegative constant. -/
theorem topEig_le_of_forall' (T : E →L[𝕜] E) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x, re ⟪T x, x⟫ ≤ c * ‖x‖ ^ 2) : topEig T ≤ c := by
  refine Real.iSup_le (fun x ↦ ?_) hc
  have hpos : 0 < ‖(x : E)‖ ^ 2 := by have := x.2; positivity
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf, div_le_iff₀ hpos]
  exact h x

/-- `topEig T` is the supremum of `re ⟪T x, x⟫` over the unit sphere. -/
theorem topEig_eq_iSup_sphere (T : E →L[𝕜] E) :
    topEig T = ⨆ x : sphere (0 : E) 1, re ⟪T x, x⟫ := by
  rw [topEig, T.iSup_rayleigh_eq_iSup_rayleigh_sphere one_pos]
  refine iSup_congr fun x ↦ ?_
  have : ‖(x : E)‖ = 1 := by simp
  simp [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf, this]

theorem abs_topEig_le_norm (T : E →L[𝕜] E) : |topEig T| ≤ ‖T‖ := by
  rcases isEmpty_or_nonempty { x : E // x ≠ 0 } with h | h
  · simp [topEig]
  rw [abs_le]
  constructor
  · obtain ⟨x⟩ := h
    exact (neg_le_of_abs_le (T.rayleighQuotient_le_norm x)).trans
      (rayleighQuotient_le_topEig T x.2)
  · exact ciSup_le fun x ↦ (le_abs_self _).trans (T.rayleighQuotient_le_norm _)

theorem rayleighQuotient_sub_le (A B : E →L[𝕜] E) (x : E) :
    |A.rayleighQuotient x - B.rayleighQuotient x| ≤ ‖A - B‖ := by
  have h := ContinuousLinearMap.rayleighQuotient_add B (A - B) (x := x)
  rw [add_sub_cancel] at h
  rw [h, add_sub_cancel_left]
  exact (A - B).rayleighQuotient_le_norm x

/-- **Weyl perturbation for the top eigenvalue**: `|λ_max(A) - λ_max(B)| ≤ ‖A - B‖`. -/
theorem abs_topEig_sub_le (A B : E →L[𝕜] E) : |topEig A - topEig B| ≤ ‖A - B‖ :=
  abs_iSup_sub_iSup_le (bddAbove_rayleighQuotient A _) (bddAbove_rayleighQuotient B _)
    (fun x ↦ rayleighQuotient_sub_le A B x) (norm_nonneg _)

theorem topEig_le_add_norm_sub (A B : E →L[𝕜] E) : topEig A ≤ topEig B + ‖A - B‖ := by
  have := (abs_sub_le_iff.1 (abs_topEig_sub_le A B)).1; linarith

/-- Monotonicity of `topEig` in the quadratic-form order. -/
theorem topEig_mono {A B : E →L[𝕜] E} (h : ∀ x, re ⟪A x, x⟫ ≤ re ⟪B x, x⟫) :
    topEig A ≤ topEig B := by
  rcases isEmpty_or_nonempty { x : E // x ≠ 0 } with hE | hE
  · simp [topEig]
  refine ciSup_le fun x ↦ (?_ : A.rayleighQuotient x ≤ _).trans (rayleighQuotient_le_topEig B x.2)
  simp only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf]
  exact div_le_div_of_nonneg_right (h x) (by positivity)

/-! ### Generalised Cauchy-Schwarz for nonnegative symmetric operators -/

/-- For symmetric `S` with `re ⟪S x, x⟫ ≥ 0`: `‖S x‖² ≤ ‖S‖ · re ⟪S x, x⟫`. -/
theorem norm_sq_apply_le_of_nonneg (S : E →L[𝕜] E) (hS : (S : E →ₗ[𝕜] E).IsSymmetric)
    (hpos : ∀ x, 0 ≤ re ⟪S x, x⟫) (x : E) : ‖S x‖ ^ 2 ≤ ‖S‖ * re ⟪S x, x⟫ := by
  have hsymm : ⟪S (S x), x⟫ = ⟪S x, S x⟫ := hS (S x) x
  have key : ∀ t : ℝ, 0 ≤ re ⟪S (S x), S x⟫ * (t * t) + (2 * ‖S x‖ ^ 2) * t + re ⟪S x, x⟫ := by
    intro t
    have h := hpos (x + (t : 𝕜) • S x)
    simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, hsymm, RCLike.conj_ofReal, mul_add, RCLike.re_ofReal_mul,
      inner_self_eq_norm_sq] at h
    nlinarith [h]
  have hd := discrim_le_zero key
  rw [discrim] at hd
  have hb : re ⟪S (S x), S x⟫ ≤ ‖S‖ * ‖S x‖ ^ 2 := by
    calc re ⟪S (S x), S x⟫ ≤ ‖S (S x)‖ * ‖S x‖ := re_inner_le_norm _ _
      _ ≤ ‖S‖ * ‖S x‖ * ‖S x‖ := by gcongr; exact S.le_opNorm _
      _ = ‖S‖ * ‖S x‖ ^ 2 := by ring
  have ha : 0 ≤ re ⟪S x, x⟫ := hpos x
  have hSn : 0 ≤ ‖S‖ := norm_nonneg _
  have h4 : ‖S x‖ ^ 2 * ‖S x‖ ^ 2 ≤ ‖S x‖ ^ 2 * (‖S‖ * re ⟪S x, x⟫) := by nlinarith
  rcases eq_or_lt_of_le (sq_nonneg ‖S x‖) with h0 | h0
  · rw [← h0]; positivity
  · exact le_of_mul_le_mul_left h4 h0

/-! ### Attainment for compact symmetric operators -/

/-- **Rayleigh characterisation of the top eigenvalue.**  If `T` is symmetric and compact and
`topEig T > 0`, then `topEig T` is an eigenvalue, attained at a unit eigenvector. -/
theorem exists_eigenvector_topEig (T : E →L[𝕜] E) (hT : (T : E →ₗ[𝕜] E).IsSymmetric)
    (hK : IsCompactOperator T) (hpos : 0 < topEig T) :
    ∃ v : E, ‖v‖ = 1 ∧ T v = (topEig T : 𝕜) • v := by
  set M := topEig T with hM
  -- the nonnegative symmetric operator `S = M - T`
  set S : E →L[𝕜] E := (M : 𝕜) • ContinuousLinearMap.id 𝕜 E - T with hSdef
  have hSapp : ∀ x, S x = (M : 𝕜) • x - T x := fun x ↦ rfl
  have hSsymm : (S : E →ₗ[𝕜] E).IsSymmetric := by
    intro x y
    simp only [ContinuousLinearMap.coe_coe, hSapp, inner_sub_left, inner_sub_right,
      inner_smul_left, inner_smul_right, RCLike.conj_ofReal]
    have := hT x y
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [this]
  have hSre : ∀ x, re ⟪S x, x⟫ = M * ‖x‖ ^ 2 - re ⟪T x, x⟫ := by
    intro x
    rw [hSapp, inner_sub_left, inner_smul_left, map_sub, RCLike.conj_ofReal,
      RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
  have hSpos : ∀ x, 0 ≤ re ⟪S x, x⟫ := fun x ↦ by
    rw [hSre]; linarith [re_inner_le_topEig_mul T x]
  -- E is nontrivial (otherwise `topEig T = 0`)
  have hne : Nonempty (sphere (0 : E) 1) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : topEig T = 0 := by rw [topEig_eq_iSup_sphere]; exact Real.iSup_of_isEmpty _
    linarith
  -- a maximising sequence on the unit sphere
  have hmax : ∀ n : ℕ, ∃ x : E, ‖x‖ = 1 ∧ M - 1 / (n + 1) < re ⟪T x, x⟫ := by
    intro n
    have hlt : M - 1 / (n + 1) < ⨆ x : sphere (0 : E) 1, re ⟪T x, x⟫ := by
      rw [← topEig_eq_iSup_sphere]; have : (0 : ℝ) < 1 / (n + 1) := by positivity
      linarith
    obtain ⟨x, hx⟩ := exists_lt_of_lt_ciSup hlt
    exact ⟨x, by simp, hx⟩
  choose x hx1 hx2 using hmax
  -- `S x_n → 0`
  have hSx : Tendsto (fun n ↦ S (x n)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : ∀ n, ‖S (x n)‖ ^ 2 ≤ ‖S‖ * (1 / ((n : ℝ) + 1)) := by
      intro n
      refine (norm_sq_apply_le_of_nonneg S hSsymm hSpos (x n)).trans ?_
      gcongr
      rw [hSre, hx1, one_pow, mul_one]
      linarith [hx2 n]
    have hlim : Tendsto (fun n : ℕ ↦ ‖S‖ * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ‖S‖
    have hsq : Tendsto (fun n ↦ ‖S (x n)‖ ^ 2) atTop (𝓝 0) :=
      squeeze_zero (fun n ↦ by positivity) hb hlim
    have := hsq.sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using this
  -- compactness: `T x_n` has a convergent subsequence
  have hcpt := hK.isCompact_closure_image_closedBall 1
  have hmem : ∀ n, T (x n) ∈ closure (T '' closedBall 0 1) := fun n ↦
    subset_closure ⟨x n, by simp [hx1 n], rfl⟩
  obtain ⟨y, -, φ, hφ, hTy⟩ := hcpt.tendsto_subseq hmem
  -- `x_{φ k} → v := M⁻¹ y`
  have hxeq : ∀ n, x n = ((M : 𝕜)⁻¹) • (T (x n) + S (x n)) := by
    intro n
    rw [hSapp, add_sub_cancel, smul_smul, inv_mul_cancel₀, one_smul]
    exact_mod_cast hpos.ne'
  have hxv : Tendsto (fun k ↦ x (φ k)) atTop (𝓝 (((M : 𝕜)⁻¹) • y)) := by
    have := (hTy.add (hSx.comp hφ.tendsto_atTop)).const_smul ((M : 𝕜)⁻¹)
    rw [add_zero] at this
    refine this.congr fun k ↦ ?_
    simp only [Function.comp_apply]
    exact (hxeq (φ k)).symm
  refine ⟨((M : 𝕜)⁻¹) • y, ?_, ?_⟩
  · have hn := hxv.norm
    have : Tendsto (fun k ↦ ‖x (φ k)‖) atTop (𝓝 1) := by simp [hx1]
    exact tendsto_nhds_unique hn this
  · have h1 : Tendsto (fun k ↦ S (x (φ k))) atTop (𝓝 (S (((M : 𝕜)⁻¹) • y))) :=
      (S.continuous.tendsto _).comp hxv
    have h2 : S (((M : 𝕜)⁻¹) • y) = 0 :=
      tendsto_nhds_unique h1 (hSx.comp hφ.tendsto_atTop)
    rw [hSapp, sub_eq_zero] at h2
    exact h2.symm

/-- Corollary: `topEig T` is an eigenvalue of a compact symmetric `T` when it is positive. -/
theorem hasEigenvalue_topEig (T : E →L[𝕜] E) (hT : (T : E →ₗ[𝕜] E).IsSymmetric)
    (hK : IsCompactOperator T) (hpos : 0 < topEig T) :
    Module.End.HasEigenvalue (T : E →ₗ[𝕜] E) (topEig T : 𝕜) := by
  obtain ⟨v, hv1, hv⟩ := exists_eigenvector_topEig T hT hK hpos
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv1
  exact Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hv, hv0⟩

/-- Corollary: the maximum of `re ⟪T x, x⟫` on the unit sphere is attained. -/
theorem exists_isMaxOn_sphere (T : E →L[𝕜] E) (hT : (T : E →ₗ[𝕜] E).IsSymmetric)
    (hK : IsCompactOperator T) (hpos : 0 < topEig T) :
    ∃ v : E, ‖v‖ = 1 ∧ re ⟪T v, v⟫ = topEig T := by
  obtain ⟨v, hv1, hv⟩ := exists_eigenvector_topEig T hT hK hpos
  refine ⟨v, hv1, ?_⟩
  rw [hv, inner_smul_left, RCLike.conj_ofReal, RCLike.re_ofReal_mul, inner_self_eq_norm_sq, hv1]
  ring

/-- Every eigenvalue of `T` is at most `topEig T`. -/
theorem eigenvalue_le_topEig (T : E →L[𝕜] E) {c : ℝ} {v : E} (hv : v ≠ 0)
    (h : T v = (c : 𝕜) • v) : c ≤ topEig T := by
  refine le_topEig_of T hv (le_of_eq ?_)
  rw [h, inner_smul_left, RCLike.conj_ofReal, RCLike.re_ofReal_mul, inner_self_eq_norm_sq]

end ArchS5
