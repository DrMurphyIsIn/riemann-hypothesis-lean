import ArchS5_Rayleigh

/-!
# ArchS5_MinMax: variational (Courant-Fischer) eigenvalues and Weyl perturbation (stage S5)

For a bounded operator `T` on an inner product space and `k ≥ 1`,

    minmaxEig T k := sup_{V, dim V = k}  inf_{0 ≠ x ∈ V}  re ⟪T x, x⟫ / ‖x‖².

* `abs_minmaxEig_sub_le` : **Weyl perturbation for every `k`**:
  `|minmaxEig A k - minmaxEig B k| ≤ ‖A - B‖` (no compactness or self-adjointness needed);
* `minmaxEig_one` : `minmaxEig T 1 = topEig T`;
* `le_minmaxEig` : a `k`-dimensional subspace on which the form is `≥ c ‖x‖²` gives
  `c ≤ minmaxEig T k`;
* `minmaxEig_le` : a `(k-1)`-dimensional subspace `U` with the form `≤ c ‖x‖²` on `Uᗮ` gives
  `minmaxEig T k ≤ c` (for `c ≥ 0`); this is the dimension-counting half of Courant-Fischer;
* `minmaxEig_eq_of_bounds` : the two together pin `minmaxEig T k` (the certificate pattern).

What is NOT proved here (open, see ARCH_S5_NOTES.md): that for a compact self-adjoint `T`,
`minmaxEig T k` equals the `k`-th largest positive eigenvalue counted with multiplicity
(this needs an ordered enumeration of the spectrum).  The two bounds above are what a certified
spectral computation actually consumes.

conjecture1_proved = False.
-/

open Filter Set Metric RCLike Module
open scoped InnerProductSpace

noncomputable section

namespace ArchS5

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- The infimum of the Rayleigh quotient of `T` over the nonzero vectors of `V` (`0` if `V = 0`). -/
def rayleighInf (T : E →L[𝕜] E) (V : Submodule 𝕜 E) : ℝ :=
  ⨅ x : { x : V // x ≠ 0 }, T.rayleighQuotient (x : E)

/-- The `k`-th variational (Courant-Fischer max-min) eigenvalue of `T`. -/
def minmaxEig (T : E →L[𝕜] E) (k : ℕ) : ℝ :=
  ⨆ V : { V : Submodule 𝕜 E // finrank 𝕜 V = k }, rayleighInf T V

theorem rayleighInf_le (T : E →L[𝕜] E) {V : Submodule 𝕜 E} {x : E} (hxV : x ∈ V) (hx : x ≠ 0) :
    rayleighInf T V ≤ T.rayleighQuotient x :=
  ciInf_le (f := fun x : { x : V // x ≠ 0 } ↦ T.rayleighQuotient (x : E))
    (bddBelow_rayleighQuotient T _) ⟨⟨x, hxV⟩, fun h ↦ hx (congrArg Subtype.val h)⟩

theorem abs_rayleighInf_le (T : E →L[𝕜] E) (V : Submodule 𝕜 E) : |rayleighInf T V| ≤ ‖T‖ := by
  rcases isEmpty_or_nonempty { x : V // x ≠ 0 } with h | h
  · simp [rayleighInf]
  rw [abs_le]
  constructor
  · exact le_ciInf fun _ ↦ neg_le_of_abs_le (T.rayleighQuotient_le_norm _)
  · obtain ⟨x⟩ := h
    exact (ciInf_le (bddBelow_rayleighQuotient T _) x).trans
      ((le_abs_self _).trans (T.rayleighQuotient_le_norm _))

theorem bddAbove_rayleighInf (T : E →L[𝕜] E) {ι : Sort*} (V : ι → Submodule 𝕜 E) :
    BddAbove (range fun i ↦ rayleighInf T (V i)) :=
  ⟨‖T‖, by rintro _ ⟨i, rfl⟩; exact (le_abs_self _).trans (abs_rayleighInf_le T _)⟩

theorem abs_rayleighInf_sub_le (A B : E →L[𝕜] E) (V : Submodule 𝕜 E) :
    |rayleighInf A V - rayleighInf B V| ≤ ‖A - B‖ :=
  abs_iInf_sub_iInf_le (bddBelow_rayleighQuotient A _) (bddBelow_rayleighQuotient B _)
    (fun _ ↦ rayleighQuotient_sub_le A B _) (norm_nonneg _)

/-- **Weyl perturbation for all variational eigenvalues**:
`|λ_k(A) - λ_k(B)| ≤ ‖A - B‖`. -/
theorem abs_minmaxEig_sub_le (A B : E →L[𝕜] E) (k : ℕ) :
    |minmaxEig A k - minmaxEig B k| ≤ ‖A - B‖ :=
  abs_iSup_sub_iSup_le (bddAbove_rayleighInf A _) (bddAbove_rayleighInf B _)
    (fun V ↦ abs_rayleighInf_sub_le A B V) (norm_nonneg _)

theorem minmaxEig_le_add_norm_sub (A B : E →L[𝕜] E) (k : ℕ) :
    minmaxEig A k ≤ minmaxEig B k + ‖A - B‖ := by
  have := (abs_sub_le_iff.1 (abs_minmaxEig_sub_le A B k)).1; linarith

theorem abs_minmaxEig_le_norm (T : E →L[𝕜] E) (k : ℕ) : |minmaxEig T k| ≤ ‖T‖ := by
  have := abs_minmaxEig_sub_le T 0 k
  have h0 : minmaxEig (0 : E →L[𝕜] E) k = 0 := by
    have : ∀ V : Submodule 𝕜 E, rayleighInf (0 : E →L[𝕜] E) V = 0 := fun V ↦ by
      simp [rayleighInf, ContinuousLinearMap.rayleighQuotient_zero_apply]
    simp [minmaxEig, this]
  rwa [h0, sub_zero, sub_zero] at this

/-! ### The two Courant-Fischer bounds -/

theorem exists_ne_zero_of_finrank_pos {V : Submodule 𝕜 E} (hV : 0 < finrank 𝕜 V) :
    ∃ x : E, x ∈ V ∧ x ≠ 0 := by
  have : Module.Finite 𝕜 V := Module.finite_of_finrank_pos hV
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hV
  exact ⟨x, x.2, fun h ↦ hx (Subtype.ext h)⟩

/-- **Lower bound**: a `k`-dimensional subspace `W` (`k ≥ 1`) on which
`re ⟪T x, x⟫ ≥ c ‖x‖²` gives `c ≤ minmaxEig T k`. -/
theorem le_minmaxEig (T : E →L[𝕜] E) {k : ℕ} (hk : 0 < k) (W : Submodule 𝕜 E)
    (hW : finrank 𝕜 W = k) {c : ℝ} (h : ∀ x ∈ W, c * ‖x‖ ^ 2 ≤ re ⟪T x, x⟫) :
    c ≤ minmaxEig T k := by
  obtain ⟨x0, hx0W, hx0⟩ := exists_ne_zero_of_finrank_pos (hW ▸ hk : 0 < finrank 𝕜 W)
  have : Nonempty { x : W // x ≠ 0 } :=
    ⟨⟨⟨x0, hx0W⟩, fun h ↦ hx0 (congrArg Subtype.val h)⟩⟩
  have hc : c ≤ rayleighInf T W := by
    refine le_ciInf fun x ↦ ?_
    have hx : ((x : W) : E) ≠ 0 := fun h ↦ x.2 (Subtype.ext h)
    have hpos : 0 < ‖((x : W) : E)‖ ^ 2 := by positivity
    rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf,
      le_div_iff₀ hpos]
    exact h _ (x : W).2
  exact hc.trans (le_ciSup (f := fun V : { V : Submodule 𝕜 E // finrank 𝕜 V = k } ↦
    rayleighInf T V) (bddAbove_rayleighInf T _) ⟨W, hW⟩)

/-- Dimension counting: a `k`-dimensional subspace meets the orthogonal complement of a
`(k-1)`-dimensional one nontrivially. -/
theorem exists_mem_orthogonal_of_finrank_lt {V U : Submodule 𝕜 E} [FiniteDimensional 𝕜 U]
    [U.HasOrthogonalProjection] (h : finrank 𝕜 U < finrank 𝕜 V) :
    ∃ x : E, x ∈ V ∧ x ∈ Uᗮ ∧ x ≠ 0 := by
  have : Module.Finite 𝕜 V := Module.finite_of_finrank_pos (lt_of_le_of_lt (Nat.zero_le _) h)
  let f : V →ₗ[𝕜] U := (U.orthogonalProjectionOnto : E →L[𝕜] U).toLinearMap ∘ₗ V.subtype
  obtain ⟨x, hxker, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt h
    (f := f))
  refine ⟨x, x.2, ?_, fun h ↦ hx0 (Subtype.ext h)⟩
  rw [LinearMap.mem_ker] at hxker
  exact Submodule.orthogonalProjectionOnto_eq_zero_iff.1 hxker

/-- **Upper bound** (the dimension-counting half of Courant-Fischer): if `U` has dimension
`k - 1` and `re ⟪T x, x⟫ ≤ c ‖x‖²` on `Uᗮ`, with `c ≥ 0`, then `minmaxEig T k ≤ c`. -/
theorem minmaxEig_le (T : E →L[𝕜] E) {k : ℕ} (U : Submodule 𝕜 E) [FiniteDimensional 𝕜 U]
    [U.HasOrthogonalProjection] (hU : finrank 𝕜 U + 1 = k) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x ∈ Uᗮ, re ⟪T x, x⟫ ≤ c * ‖x‖ ^ 2) : minmaxEig T k ≤ c := by
  refine Real.iSup_le (fun V ↦ ?_) hc
  obtain ⟨x, hxV, hxU, hx0⟩ := exists_mem_orthogonal_of_finrank_lt (V := (V : Submodule 𝕜 E))
    (U := U) (by rw [V.2]; omega)
  refine (rayleighInf_le T hxV hx0).trans ?_
  have hpos : 0 < ‖x‖ ^ 2 := by positivity
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf, div_le_iff₀ hpos]
  exact h x hxU

/-- The certificate pattern: matching lower and upper bounds pin the `k`-th variational
eigenvalue. -/
theorem minmaxEig_eq_of_bounds (T : E →L[𝕜] E) {k : ℕ} (hk : 0 < k) (W U : Submodule 𝕜 E)
    [FiniteDimensional 𝕜 U] [U.HasOrthogonalProjection] (hW : finrank 𝕜 W = k)
    (hU : finrank 𝕜 U + 1 = k) {c : ℝ} (hc : 0 ≤ c)
    (hlo : ∀ x ∈ W, c * ‖x‖ ^ 2 ≤ re ⟪T x, x⟫) (hhi : ∀ x ∈ Uᗮ, re ⟪T x, x⟫ ≤ c * ‖x‖ ^ 2) :
    minmaxEig T k = c :=
  le_antisymm (minmaxEig_le T U hU hc hhi) (le_minmaxEig T hk W hW hlo)

/-! ### `k = 1` is the top eigenvalue -/

theorem rayleighInf_span_singleton (T : E →L[𝕜] E) {x : E} (hx : x ≠ 0) :
    rayleighInf T (𝕜 ∙ x) = T.rayleighQuotient x := by
  have : Nonempty { z : (𝕜 ∙ x) // z ≠ 0 } :=
    ⟨⟨⟨x, Submodule.mem_span_singleton_self x⟩, fun h ↦ hx (congrArg Subtype.val h)⟩⟩
  refine le_antisymm (rayleighInf_le T (Submodule.mem_span_singleton_self x) hx)
    (le_ciInf fun z ↦ le_of_eq ?_)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (z : (𝕜 ∙ x)).2
  have hz : ((z : (𝕜 ∙ x)) : E) ≠ 0 := fun h ↦ z.2 (Subtype.ext h)
  have ha0 : a ≠ 0 := by rintro rfl; rw [zero_smul] at ha; exact hz ha.symm
  rw [← ha, ContinuousLinearMap.rayleigh_smul T x ha0]

/-- `minmaxEig T 1 = topEig T`. -/
theorem minmaxEig_one (T : E →L[𝕜] E) : minmaxEig T 1 = topEig T := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have h1 : IsEmpty { V : Submodule 𝕜 E // finrank 𝕜 V = 1 } := by
      constructor
      rintro ⟨V, hV⟩
      obtain ⟨x, -, hx⟩ := exists_ne_zero_of_finrank_pos (V := V) (by omega)
      exact hx (Subsingleton.elim _ _)
    have h2 : IsEmpty { x : E // x ≠ 0 } := ⟨fun x ↦ x.2 (Subsingleton.elim _ _)⟩
    simp [minmaxEig, topEig]
  obtain ⟨x0, hx0⟩ := exists_ne (0 : E)
  have : Nonempty { V : Submodule 𝕜 E // finrank 𝕜 V = 1 } := ⟨⟨_, finrank_span_singleton hx0⟩⟩
  have : Nonempty { x : E // x ≠ 0 } := ⟨⟨x0, hx0⟩⟩
  refine le_antisymm (ciSup_le fun V ↦ ?_) (ciSup_le fun x ↦ ?_)
  · obtain ⟨x, hxV, hx⟩ := exists_ne_zero_of_finrank_pos (V := (V : Submodule 𝕜 E))
      (by rw [V.2]; omega)
    exact (rayleighInf_le T hxV hx).trans (rayleighQuotient_le_topEig T hx)
  · rw [← rayleighInf_span_singleton T x.2]
    exact le_ciSup (f := fun V : { V : Submodule 𝕜 E // finrank 𝕜 V = 1 } ↦ rayleighInf T V)
      (bddAbove_rayleighInf T _) ⟨_, finrank_span_singleton x.2⟩

end ArchS5
