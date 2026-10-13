/-
  W2cAssembly -- the MIRRORMERE milestone MM_zeta_ordinates_not_uniformly_discrete
  (W2c, unconditional form), assembled on the rvm_bridge island (2026-09-18).

  WHAT THIS IS.  The registry node says: the set of ordinates (imaginary parts) of the
  nontrivial zeta zeros is NOT uniformly discrete -- there are pairs of distinct ordinates
  at arbitrarily small separation.  Its two registry dependencies are both proved, but on
  DIFFERENT toolchains:

    * MM_nt_brick_conditional -- the pigeonhole brick
        zeta_ordinates_not_uniformlyDiscrete_of_unbounded_density
      on the v4.32.0 quasicrystal island (telperion/examples/quasicrystal/lean/
      BoundaryLemmas.lean, branch rh/million-turing @ 0bac3e608, blob
      b019e8e9167d51504a8775e9006ec8fceb9255bd).  Mathlib-only, zeta-free.
    * MM_rvm_unbounded_mean_density -- RvMBridge.rvm_unbounded_mean_density on THIS
      island (E6Bridge.lean, Lean v4.33.0-rc2 / Mathlib 51e6992e), from Zeta23.thmA_0
      (Alpoege--Furman Theorem A) + the unconditional Riemann--von Mangoldt main clause.

  They cannot meet in one Lean environment, so the assembly happens here by RE-PROVING
  the brick VERBATIM (the four lemmas + two definitions below are line-for-line copies of
  the v4.32 artifact, source line ranges cited above each; the only edits are the
  namespace and the removal of docstrings).  The registry dependency MM_nt_brick_conditional
  is therefore satisfied by a verbatim re-proof on the rvm island, NOT by consuming the
  v4.32 olean.  The drift check examples/rvm_bridge/generate.py --check pins every ported
  statement to the v4.32 text so the re-proof cannot silently diverge from the artifact.

  The load-bearing analytic input remains Zeta23 Theorem A (via E6Bridge); everything
  in this file is elementary pigeonhole packing.

  Mirrored vocabulary: `IsUniformlyDiscrete` is a verbatim copy of
  telperion/missions/mirrormere/lean/Statements/MMDefs.lean:44-45 (BoundaryLemmas.lean:42-43);
  `RvMUnboundedMeanDensity` and `zetaOrdinates` come from E6Bridge (MMDefs.lean:48-55).
  The final theorem line is the node statement of
  telperion/missions/mirrormere/lean/Statements/MM_zeta_ordinates_not_uniformly_discrete.lean
  verbatim (name and binder-free form), so the registry's normalized-containment grant
  gate matches.

  No RH progress is claimed: "the zeta ordinates escape the crystalline class on the
  SPACE side" is a classical consequence of N(T)/T -> infinity, machine-checked.
  conjecture1_proved = False.
-/
import E6Bridge

namespace RvMBridge

-- ===== MIRROR of MMDefs.lean:44-45 (BoundaryLemmas.lean:42-43) =====
def IsUniformlyDiscrete (S : Set ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → δ ≤ |x - y|

-- ===== PORT of BoundaryLemmas.lean:170-175 (verbatim) =====
theorem not_uniformlyDiscrete_of_gaps_to_zero {S : Set ℝ}
    (hgap : ∀ δ : ℝ, 0 < δ → ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ |x - y| < δ) :
    ¬ IsUniformlyDiscrete S := by
  rintro ⟨δ, hδ, hsep⟩
  obtain ⟨x, hxS, y, hyS, hne, hlt⟩ := hgap δ hδ
  exact absurd (hsep hxS hyS hne) (not_le.mpr hlt)

-- ===== PORT of BoundaryLemmas.lean:183-221 (verbatim) =====
theorem exists_close_of_card_gt {F : Finset ℝ} {a L δ : ℝ}
    (hδ : 0 < δ) (hmem : ∀ x ∈ F, x ∈ Set.Icc a (a + L))
    (hcard : ⌊L / δ⌋₊ + 1 < F.card) :
    ∃ x ∈ F, ∃ y ∈ F, x ≠ y ∧ |x - y| < δ := by
  set B : ℕ := ⌊L / δ⌋₊ + 1 with hB
  let bin : ℝ → ℕ := fun x => ⌊(x - a) / δ⌋₊
  have hmaps : ∀ x ∈ F, bin x ∈ Finset.range B := by
    intro x hx
    obtain ⟨hxa, hxb⟩ := hmem x hx
    simp only [bin, Finset.mem_range, hB]
    -- (x - a)/δ ≤ L/δ, so ⌊(x-a)/δ⌋ ≤ ⌊L/δ⌋ < B
    have hle : (x - a) / δ ≤ L / δ := by
      gcongr
      linarith
    have := Nat.floor_le_floor hle
    omega
  have hlt : (Finset.range B).card < F.card := by simpa using hcard
  obtain ⟨x, hxF, y, hyF, hxy, hbeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  refine ⟨x, hxF, y, hyF, hxy, ?_⟩
  -- same floor bin ⇒ |(x-a)/δ - (y-a)/δ| < 1 ⇒ |x - y| < δ
  obtain ⟨hxa, _⟩ := hmem x hxF
  obtain ⟨hya, _⟩ := hmem y hyF
  have hxnn : 0 ≤ (x - a) / δ := div_nonneg (by linarith) hδ.le
  have hynn : 0 ≤ (y - a) / δ := div_nonneg (by linarith) hδ.le
  have hfeq : ⌊(x - a) / δ⌋₊ = ⌊(y - a) / δ⌋₊ := hbeq
  -- both reals lie in [⌊·⌋, ⌊·⌋+1), same floor ⇒ within 1
  have hxlo : (⌊(x - a) / δ⌋₊ : ℝ) ≤ (x - a) / δ := Nat.floor_le hxnn
  have hxhi : (x - a) / δ < ⌊(x - a) / δ⌋₊ + 1 := Nat.lt_floor_add_one _
  have hylo : (⌊(y - a) / δ⌋₊ : ℝ) ≤ (y - a) / δ := Nat.floor_le hynn
  have hyhi : (y - a) / δ < ⌊(y - a) / δ⌋₊ + 1 := Nat.lt_floor_add_one _
  rw [hfeq] at hxlo hxhi
  have hdiff : |(x - a) / δ - (y - a) / δ| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  have hxy_over : |(x - y) / δ| < 1 := by
    have : (x - a) / δ - (y - a) / δ = (x - y) / δ := by ring
    rwa [this] at hdiff
  rw [abs_div, abs_of_pos hδ, div_lt_one hδ] at hxy_over
  exact hxy_over

-- ===== PORT of BoundaryLemmas.lean:321-323 (verbatim) =====
def RvMWindowedDensity (S : Set ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ (F : Finset ℝ) (a L : ℝ),
    (↑F ⊆ S) ∧ (∀ x ∈ F, x ∈ Set.Icc a (a + L)) ∧ ⌊L / δ⌋₊ + 1 < F.card

-- ===== PORT of BoundaryLemmas.lean:350-360 (verbatim; RvMUnboundedMeanDensity is
-- E6Bridge's mirror of BoundaryLemmas.lean:342-344) =====
theorem windowedDensity_of_unboundedMeanDensity {S : Set ℝ}
    (h : RvMUnboundedMeanDensity S) : RvMWindowedDensity S := by
  intro δ hδ
  obtain ⟨F, a, L, hL0, hFsub, hmem, hcard⟩ := h (1 / δ) (by positivity)
  refine ⟨F, a, L, hFsub, hmem, ?_⟩
  have hfloor_le : (⌊L / δ⌋₊ : ℝ) ≤ (1 / δ) * L := by
    have hnn : 0 ≤ L / δ := div_nonneg hL0 hδ.le
    calc (⌊L / δ⌋₊ : ℝ) ≤ L / δ := Nat.floor_le hnn
      _ = (1 / δ) * L := by ring
  have : (↑(⌊L / δ⌋₊ + 1) : ℝ) < (F.card : ℝ) := by push_cast; linarith
  exact_mod_cast this

-- ===== PORT of BoundaryLemmas.lean:365-371 (verbatim) =====
theorem not_uniformlyDiscrete_of_windowedDensity {S : Set ℝ}
    (hRvM : RvMWindowedDensity S) : ¬ IsUniformlyDiscrete S := by
  apply not_uniformlyDiscrete_of_gaps_to_zero
  intro δ hδ
  obtain ⟨F, a, L, hFsub, hFmem, hFcard⟩ := hRvM δ hδ
  obtain ⟨x, hxF, y, hyF, hxy, hclose⟩ := exists_close_of_card_gt hδ hFmem hFcard
  exact ⟨x, hFsub hxF, y, hFsub hyF, hxy, hclose⟩

-- ===== PORT of BoundaryLemmas.lean:378-381 (verbatim): the conditional brick, i.e. the
-- content of the registry node MM_nt_brick_conditional, re-proved on this island =====
theorem zeta_ordinates_not_uniformlyDiscrete_of_unbounded_density
    {Ordinates : Set ℝ} (hRvM : RvMUnboundedMeanDensity Ordinates) :
    ¬ IsUniformlyDiscrete Ordinates :=
  not_uniformlyDiscrete_of_windowedDensity (windowedDensity_of_unboundedMeanDensity hRvM)

/-- The MIRRORMERE node statement, verbatim: the zeta ordinates are not uniformly
discrete, with no hypotheses.  Brick (above) applied to the E6 bridge's discharge of the
RvM residual (Zeta23 Theorem A + RvM main clause). -/
theorem zeta_ordinates_not_uniformly_discrete :
    ¬ IsUniformlyDiscrete zetaOrdinates :=
  zeta_ordinates_not_uniformlyDiscrete_of_unbounded_density rvm_unbounded_mean_density

end RvMBridge
