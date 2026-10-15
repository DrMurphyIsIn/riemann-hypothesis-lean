import PFConverseD

/-!
# Registry-shape statement: the trivial converse of the RR-square chain (2026-10-14)

One root-namespace theorem whose statement is the registry statement of `MM_rr_windows_of_rh`
VERBATIM (fully qualified; the structure `RvMBridgePF.RRWindow` expanded into explicit data, the
same data and the same clauses, in the same order, as the hypotheses of `rr_windows_imply_rh` in
`RegRRChain.lean`), proved from `RvMBridgePF.rh_iff_exists_rr_windows` (`PFConverseD`):
* `rh_implies_rr_windows` : RiemannHypothesis => there is a family of RR-square windows covering
                            every pole-free Weil test.
Together with `rr_windows_imply_rh` (node `MM_rr_windows_imply_rh`) this is
"RH iff such windows exist".  THE TRIVIAL DIRECTION: the windows are read off from Weil positivity
(collapse model: V = Div = R, f = 0, h0 = 0), so the existence form is circular and the content of
Conjecture RR-square is a construction independent of the zeros.  Not progress on RH.
conjecture1_proved = False.
-/

open RvMBridgePF RvMBridgePF.RRSquare

/-- Registry shape of `MM_rr_windows_of_rh`. -/
theorem rh_implies_rr_windows (hRH : RiemannHypothesis) :
    ∃ (ι' : Type) (V Div : ι' → Type) (_ : ∀ i, AddCommGroup (V i)) (_ : ∀ i, Module ℝ (V i))
      (_ : ∀ i, AddCommGroup (Div i)) (_ : ∀ i, Module ℝ (Div i))
      (B : ∀ i, LinearMap.BilinForm ℝ (V i)) (f : ∀ i, V i) (ι : ∀ i, V i →ₗ[ℝ] Div i)
      (deg : ∀ i, Div i →ₗ[ℝ] ℝ) (Prin : ∀ i, Submodule ℝ (Div i)) (h0 h1 : ∀ i, Div i → ℝ)
      (K : ∀ i, Div i) (a : ∀ i, V i → ℝ) (χ : ι' → ℝ) (τ : ∀ i, V i → ℝ → ℂ) (c : ι' → ℝ),
      (∀ i v, deg i (ι i v) = B i v (f i)) ∧ (∀ i, ∀ X ∈ Prin i, deg i X = 0) ∧
      (∀ i X, 0 ≤ h0 i X) ∧ (∀ i X, 0 ≤ h1 i X) ∧
      (∀ i (v : V i) (n : ℕ), h0 i (ι i ((n : ℝ) • v)) - h1 i (ι i ((n : ℝ) • v)) + h0 i (K i - ι i ((n : ℝ) • v))
        = (1 / 2) * (n : ℝ) ^ 2 * B i v v - (1 / 2) * (n : ℝ) * a i v + χ i) ∧
      (∀ i X, 0 < h0 i X → ∃ E, X - E ∈ Prin i ∧ (0 < deg i E ∨ E ∈ Prin i)) ∧
      (∀ i v, ι i v ∈ Prin i → B i v v = 0) ∧
      (∀ i, (∃ β : ℝ → ℝ, ∀ X, h0 i X ≤ β (deg i X)) ∨ (∀ X Y, 0 < h0 i X → h0 i Y ≤ h0 i (X + Y))) ∧
      (∀ i, 0 < c i) ∧
      (∀ i v, B i v v = -(c i * (WeilExplicit.weilForm (WeilExplicit.autocorr (τ i v))).re)) ∧
      (∀ i v, Zeta23.paperFT (τ i v) (Complex.I / 2) = 0 → Zeta23.paperFT (τ i v) (-Complex.I / 2) = 0 →
        B i v (f i) = 0) ∧
      (∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g → Zeta23.paperFT g (Complex.I / 2) = 0 →
        Zeta23.paperFT g (-Complex.I / 2) = 0 → ∃ i, ∃ v : V i, τ i v = g) := by
  obtain ⟨ι', W, hcov⟩ := RvMBridgePF.rh_iff_exists_rr_windows.1 hRH
  let base : ∀ i, RRAxioms (W i).B (W i).f (W i).ι := fun i =>
    Sum.elim RRAxiomsBounded.toRRAxioms RRAxiomsDomain.toRRAxioms (W i).ax
  refine ⟨ι', fun i => (W i).V, fun i => (W i).Div, fun i => (W i).iV, fun i => (W i).mV,
    fun i => (W i).iD, fun i => (W i).mD, fun i => (W i).B, fun i => (W i).f, fun i => (W i).ι,
    fun i => (base i).deg, fun i => (base i).Prin, fun i => (base i).h0, fun i => (base i).h1,
    fun i => (base i).K, fun i => (base i).a, fun i => (base i).χ, fun i => (W i).τ, fun i => (W i).c,
    fun i => (base i).deg_ι, fun i => (base i).deg_prin, fun i => (base i).h0_nonneg,
    fun i => (base i).h1_nonneg, fun i => (base i).rr, fun i X hX => ?_, fun i => (base i).compat,
    fun i => ?_, fun i => (W i).hc, fun i => (W i).hdiag, fun i v h1 h2 => (W i).hpole v ⟨h1, h2⟩,
    fun g hg h1 h2 => hcov g hg ⟨h1, h2⟩⟩
  · obtain ⟨E, -, hE⟩ := (base i).eff X hX
    exact ⟨E, hE⟩
  · simp only [base]
    rcases (W i).ax with A | A
    · exact Or.inl ⟨A.β, A.bound⟩
    · exact Or.inr A.domain
