import Mathlib.NumberTheory.LSeries.AbstractFuncEq

/-!
# Self-dual weak FE-pairs

For a `WeakFEPair` that is self-dual (`g = f`, `g₀ = f₀`, `ε = 1`), the reflected pair has the
same completed function `Λ`, so Mathlib's functional equation `Λ (k - s) = ε • symm.Λ s` reads
`Λ (k - s) = Λ s`.

Kept internally (2026-10-12): this was Mathlib PR #44807, closed at the owner's decision to keep
Mathlib-candidate work inside Arda. Fork branch DrMurphyIsIn/mathlib4 `weakfepair-selfdual`.
Intended consumer: completed zeta / Dedekind-zeta functional equations. Nothing here is progress on
RH. conjecture1_proved = False.
-/

namespace WeakFEPair

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (P : WeakFEPair E)

/-- For a self-dual pair (`g = f`, `g₀ = f₀`, `ε = 1`), the reflected pair has the same `Λ`. -/
lemma symm_Λ_eq_of_selfDual (hg : P.g = P.f) (hg₀ : P.g₀ = P.f₀) (hε : P.ε = 1) :
    P.symm.Λ = P.Λ := by
  unfold WeakFEPair.Λ WeakFEPair.Λ₀ WeakFEPair.f_modif
  simp only [WeakFEPair.symm, hg, hg₀, hε, inv_one]

/-- Functional equation for a self-dual pair (`g = f`, `g₀ = f₀`, `ε = 1`): `Λ (k - s) = Λ s`. -/
theorem functional_equation_of_selfDual (hg : P.g = P.f) (hg₀ : P.g₀ = P.f₀) (hε : P.ε = 1)
    (s : ℂ) : P.Λ (P.k - s) = P.Λ s := by
  rw [P.functional_equation s, P.symm_Λ_eq_of_selfDual hg hg₀ hε, hε, one_smul]

end WeakFEPair
