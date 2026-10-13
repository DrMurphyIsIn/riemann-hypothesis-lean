/-  E6Bridge13 -- THE WALL MAP (2026-09-21, WALL ASSAULT assembly).

    Composes seam A (E6Bridge10: the Wall in two real parameters and the Gaussian explicit
    formula) with seam B (E6Bridge11: the small-width region is unconditional, with the absolute
    threshold lam₀ = 1e-7) to state the Wall as sharply as the campaign can certify it:

      RH  <->  Gaussian positivity on widths lam > lam₀ only.

    Below lam₀ positivity is a theorem (archimedean dominance: the prime side is exponentially
    small in 1/lam while the archimedean side is not).  Everything above lam₀ is the Wall.
    Seam C (E6Bridge12) certifies, from finite ladder data, the part |c| <= T - D of that
    residual for lam above an explicit threshold; the part |c| > T - D is RH.

    NOT a proof of RH: an equivalence says nothing about whether either side holds.
    conjecture1_proved = False. -/
import E6Bridge10
import E6Bridge11
import E6Bridge12

open WeilExplicit

namespace RvMBridge13

/-- Seam A's Gaussian explicit formula discharges seam B's one hypothesis. -/
theorem gaussianExplicitFormula : RvMBridge11.GaussianExplicitFormula := by
  intro c lam hlam
  rw [RvMBridge10.zeroSide_gaussTest_eq c lam hlam]

/-- The small-width region of the Wall, UNCONDITIONAL on the zero side: for every centre c and
every width 0 < lam <= lam₀ the Gaussian-weighted zero sum is nonnegative. -/
theorem gaussian_positivity_small_lam (c lam : ℝ) (hlam : 0 < lam)
    (hle : lam ≤ RvMBridge11.lam₀) :
    0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re :=
  RvMBridge11.gaussian_positivity_small_lam_explicit_of gaussianExplicitFormula c lam hlam hle

/-- THE WALL MAP: Mathlib's RiemannHypothesis is equivalent to Gaussian positivity on widths
strictly above lam₀.  The region lam <= lam₀ is free (gaussian_positivity_small_lam). -/
theorem rh_iff_gaussian_positivity_above_lam₀ :
    RiemannHypothesis ↔ ∀ (c lam : ℝ), RvMBridge11.lam₀ < lam →
      0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re := by
  constructor
  · intro hRH c lam hlam
    have h0 : (0 : ℝ) < RvMBridge11.lam₀ := by norm_num [RvMBridge11.lam₀]
    exact (RvMBridge10.rh_iff_gaussian_positivity.mp hRH) c lam (lt_trans h0 hlam)
  · intro h
    refine RvMBridge10.rh_iff_gaussian_positivity.mpr ?_
    intro c lam hlam
    rcases le_or_gt lam RvMBridge11.lam₀ with hle | hgt
    · exact gaussian_positivity_small_lam c lam hlam hle
    · exact h c lam hgt

end RvMBridge13
