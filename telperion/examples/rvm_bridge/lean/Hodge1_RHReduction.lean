/-
  Hodge1_RHReduction -- the honest frontier after HODGE-1 (rvm_bridge island, 2026-10-13).

  `rh_iff_poleFree2_outside_window5493`: RiemannHypothesis holds iff Weil positivity holds for every
  pole-free (PoleFree2) Weil test whose support is NOT contained in [-5493/10000, 5493/10000].

  Both directions use real inputs:
  * (→) RvMBridge5.rh_implies_weil_positivity (the forward half of Weil's criterion);
  * (←) a case split on the support. Supports inside the window are handled by
    `Hodge1.weil_positivity_poleFree2_window5493` (the HODGE-1 1b-B certificate, p = 2 inside); the
    rest come from the hypothesis. Then `RvMBridgePF.weil_positivity_poleFree_implies_rh` (e9's
    pole-free converse) gives RH.

  The statement shape follows a correction from an independent session: quantifying over all supports wider than
  the window would make the window theorem unnecessary, since every compactly supported test fits in
  some wider window. Hodge1.PoleFree2 and RvMBridgePF.PoleFree are the same definition.

  This is a reformulation, not progress on RH: the right-hand side is the open content.
  conjecture1_proved = False.
-/
import Hodge1_Window5493
import PFConverseC

open Real MeasureTheory Set

namespace Hodge1

theorem poleFree2_iff_poleFree (g : ℝ → ℂ) : PoleFree2 g ↔ RvMBridgePF.PoleFree g := Iff.rfl

/-- **The frontier after HODGE-1.** RH is equivalent to pole-free Weil positivity for every test whose
    support is not contained in the HODGE-1 window [-5493/10000, 5493/10000]. -/
theorem rh_iff_poleFree2_outside_window5493 :
    RiemannHypothesis ↔
      ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g → PoleFree2 g →
        ¬ (tsupport g ⊆ Icc (-(5493 / 10000 : ℝ)) (5493 / 10000)) →
        0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re := by
  constructor
  · intro h g hg _ _
    exact RvMBridge5.rh_implies_weil_positivity h g hg
  · intro hout
    apply RvMBridgePF.weil_positivity_poleFree_implies_rh
    intro g hg hpf
    by_cases hs : tsupport g ⊆ Icc (-(5493 / 10000 : ℝ)) (5493 / 10000)
    · exact weil_positivity_poleFree2_window5493 g hg hpf (5493 / 10000) le_rfl hs
    · exact hout g hg hpf hs

end Hodge1
