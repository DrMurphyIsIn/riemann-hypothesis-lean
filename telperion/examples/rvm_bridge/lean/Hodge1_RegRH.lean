/-
  Hodge1_RegRH -- the registry shape of RH iff pole-free Weil positivity outside the HODGE-1 window for the mirrormere node MM_hodge1_rh_reduction (2026-10-13). The theorem
  below is CHARACTER FOR CHARACTER the registered statement
  (missions/mirrormere/lean/Statements/MM_hodge1_rh_reduction.lean), stated in MMDefs vocabulary (fully qualified),
  and proved from Hodge1.rh_iff_poleFree2_outside_window5493 (Hodge1_RHReduction.lean). Hodge1.PoleFree2 g unfolds to the two paperFT conditions below.
  HEAVY (imports the 5493 certificates): built in rvm-bridge-hodge1-heavy, not defaultTargets. A reformulation, not progress on RH. conjecture1_proved = False.
-/
import Hodge1_RHReduction

theorem rh_iff_poleFree_outside_window5493 :
    RiemannHypothesis ↔
      ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g →
        (Zeta23.paperFT g (Complex.I / 2) = 0 ∧ Zeta23.paperFT g (-Complex.I / 2) = 0) →
        ¬ (tsupport g ⊆ Set.Icc (-(5493 / 10000 : ℝ)) (5493 / 10000)) →
        0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re :=
  Hodge1.rh_iff_poleFree2_outside_window5493
