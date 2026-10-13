/-
  Hodge1_RegWindow45 -- the registry shape of pole-free one-prime Weil positivity for L <= 9/20 for the mirrormere node MM_hodge1_window45 (2026-10-13). The theorem
  below is CHARACTER FOR CHARACTER the registered statement
  (missions/mirrormere/lean/Statements/MM_hodge1_window45.lean), stated in MMDefs vocabulary (fully qualified),
  and proved from Hodge1.weil_positivity_poleFree2_window45 (Hodge1_Window45.lean). Hodge1.PoleFree2 g unfolds to the two paperFT conditions below.
  HEAVY (imports the H45 certificates): built in rvm-bridge-hodge1-heavy, not defaultTargets. conjecture1_proved = False.
-/
import Hodge1_Window45

theorem weil_positivity_poleFree_window45 (g : ℝ → ℂ) (hg : WeilExplicit.IsWeilTest g)
    (hP : Zeta23.paperFT g (Complex.I / 2) = 0 ∧ Zeta23.paperFT g (-Complex.I / 2) = 0) (L : ℝ) (hL : L ≤ 9 / 20) (hsupp : tsupport g ⊆ Set.Icc (-L) L) :
    0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re :=
  Hodge1.weil_positivity_poleFree2_window45 g hg hP L hL hsupp
