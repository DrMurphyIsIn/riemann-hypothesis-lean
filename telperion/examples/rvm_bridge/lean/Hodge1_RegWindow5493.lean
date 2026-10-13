/-
  Hodge1_RegWindow5493 -- the registry shape of pole-free one-prime Weil positivity for L <= 5493/10000 for the mirrormere node MM_hodge1_window5493 (2026-10-13). The theorem
  below is CHARACTER FOR CHARACTER the registered statement
  (missions/mirrormere/lean/Statements/MM_hodge1_window5493.lean), stated in MMDefs vocabulary (fully qualified),
  and proved from Hodge1.weil_positivity_poleFree2_window5493 (Hodge1_Window5493.lean). Hodge1.PoleFree2 g unfolds to the two paperFT conditions below.
  HEAVY (imports the 5493 certificates): built in rvm-bridge-hodge1-heavy, not defaultTargets. conjecture1_proved = False.
-/
import Hodge1_Window5493

theorem weil_positivity_poleFree_window5493 (g : ℝ → ℂ) (hg : WeilExplicit.IsWeilTest g)
    (hP : Zeta23.paperFT g (Complex.I / 2) = 0 ∧ Zeta23.paperFT g (-Complex.I / 2) = 0) (L : ℝ) (hL : L ≤ 5493 / 10000) (hsupp : tsupport g ⊆ Set.Icc (-L) L) :
    0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re :=
  Hodge1.weil_positivity_poleFree2_window5493 g hg hP L hL hsupp
