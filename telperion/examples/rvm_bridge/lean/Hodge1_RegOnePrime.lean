/-
  Hodge1_RegOnePrime -- the registry shape of the exact one-prime Weil identity for the mirrormere node MM_hodge1_one_prime_identity (2026-10-13). The theorem
  below is CHARACTER FOR CHARACTER the registered statement
  (missions/mirrormere/lean/Statements/MM_hodge1_one_prime_identity.lean), stated in MMDefs vocabulary (fully qualified),
  and proved from Hodge1.re_weilForm_eq_archW_sub_prime (Hodge1_Reduction.lean). Hodge1.PoleFree2 g unfolds to the two paperFT conditions below.
  Light module. conjecture1_proved = False.
-/
import Hodge1_Reduction

theorem re_weilForm_eq_archW_sub_prime {g : ℝ → ℂ} (hg : WeilExplicit.IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) (hL : 2 * L ≤ Real.log 3)
    (h0 : Zeta23.paperFT g (Complex.I / 2) = 0) :
    (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re
      = ArchS3.archW g - (Real.log 2 / Real.sqrt 2)
          * (WeilExplicit.autocorr g (Real.log 2) + WeilExplicit.autocorr g (-Real.log 2)).re :=
  Hodge1.re_weilForm_eq_archW_sub_prime hg hsupp hL h0
