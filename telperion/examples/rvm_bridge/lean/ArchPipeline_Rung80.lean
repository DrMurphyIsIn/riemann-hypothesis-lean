/-
  ArchPipeline_Rung80 -- first end-to-end CONCEPTUAL rung of the archimedean Connes-Consani programme.

  Composes stage S3 (`ArchS3.ell_nonneg`, CC Cor 2.3 by a structural proof: ell(t) = ∫₁^∞ |Φ_t(a)|² da/a)
  with stage S4's bridge (`ArchS4.weil_nonneg_of_ell_nonneg`, the jump lemma D∘Q = -2 Id + K^δ and a sup bound
  on K^δ).  Result: Weil positivity on the pole-free class for supports of half-width L ≤ 1/80.

  This is a PIPELINE TEST.  The statement is far weaker than what is already kernel-proved on main
  (`KWin_Bridge.weil_positivity_prime_free_window`: full IsWeilTest class, pole terms kept, 2L ≤ log 2).
  Its value is that every step is structural (no certificate), assembled from S1, S2, S3, S4.
  conjecture1_proved = False.  Nothing here is RH progress.
-/
import ArchS4_Bridge
import ArchS3_Limits

open Zeta23 MeasureTheory Set Complex
open scoped ComplexConjugate

namespace ArchPipeline
open WeilExplicit RvMBridge31

theorem weil_nonneg_pole_free_eightieth {g : ℝ → ℂ} (hg : IsWeilTest g)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : L ≤ 1 / 80) (hsupp : tsupport g ⊆ Icc (-L) L)
    (h0 : paperFT g (I / 2) = 0) :
    0 ≤ (weilForm (autocorr g)).re :=
  ArchS4.weil_nonneg_of_ell_nonneg ArchS3.ell_nonneg hg hL0 hL hsupp h0

end ArchPipeline
