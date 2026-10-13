/-
  ArchRegistry_CCCor23 -- the registry shape of Connes-Consani Corollary 2.3 for the mirrormere
  node MM_cc_cor_2_3 (2026-10-11).  The theorem below is CHARACTER FOR CHARACTER the registered
  statement (missions/mirrormere/lean/Statements/MM_cc_cor_2_3.lean), proved from
  ArchS3.cc_cor_2_3 (ArchS3_Limits.lean), where Lfun g is by definition archW g + Dfun g.

  Content: for EVERY Weil test g (smooth, compactly supported, any support width), the
  archimedean Weil functional W_inf(g * g^*) = (1/2pi) int |g^|^2 (psiR - log pi) plus CC's
  explicit delta-correction D(g * g^*) is >= 0.  Structural proof (manifest-positivity identity
  ell(t) = int_1^inf |Phi_t(a)|^2 da/a).  This is NOT Weil positivity (no prime side) and NOT RH.
  conjecture1_proved = False.
-/
import ArchS3_Limits

theorem cc_cor_2_3 (g : ℝ → ℂ) (hg : WeilExplicit.IsWeilTest g) :
    0 ≤ ArchS3.archW g + ArchS3.Dfun g :=
  ArchS3.cc_cor_2_3 hg
