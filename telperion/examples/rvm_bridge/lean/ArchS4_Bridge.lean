/-
  ArchS4_Bridge -- identifies stage S3's delta (ArchS3_Delta) with stage S4's (ArchS4_Delta) and
  restates the S4' delta rung with exactly the hypothesis S3 will produce.

    ccS_eq_sincInt      : ccS a = ArchS3.sincInt a        (Fubini: ∫_0^1 cos(a s r) dr = sinc(a s))
    deltaK_eq_deltaE    : ArchS3.deltaK u = deltaE |u|
    S3_Dfun_eq          : ArchS3.Dfun g = (ArchS4.Dfun (autocorr g)).re
    S3_Dfun_nonpos_poleFree : ArchS3.Dfun g ≤ 0 on the pole-free window L ≤ 1/80
    weil_nonneg_of_Lfun_nonneg : 0 ≤ ArchS3.Lfun g ⇒ 0 ≤ Re weilForm (autocorr g)  (window ≤ 1/80)
    weil_nonneg_of_ell_nonneg  : (∀ r, 0 ≤ ArchS3.ell r) ⇒ the same               (one application
                                 of S3's M3 makes the rung unconditional)
  conjecture1_proved = False.  Nothing here is RH progress.
-/
import ArchS4_Rung
import ArchS3_Delta

open Zeta23 MeasureTheory Set Complex
open scoped ComplexConjugate

noncomputable section

namespace ArchS4
open WeilExplicit RvMBridge31

/-- **The two S's agree**: ∫∫_{[0,1]²} cos(a s r) = ∫_0^1 sinc(a s) ds. -/
theorem ccS_eq_sincInt (a : ℝ) : ccS a = ArchS3.sincInt a := by
  have hint : Integrable (fun p : ℝ × ℝ => Real.cos (a * (p.1 * p.2))) sq := by
    simpa using integrable_momIntegrand Real.continuous_cos Real.abs_cos_le_one 0 a
  unfold ccS Cm mom ArchS3.sincInt
  simp only [pow_zero, one_mul]
  unfold sq
  rw [integral_prod _ (by simpa [sq] using hint), integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  simp only
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    ← integral_cos_mul_eq_sinc]
  refine intervalIntegral.integral_congr (fun r _ => ?_)
  simp only [mul_assoc]

/-- **The two deltas agree**: S3's deltaK u = S4's deltaE |u|. -/
theorem deltaK_eq_deltaE (u : ℝ) : ArchS3.deltaK u = deltaE |u| := by
  unfold ArchS3.deltaK deltaE
  rw [ccS_eq_sincInt, ccS_eq_sincInt, add_comm (1 : ℝ) (Real.exp |u|)]

/-- **The two D's agree**: S3's Dfun g is the real part of S4's D on autocorr g. -/
theorem S3_Dfun_eq (g : ℝ → ℂ) : ArchS3.Dfun g = (Dfun (autocorr g)).re := by
  unfold ArchS3.Dfun Dfun
  simp_rw [deltaK_eq_deltaE]

/-- S4' in S3's vocabulary: D∘Q ≤ 0 on the pole-free window L ≤ 1/80. -/
theorem S3_Dfun_nonpos_poleFree {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : L ≤ 1 / 80) (hsupp : tsupport g ⊆ Icc (-L) L) (h0 : paperFT g (I / 2) = 0) :
    ArchS3.Dfun g ≤ 0 := by
  rw [S3_Dfun_eq]
  exact DQ_nonpos_poleFree hg hL0 hL hsupp h0

/-- **The delta rung with S3's hypothesis**: L(g) = W∞(g) + D(g) ≥ 0 gives Weil positivity on
    the pole-free window L ≤ 1/80. -/
theorem weil_nonneg_of_Lfun_nonneg {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : L ≤ 1 / 80) (hsupp : tsupport g ⊆ Icc (-L) L) (h0 : paperFT g (I / 2) = 0)
    (hLf : 0 ≤ ArchS3.Lfun g) :
    0 ≤ (weilForm (autocorr g)).re := by
  have hlog : 2 * L ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  rw [ArchS3.re_weilForm_eq_archW hg hsupp hlog h0]
  unfold ArchS3.Lfun at hLf
  linarith [S3_Dfun_nonpos_poleFree hg hL0 hL hsupp h0]

/-- **The delta rung with CC Cor 2.3 (ii)**: pointwise ell ≥ 0 (S3's M3 target) gives Weil
    positivity on the pole-free window L ≤ 1/80. -/
theorem weil_nonneg_of_ell_nonneg (hell : ∀ r, 0 ≤ ArchS3.ell r) {g : ℝ → ℂ} (hg : IsWeilTest g)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : L ≤ 1 / 80) (hsupp : tsupport g ⊆ Icc (-L) L)
    (h0 : paperFT g (I / 2) = 0) :
    0 ≤ (weilForm (autocorr g)).re :=
  weil_nonneg_of_Lfun_nonneg hg hL0 hL hsupp h0 (ArchS3.Lfun_nonneg_of_ell_nonneg hell hg)

end ArchS4
