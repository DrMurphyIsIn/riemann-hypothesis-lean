/-
  Hodge1_Reduction -- HODGE-1 Phase 1: the pole-free one-prime reduction (2026-10-12,
  HODGE-1 plan, unpublished, "Phase 1", step 1).

  For an IsWeilTest g with tsupport g ⊆ [-L, L], 2L <= log 3 and paperFT g (i/2) = 0:

      archW g - (log 2 / sqrt 2) ∫_S |g|^2  <=  Re weilForm (autocorr g),
      S = stripSet L = [-L, L - log 2] ∪ [log 2 - L, L],

  so Weil positivity on the pole-free one-prime window follows from the PRIME-FREE archimedean
  inequality (log 2 / sqrt 2) ∫_S |g|^2 <= archW g (step 2 of the plan, not proved here).

  Assembly (no numerics):
    Re weilForm (autocorr g) = Re archSide - Re primeSide                      (definition)
      = Re (H(0) + H(1)) + archW g - Re primeSide       (ArchS3.re_archSide_eq_poles_add_archW)
      = archW g - (log 2/sqrt 2) Re (f(log 2) + f(-log 2))  (RvMBridge31.poles_vanish; (b))
      >= archW g - (log 2/sqrt 2) ∫_S |g|^2                                     ((a))

  DEVIATIONS FROM THE PLAN'S HYPOTHESES (each makes the statement stronger, none weaker):
    * pole-free condition: ONE condition, paperFT g (I/2) = 0.  The two pole terms of the
      autocorrelation are H(0) = ĝ(i/2) conj ĝ(-i/2) and H(1) = ĝ(-i/2) conj ĝ(i/2)
      (RvMBridge31.poles_vanish), so ĝ(i/2) = 0 already kills both; the plan's second condition
      paperFT g (-I/2) = 0 is not needed (it is the condition used in E6Bridge31/ArchS3).
    * window: 2L <= log 3 (the plan has 2L < log 3; at 2L = log 3 the n = 3 atom sits on the
      boundary of supp f and vanishes by continuity).  L < log 2 is DERIVED (log 3 < log 4), and
      the lower end log 2 < 2L is NOT assumed: for 2L <= log 2 the strips are empty or a point
      and the bound degenerates to Re weilForm >= archW, consistent with ArchS3.re_weilForm_eq_archW.
    * normalisation: primeSide weights n by Λ(n)/sqrt n with Λ(2) = log 2, so w2 = log 2/sqrt 2,
      as in the plan.

  THE CLASS THE STRIP ROUTE NEEDS (added 2026-10-12 after the adversary's check): the theorems
  above are true on the one-condition class, but the prime-free inequality hArch FAILS there
  (-0.547 at L = 0.45: cross-sector g with ĝ_even(i/2) = -ĝ_odd(i/2) ≠ 0 are allowed).  Step 2
  is to be proved on the two-condition class
      PoleFree2 g :  paperFT g (I/2) = 0 ∧ paperFT g (-I/2) = 0,
  i.e. ∫ g e^{-u/2} = 0 and ∫ g e^{u/2} = 0 (paperFT g z = ∫ g(u) e^{i z u}; see
  paperFT_I_half, paperFT_neg_I_half), and weil_positivity_pole_free2_of_arch is the form a
  future discharge of hArch on that class plugs into.

  Nothing here involves the zeros; no RH progress is claimed.  conjecture1_proved = False.
-/
import Hodge1_Strip
import ArchS3_Delta

open Zeta23 Complex MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Hodge1
open WeilExplicit

/-- w2 = log 2 / sqrt 2 >= 0. -/
lemma w2_nonneg : 0 ≤ Real.log 2 / Real.sqrt 2 :=
  div_nonneg (Real.log_nonneg (by norm_num)) (Real.sqrt_nonneg 2)

/-- (c) + (b) assembled: on the pole-free one-prime window the Weil form is
archW g - w2 Re (f(log 2) + f(-log 2)). -/
theorem re_weilForm_eq_archW_sub_prime {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) (hL : 2 * L ≤ Real.log 3)
    (h0 : paperFT g (I / 2) = 0) :
    (weilForm (autocorr g)).re
      = ArchS3.archW g - (Real.log 2 / Real.sqrt 2)
          * (autocorr g (Real.log 2) + autocorr g (-Real.log 2)).re := by
  unfold weilForm
  obtain ⟨hz, ho⟩ := RvMBridge31.poles_vanish hg h0
  rw [Complex.sub_re, ArchS3.re_archSide_eq_poles_add_archW hg, hz, ho,
    primeSide_autocorr_eq_two hg hsupp hL, Complex.re_ofReal_mul]
  simp

/-- HEADLINE: archW g - (log 2/sqrt 2) ∫_S |g|^2 <= Re weilForm (autocorr g) on the pole-free
one-prime window. -/
theorem weilForm_ge_archW_sub_strip {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) (hL : 2 * L ≤ Real.log 3)
    (h0 : paperFT g (I / 2) = 0) :
    ArchS3.archW g - (Real.log 2 / Real.sqrt 2) * ∫ u in stripSet L, ‖g u‖ ^ 2
      ≤ (weilForm (autocorr g)).re := by
  rw [re_weilForm_eq_archW_sub_prime hg hsupp hL h0]
  have hs := re_autocorr_pair_le_stripEnergy hg hsupp (lt_log_two_of_le_log_three hL)
  unfold stripEnergy at hs
  linarith [mul_le_mul_of_nonneg_left hs w2_nonneg]

/-- COROLLARY: the prime-free archimedean inequality (log 2/sqrt 2) ∫_S |g|^2 <= archW g gives
Weil positivity on the pole-free one-prime window. -/
theorem weil_positivity_pole_free_of_arch {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) (hL : 2 * L ≤ Real.log 3)
    (h0 : paperFT g (I / 2) = 0)
    (hArch : (Real.log 2 / Real.sqrt 2) * ∫ u in stripSet L, ‖g u‖ ^ 2 ≤ ArchS3.archW g) :
    0 ≤ (weilForm (autocorr g)).re := by
  linarith [weilForm_ge_archW_sub_strip hg hsupp hL h0]

/-! ## The two-condition pole-free class (the class step 2 is proved on). -/

/-- H = {∫ g e^{u/2} = ∫ g e^{-u/2} = 0}: both pole functionals vanish. -/
def PoleFree2 (g : ℝ → ℂ) : Prop := paperFT g (I / 2) = 0 ∧ paperFT g (-I / 2) = 0

/-- paperFT g (i/2) = ∫ g(u) e^{-u/2} du. -/
lemma paperFT_I_half (g : ℝ → ℂ) :
    paperFT g (I / 2) = ∫ u : ℝ, g u * Complex.exp (-(u : ℂ) / 2) := by
  unfold paperFT
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  congr 2
  linear_combination ((u : ℂ) / 2) * I_sq

/-- paperFT g (-i/2) = ∫ g(u) e^{u/2} du. -/
lemma paperFT_neg_I_half (g : ℝ → ℂ) :
    paperFT g (-I / 2) = ∫ u : ℝ, g u * Complex.exp ((u : ℂ) / 2) := by
  unfold paperFT
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  congr 2
  linear_combination (-(u : ℂ) / 2) * I_sq

/-- COROLLARY on the two-condition class: hArch on PoleFree2 gives Weil positivity
(the extra condition h1 is not used by the reduction; it fixes the class hArch is proved on). -/
theorem weil_positivity_pole_free2_of_arch {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) (hL : 2 * L ≤ Real.log 3)
    (h0 : paperFT g (I / 2) = 0) (_h1 : paperFT g (-I / 2) = 0)
    (hArch : (Real.log 2 / Real.sqrt 2) * ∫ u in stripSet L, ‖g u‖ ^ 2 ≤ ArchS3.archW g) :
    0 ≤ (weilForm (autocorr g)).re :=
  weil_positivity_pole_free_of_arch hg hsupp hL h0 hArch

/-- The same corollary with the class as a predicate. -/
theorem weil_positivity_poleFree2_of_arch {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) (hL : 2 * L ≤ Real.log 3) (hP : PoleFree2 g)
    (hArch : (Real.log 2 / Real.sqrt 2) * ∫ u in stripSet L, ‖g u‖ ^ 2 ≤ ArchS3.archW g) :
    0 ≤ (weilForm (autocorr g)).re :=
  weil_positivity_pole_free2_of_arch hg hsupp hL hP.1 hP.2 hArch

end Hodge1
