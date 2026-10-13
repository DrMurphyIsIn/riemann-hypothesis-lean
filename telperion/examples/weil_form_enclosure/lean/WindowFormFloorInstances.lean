/- telperion 0.1.6 | family WindowFormFloorInstances | input-hash 721d3a001d42f4bf
   2 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import WeilFormDefs

namespace WindowFormFloorInstances

/-! ## Zhu's window-floor vocabulary (arXiv:2608.24827) and the rounding lemma.

`WindowFloor L lam` says the Weil pairing of every smooth compactly supported test function
supported in `[-L, L]` is at least `lam * ||f||_2^2`.  At a FIXED `L` with `lam > 0` this is
a finite fragment of RH (Weil 1952; Yoshida and Connes-Consani for `2L <= log 2`); the
RH-equivalent clause is `WindowFloor L 0` for EVERY L, and nothing here approaches it.
conjecture1_proved = False. -/

open MeasureTheory in
/-- The window floor predicate (Zhu eq. 1, written with the registry's E8 vocabulary). -/
def WindowFloor (L lam : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, WeilExplicit.IsWeilTest f →
    tsupport f ⊆ Set.Icc (-L) L →
    lam * (∫ x : ℝ, ‖f x‖ ^ 2) ≤
      (WeilForm.weilForm (WeilForm.autocorr f)).re

open MeasureTheory in
/-- Monotonicity of the floor: a window floor at `lam` gives one at any `mu ≤ lam`,
    since the L2 mass is non-negative.  This is exactly the rounding step in the last line
    of Zhu Thm 1.2 (raw `9e-18 - 4e-43 - 1e-100`, published `8.9e-18`). -/
theorem windowFloor_of_le {L lam mu : ℝ} (h : WindowFloor L lam) (hmu : mu ≤ lam) :
    WindowFloor L mu := by
  intro f hf hsupp
  refine le_trans ?_ (h f hf hsupp)
  have hnn : (0 : ℝ) ≤ ∫ x : ℝ, ‖f x‖ ^ 2 :=
    integral_nonneg fun x => by positivity
  exact mul_le_mul_of_nonneg_right hmu hnn

-- zhu_window_floor_L08_T150: Zhu arXiv:2608.24827 Thm 1.1 instantiated at L = 4/5 (autocorrelation support 8/5), T# = 150, N = 200 even Legendre modes.
-- FINITE constants, RE-DERIVED by the emitter and never trusted: comb mass A_L = 2.9419735 = sum_(log n < 2L) 2*Lambda(n)/sqrt(n) (a finite von Mangoldt sum); and
-- beta* = log(T#/2pi) - 1/T# - A_L = 0.224118 > 0, which is exactly the condition T# > T_1 = 2*pi*e^(A_L) = 119.087, the Thm 1.4 barrier threshold
-- (unimprovable within pointwise-envelope certificates by Lemma 3.2, sup_t P_L(t) = A_L exactly via Weyl equidistribution on (log p)).
-- TRUST SEAM, NON-KERNEL: lam0 = 1.2e-18 is an Arb / mpmath certified least-eigenvalue floor for the leading Legendre block; eps_d = 1e-100 (tail-block deviation) and
-- eps_b = 1e-100 (leading-tail coupling norm) are the super-exponentially small constants bounded in the proof.  The kernel asserts NONE of them.
-- They enter through hred, together with the four UNDISCHARGED analytic inputs of Thm 1.1: eq. (2) the frequency-side symbol representation, Lemma 3.1 the digamma envelope,
-- eqs. (6) and (12) the Legendre / spherical-Bessel localization, and the block floor itself.  What the kernel DOES prove is that the published rounding is sound.
-- Category-(b): finite, consistent with RH, PROVES NOTHING about RH.  The route is closed by Thm 1.4 at doubly exponential cost.  conjecture1_proved = False.
theorem zhu_window_floor_L08_T150
    (hred : WindowFloor ((4 / 5)) (min ((3 / 2500000000000000000)) (((112059 / 500000)) - ((1 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))) - ((1 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))) :
    WindowFloor ((4 / 5)) ((11 / 10000000000000000000)) :=
  windowFloor_of_le hred (by norm_num)

-- zhu_window_floor_L08_T200: Zhu arXiv:2608.24827 Thm 1.1 instantiated at L = 4/5 (autocorrelation support 8/5), T# = 200, N = 200 even Legendre modes.
-- FINITE constants, RE-DERIVED by the emitter and never trusted: comb mass A_L = 2.9419735 = sum_(log n < 2L) 2*Lambda(n)/sqrt(n) (a finite von Mangoldt sum); and
-- beta* = log(T#/2pi) - 1/T# - A_L = 0.5134667 > 0, which is exactly the condition T# > T_1 = 2*pi*e^(A_L) = 119.087, the Thm 1.4 barrier threshold
-- (unimprovable within pointwise-envelope certificates by Lemma 3.2, sup_t P_L(t) = A_L exactly via Weyl equidistribution on (log p)).
-- TRUST SEAM, NON-KERNEL: lam0 = 9e-18 is an Arb / mpmath certified least-eigenvalue floor for the leading Legendre block; eps_d = 1e-100 (tail-block deviation) and
-- eps_b = 1e-100 (leading-tail coupling norm) are the super-exponentially small constants bounded in the proof.  The kernel asserts NONE of them.
-- They enter through hred, together with the four UNDISCHARGED analytic inputs of Thm 1.1: eq. (2) the frequency-side symbol representation, Lemma 3.1 the digamma envelope,
-- eqs. (6) and (12) the Legendre / spherical-Bessel localization, and the block floor itself.  What the kernel DOES prove is that the published rounding is sound.
-- Category-(b): finite, consistent with RH, PROVES NOTHING about RH.  The route is closed by Thm 1.4 at doubly exponential cost.  conjecture1_proved = False.
theorem zhu_window_floor_L08_T200
    (hred : WindowFloor ((4 / 5)) (min ((9 / 1000000000000000000)) (((5134667 / 10000000)) - ((1 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))) - ((1 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))) :
    WindowFloor ((4 / 5)) ((89 / 10000000000000000000)) :=
  windowFloor_of_le hred (by norm_num)

end WindowFormFloorInstances
