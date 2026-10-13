import WeilFormDefs
import RRSquare

/-!
# Link: RR-square on a window delivers Weil positivity in Arda's own vocabulary

This module imports this island's `WeilFormDefs` (whose `WeilExplicit` block mirrors the registry's RHDefs, gated by
`generate.py --check`). Nothing is restated: the conclusion is about `WeilForm.weilForm (WeilForm.autocorr g)`, the
quadratic form of Weil's explicit formula.

A window RR-square is a real vector space `V` of test functions (`τ`), a bilinear form `B` whose diagonal is a negative
multiple of Weil's quadratic form (the dictionary sign: restricted Weil form = -ℓ × primitive Gram), and a degree class
`f` such that pole-free tests have degree 0. Given the bounded RR axioms on it, Weil positivity holds on every pole-free
test in the window. Over all windows that is Weil's criterion (Connes 1509.05576 (17); g6_transport Lemma A).

conjecture1_proved = False. Nothing here is progress on RH: the hypothesis `A` is the open content.
-/

namespace RRSquare

open WeilExplicit WeilForm

variable {V Div : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup Div] [Module ℝ Div]

/-- A test function is pole-free when both pole terms of the explicit formula vanish. -/
def PoleFree (g : ℝ → ℂ) : Prop := weilKernel g 0 = 0 ∧ weilKernel g 1 = 0

/-- **Weil positivity from RR-square.** -/
theorem weil_positive_of_rr {B : LinearMap.BilinForm ℝ V} {f : V} {ι : V →ₗ[ℝ] Div}
    (A : RRAxiomsBounded B f ι) (τ : V → (ℝ → ℂ)) (c : ℝ) (hc : 0 < c)
    (hdiag : ∀ v, B v v = -(c * (weilForm (autocorr (τ v))).re))
    (hpole : ∀ v, PoleFree (τ v) → B v f = 0) :
    ∀ v, PoleFree (τ v) → 0 ≤ (weilForm (autocorr (τ v))).re := by
  intro v hv
  have h := hodge_index A v (hpole v hv)
  rw [hdiag] at h
  by_contra hneg
  push_neg at hneg
  nlinarith

end RRSquare
