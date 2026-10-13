/- telperion 0.1.6 | family WeilFormEnclosure | input-hash f8a5d61617bf7119
   3 theorems, 3 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import WeilFormDefs

namespace WeilFormEnclosure

open Complex

/-- Enclosure box consequence: a box with a positive lower end forces positivity.  Pure
real arithmetic -- the zeta content is entirely in what the caller instantiates. -/
theorem box_pos {x lo hi : ℝ} (h : lo ≤ x ∧ x ≤ hi) (hlo : 0 < lo) : 0 < x :=
  lt_of_lt_of_le hlo h.1

/-- Sylvester from three enclosure boxes: if the two diagonal boxes sit strictly above
zero and the worst-case determinant `lo_a * lo_b - max (c0^2) (c1^2)` is positive, then the
2x2 symmetric block `!![a, c; c, b]` has both leading principal minors positive, hence is
positive definite.  Pure real arithmetic. -/
theorem box_minor_pos {a b c a0 a1 b0 b1 c0 c1 : ℝ}
    (ha : a0 ≤ a ∧ a ≤ a1) (hb : b0 ≤ b ∧ b ≤ b1) (hc : c0 ≤ c ∧ c ≤ c1)
    (ha0 : 0 < a0) (hb0 : 0 < b0)
    (hdet : max (c0 * c0) (c1 * c1) < a0 * b0) :
    0 < a ∧ 0 < a * b - c ^ 2 := by
  obtain ⟨ha0', _⟩ := ha
  obtain ⟨hb0', _⟩ := hb
  obtain ⟨hc0', hc1'⟩ := hc
  have hapos : 0 < a := lt_of_lt_of_le ha0 ha0'
  have hbpos : 0 < b := lt_of_lt_of_le hb0 hb0'
  have hab : a0 * b0 ≤ a * b :=
    mul_le_mul ha0' hb0' (le_of_lt hb0) (le_of_lt hapos)
  have hcsq : c ^ 2 ≤ max (c0 * c0) (c1 * c1) := by
    rcases le_total 0 c with hcn | hcn
    · have : c ^ 2 ≤ c1 * c1 := by nlinarith
      exact this.trans (le_max_right _ _)
    · have : c ^ 2 ≤ c0 * c0 := by nlinarith
      exact this.trans (le_max_left _ _)
  exact ⟨hapos, by linarith⟩

/-- The falsifiability face of the Weil-form ladder.  A certified STRICTLY NEGATIVE
autocorrelation pairing refutes RH -- through the explicit, UNDISCHARGED hypothesis
`hpos`, the classical Weil direction (RH implies positivity of the form on
autocorrelations), which is NEVER proved here.  Not expected to fire; emitted so the
ladder is falsifiable rather than confirmation-only.  conjecture1_proved = False. -/
theorem weil_negative_refutes_rh (g : ℝ → ℂ) (_hg : WeilExplicit.IsWeilTest g)
    (hpos : RiemannHypothesis → 0 ≤ (WeilForm.weilForm (WeilForm.crossCorr g g)).re)
    (hneg : (WeilForm.weilForm (WeilForm.crossCorr g g)).re < 0) : ¬ RiemannHypothesis :=
  fun h => absurd (hpos h) (not_le.mpr hneg)

-- weil_autocorr_pos_bump_w1: the E8 Weil pairing of the autocorrelation of the test function 'bump_w1'
-- (smooth, compactly supported, support radius 2) is Arb-enclosed in
-- [7747363657/62500000000000, 126896128613/1000000000000000]; the kernel derives only the consequence 0 < weilForm.
-- Arb seam: archimedean quadrature to |r| <= 1024 with an 5-fold integration-by-parts tail.
-- This is what RH PREDICTS for an autocorrelation (Weil positivity); observing it confirms
-- NOTHING -- positivity over EVERY admissible test is RH-equivalent and no finite family
-- approaches that.  See weil_negative_refutes_rh for the falsifiable direction.  conjecture1_proved = False.
theorem weil_autocorr_pos_bump_w1 (g : ℝ → ℂ) (_hg : WeilExplicit.IsWeilTest g)
    (henc : ((7747363657 / 62500000000000) : ℝ) ≤ (WeilForm.weilForm (WeilForm.crossCorr g g)).re ∧ (WeilForm.weilForm (WeilForm.crossCorr g g)).re ≤ (126896128613 / 1000000000000000)) :
    0 < (WeilForm.weilForm (WeilForm.crossCorr g g)).re :=
  box_pos henc (by norm_num)

-- weil_autocorr_pos_bump_w3o2: the E8 Weil pairing of the autocorrelation of the test function 'bump_w3o2'
-- (smooth, compactly supported, support radius 3) is Arb-enclosed in
-- [126703996189/5000000000000000, 131057048217/5000000000000000]; the kernel derives only the consequence 0 < weilForm.
-- Arb seam: archimedean quadrature to |r| <= 1024 with an 5-fold integration-by-parts tail.
-- This is what RH PREDICTS for an autocorrelation (Weil positivity); observing it confirms
-- NOTHING -- positivity over EVERY admissible test is RH-equivalent and no finite family
-- approaches that.  See weil_negative_refutes_rh for the falsifiable direction.  conjecture1_proved = False.
theorem weil_autocorr_pos_bump_w3o2 (g : ℝ → ℂ) (_hg : WeilExplicit.IsWeilTest g)
    (henc : ((126703996189 / 5000000000000000) : ℝ) ≤ (WeilForm.weilForm (WeilForm.crossCorr g g)).re ∧ (WeilForm.weilForm (WeilForm.crossCorr g g)).re ≤ (131057048217 / 5000000000000000)) :
    0 < (WeilForm.weilForm (WeilForm.crossCorr g g)).re :=
  box_pos henc (by norm_num)

-- weil_gram_minor_0_1: the 2x2 Weil-Gram block of the test pair ('bump_w1', 'bump_w3o2').  Each
-- cross-correlation pairing is Arb-enclosed; the kernel derives Sylvester's two leading
-- principal minors, i.e. the block is POSITIVE DEFINITE.  Worst-case determinant over the
-- boxes: 61929633980856078265831/100000000000000000000000000000000 > 0.  Arb seam: |r| <= 1024, 5-fold by-parts tail; widths <= 1/100000.
-- Finite category-b: consistent with RH, PROVING NOTHING about it.  conjecture1_proved = False.
theorem weil_gram_minor_0_1 (g0 g1 : ℝ → ℂ)
    (_hg0 : WeilExplicit.IsWeilTest g0) (_hg1 : WeilExplicit.IsWeilTest g1)
    (h00 : ((7747363657 / 62500000000000) : ℝ) ≤ (WeilForm.weilForm (WeilForm.crossCorr g0 g0)).re ∧ (WeilForm.weilForm (WeilForm.crossCorr g0 g0)).re ≤ (126896128613 / 1000000000000000))
    (h11 : ((126703996189 / 5000000000000000) : ℝ) ≤ (WeilForm.weilForm (WeilForm.crossCorr g1 g1)).re ∧ (WeilForm.weilForm (WeilForm.crossCorr g1 g1)).re ≤ (131057048217 / 5000000000000000))
    (h01 : ((458109961271 / 10000000000000000) : ℝ) ≤ (WeilForm.weilForm (WeilForm.crossCorr g0 g1)).re ∧ (WeilForm.weilForm (WeilForm.crossCorr g0 g1)).re ≤ (502184612773 / 10000000000000000)) :
    0 < (WeilForm.weilForm (WeilForm.crossCorr g0 g0)).re ∧
      0 < (WeilForm.weilForm (WeilForm.crossCorr g0 g0)).re * (WeilForm.weilForm (WeilForm.crossCorr g1 g1)).re - (WeilForm.weilForm (WeilForm.crossCorr g0 g1)).re ^ 2 :=
  box_minor_pos h00 h11 h01 (by norm_num) (by norm_num) (by norm_num)

end WeilFormEnclosure
