/-
  Dogfood_enclosure_tree -- the Telperion `enclosure_tree` kind (SHAPES_AUDIT_48H_2026-09-22.md
  section 2 rank 1; A N2 / N3) regenerating LeakageDictionary.lean:276-359, 2026-09-22: the nine
  bracket lemmas `sqrt_five_bounds`, `sqrt_inner_bounds`, `dhKappa_gt`, `dhKappa_lt`,
  `dhKappa_bounds`, `log_three_halves_bounds`, `log_six_bounds`, `log_two_bounds`,
  `log_three_bounds`, as seven emitted theorems under NEW names (`qc_*`; the three `dhKappa`
  lemmas are one two-sided enclosure of the unfolded constant).  The emitted theorems chain like
  the hand proofs: `sqrt 5` is consumed by name by the inner radical and the DH quotient, `log 2`
  and `log (3/2)` by both folds.

  The block between the telperion provenance header and `end DogfoodEnclosureTreeQC` is the FROZEN
  emitter output (examples/li_positivity/dogfood_enclosure_tree.py regenerates it; a test pins the
  bytes).  The cross-checks after it prove every ORIGINAL statement from the regenerated theorems
  and every regenerated statement from the originals.  Nothing in LeakageDictionary is modified.

  Run: cd telperion/examples/quasicrystal/lean && lake env lean Probes/Dogfood_enclosure_tree.lean
  Expected axioms for every theorem: [propext, Classical.choice, Quot.sound].
  (The same seven theorems are compiled on the li_positivity island's Mathlib as the `qc_*`
  section of li_positivity/lean/Probes/Dogfood_enclosure_tree.lean.)

  conjecture1_proved = False.  Nothing here bears on RH: finite rational arithmetic facts about
  sqrt 5, the Davenport-Heilbronn constant and log 2, log 3, log 6, log (3/2).
-/
/- telperion 0.1.6 | family DogfoodEnclosureTreeQC | input-hash df3043ab97fdabd3
   7 theorems, 14 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import LeakageDictionary

namespace DogfoodEnclosureTreeQC

/-- `qc_sqrt_five_bounds` -- a certified RATIONAL ENCLOSURE of `Real.sqrt 5`.
    Route: Real.sq_sqrt + Real.sqrt_nonneg, nlinarith against two exact rational squares.
    Checked exactly against the radicand interval [5, 5] by rational squares (lo^2 vs 5, 5 vs hi^2).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem qc_sqrt_five_bounds :
    (1118033988749 / 500000000000 : ℝ) < Real.sqrt 5 ∧
      Real.sqrt 5 < (2236067977501 / 1000000000000 : ℝ) := by
  have harg : (0 : ℝ) ≤ 5 := by norm_num
  have h2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt harg
  have hn : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  constructor <;> nlinarith [h2, hn]

/-- `qc_sqrt_inner_bounds` -- a certified RATIONAL ENCLOSURE of `Real.sqrt (10 - 2 * Real.sqrt 5)`.
    Route: Real.sq_sqrt + Real.sqrt_nonneg, nlinarith against two exact rational squares.
    Checked exactly against the radicand interval [2763932022499/500000000000, 1381966011251/250000000000] by rational squares (lo^2 vs 2763932022499/500000000000, 1381966011251/250000000000 vs hi^2).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem qc_sqrt_inner_bounds :
    (1175570504583 / 500000000000 : ℝ) < Real.sqrt (10 - 2 * Real.sqrt 5) ∧
      Real.sqrt (10 - 2 * Real.sqrt 5) < (2351141009173 / 1000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := qc_sqrt_five_bounds
  have harg : (0 : ℝ) ≤ 10 - 2 * Real.sqrt 5 := by linarith
  have h2 : Real.sqrt (10 - 2 * Real.sqrt 5) ^ 2 = 10 - 2 * Real.sqrt 5 := Real.sq_sqrt harg
  have hn : (0 : ℝ) ≤ Real.sqrt (10 - 2 * Real.sqrt 5) := Real.sqrt_nonneg _
  constructor <;> nlinarith [h2, hn, h0lo, h0hi]

/-- `qc_dhKappa_bounds` -- a certified RATIONAL ENCLOSURE of `(Real.sqrt (10 - 2 * Real.sqrt 5) - 2) / (Real.sqrt 5 - 1)`.
    Route: le_div_iff0 / div_le_iff0 against a certified positive denominator.
    Exact fold [351141009166/1236067977501, 351141009173/1236067977498], inside the stated bracket with slack (3506706343459/1236067977501000000000, 666445326727/309016994374500000000).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem qc_dhKappa_bounds :
    (284079041 / 1000000000 : ℝ) < (Real.sqrt (10 - 2 * Real.sqrt 5) - 2) / (Real.sqrt 5 - 1) ∧
      (Real.sqrt (10 - 2 * Real.sqrt 5) - 2) / (Real.sqrt 5 - 1) < (142039523 / 500000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := qc_sqrt_inner_bounds
  obtain ⟨h1lo, h1hi⟩ := qc_sqrt_five_bounds
  have hden : (0 : ℝ) < Real.sqrt 5 - 1 := by linarith
  constructor
  · rw [lt_div_iff₀ hden]
    linarith
  · rw [div_lt_iff₀ hden]
    linarith

/-- `qc_log_three_halves_bounds` -- a certified RATIONAL ENCLOSURE of `Real.log (3 / 2)`.
    Route: the order-24 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [6070423640075591/14971509072199680, 6070425424818551/14971509072199680], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem qc_log_three_halves_bounds :
    (6070423640075591 / 14971509072199680 : ℝ) ≤ Real.log (3 / 2) ∧
      Real.log (3 / 2) ≤ (6070425424818551 / 14971509072199680 : ℝ) := by
  have hx : |((-(1 / 2)) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 24
  rw [show (1 : ℝ) - (-(1 / 2)) = (3 / 2) by norm_num] at h
  generalize Real.log (3 / 2) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `qc_log_two_bounds` -- a certified RATIONAL ENCLOSURE of `Real.log 2`.
    Route: Real.log_two_gt_d9 / Real.log_two_lt_d9.
    Exact fold [6931471803/10000000000, 108304247/156250000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem qc_log_two_bounds :
    (6931471803 / 10000000000 : ℝ) < Real.log 2 ∧ Real.log 2 < (108304247 / 156250000 : ℝ) := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  norm_num at h1 h2
  constructor <;> linarith

/-- `qc_log_six_bounds` -- a certified RATIONAL ENCLOSURE of `Real.log 6`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [52393246555737784416259/29241228656640000000000, 52393250070805106822899/29241228656640000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem qc_log_six_bounds :
    (52393246555737784416259 / 29241228656640000000000 : ℝ) < Real.log 6 ∧
      Real.log 6 < (52393250070805106822899 / 29241228656640000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := qc_log_two_bounds
  obtain ⟨h1lo, h1hi⟩ := qc_log_three_halves_bounds
  have hfold : Real.log 6 = Real.log 2 + Real.log 2 + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    rw [← Real.log_mul (by norm_num : (2 * 2 : ℝ) ≠ 0) (by norm_num : ((3 / 2) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

/-- `qc_log_three_bounds` -- a certified RATIONAL ENCLOSURE of `Real.log 3`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [32124771363880211544067/29241228656640000000000, 32124774864326919622387/29241228656640000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem qc_log_three_bounds :
    (32124771363880211544067 / 29241228656640000000000 : ℝ) < Real.log 3 ∧
      Real.log 3 < (32124774864326919622387 / 29241228656640000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := qc_log_two_bounds
  obtain ⟨h1lo, h1hi⟩ := qc_log_three_halves_bounds
  have hfold : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : ((3 / 2) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

end DogfoodEnclosureTreeQC

/-! ## Kernel cross-checks against the hand-written originals (generator-appended; the block above
    is the frozen emitter output).  Regenerated => original: every one of the nine ORIGINAL
    statements is proved from the emitted theorems (`dhKappa` unfolded; `linarith` absorbs the
    one literal the emitter writes in lowest terms, `6931471808 / 10000000000 = 108304247 / 156250000`).
    Original => regenerated: every emitted statement is proved from the originals. -/

section CrossChecks
open DogfoodEnclosureTreeQC

/-- regenerated `qc_sqrt_five_bounds` => original `Quasicrystal.sqrt_five_bounds`. -/
example :
    (1118033988749 / 500000000000 : ℝ) < Real.sqrt 5 ∧ Real.sqrt 5 < (2236067977501 / 1000000000000 : ℝ) := by
  have h := qc_sqrt_five_bounds
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- regenerated `qc_sqrt_inner_bounds` => original `Quasicrystal.sqrt_inner_bounds`. -/
example :
    (1175570504583 / 500000000000 : ℝ) < Real.sqrt (10 - 2 * Real.sqrt 5) ∧
    Real.sqrt (10 - 2 * Real.sqrt 5) < (2351141009173 / 1000000000000 : ℝ) := by
  have h := qc_sqrt_inner_bounds
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- regenerated `qc_dhKappa_bounds` => original `Quasicrystal.dhKappa_gt`. -/
example :
    (284079041 / 1000000000 : ℝ) < Quasicrystal.dhKappa := by
  have h := (qc_dhKappa_bounds).1
  unfold Quasicrystal.dhKappa
  linarith

/-- regenerated `qc_dhKappa_bounds` => original `Quasicrystal.dhKappa_lt`. -/
example :
    Quasicrystal.dhKappa < (142039523 / 500000000 : ℝ) := by
  have h := (qc_dhKappa_bounds).2
  unfold Quasicrystal.dhKappa
  linarith

/-- regenerated `qc_dhKappa_bounds` => original `Quasicrystal.dhKappa_bounds`. -/
example :
    (284079041 / 1000000000 : ℝ) < Quasicrystal.dhKappa ∧ Quasicrystal.dhKappa < (142039523 / 500000000 : ℝ) := by
  have h := qc_dhKappa_bounds
  unfold Quasicrystal.dhKappa
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- regenerated `qc_log_three_halves_bounds` => original `Quasicrystal.log_three_halves_bounds`. -/
example :
    (6070423640075591 / 14971509072199680 : ℝ) ≤ Real.log (3 / 2) ∧ Real.log (3 / 2) ≤ (6070425424818551 / 14971509072199680 : ℝ) := by
  have h := qc_log_three_halves_bounds
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- regenerated `qc_log_six_bounds` => original `Quasicrystal.log_six_bounds`. -/
example :
    (52393246555737784416259 / 29241228656640000000000 : ℝ) < Real.log 6 ∧ Real.log 6 < (52393250070805106822899 / 29241228656640000000000 : ℝ) := by
  have h := qc_log_six_bounds
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- regenerated `qc_log_two_bounds` => original `Quasicrystal.log_two_bounds`. -/
example :
    (6931471803 / 10000000000 : ℝ) < Real.log 2 ∧
    Real.log 2 < (6931471808 / 10000000000 : ℝ) := by
  have h := qc_log_two_bounds
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- regenerated `qc_log_three_bounds` => original `Quasicrystal.log_three_bounds`. -/
example :
    (32124771363880211544067 / 29241228656640000000000 : ℝ) < Real.log 3 ∧
    Real.log 3 < (32124774864326919622387 / 29241228656640000000000 : ℝ) := by
  have h := qc_log_three_bounds
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- original => regenerated, for each of the seven emitted statements. -/
example : type_of% qc_sqrt_five_bounds := by
  have h := Quasicrystal.sqrt_five_bounds
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

example : type_of% qc_sqrt_inner_bounds := by
  have h := Quasicrystal.sqrt_inner_bounds
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

example : type_of% qc_dhKappa_bounds := by
  have h := Quasicrystal.dhKappa_bounds
  unfold Quasicrystal.dhKappa at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

example : type_of% qc_log_three_halves_bounds := by
  have h := Quasicrystal.log_three_halves_bounds
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

example : type_of% qc_log_six_bounds := by
  have h := Quasicrystal.log_six_bounds
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

example : type_of% qc_log_two_bounds := by
  have h := Quasicrystal.log_two_bounds
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

example : type_of% qc_log_three_bounds := by
  have h := Quasicrystal.log_three_bounds
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

end CrossChecks

#print axioms DogfoodEnclosureTreeQC.qc_sqrt_five_bounds
#print axioms DogfoodEnclosureTreeQC.qc_sqrt_inner_bounds
#print axioms DogfoodEnclosureTreeQC.qc_dhKappa_bounds
#print axioms DogfoodEnclosureTreeQC.qc_log_three_halves_bounds
#print axioms DogfoodEnclosureTreeQC.qc_log_two_bounds
#print axioms DogfoodEnclosureTreeQC.qc_log_six_bounds
#print axioms DogfoodEnclosureTreeQC.qc_log_three_bounds
