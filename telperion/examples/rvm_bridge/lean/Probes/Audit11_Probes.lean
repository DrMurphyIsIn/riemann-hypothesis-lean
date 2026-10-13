/- Audit probes for E6Bridge11 / E6Bridge13. -/
import E6Bridge13
open Zeta23 Complex MeasureTheory Filter Topology RvMBridge6 RvMBridge8 RvMBridge11 RvMBridge13 WeilExplicit

/- 1. lam₀ > 0 and the small-width region is nonempty (expected SUCCESS). -/
example : 0 < lam₀ := by unfold lam₀; norm_num
example : ∃ lam : ℝ, 0 < lam ∧ lam ≤ lam₀ := ⟨lam₀, by unfold lam₀; norm_num, le_rfl⟩

/- 2. c-uniformity: the theorem instantiates at negative, zero and huge centres (expected SUCCESS). -/
example (lam : ℝ) (h : 0 < lam) (h0 : lam ≤ lam₀) :
    0 ≤ (archSide (autocorr (gaussPhi (-123456789) lam)) - primeSide (autocorr (gaussPhi (-123456789) lam))).re :=
  re_weilForm_gauss_nonneg _ lam h h0
example (lam : ℝ) (h : 0 < lam) (h0 : lam ≤ lam₀) :
    0 ≤ (archSide (autocorr (gaussPhi 0 lam)) - primeSide (autocorr (gaussPhi 0 lam))).re :=
  re_weilForm_gauss_nonneg _ lam h h0

/- 3. The E6Bridge13 discharge is literally the seam A identity, and the wall map composes from the
   named inputs (expected SUCCESS). -/
example : RvMBridge11.GaussianExplicitFormula := fun c lam hlam => by
  rw [RvMBridge10.zeroSide_gaussTest_eq c lam hlam]
example : RiemannHypothesis ↔ ∀ (c lam : ℝ), lam₀ < lam → 0 ≤ (zeroSide (gaussTest c lam)).re := by
  constructor
  · intro hRH c lam hlam
    exact (RvMBridge10.rh_iff_gaussian_positivity.mp hRH) c lam (lt_trans (by unfold lam₀; norm_num) hlam)
  · intro h
    refine RvMBridge10.rh_iff_gaussian_positivity.mpr fun c lam hlam => ?_
    rcases le_or_gt lam lam₀ with hle | hgt
    · exact gaussian_positivity_small_lam_explicit c lam hlam hle
    · exact h c lam hgt

/- 4. The wall map's converse needs the hypothesis above lam₀: with it deleted (i.e. from the
   small-width theorem alone) RH does not follow (expected FAIL). -/
example : RiemannHypothesis := by
  refine RvMBridge10.rh_iff_gaussian_positivity.mpr fun c lam hlam => ?_
  rcases le_or_gt lam lam₀ with hle | hgt
  · exact gaussian_positivity_small_lam_explicit c lam hlam hle
  · exact gaussian_positivity_small_lam_explicit c lam hlam hgt.le

/- 5. Small-width positivity is not simp/positivity-trivial (expected FAIL). -/
example (c lam : ℝ) (hlam : 0 < lam) (hle : lam ≤ lam₀) :
    0 ≤ (zeroSide (gaussTest c lam)).re := by
  simp [zeroSide, gaussTest]
example (c lam : ℝ) (hlam : 0 < lam) (hle : lam ≤ lam₀) :
    0 ≤ (archSide (autocorr (gaussPhi c lam)) - primeSide (autocorr (gaussPhi c lam))).re := by
  positivity

/- 6. The threshold hypothesis is load-bearing in re_weilForm_gauss_nonneg: the numeric closing
   fails at lam = 1 (expected FAIL at the hσ step). -/
example (c : ℝ) :
    0 ≤ (archSide (autocorr (gaussPhi c 1)) - primeSide (autocorr (gaussPhi c 1))).re :=
  re_weilForm_gauss_nonneg c 1 one_pos (by unfold lam₀; norm_num)

/- 7. Consistency of the envelope with E6Bridge7's dominance: both are theorems; at a fixed lam an
   off-line zero forces negativity SOMEWHERE, and the envelope says positivity for |c| >= c₁(lam):
   no contradiction because dominance chooses lam after c (expected SUCCESS: both elaborate). -/
example (c lam : ℝ) (hlam : 0 < lam) (hc : envelopeC lam ≤ |c|) :
    0 ≤ (zeroSide (gaussTest c lam)).re := gaussian_positivity_envelope c lam hlam hc
example : RvMBridge6.GaussianDominance := RvMBridge7.gaussian_dominance
