/- Audit probe: each hypothesis of weil_positivity_implies_rh_of is load-bearing.
   Every example is EXPECTED TO FAIL at the step that consumed the deleted hypothesis. -/
import E6Bridge6
open Zeta23 Complex MeasureTheory Filter Topology RvMBridge6 WeilExplicit

/- 1. hpos deleted: hnn has nothing to feed it. -/
example (hO1 : GaussianTransfer) (hO2 : GaussianDominance) : RiemannHypothesis := by
  apply rh_of_all_on_line
  intro ρ₀ hρ₀
  by_contra hre
  obtain ⟨c, lam, hlam, hneg⟩ := hO2 ρ₀ hρ₀ hre
  obtain ⟨g, hg, hlim⟩ := hO1 c lam hlam
  have hnn : ∀ n, 0 ≤ (zeroSide (hermitianTransform (g n))).re := fun n => by
    rw [← weilForm_autocorr_eq_zeroSide (hg n)]
    positivity
  have hlim_nn : 0 ≤ (zeroSide (gaussTest c lam)).re := ge_of_tendsto' hlim hnn
  linarith

/- 2. hO2 deleted: no c, lam, no negative value; positivity + transfer alone say nothing. -/
example (hO1 : GaussianTransfer)
    (hpos : ∀ g : ℝ → ℂ, IsWeilTest g → 0 ≤ (weilForm (autocorr g)).re) : RiemannHypothesis := by
  apply rh_of_all_on_line
  intro ρ₀ hρ₀
  by_contra hre
  obtain ⟨g, hg, hlim⟩ := hO1 ρ₀.im 1 one_pos
  have hnn : ∀ n, 0 ≤ (zeroSide (hermitianTransform (g n))).re := fun n => by
    rw [← weilForm_autocorr_eq_zeroSide (hg n)]
    exact hpos _ (hg n)
  have hlim_nn : 0 ≤ (zeroSide (gaussTest ρ₀.im 1)).re := ge_of_tendsto' hlim hnn
  rw [gauss_zeroSide_pair_split 1 one_pos hre] at hlim_nn
  simp only [Complex.add_re, Complex.ofReal_re] at hlim_nn
  have := gaussTest_axis_re_neg ρ₀.im 1 (1 / 2 - ρ₀.re) (sub_ne_zero.mpr (Ne.symm hre))
  linarith

/- 3. hO1 deleted: positivity on IsWeilTest never reaches the Gaussian test. -/
example (hO2 : GaussianDominance)
    (hpos : ∀ g : ℝ → ℂ, IsWeilTest g → 0 ≤ (weilForm (autocorr g)).re) : RiemannHypothesis := by
  apply rh_of_all_on_line
  intro ρ₀ hρ₀
  by_contra hre
  obtain ⟨c, lam, hlam, hneg⟩ := hO2 ρ₀ hρ₀ hre
  have : 0 ≤ (zeroSide (gaussTest c lam)).re := by
    rw [← weilForm_autocorr_eq_zeroSide]
    exact hpos _ ‹_›
  linarith

/- 4. Automation on the whole reduced sentence without hpos (expected FAIL). -/
example (hO1 : GaussianTransfer) (hO2 : GaussianDominance) : RiemannHypothesis := by
  aesop
