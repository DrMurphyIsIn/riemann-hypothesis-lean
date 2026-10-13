/- Audit probe: are the obligations honest?  Automation attempts are EXPECTED TO FAIL;
   the RH-vacuity of O2 is EXPECTED TO SUCCEED. -/
import E6Bridge6
open Zeta23 Complex MeasureTheory Filter Topology RvMBridge6 WeilExplicit
open scoped ComplexConjugate

/- 1. O2 is vacuous under RH (expected SUCCESS; this is the documented fact, not a defect). -/
theorem audit_O2_of_rh (hRH : RiemannHypothesis) : GaussianDominance := by
  intro ρ₀ h₀ hre
  exact absurd (Zeta23.RH_implies_on_line hRH h₀) hre
#print axioms audit_O2_of_rh

/- 2. O2 by automation with no hypothesis (expected FAIL). -/
example : GaussianDominance := by
  unfold GaussianDominance
  intro ρ₀ h₀ hre
  refine ⟨ρ₀.im, 1, one_pos, ?_⟩
  simp [zeroSide, gaussTest]

example : GaussianDominance := by
  unfold GaussianDominance zeroSide gaussTest
  aesop

/- 3. O2 with the pair split: the pair term is negative but the remainder is unconstrained
   (expected FAIL: the remainder tsum cannot be bounded without analysis). -/
example : GaussianDominance := by
  intro ρ₀ h₀ hre
  refine ⟨ρ₀.im, 1, one_pos, ?_⟩
  rw [gauss_zeroSide_pair_split 1 one_pos hre]
  simp only [Complex.add_re, Complex.ofReal_re]
  have := gaussTest_axis_re_neg ρ₀.im 1 (1 / 2 - ρ₀.re) (sub_ne_zero.mpr (Ne.symm hre))
  positivity

/- 4. O2 from a huge lam alone (expected FAIL: on-line zeros contribute >= 0 for every lam). -/
example (c : ℝ) : ∃ lam : ℝ, 0 < lam ∧ (zeroSide (gaussTest c lam)).re < 0 := by
  refine ⟨1000, by norm_num, ?_⟩
  simp [zeroSide, gaussTest]

/- 5. O2 does NOT imply RH on its own (the converse needs hpos); expected FAIL. -/
example (hO2 : GaussianDominance) : RiemannHypothesis := by
  apply rh_of_all_on_line
  intro ρ hρ
  by_contra hre
  obtain ⟨c, lam, hlam, hneg⟩ := hO2 ρ hρ hre
  exact absurd hneg (not_lt.mpr (by positivity))

/- 6. O1 / O1' by automation (expected FAIL): a constant sequence is not a witness. -/
example : GaussianTransfer := by
  intro c lam hlam
  refine ⟨fun _ => 0, fun _ => ⟨contDiff_const, HasCompactSupport.zero⟩, ?_⟩
  simp [zeroSide, hermitianTransform, paperFT, gaussTest]

example : GaussianApprox := by
  intro c lam hlam
  refine ⟨fun _ => 0, fun _ => ⟨contDiff_const, HasCompactSupport.zero⟩, ⟨0, ?_⟩, ?_⟩
  · intro n z hz; simp [hermitianTransform, paperFT]
  · intro z hz; simp [hermitianTransform, paperFT, gaussTest]

/- 7. The obligations are not refutable either (expected FAIL). -/
example : ¬ GaussianDominance := by
  intro h
  simp [GaussianDominance] at h

example : ¬ GaussianTransfer := by
  intro h
  obtain ⟨g, hg, hlim⟩ := h 0 1 one_pos
  simp at hlim

/- 8. The zero side in O2 is a genuine sum: HasSum form (expected SUCCESS). -/
example (c lam : ℝ) (hlam : 0 < lam) :
    HasSum (fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℂ) * gaussTest c lam (gammaOf ρ))
      (zeroSide (gaussTest c lam)) :=
  (summable_gauss_zeroSide c lam hlam).hasSum
