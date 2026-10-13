/- Audit probes for E6Bridge22. -/
import E6Bridge22
open Zeta23 Complex Filter Topology RvMBridge18 RvMBridge20 RvMBridge22 WeilExplicit

/- 1. Obligations not automation-closable (expected FAIL each). -/
example : LocalCountSum := by unfold LocalCountSum; refine ⟨1, fun a => ?_⟩; simp
example : LocalCountSum := by unfold LocalCountSum; aesop
example : StripDerivBound := by unfold StripDerivBound; refine ⟨1, fun s h1 h2 h3 h4 => ?_⟩; simp
example : StripDerivBound := by unfold StripDerivBound; aesop

/- 2. RightDerivBound alone does not give the growth (expected FAIL). -/
example : XiDiffExtGrowthRight := xiDiffExtGrowthRight_of_two rightDerivBound rightDerivBound

/- 3. The chain from the two remaining inequalities to the partial fraction (expected SUCCESS). -/
example (h1 : LocalCountSum) (h2 : StripDerivBound) : XiLogDerivDerivEq := xiLogDerivDerivEq_of_two h1 h2
example (h1 : LocalCountSum) (h2 : StripDerivBound) : XiDiffRegular :=
  xiDiffRegular_of_right (xiDiffExtGrowthRight_of_two h1 h2)
example : RightDerivBound := rightDerivBound

/- 4. The factor-2 far comparison, re-proved abstractly: for d^2 ≥ 1, 1/d^2 ≤ 2/(1 + d^2)
   (expected SUCCESS). -/
theorem audit_far_factor {d2 : ℝ} (h : 1 ≤ d2) : 1 / d2 ≤ 2 / (1 + d2) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
#print axioms audit_far_factor

/- 5. The right comparison, re-proved: for Re s ≥ 2 and 0 < Re ρ < 1, ‖s - ρ‖^2 ≥ 1 + (Im s - Im ρ)^2
   (expected SUCCESS). -/
theorem audit_right_compare {s ρ : ℂ} (hs : 2 ≤ s.re) (hρ : ρ.re < 1) :
    1 + (s.im - ρ.im) ^ 2 ≤ ‖s - ρ‖ ^ 2 := by
  have hns : ‖s - ρ‖ ^ 2 = (s.re - ρ.re) ^ 2 + (s.im - ρ.im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]; ring
  rw [hns]; nlinarith
#print axioms audit_right_compare

/- 6. The summability of the local-count family at every centre (expected SUCCESS). -/
example (a : ℝ) : Summable (lcTerm a) := summable_lcTerm a

/- 7. Region (B) sits inside the strip obligation's region (expected SUCCESS). -/
example (s : ℂ) (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 2) (h3 : 6 ≤ |s.im|) :
    1 / 4 ≤ s.re ∧ s.re ≤ 9 / 4 ∧ 5 ≤ |s.im| := ⟨by linarith, by linarith, by linarith⟩
