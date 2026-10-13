/- Audit probes for E6Bridge18 / E6Bridge20. -/
import E6Bridge20
open Zeta23 Complex MeasureTheory Filter Topology RvMBridge18 RvMBridge20 WeilExplicit

/- 1. xi 0 = xi 1 = 1/2: the s(s-1)/2 factor's zeros at 0 and 1 are killed by the +1/2
   (expected SUCCESS). -/
theorem audit_xi_zero : xi 0 = 1 / 2 := by unfold xi; simp
theorem audit_xi_one : xi 1 = 1 / 2 := by unfold xi; simp
#print axioms audit_xi_zero

/- 2. Non-vacuity of the Liouville lemma: the identity function admits NO logarithmic bound
   (otherwise it would be constant, but id 1 ≠ id 0) (expected SUCCESS). -/
theorem audit_id_no_log_bound : ¬ ∃ C : ℝ, ∀ z : ℂ, ‖z‖ ≤ C * (1 + Real.log (2 + ‖z‖)) := by
  rintro ⟨C, hC⟩
  have h := eq_const_of_log_growth (G := fun z : ℂ => z) differentiable_id (fun z => hC z) 1
  simp at h
#print axioms audit_id_no_log_bound

/- 3. The obligations are not automation-closable (expected FAIL each). -/
example : XiDiffExtGrowthRight := by unfold XiDiffExtGrowthRight; refine ⟨1, fun s hs => ?_⟩; simp
example : XiDiffExtGrowthRight := by unfold XiDiffExtGrowthRight; aesop
example : XiLogDerivDerivDecay := by unfold XiLogDerivDerivDecay; simp
example : XiLogDerivDerivDecay := by unfold XiLogDerivDerivDecay; aesop

/- 4. The full chain consumes exactly the two named obligations (expected SUCCESS). -/
example (h1 : XiDiffExtGrowthRight) (h2 : XiLogDerivDerivDecay) : XiLogDerivDerivEq :=
  xi_logDeriv_deriv_eq_of (xiDiffRegular_of_right h1) h2
example (h1 : XiDiffExtGrowthRight) (h2 : XiLogDerivDerivDecay) (s : ℂ) (hs : ¬ IsNontrivialZero s) :
    deriv (logDeriv xi) s = -∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2 :=
  xi_logDeriv_deriv_eq_of (xiDiffRegular_of_right h1) h2 s hs

/- 5. Functional-equation sign, abstractly: if f(1 - z) = -f(z) and f is differentiable then
   f'(1 - s) = f'(s) (expected SUCCESS). -/
theorem audit_fe_sign {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfe : ∀ z, f (1 - z) = -f z) (s : ℂ) :
    deriv f (1 - s) = deriv f s := by
  have h1 : HasDerivAt (fun u : ℂ => f (1 - u)) (deriv f (1 - s) * (-1)) s :=
    (hf (1 - s)).hasDerivAt.comp s ((hasDerivAt_id s).const_sub 1)
  have hF : (fun u : ℂ => f (1 - u)) = fun u => -f u := funext hfe
  rw [hF] at h1
  have h2 : HasDerivAt (fun u : ℂ => -f u) (-deriv f s) s := (hf s).hasDerivAt.neg
  have := h1.unique h2
  linear_combination -this
#print axioms audit_fe_sign

/- 6. Summability holds at every s (the file notes the non-zero hypothesis is unused), the
   extension agrees off the zeros, and the order identity holds at a non-zero (expected SUCCESS). -/
example (s : ℂ) : Summable (polTerm s) := summable_polTerm s
example {s : ℂ} (hs : ¬ IsNontrivialZero s) : xiDiffExt s = xiDiffReg s := xiDiffExt_eq hs
example : analyticOrderAt xi 2 = 0 := by
  rw [analyticOrderAt_xi_eq, RvMBridge4.zeroMult_eq_zero_of_not_nontrivial]
  · rfl
  · exact not_nontrivialZero_of_one_le_re (by norm_num)

/- 7. The extension's value at a zero is NOT xiDiffReg's junk value by definition (the if-branch):
   xiDiffExt is a limUnder there; an attempt to rewrite it as xiDiffReg fails (expected FAIL). -/
example {s : ℂ} (hs : IsNontrivialZero s) : xiDiffExt s = xiDiffReg s := xiDiffExt_eq hs
