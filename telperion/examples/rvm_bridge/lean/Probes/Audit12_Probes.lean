/- Audit probes for E6Bridge12. -/
import E6Bridge12
open Zeta23 Complex MeasureTheory Filter Topology RvMBridge6 RvMBridge7 RvMBridge12 WeilExplicit RvMBridgeGauss

/- 1. hwin is load-bearing: an OFF-line nontrivial zero at ordinate c contributes a strictly
   NEGATIVE summand (expected SUCCESS). -/
theorem audit_re_term_neg_of_off_line (c lam : ℝ) {ρ : ℂ} (hnt : IsNontrivialZero ρ)
    (hoff : ρ.re ≠ 1 / 2) (hc : ρ.im = c) : (term c lam ρ).re < 0 := by
  have hγ : gammaOf ρ = (c : ℂ) + ((1 / 2 - ρ.re : ℝ) : ℂ) * I := by
    apply Complex.ext
    · rw [Zeta23.WeilEF.gammaOf_re]; simp [hc]
    · rw [Zeta23.WeilEF.gammaOf_im]; simp
  have hm : (1 : ℝ) ≤ WeilExplicit.zeroMult ρ := by
    rw [RvMBridge4.zeroMult_eq_mult hnt]
    exact_mod_cast zetaSeam.one_le_mult ρ hnt
  have hneg := gaussTest_axis_re_neg c lam (1 / 2 - ρ.re) (sub_ne_zero.mpr (Ne.symm hoff))
  unfold term
  rw [hγ, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  nlinarith
#print axioms audit_re_term_neg_of_off_line

/- 2. The theorem with hwin DELETED does not go through: the on-line step has no source
   (expected FAIL at h₁line). -/
example {c D d δ lam : ℝ} (hD : 0 ≤ D) (hδ : 0 < δ) (hgap : d ^ 2 + 1 / 4 < D ^ 2)
    (hnear : ∃ ρ : ℂ, IsNontrivialZero ρ ∧ δ ≤ |ρ.im - c| ∧ |ρ.im - c| ≤ d)
    (hlam : lamThreshold c D d δ ≤ lam) : 0 ≤ (zeroSide (gaussTest c lam)).re := by
  obtain ⟨ρ₁, h₁nt, hδ₁, hd₁⟩ := hnear
  have hlam1 : 1 ≤ lam := le_trans (le_max_left _ _) hlam
  have hlam0 : 0 < lam := by linarith
  have h₁line : ρ₁.re = 1 / 2 := by
    exact?
  exact absurd h₁line (by sorry)

/- 3. Non-vacuity: under the all-on-line hypothesis, any nontrivial zero rho and any
   0 < δ ≤ d yield BOTH hypotheses at centre c = Im rho - d (expected SUCCESS). -/
theorem audit_hyps_satisfiable (h : ∀ ρ : ℂ, IsNontrivialZero ρ → ρ.re = 1 / 2)
    {ρ : ℂ} (hρ : IsNontrivialZero ρ) {δ d D : ℝ} (hδ : 0 < δ) (hδd : δ ≤ d) :
    WindowOnLine (ρ.im - d) D ∧
      ∃ ρ' : ℂ, IsNontrivialZero ρ' ∧ δ ≤ |ρ'.im - (ρ.im - d)| ∧ |ρ'.im - (ρ.im - d)| ≤ d := by
  refine ⟨windowOnLine_of_all_on_line h _ _, ρ, hρ, ?_, ?_⟩
  · rw [show ρ.im - (ρ.im - d) = d by ring, abs_of_pos (by linarith)]; exact hδd
  · rw [show ρ.im - (ρ.im - d) = d by ring, abs_of_pos (by linarith)]
#print axioms audit_hyps_satisfiable

/- lamThreshold is a real number ≥ 1 (finite, positive) for every argument (expected SUCCESS). -/
example (c D d δ : ℝ) : 0 < lamThreshold c D d δ := lt_of_lt_of_le one_pos (one_le_lamThreshold c D d δ)

/- 4. Independent re-proof of the threshold inequality with the file's constants
   (expected SUCCESS). -/
theorem audit_threshold (B A κ δ lam : ℝ) (hB : 0 ≤ B) (hκ : 0 < κ) (hδ : 0 < δ)
    (hlam : B * Real.exp (2 * A) / (2 * κ * δ ^ 2) ≤ lam) :
    Real.exp (2 * A) * Real.exp (-(2 * lam * κ)) * B ≤ δ ^ 2 := by
  have hden : 0 < 2 * κ * δ ^ 2 := by positivity
  have h1 : B * Real.exp (2 * A) ≤ lam * (2 * κ * δ ^ 2) := by rwa [div_le_iff₀ hden] at hlam
  have h2 : Real.exp (-(2 * lam * κ)) * (2 * lam * κ) ≤ 1 := by
    have := Real.add_one_le_exp (2 * lam * κ)
    rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _), mul_one]
    linarith
  have hE : 0 ≤ Real.exp (-(2 * lam * κ)) := (Real.exp_pos _).le
  calc Real.exp (2 * A) * Real.exp (-(2 * lam * κ)) * B
      = Real.exp (-(2 * lam * κ)) * (B * Real.exp (2 * A)) := by ring
    _ ≤ Real.exp (-(2 * lam * κ)) * (lam * (2 * κ * δ ^ 2)) := mul_le_mul_of_nonneg_left h1 hE
    _ = (Real.exp (-(2 * lam * κ)) * (2 * lam * κ)) * δ ^ 2 := by ring
    _ ≤ 1 * δ ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    _ = δ ^ 2 := one_mul _
#print axioms audit_threshold

/- 5. The window finiteness is a THEOREM from Zeta23 (expected SUCCESS), and the window/tail
   split has both parts Summable (expected SUCCESS). -/
example (c D : ℝ) : (zeroWindowSet c D).Finite := zeroWindowSet_finite c D
example (c D lam : ℝ) (hlam : 0 < lam) :
    Summable (term c lam ∘ (Subtype.val : winSet c D → ℂ)) ∧
    Summable (term c lam ∘ (Subtype.val : ↥(winSet c D)ᶜ → ℂ)) :=
  ⟨summable_term_subtype c lam hlam _, summable_term_subtype c lam hlam _⟩

/- 6. WindowOnLine is not closed by automation (expected FAIL). -/
example (c D : ℝ) : WindowOnLine c D := by
  unfold WindowOnLine
  aesop
