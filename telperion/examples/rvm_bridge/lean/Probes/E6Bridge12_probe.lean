/-
  Probes for E6Bridge12 (2026-09-21): axiom audit of the ladder-certified-region instrument, the
  signatures, and the LOAD-BEARING check that the on-line hypothesis cannot be dropped.
  Run: cd telperion/examples/rvm_bridge/lean && lake env lean Probes/E6Bridge12_probe.lean
  conjecture1_proved = False.
-/
import E6Bridge12

open Zeta23 Complex
open RvMBridge12

/-! ### Axiom audit: every delivered statement is [propext, Classical.choice, Quot.sound]. -/
#print axioms RvMBridge12.gaussian_positivity_of_window
#print axioms RvMBridge12.gaussian_positivity_of_window_two
#print axioms RvMBridge12.gaussian_positivity_of_all_on_line
#print axioms RvMBridge12.windowOnLine_of_all_on_line
#print axioms RvMBridge12.re_term_of_on_line
#print axioms RvMBridge12.re_term_nonneg
#print axioms RvMBridge12.near_term_ge
#print axioms RvMBridge12.zeroSide_split
#print axioms RvMBridge12.re_window_ge_term
#print axioms RvMBridge12.phi_le_of_far
#print axioms RvMBridge12.norm_term_le_tail
#print axioms RvMBridge12.tail_bound_window
#print axioms RvMBridge12.tail_le_near_of_threshold
#print axioms RvMBridge12.tsum_tailWeight
#print axioms RvMBridge12.gaussian_positivity_of_window_dominance
#print axioms RvMBridge12.re_zeroSide_ge_windowSum_sub
#print axioms RvMBridge12.re_window_eq_windowSum
#print axioms RvMBridgeGauss.zeroWindowSet_finite
#print axioms RvMBridge12.near_term_le_windowSum

/-! ### Signatures. -/
#check @RvMBridge12.WindowOnLine
#check @RvMBridge12.lamThreshold
#check @RvMBridge12.gaussian_positivity_of_window
#check @RvMBridge12.gaussian_positivity_of_window_two
#check @RvMBridge12.gaussian_positivity_of_all_on_line
#check @RvMBridge12.windowSum
#check @RvMBridge12.tailEnvelope
#check @RvMBridge12.gaussian_positivity_of_window_dominance
#check @RvMBridge12.re_zeroSide_ge_windowSum_sub

/-! ### The dominance hypothesis is a FINITE computable inequality: windowSum is a Finset sum over
the certified zeros (definitional), tailEnvelope an explicit real. -/
example (c D lam : ℝ) : RvMBridge12.windowSum c D lam
    = ∑ ρ ∈ RvMBridgeGauss.zeroWindow c D, (WeilExplicit.zeroMult ρ : ℝ)
        * ((ρ.im - c) ^ 2 * Real.exp (-(2 * lam) * (ρ.im - c) ^ 2)) := rfl
example (c D lam : ℝ) : RvMBridge12.tailEnvelope c D lam
    = Real.exp (2 * (lam - 1) * (1 / 4 - D ^ 2)) * RvMBridge7.constB c := rfl
example (c D : ℝ) (ρ : ℂ) : ρ ∈ RvMBridgeGauss.zeroWindow c D ↔
    IsNontrivialZero ρ ∧ |ρ.im - c| ≤ D := RvMBridgeGauss.mem_zeroWindow

/-! ### The hypothesis WindowOnLine is a genuine Prop about the zeros: neither closed nor refuted
by simp/aesop at any (c, D). -/
/-- error: `simp` made no progress -/
#guard_msgs in
example (c D : ℝ) : RvMBridge12.WindowOnLine c D := by simp

/-- error: `simp` made no progress -/
#guard_msgs in
example (c D : ℝ) : ¬ RvMBridge12.WindowOnLine c D := by simp

/-! ### LOAD-BEARING (local): the termwise nonnegativity behind the window sum FAILS off the line.
An off-line nontrivial zero at ordinate c contributes a strictly NEGATIVE summand
(-m y^2 e^{2 lam y^2}, y = 1/2 - Re rho), so `re_term_nonneg_of_on_line` cannot be extended to
zeros the window hypothesis does not cover.  Unconditional; axiom-clean. -/
theorem re_term_neg_of_off_line (c lam : ℝ) {ρ : ℂ} (hnt : IsNontrivialZero ρ)
    (hoff : ρ.re ≠ 1 / 2) (hc : ρ.im = c) : (RvMBridge7.term c lam ρ).re < 0 := by
  have hγ : gammaOf ρ = (c : ℂ) + ((1 / 2 - ρ.re : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp [Zeta23.WeilEF.gammaOf_re, hc]
    · simp [Zeta23.WeilEF.gammaOf_im]
  have hy : (1 / 2 - ρ.re) ≠ 0 := sub_ne_zero.mpr (Ne.symm hoff)
  have hneg := RvMBridge6.gaussTest_axis_re_neg c lam (1 / 2 - ρ.re) hy
  rw [← hγ] at hneg
  have hm : (1 : ℝ) ≤ WeilExplicit.zeroMult ρ := by
    rw [RvMBridge4.zeroMult_eq_mult hnt]
    exact_mod_cast zetaSeam.one_le_mult ρ hnt
  unfold RvMBridge7.term
  rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  exact mul_neg_of_pos_of_neg (by linarith) hneg

#print axioms re_term_neg_of_off_line

/-! ### LOAD-BEARING (global): the conclusion of gaussian_positivity_of_all_on_line FAILS somewhere
whenever its hypothesis fails.  This is E6Bridge7's O2 discharge read contrapositively: one
off-line zero forces some F(c, lam) < 0 with lam > 0.  So the on-line hypothesis is not
decorative; the certified-window theorem is exactly as strong as the certification it consumes. -/
theorem some_gauss_negative_of_off_line_zero
    (h : ∃ ρ : ℂ, IsNontrivialZero ρ ∧ ρ.re ≠ 1 / 2) :
    ∃ c lam : ℝ, 0 < lam ∧ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re < 0 := by
  obtain ⟨ρ, hρ, hre⟩ := h
  exact RvMBridge7.gaussian_dominance ρ hρ hre

#print axioms some_gauss_negative_of_off_line_zero

/-! ### Consistency: the two halves together are the forward direction of the Wall
(nothing about RH is proved; this only checks the shapes compose). -/
example (h : ∀ ρ : ℂ, IsNontrivialZero ρ → ρ.re = 1 / 2) (c lam : ℝ) (hlam : 0 < lam) :
    0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re :=
  RvMBridge12.gaussian_positivity_of_all_on_line h c lam hlam

/-- The window theorem specialises to full RH: WindowOnLine at every (c, D) is supplied by
windowOnLine_of_all_on_line, so with a near zero the window theorem applies (large lam). -/
example (h : ∀ ρ : ℂ, IsNontrivialZero ρ → ρ.re = 1 / 2) (c δ lam : ℝ) (hδ : 0 < δ)
    (hnear : ∃ ρ : ℂ, IsNontrivialZero ρ ∧ δ ≤ |ρ.im - c| ∧ |ρ.im - c| ≤ 1)
    (hlam : RvMBridge12.lamThreshold c 2 1 δ ≤ lam) :
    0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re :=
  RvMBridge12.gaussian_positivity_of_window_two hδ
    (RvMBridge12.windowOnLine_of_all_on_line h c 2) hnear hlam

/-! ### The threshold is explicit and at least 1. -/
example (c D d δ : ℝ) : 1 ≤ RvMBridge12.lamThreshold c D d δ :=
  RvMBridge12.one_le_lamThreshold c D d δ
example (c D d δ : ℝ) : RvMBridge12.lamThreshold c D d δ
    = max 1 (RvMBridge7.constB c * Real.exp (2 * (D ^ 2 - 1 / 4))
        / (2 * (D ^ 2 - 1 / 4 - d ^ 2) * δ ^ 2)) := rfl
