/-
  Probes for E6Bridge25 (2026-09-21): NoRealZeroInUnitInterval is a THEOREM; the B7 value half and
  the node RH_bl_explicit_formula rest on E6Bridge22's two inequalities.
  Run: cd telperion/examples/rvm_bridge/lean && lake env lean Probes/E6Bridge25_probe.lean
  Expected: every #print axioms line is exactly [propext, Classical.choice, Quot.sound]; no errors.
-/
import E6Bridge25

open Zeta23 Complex Filter Topology RvMBridge15 RvMBridge15.BombieriLagarias RvMBridge25

#print axioms RvMBridge25.norm_tail_integral_le
#print axioms RvMBridge25.re_riemannZeta_neg_of_unit_interval
#print axioms RvMBridge25.riemannZeta_ne_zero_of_unit_interval
#print axioms RvMBridge25.noRealZeroInUnitInterval
#print axioms RvMBridge25.liValue_of_partialFraction
#print axioms RvMBridge25.liValue_of_growth
#print axioms RvMBridge25.liValue_of_two
#print axioms RvMBridge25.bl_explicit_formula_of_two

/-! ### The segment Prop is exactly E6Bridge19's (no restatement). -/
example : RvMBridge19.NoRealZeroInUnitInterval := noRealZeroInUnitInterval
example (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1) : riemannZeta (σ : ℂ) ≠ 0 := noRealZeroInUnitInterval σ h0 h1

/-! ### Non-vacuity of the sign statement: it is NOT the junk-value trick (zeta(1/2) really has
Re < 0), and the hypotheses are load-bearing: at σ = 2, Re zeta(2) = π²/6 > 0. -/
example : (riemannZeta ((1 / 2 : ℝ) : ℂ)).re < 0 :=
  re_riemannZeta_neg_of_unit_interval (by norm_num) (by norm_num)
example : 0 < (riemannZeta ((2 : ℝ) : ℂ)).re := by
  have := riemannZeta_re_pos_of_one_lt (x := 2) (by norm_num)
  exact this

/-! ### The node statement (RH_bl_explicit_formula.lean), verbatim shape, modulo the two
inequalities. -/
example (h1 : RvMBridge22.LocalCountSum) (h2 : RvMBridge22.StripDerivBound) (n : ℕ) (hn : 0 < n) :
    Tendsto (BombieriLagarias.liZeroSum n) atTop
      (𝓝 (BombieriLagarias.archSide n + BombieriLagarias.finiteSide n)) :=
  bl_explicit_formula_of_two h1 h2 n hn

/-! ### Still false at n = 0 (the 0 < n is load-bearing, not absorbed by the hypotheses). -/
example : ¬ LiValue 0 := by
  unfold LiValue liLimit liPaired liKernel BombieriLagarias.archSide BombieriLagarias.finiteSide
  simp
