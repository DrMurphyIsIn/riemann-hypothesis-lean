/-
  Probes for E6Bridge19 (2026-09-21): axiom audit of the LiValue bookkeeping and assembly.
  Run: cd telperion/examples/rvm_bridge/lean && lake env lean Probes/E6Bridge19_probe.lean
  Expected: every #print axioms line is exactly [propext, Classical.choice, Quot.sound]; no errors.
-/
import E6Bridge19

open Zeta23 Complex Filter Topology RvMBridge15 RvMBridge15.BombieriLagarias RvMBridge19
open RvMBridge18 (xi XiLogDerivDerivEq)

#print axioms RvMBridge19.powerSum_eq_taylor
#print axioms RvMBridge19.summable_powerSum
#print axioms RvMBridge19.powerSum_conj
#print axioms RvMBridge19.pairedPowerSum_one_eq
#print axioms RvMBridge19.summable_pairedPowerSum
#print axioms RvMBridge19.tsum_refTerm
#print axioms RvMBridge19.eta_eq
#print axioms RvMBridge19.iteratedDeriv_psiHalf
#print axioms RvMBridge19.tsum_odd_inv_pow
#print axioms RvMBridge19.archCoeff_zero
#print axioms RvMBridge19.archCoeff_succ
#print axioms RvMBridge19.logDeriv_xi_eventuallyEq_one
#print axioms RvMBridge19.taylorOne_eq
#print axioms RvMBridge19.taylorZero_eq
#print axioms RvMBridge19.liLimit_eq_taylorOne
#print axioms RvMBridge19.liValue_of
#print axioms RvMBridge19.bl_explicit_formula_of_partialFraction
#print axioms RvMBridgeXi.xi_eq_zero_iff

/-! ### The Lambda-form equivalence and the Lambda-form entry point. -/
#print axioms RvMBridge19.xiDerivPartialFraction_iff
#print axioms RvMBridge19.liValue_of_lambda
#print axioms RvMBridge19.deriv_logDeriv_lambda_eq
#print axioms RvMBridge19.liValue_of_growth
#print axioms RvMBridge19.bl_explicit_formula_of_growth

/-! ### The node statement (RH_bl_explicit_formula.lean), verbatim shape, modulo the two Props. -/
example (hP : XiLogDerivDerivEq) (hR : NoRealZeroInUnitInterval) (n : ℕ) (hn : 0 < n) :
    Tendsto (BombieriLagarias.liZeroSum n) atTop
      (𝓝 (BombieriLagarias.archSide n + BombieriLagarias.finiteSide n)) :=
  bl_explicit_formula_of_partialFraction hP hR n hn

/-! ### Non-vacuity: the delivered LiValue is E6Bridge15's LiValue, which is FALSE at n = 0
(so the 0 < n hypothesis is load-bearing and the Props do not make it a tautology). -/
example : ¬ LiValue 0 := by
  unfold LiValue liLimit liPaired liKernel BombieriLagarias.archSide BombieriLagarias.finiteSide
  simp

/-! ### The two Props are the stated shapes (no hidden strengthening). -/
example : RvMBridge18.XiLogDerivDerivEq = (∀ s : ℂ, ¬ IsNontrivialZero s →
    deriv (logDeriv RvMBridge18.xi) s = -∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2) := rfl
example : NoRealZeroInUnitInterval = (∀ σ : ℝ, 0 < σ → σ < 1 → riemannZeta (σ : ℂ) ≠ 0) := rfl
example : RvMBridge18.xi = fun s : ℂ => s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2 := rfl

/-! ### One obligation away: the node from RvMBridge20.XiDiffExtGrowthRight + the segment Prop. -/
example (h : RvMBridge20.XiDiffExtGrowthRight) (hR : NoRealZeroInUnitInterval) (n : ℕ) (hn : 0 < n) :
    Tendsto (BombieriLagarias.liZeroSum n) atTop
      (𝓝 (BombieriLagarias.archSide n + BombieriLagarias.finiteSide n)) :=
  bl_explicit_formula_of_growth h hR n hn
