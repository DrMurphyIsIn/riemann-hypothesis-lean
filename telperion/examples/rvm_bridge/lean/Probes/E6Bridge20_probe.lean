/-
  Probes for E6Bridge20 (2026-09-21): axiom audit of the entire extension of xiDiffReg across the
  zeros (part A of obligation 1), the functional equation, the half-plane reduction and the
  assembly xiDiffRegular_of; non-vacuity checks (xi has genuine zeros exactly at the nontrivial
  zeros, the order equals the E8 multiplicity).
  Run: cd telperion/examples/rvm_bridge/lean && lake env lean Probes/E6Bridge20_probe.lean
  Expected: every #print axioms line is exactly [propext, Classical.choice, Quot.sound]; no errors.
  (Automation attempts on the growth obligation: E6Bridge20_obligation_probe.lean, expected FAIL.)
-/
import E6Bridge20

open Zeta23 Complex Filter Topology RvMBridge18 RvMBridge20

#print axioms RvMBridge20.xiDiffExt_differentiable
#print axioms RvMBridge20.xiDiffExt_eq
#print axioms RvMBridge20.xiDiffExt_one_sub
#print axioms RvMBridge20.exists_local_form
#print axioms RvMBridge20.exists_ball_rest
#print axioms RvMBridgeXi.xi_eq_zero_iff
#print axioms RvMBridge20.analyticOrderAt_xi_eq
#print axioms RvMBridge20.deriv_logDeriv_xi_local
#print axioms RvMBridge20.xiDiffExtGrowth_of_right
#print axioms RvMBridge20.xiDiffRegular_of
#print axioms RvMBridge20.xiDiffRegular_of_right

/-! ### The delivered shape: obligation 1 of E6Bridge18 modulo the growth bound. -/
example (h : XiDiffExtGrowth) : RvMBridge18.XiDiffRegular := xiDiffRegular_of h

/-! ### The two clauses of XiDiffRegular that ARE proved, stated verbatim. -/
example : Differentiable ℂ xiDiffExt ∧ ∀ s : ℂ, ¬ IsNontrivialZero s → xiDiffExt s = xiDiffReg s :=
  ⟨xiDiffExt_differentiable, fun _ hs => xiDiffExt_eq hs⟩

/-! ### Non-vacuity: the zero set of xi is exactly the nontrivial zeros, so the gluing is across a
genuine (infinite) set of double poles, not an empty one. -/
example (ρ : ℂ) (h : IsNontrivialZero ρ) : xi ρ = 0 := (RvMBridgeXi.xi_eq_zero_iff ρ).mpr h
example (ρ : ℂ) (_h : IsNontrivialZero ρ) : analyticOrderAt xi ρ = (WeilExplicit.zeroMult ρ : ℕ∞) :=
  analyticOrderAt_xi_eq ρ
