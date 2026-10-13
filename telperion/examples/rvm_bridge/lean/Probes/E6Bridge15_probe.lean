/-
  Probes for E6Bridge15 (2026-09-21): axiom audit of the B7 convergence half and of every stage;
  the node statement modulo LiValue type-checks verbatim; the obligation is FALSE at n = 0 (so it
  is not a tautology and the node's 0 < n is load-bearing); the forward half of Li's criterion.
  Run: cd telperion/examples/rvm_bridge/lean && lake env lean Probes/E6Bridge15_probe.lean
  Expected: every #print axioms line is exactly [propext, Classical.choice, Quot.sound]; no errors.
  (Automation attempts on LiValue are in E6Bridge15_obligation_probe.lean, expected to FAIL.)
-/
import E6Bridge15

open Zeta23 Complex Filter Topology RvMBridge15 RvMBridge15.BombieriLagarias

/-! ### The delivered convergence theorem and its stages. -/
#print axioms RvMBridge15.liZeroSum_tendsto
#print axioms RvMBridge15.zeroMult_conj
#print axioms RvMBridge15.liZeroSum_eq_tsum_paired
#print axioms RvMBridge15.liZeroSum_im
#print axioms RvMBridge15.abs_re_liKernel_le
#print axioms RvMBridge15.summable_liPaired
#print axioms RvMBridge15.bl_explicit_formula_of
#print axioms RvMBridge15.rh_implies_liZeroSum_re_nonneg
#print axioms RvMBridge15.rh_implies_liLimit_re_nonneg

/-! ### The node statement (RH_bl_explicit_formula.lean), verbatim shape, modulo LiValue. -/
example (n : ℕ) (hn : 0 < n) (h : LiValue n) :
    Tendsto (BombieriLagarias.liZeroSum n) atTop
      (𝓝 (BombieriLagarias.archSide n + BombieriLagarias.finiteSide n)) :=
  bl_explicit_formula_of hn h

/-! ### The obligation is not a tautology: at n = 0 it is FALSE (0 = 1). -/
theorem probe_liValue_zero_false : ¬ LiValue 0 := by
  unfold LiValue liLimit liPaired liKernel BombieriLagarias.archSide BombieriLagarias.finiteSide
  simp

#print axioms probe_liValue_zero_false

/-! ### Non-vacuity of the pairing: the window sums are real for every n, T. -/
example (n : ℕ) (T : ℝ) : (liZeroSum n T).im = 0 := liZeroSum_im n T
