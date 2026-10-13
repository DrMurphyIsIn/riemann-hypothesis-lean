/-
  Probes for E6Bridge18 (2026-09-21): axiom audit of the derivative partial fraction interface
  (summability PROVED; identity PROVED modulo XiDiffRegular + XiLogDerivDerivDecay), of the
  log-growth Liouville lemma and the real-axis decay of the sum; the interface shapes type-check
  verbatim.  Run: cd telperion/examples/rvm_bridge/lean && lake env lean Probes/E6Bridge18_probe.lean
  Expected: every #print axioms line is exactly [propext, Classical.choice, Quot.sound]; no errors.
  (Automation attempts on the obligations: E6Bridge18_obligation_probe.lean, expected to FAIL.)
-/
import E6Bridge18

open Zeta23 Complex Filter Topology RvMBridge18

#print axioms RvMBridge18.summable_inv_sub_sq
#print axioms RvMBridge18.xi_logDeriv_deriv_eq_of
#print axioms RvMBridge18.eq_const_of_log_growth
#print axioms RvMBridge18.tsum_inv_sub_sq_tendsto
#print axioms RvMBridge18.logDeriv_xi_eq
#print axioms RvMBridge18.xi_differentiable
#print axioms RvMBridge18.xi_eq

/-! ### The interface, verbatim shapes. -/
example (s : ℂ) (hs : ¬ IsNontrivialZero s) :
    Summable (fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2) :=
  summable_inv_sub_sq s hs

example (h1 : XiDiffRegular) (h2 : XiLogDerivDerivDecay) (s : ℂ) (hs : ¬ IsNontrivialZero s) :
    deriv (logDeriv xi) s = -∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2 :=
  xi_logDeriv_deriv_eq_of h1 h2 s hs

/-! ### Non-vacuity of the Liouville lemma: a genuinely bounded entire function is constant,
and a non-constant entire function (id) violates every log bound (so the lemma is not vacuous). -/
example : ∀ z : ℂ, (fun _ : ℂ => (7 : ℂ)) z = (fun _ : ℂ => (7 : ℂ)) 0 :=
  eq_const_of_log_growth (differentiable_const _) (C := 7) fun z => by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + ‖z‖ by linarith [norm_nonneg z])
    simp only [norm_ofNat]
    nlinarith

theorem probe_id_not_log_bounded : ¬ ∃ C : ℝ, ∀ z : ℂ, ‖(id z : ℂ)‖ ≤ C * (1 + Real.log (2 + ‖z‖)) := by
  rintro ⟨C, hC⟩
  have h := eq_const_of_log_growth differentiable_id hC 1
  simp at h

#print axioms probe_id_not_log_bounded
