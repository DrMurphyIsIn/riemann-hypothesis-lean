/-
  Probes for E6Bridge10 (2026-09-21): axiom audit of the two-parameter Wall
  (RvMBridge10.rh_iff_gaussian_positivity), of the Gaussian explicit formula
  (RvMBridge10.zeroSide_gaussTest_eq) and of every stage, plus shape / non-vacuity probes.
  Run: cd telperion/examples/rvm_bridge/lean && lake env lean Probes/E6Bridge10_probe.lean
  Expected: every #print axioms line is exactly [propext, Classical.choice, Quot.sound].
  Nothing here proves RH. conjecture1_proved = False.
-/
import E6Bridge10

open Zeta23 Complex RvMBridge10 WeilExplicit

/-! ### Deliverable 1, verbatim types. -/
example : RvMBridge10.GaussianPositivity =
    (∀ (c lam : ℝ), 0 < lam → 0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re) := rfl
example : RiemannHypothesis ↔ RvMBridge10.GaussianPositivity := RvMBridge10.rh_iff_gaussian_positivity
example : RvMBridge10.GaussianPositivity ↔ (∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g →
    0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re) :=
  RvMBridge10.gaussian_positivity_iff_weil_positivity

#print axioms RvMBridge10.rh_iff_gaussian_positivity
#print axioms RvMBridge10.rh_implies_gaussian_positivity
#print axioms RvMBridge10.gaussian_positivity_implies_rh
#print axioms RvMBridge10.gaussian_positivity_iff_weil_positivity

/-! ### Deliverable 2, verbatim type. -/
example (c lam : ℝ) (hlam : 0 < lam) :
    RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)
      = WeilExplicit.archSide (WeilExplicit.autocorr (RvMBridge8.gaussPhi c lam))
        - WeilExplicit.primeSide (WeilExplicit.autocorr (RvMBridge8.gaussPhi c lam)) :=
  RvMBridge10.zeroSide_gaussTest_eq c lam hlam

#print axioms RvMBridge10.zeroSide_gaussTest_eq
#print axioms RvMBridge10.gaussian_positivity_iff_prime_le_arch
#print axioms RvMBridge10.rh_iff_gaussian_prime_le_arch

/-! ### Stages. -/
#print axioms RvMBridge10.zeroSide_gaussTests_tendsto
#print axioms RvMBridge10.norm_autocorr_gaussTests_le
#print axioms RvMBridge10.autocorr_gaussTests_tendsto
#print axioms RvMBridge10.summable_primeBound
#print axioms RvMBridge10.primeSide_gaussTests_tendsto
#print axioms RvMBridge10.weilKernel_gaussTests_tendsto
#print axioms RvMBridge10.archIntegral_gaussTests_tendsto
#print axioms RvMBridge10.archSide_gaussTests_tendsto
#print axioms RvMBridge10.integral_vMaj
#print axioms RvMBridge10.integrable_archBound

/-! ### Shape: the two-parameter statement quantifies over two reals only (no test function,
no sequence, no existential).  Checked by elaborating the definition body as a Prop over R x R. -/
example : ∃ P : ℝ → ℝ → Prop, RvMBridge10.GaussianPositivity = ∀ c lam, 0 < lam → P c lam :=
  ⟨fun c lam => 0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re, rfl⟩

/-! ### Non-vacuity 1: GaussianPositivity is NOT a tautology -- an off-line zero would refute it
(this is gaussian_dominance read through the new definition). -/
theorem probe_offline_zero_refutes (ρ₀ : ℂ) (h : IsNontrivialZero ρ₀) (h' : ρ₀.re ≠ 1 / 2) :
    ¬ RvMBridge10.GaussianPositivity := by
  intro hGP
  obtain ⟨c, lam, hlam, hneg⟩ := RvMBridge7.gaussian_dominance ρ₀ h h'
  linarith [hGP c lam hlam]

#print axioms probe_offline_zero_refutes

/-! ### Non-vacuity 2: the falsifiability face of the prime-side form.  RH fails iff for some
centre and width the prime side strictly exceeds the archimedean side. -/
theorem probe_not_rh_iff_prime_gt_arch :
    ¬ RiemannHypothesis ↔ ∃ (c lam : ℝ), 0 < lam ∧
      (WeilExplicit.archSide (WeilExplicit.autocorr (RvMBridge8.gaussPhi c lam))).re
        < (WeilExplicit.primeSide (WeilExplicit.autocorr (RvMBridge8.gaussPhi c lam))).re := by
  rw [RvMBridge10.rh_iff_gaussian_prime_le_arch]
  push Not
  rfl

#print axioms probe_not_rh_iff_prime_gt_arch

/-! ### Non-vacuity 3: the test phi is not the zero function (so autocorr phi is a genuine
autocorrelation, not 0 = 0). -/
theorem probe_gaussPhi_ne_zero (c lam : ℝ) (hlam : 0 < lam) : RvMBridge8.gaussPhi c lam 1 ≠ 0 := by
  unfold RvMBridge8.gaussPhi
  exact mul_ne_zero (mul_ne_zero (RvMBridge8.gaussK_ne_zero hlam) (by norm_num))
    (Complex.exp_ne_zero _)

#print axioms probe_gaussPhi_ne_zero

/-! ### The Wall is a change of coordinates, not a crossing: the hypothesis-free theorems below
say RH <-> (two-parameter statement); neither side is asserted.  This example just records that
RH itself is NOT a theorem of this file (it is an open Prop; `sorry`-free files cannot prove it). -/
example : (RiemannHypothesis ↔ RvMBridge10.GaussianPositivity) ∧
    (RiemannHypothesis ↔ ∀ (c lam : ℝ), 0 < lam →
      (WeilExplicit.primeSide (WeilExplicit.autocorr (RvMBridge8.gaussPhi c lam))).re
        ≤ (WeilExplicit.archSide (WeilExplicit.autocorr (RvMBridge8.gaussPhi c lam))).re) :=
  ⟨RvMBridge10.rh_iff_gaussian_positivity, RvMBridge10.rh_iff_gaussian_prime_le_arch⟩
