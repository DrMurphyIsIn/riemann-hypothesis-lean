/- Audit probe: the HYPOTHESIS-FREE sentence must NOT be closable by automation. Every example here is EXPECTED TO FAIL. -/
import E6Bridge5
open Zeta23 Complex MeasureTheory

example : ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g →
    0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re := by
  simp

example : ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g →
    0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re := by
  simp [WeilExplicit.weilForm, WeilExplicit.autocorr, WeilExplicit.archSide, WeilExplicit.primeSide,
    WeilExplicit.weilKernel, WeilExplicit.archIntegrand]

example : ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g →
    0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re := by
  aesop

example : ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g →
    0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re := by
  intro g hg
  positivity

example : ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g →
    0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re := by
  intro g hg
  unfold WeilExplicit.weilForm
  positivity

example : ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g →
    0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re := by
  intro g hg
  exact?

/- weilForm is not simp-trivially zero -/
example (f : ℝ → ℂ) : WeilExplicit.weilForm f = 0 := by
  simp [WeilExplicit.weilForm, WeilExplicit.archSide, WeilExplicit.primeSide]

/- The E8 HasSum: weilForm f IS the zero-side sum (definitional check, expected to SUCCEED). -/
example (g : ℝ → ℂ) (hg : WeilExplicit.IsWeilTest g) :
    HasSum (fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℂ) * WeilExplicit.weilKernel g ρ)
      (WeilExplicit.weilForm g) :=
  (RvMBridge4.limit_explicit_formula g hg).2
