/- Audit probes for E6Bridge21. -/
import E6Bridge21
open Zeta23 Complex Filter Topology RvMBridge18 RvMBridge21 WeilExplicit
open scoped LSeries.notation ArithmeticFunction

/- 1. Obligation 2 is closed: the decay is a theorem, and the interface identity now rests on
   XiDiffRegular alone; with E6Bridge20, on XiDiffExtGrowthRight alone (expected SUCCESS). -/
example : XiLogDerivDerivDecay := xi_logDeriv_deriv_decay
example (h1 : XiDiffRegular) : XiLogDerivDerivEq := xi_logDeriv_deriv_eq_of_regular h1

/- 2. The termwise formula instantiates at σ = 3 (expected SUCCESS). -/
example : deriv (logDeriv xi) (3 : ℝ) = -1 / ((3 : ℝ) : ℂ) ^ 2 - 1 / (((3 : ℝ) : ℂ) - 1) ^ 2
    + (1 / 4 : ℂ) * deriv Complex.digamma (((3 : ℝ) : ℂ) / 2) + deriv (logDeriv riemannZeta) ((3 : ℝ) : ℂ) :=
  deriv_logDeriv_xi_real (by norm_num)

/- 3. Signs, from the sources: logDeriv ζ = -L(Λ) and (logDeriv ζ)' = +L(logMul Λ) on Re s > 1
   (expected SUCCESS, consumption). -/
example {s : ℂ} (hs : 1 < s.re) : logDeriv riemannZeta s = -LSeries ↗Λ s := logDeriv_zeta_eq hs
example {s : ℂ} (hs : 1 < s.re) : deriv (logDeriv riemannZeta) s = LSeries (LSeries.logMul ↗Λ) s :=
  deriv_logDeriv_zeta_eq hs
example (f : ℕ → ℂ) (n : ℕ) : LSeries.logMul f n = Complex.log n * f n := rfl

/- 4. The trigamma series at a positive INTEGER (the extension across the integers), and the real
   bound at x = 1 (expected SUCCESS). -/
example : HasSum (fun n : ℕ => 1 / ((2 : ℂ) + n) ^ 2) (deriv Complex.digamma 2) :=
  hasSum_trigamma_of_re_pos (by norm_num)
example : ‖deriv Complex.digamma ((1 : ℝ) : ℂ)‖ ≤ 1 / ((1 : ℝ) - 1 / 2) :=
  norm_deriv_digamma_real_le le_rfl

/- 5. The telescoping step, re-proved: 1/a^2 ≤ 1/(a - 1/2) - 1/(a + 1/2) for a ≥ 1
   (expected SUCCESS). -/
theorem audit_telescope {a : ℝ} (ha : 1 ≤ a) : 1 / a ^ 2 ≤ 1 / (a - 1 / 2) - 1 / (a + 1 / 2) := by
  have hne1 : a - 1 / 2 ≠ 0 := by linarith
  have hne2 : a + 1 / 2 ≠ 0 := by linarith
  have hprod : 0 < (a - 1 / 2) * (a + 1 / 2) := by nlinarith
  rw [div_sub_div _ _ hne1 hne2, div_le_div_iff₀ (by positivity) hprod]
  nlinarith
#print axioms audit_telescope
