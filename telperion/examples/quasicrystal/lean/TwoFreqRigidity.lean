/-
  TwoFreqRigidity.lean -- PROGRAM MIRRORMERE (reverse-Dyson) QC-1, kernel handoff K1.

  Theorem A (qc-rigidity memo §2.1), the program's FIRST rigidity theorem --
  self-contained, zero residual analytic content, does NOT depend on LeeYangCore.

  For a two-frequency exponential sum
      F(x) = c₁ · e^{i λ₁ x} + c₂ · e^{i λ₂ x},   c₁,c₂ ∈ ℂ*,  λ₁ ≠ λ₂ ∈ ℝ,
  set w = λ₂ − λ₁ ≠ 0.  Then:
    (a) every zero of F lies on the SINGLE horizontal line
          Im x = −(1/w) · log|c₁/c₂|,
        so the imaginary part of every zero is the same real constant; and
    (b) F is REAL-ROOTED  ⟺  |c₁| = |c₂|
        (an equal-modulus / self-inversive positivity condition on the dual side).

  This is the reverse-Dyson signature: the reality of the SUPPORT is forced by an
  equal-modulus condition on the COEFFICIENTS (spectrum/weight side), never a
  condition on the support.  At n = 2 the finite (H-fin-spec) hypothesis IS
  |c₁| = |c₂|.

  Proof (memo): factor F(x) = c₁ e^{iλ₁x}(1 + (c₂/c₁) e^{iwx}); the prefactor never
  vanishes, so F(x)=0 ⟺ e^{iwx} = −c₁/c₂.  Taking norms, |e^{iwx}| = exp(−w·Im x),
  which equals |c₁/c₂| exactly on the stated line; it equals 1 (⟺ real zero for all
  branches) exactly when |c₁| = |c₂|.

  conjecture1_proved = False.  Unconditional finite fact; NOT a proof of RH.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Exp

open Complex

namespace Quasicrystal

noncomputable section

/-- The two-frequency exponential sum `F(x) = c₁ e^{i λ₁ x} + c₂ e^{i λ₂ x}`,
evaluated at complex `x` (zeros may a priori be complex). -/
def twoFreq (c₁ c₂ : ℂ) (lam₁ lam₂ : ℝ) (x : ℂ) : ℂ :=
  c₁ * Complex.exp ((lam₁ : ℂ) * x * Complex.I)
    + c₂ * Complex.exp ((lam₂ : ℂ) * x * Complex.I)

/-- `e^{i(λ₂−λ₁)x} = e^{iλ₂x} / e^{iλ₁x}` (helper). -/
private theorem exp_diff (lam₁ lam₂ : ℝ) (x : ℂ) :
    Complex.exp (((lam₂ - lam₁ : ℝ) : ℂ) * x * Complex.I)
      = Complex.exp ((lam₂ : ℂ) * x * Complex.I)
        / Complex.exp ((lam₁ : ℂ) * x * Complex.I) := by
  rw [← Complex.exp_sub]; congr 1; push_cast; ring

/-- **Factorization / zero criterion.**  With `c₁,c₂ ≠ 0`, `x` is a zero of `F` iff
`e^{i(λ₂−λ₁)x} = −c₁/c₂`.  The nonvanishing prefactor `c₁ e^{iλ₁x}` is divided out. -/
theorem twoFreq_eq_zero_iff (c₁ c₂ : ℂ) (lam₁ lam₂ : ℝ) (x : ℂ)
    (_hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) :
    twoFreq c₁ c₂ lam₁ lam₂ x = 0
      ↔ Complex.exp (((lam₂ - lam₁ : ℝ) : ℂ) * x * Complex.I) = -c₁ / c₂ := by
  unfold twoFreq
  set E₁ : ℂ := Complex.exp ((lam₁ : ℂ) * x * Complex.I) with hE₁
  set E₂ : ℂ := Complex.exp ((lam₂ : ℂ) * x * Complex.I) with hE₂
  have e1 : E₁ ≠ 0 := by rw [hE₁]; exact Complex.exp_ne_zero _
  rw [exp_diff, ← hE₁, ← hE₂]
  rw [div_eq_div_iff e1 hc₂]
  -- goal: E₂ * c₂ = -c₁ * E₁   ⟺   c₁ * E₁ + c₂ * E₂ = 0
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-- **(a) Single-line location.**  Every zero of `F` has the SAME imaginary part
`Im x = −(1/w)·log|c₁/c₂|`, where `w = λ₂ − λ₁`.  Stated as: the norm of
`e^{iwx}` equals `|c₁/c₂|`, i.e. `exp(−w·Im x) = |c₁|/|c₂|` at every zero. -/
theorem twoFreq_zero_norm (c₁ c₂ : ℂ) (lam₁ lam₂ : ℝ) (x : ℂ)
    (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0)
    (hz : twoFreq c₁ c₂ lam₁ lam₂ x = 0) :
    Real.exp (-((lam₂ - lam₁) * x.im)) = ‖c₁‖ / ‖c₂‖ := by
  rw [twoFreq_eq_zero_iff c₁ c₂ lam₁ lam₂ x hc₁ hc₂] at hz
  have hnorm := congrArg (‖·‖) hz
  rw [Complex.norm_exp, norm_div, norm_neg] at hnorm
  have hre : (((lam₂ - lam₁ : ℝ) : ℂ) * x * Complex.I).re
      = -((lam₂ - lam₁) * x.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre] at hnorm
  exact hnorm

/-- `Real.exp t = 1 → t = 0`. -/
private theorem real_exp_eq_one (t : ℝ) (h : Real.exp t = 1) : t = 0 :=
  Real.exp_injective (by rw [h, Real.exp_zero])

/-- **(b) Real-rooted ⟺ equal modulus.**  `F` is real-rooted (every zero has zero
imaginary part) IF AND ONLY IF `|c₁| = |c₂|`.  The reverse-Dyson rigidity base case
R3(n=2): reality of the support is governed by an equal-modulus condition on the
coefficients alone. -/
theorem twoFreq_realRooted_iff (c₁ c₂ : ℂ) (lam₁ lam₂ : ℝ)
    (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hlam : lam₁ ≠ lam₂) :
    (∀ x : ℂ, twoFreq c₁ c₂ lam₁ lam₂ x = 0 → x.im = 0) ↔ ‖c₁‖ = ‖c₂‖ := by
  have hw : lam₂ - lam₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hlam)
  have hc₂norm : (0 : ℝ) < ‖c₂‖ := norm_pos_iff.mpr hc₂
  constructor
  · -- all zeros real ⇒ |c₁|=|c₂|.  Exhibit one zero and read off the norm.
    intro hall
    set r : ℂ := -c₁ / c₂ with hr
    have hrne : r ≠ 0 := div_ne_zero (neg_ne_zero.mpr hc₁) hc₂
    set x₀ : ℂ := Complex.log r / (((lam₂ - lam₁ : ℝ) : ℂ) * Complex.I) with hx₀
    have hden : ((lam₂ - lam₁ : ℝ) : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hw) Complex.I_ne_zero
    have hzero : twoFreq c₁ c₂ lam₁ lam₂ x₀ = 0 := by
      rw [twoFreq_eq_zero_iff c₁ c₂ lam₁ lam₂ x₀ hc₁ hc₂]
      have hscalar : ((lam₂ - lam₁ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw
      have harg : ((lam₂ - lam₁ : ℝ) : ℂ) * x₀ * Complex.I = Complex.log r := by
        rw [hx₀]
        field_simp
      rw [harg, Complex.exp_log hrne]
    have him : x₀.im = 0 := hall x₀ hzero
    have hnorm := twoFreq_zero_norm c₁ c₂ lam₁ lam₂ x₀ hc₁ hc₂ hzero
    rw [him, mul_zero, neg_zero, Real.exp_zero] at hnorm
    -- 1 = ‖c₁‖/‖c₂‖ ⇒ ‖c₁‖ = ‖c₂‖
    rw [eq_div_iff (ne_of_gt hc₂norm)] at hnorm
    linarith [hnorm]
  · -- |c₁|=|c₂| ⇒ every zero real
    intro hEq x hz
    have hnorm := twoFreq_zero_norm c₁ c₂ lam₁ lam₂ x hc₁ hc₂ hz
    rw [hEq, div_self (ne_of_gt hc₂norm)] at hnorm
    have hzero_arg : -((lam₂ - lam₁) * x.im) = 0 := real_exp_eq_one _ hnorm
    have hprod : (lam₂ - lam₁) * x.im = 0 := by linarith [hzero_arg]
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd h hw
    · exact h

end

end Quasicrystal
