/-
  RationalFreqReduction.lean -- PROGRAM MIRRORMERE (reverse-Dyson) QC-1, kernel
  handoff K2.

  Theorem B bridge (qc-rigidity memo §2.2): the rationally-dependent case reduces
  R3 to the Lee-Yang-on-the-circle statement of `LeeYangCore`, with zero residual
  analytic content.

  For a rationally-dependent exponential sum
      F(x) = e^{i λ₀ x} · Σ_j c_j e^{i m_j ω x},   ω ∈ ℝ*,  m_j ∈ ℕ,
  the substitution `z = e^{iωx}` turns the inner sum into the polynomial
      P(z) = Σ_j c_j z^{m_j}      (P : ℂ[X]),
  so `F(x) = e^{iλ₀x} · P(e^{iωx})`.  Since `x ↦ z = e^{iωx}` maps the real line
  onto the unit circle (`x ∈ ℝ ⟺ |z| = 1`) and the prefactor never vanishes:

      F is REAL-ROOTED  ⟸  every zero of P lies on `|z| = 1`
                          (i.e. `IsLeeYangCircle P`, the LeeYangCore predicate).

  So R3(rational-n) reduces to `LeeYangCore` by the elementary substitution below.
  We prove the load-bearing direction (Lee-Yang-circle ⇒ real-rooted) end-to-end by
  composing with `LeeYangCore.leeYang_root_norm_one`.

  conjecture1_proved = False.  Unconditional finite reduction; NOT a proof of RH.
-/
import LeeYangCore
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Exp

open Polynomial Complex

namespace Quasicrystal

noncomputable section

/-- The rationally-dependent exponential sum `F(x) = e^{iλ₀x} · P(e^{iωx})`, where
`P : ℂ[X]` is the polynomial `Σ_j c_j z^{m_j}` obtained by the substitution
`z = e^{iωx}`.  Evaluated at complex `x` (zeros may a priori be complex). -/
def ratFreq (P : ℂ[X]) (lam₀ ω : ℝ) (x : ℂ) : ℂ :=
  Complex.exp ((lam₀ : ℂ) * x * Complex.I) * P.eval (Complex.exp ((ω : ℂ) * x * Complex.I))

/-- `‖e^{iωx}‖ = exp(−ω · Im x)` for real `ω` and complex `x`. -/
theorem norm_exp_omega (ω : ℝ) (x : ℂ) :
    ‖Complex.exp ((ω : ℂ) * x * Complex.I)‖ = Real.exp (-(ω * x.im)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- **Real ⟺ on the circle.**  For `ω ≠ 0`, `x` is real iff its image
`z = e^{iωx}` lies on the unit circle. -/
theorem im_zero_iff_norm_one (ω : ℝ) (x : ℂ) (hω : ω ≠ 0) :
    x.im = 0 ↔ ‖Complex.exp ((ω : ℂ) * x * Complex.I)‖ = 1 := by
  rw [norm_exp_omega]
  constructor
  · intro h; rw [h, mul_zero, neg_zero, Real.exp_zero]
  · intro h
    have : -(ω * x.im) = 0 := Real.exp_injective (by rw [h, Real.exp_zero])
    have hprod : ω * x.im = 0 := by linarith
    rcases mul_eq_zero.mp hprod with h1 | h1
    · exact absurd h1 hω
    · exact h1

/-- **Zero correspondence.**  The prefactor `e^{iλ₀x}` never vanishes, so `x` is a
zero of `F` iff `e^{iωx}` is a root of `P`. -/
theorem ratFreq_eq_zero_iff (P : ℂ[X]) (lam₀ ω : ℝ) (x : ℂ) :
    ratFreq P lam₀ ω x = 0 ↔ P.eval (Complex.exp ((ω : ℂ) * x * Complex.I)) = 0 := by
  unfold ratFreq
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (Complex.exp_ne_zero _)
    · exact h
  · intro h; right; exact h

/-- **K2 BRIDGE (load-bearing direction).**  If every zero of `P` lies on the unit
circle (`IsLeeYangCircle P` -- the LeeYangCore predicate), then `F` is real-rooted:
every zero of `F` has zero imaginary part.  This is R3(rational) reduced end-to-end
to `LeeYangCore`. -/
theorem ratFreq_realRooted_of_leeYangCircle (P : ℂ[X]) (lam₀ ω : ℝ)
    (hω : ω ≠ 0) (hP : IsLeeYangCircle P) :
    ∀ x : ℂ, ratFreq P lam₀ ω x = 0 → x.im = 0 := by
  intro x hx
  rw [ratFreq_eq_zero_iff] at hx
  -- the image z = e^{iωx} is a root of P, hence on the circle, hence x real
  have hcirc : ‖Complex.exp ((ω : ℂ) * x * Complex.I)‖ = 1 :=
    leeYang_root_norm_one P hP hx
  exact (im_zero_iff_norm_one ω x hω).mpr hcirc

/-- **K2 BRIDGE (converse, honest form).**  Conversely, if `F` is real-rooted then
every root of `P` that is REACHED by the substitution `z = e^{iωx}` lies on the
circle.  (The full converse `IsLeeYangCircle P` needs surjectivity of `x ↦ e^{iωx}`
onto `ℂ*`, i.e. every nonzero `z` has a complex log; recorded here in the reached-root
form that follows directly, which is what the reduction consumes.) -/
theorem leeYangCircle_reached_of_realRooted (P : ℂ[X]) (lam₀ ω : ℝ)
    (hω : ω ≠ 0)
    (hRR : ∀ x : ℂ, ratFreq P lam₀ ω x = 0 → x.im = 0) :
    ∀ x : ℂ, P.eval (Complex.exp ((ω : ℂ) * x * Complex.I)) = 0 →
      ‖Complex.exp ((ω : ℂ) * x * Complex.I)‖ = 1 := by
  intro x hx
  have hzero : ratFreq P lam₀ ω x = 0 := by
    rw [ratFreq_eq_zero_iff]; exact hx
  exact (im_zero_iff_norm_one ω x hω).mp (hRR x hzero)

end

end Quasicrystal
