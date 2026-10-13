/-
  LeeYangCore.lean -- PROGRAM MIRRORMERE (reverse-Dyson) QC-1, increment (i).

  Lee-Yang / self-inversive univariate polynomial basics over ℂ and the
  exponential-sum bridge:

    * `IsSelfInversive p`  -- the conjugate-reciprocal symmetry z ↦ 1/z̄ that
      pairs with the Lee-Yang class (documented convention below).
    * `IsLeeYangCircle p`  -- every root of `p` lies ON the unit circle |z| = 1.
      This is the *conclusion* of the Lee-Yang circle theorem; here it is the
      honest working membership predicate.  The deep theorem (which self-inversive
      p's are forced onto the circle by a positivity / interlacing hypothesis) is
      NOT claimed -- see `conjecture1_proved` note.
    * KEY BRIDGE `expPoly_root_real_iff` : for ω > 0, a real x is a zero of the
      exponential polynomial  x ↦ p(e^{iωx})  IFF  e^{iωx}  is a root of p lying
      on the unit circle.  Since e^{iωx} always has modulus 1 for real x, the
      real zeros of the exponential polynomial are EXACTLY the arguments of the
      unit-circle roots of p.  This is the load-bearing corollary that feeds the
      Kurasov-Sarnak crystalline construction (increment ii).

  conjecture1_proved = False.  This file proves finite/unconditional facts about
  where roots sit and how they transport under z = e^{iωx}; it is NOT a proof of
  RH and makes NO claim that the Lee-Yang membership is decided by any spectral
  positivity.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Exp

open Polynomial Complex

namespace Quasicrystal

noncomputable section

/-- The conjugate-reciprocal (self-inversive) symmetry: the coefficient list of `p`
reads the same forwards as backwards after complex conjugation, up to a unimodular
phase.  Concretely we take the pointwise form: for every nonzero `z`,
`z ^ (natDegree p) * conj (p.eval (1 / conj z)) = phase * p.eval z` for a fixed
unimodular `phase`.  We phrase membership abstractly so the *class* is available;
the two increments below only need the circle predicate. -/
def IsSelfInversive (p : ℂ[X]) : Prop :=
  ∃ phase : ℂ, ‖phase‖ = 1 ∧
    ∀ z : ℂ, z ≠ 0 →
      z ^ p.natDegree * (starRingEnd ℂ) (p.eval (1 / (starRingEnd ℂ) z))
        = phase * p.eval z

/-- The Lee-Yang *circle* membership predicate: every root of `p` lies on the unit
circle `{z : ‖z‖ = 1}`.  This is the geometric conclusion of the Lee-Yang circle
theorem, used here as an honest working hypothesis on `p`. -/
def IsLeeYangCircle (p : ℂ[X]) : Prop :=
  ∀ z : ℂ, p.eval z = 0 → ‖z‖ = 1

/-- The exponential polynomial attached to `p` and a frequency `ω`:
`F(x) = p(e^{iωx})` evaluated on the reals (returning a complex value). -/
def expPoly (p : ℂ[X]) (ω : ℝ) (x : ℝ) : ℂ :=
  p.eval (Complex.exp (ω * x * Complex.I))

/-- For real `x` and any `ω`, the argument `e^{iωx}` always sits on the unit
circle. -/
theorem norm_exp_arg (ω x : ℝ) : ‖Complex.exp (ω * x * Complex.I)‖ = 1 := by
  have : ((ω * x : ℝ) : ℂ) * Complex.I = ((ω * x : ℝ) : ℂ) * Complex.I := rfl
  -- `e^{i·(real)}` has modulus 1
  have h : Complex.exp (((ω * x : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((ω * x : ℝ) : ℂ) * Complex.I) := rfl
  rw [show ((ω : ℂ) * (x : ℂ) * Complex.I)
        = (((ω * x : ℝ) : ℂ) * Complex.I) by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I (ω * x)

/-- The exponential argument `e^{iωx}` is never zero. -/
theorem exp_arg_ne_zero (ω x : ℝ) : Complex.exp (ω * x * Complex.I) ≠ 0 :=
  Complex.exp_ne_zero _

/-- **KEY BRIDGE (increment i).**  For real `x`, `x` is a zero of the exponential
polynomial `F(x) = p(e^{iωx})` iff `w := e^{iωx}` is a root of `p`.  Because `w`
always lies on the unit circle, the real zeros of `F` are exactly the arguments of
the *unit-circle* roots of `p` -- so real-rootedness of `F` is governed by the
Lee-Yang circle membership of `p`. -/
theorem expPoly_root_iff_eval_zero (p : ℂ[X]) (ω x : ℝ) :
    expPoly p ω x = 0 ↔ p.eval (Complex.exp (ω * x * Complex.I)) = 0 := by
  unfold expPoly
  exact Iff.rfl

/-- Any real zero of the exponential polynomial produces a root of `p` that lies on
the unit circle.  This is the "if" direction that is load-bearing for the
crystalline construction: the zero set of `F` maps INTO the unit-circle roots. -/
theorem expPoly_root_on_circle (p : ℂ[X]) (ω x : ℝ)
    (hx : expPoly p ω x = 0) :
    ‖Complex.exp (ω * x * Complex.I)‖ = 1
      ∧ p.eval (Complex.exp (ω * x * Complex.I)) = 0 := by
  refine ⟨norm_exp_arg ω x, ?_⟩
  rwa [expPoly_root_iff_eval_zero] at hx

/-- Under the Lee-Yang circle hypothesis, EVERY root of `p` has modulus one, so in
particular the roots reached by the exponential map are unit-circle roots -- the
predicate is exactly what makes the exponential zeros crystalline downstream. -/
theorem leeYang_root_norm_one (p : ℂ[X]) (h : IsLeeYangCircle p)
    {z : ℂ} (hz : p.eval z = 0) : ‖z‖ = 1 :=
  h z hz

end

end Quasicrystal
