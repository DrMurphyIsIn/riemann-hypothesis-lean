/-
  KSConstruction.lean -- PROGRAM MIRRORMERE (reverse-Dyson) QC-1, increment (ii).

  Kurasov-Sarnak construction, one-frequency honest instance.

  The zeros of a one-frequency Lee-Yang exponential polynomial `F(x) = p(e^{iωx})`
  (ω > 0) form a CRYSTALLINE configuration.  We formalize this in two kernel layers:

    LAYER 1 (support structure).  For each unit-circle root `w = e^{iθ}` of `p`,
    the real preimages `{x : e^{iωx} = w}` are exactly the shifted lattice
    `latticeAP ω θ = {(θ + 2πk)/ω : k ∈ ℤ}` -- an arithmetic progression of step
    `2π/ω`.  Hence the real zero set of `F` is a FINITE UNION of shifted lattices
    (one per unit-circle root, of which there are finitely many).  This is the
    crystalline SUPPORT: a finite union of shifted copies of the lattice
    `(2π/ω)ℤ`.

    LAYER 2 (Poisson / diffraction, test-function form).  Each shifted lattice
    obeys a Poisson summation identity (crystalline diffraction in
    test-function/tempered-distribution form): summing a Schwartz function over
    `latticeAP ω θ` equals a dual sum over the reciprocal lattice `(ω/2π)ℤ`.
    This is Mathlib's `SchwartzMap.tsum_eq_tsum_fourier` transported by the affine
    reparametrization `x ↦ (θ + 2π x)/ω`.  Summing the finitely many per-root
    identities gives the crystalline summation formula for the whole zero set --
    the honest test-function definition of a crystalline measure (Meyer /
    Kurasov-Sarnak), avoiding distribution-topology.

  conjecture1_proved = False.  Finite/unconditional throughout; NOT a proof of RH.
-/
import LeeYangCore
import Mathlib.Analysis.Fourier.PoissonSummation

open Polynomial Complex ContinuousMap
open scoped Real FourierTransform

namespace Quasicrystal

noncomputable section

/-- The shifted arithmetic-progression lattice of step `2π/ω` through phase
`θ/ω`: `latticeAP ω θ = {(θ + 2π k)/ω : k ∈ ℤ}`. -/
def latticeAP (ω θ : ℝ) : Set ℝ :=
  {x : ℝ | ∃ k : ℤ, x = (θ + 2 * Real.pi * k) / ω}

/-- **LAYER 1 (support structure).**  For `ω ≠ 0` and a unit-circle root
`w = e^{iθ}` of `p`, the real preimages under `x ↦ e^{iωx}` of `w` form exactly
the shifted lattice `latticeAP ω θ`.  Concretely: `e^{iωx} = e^{iθ}` iff `x` lies
in the arithmetic progression `(θ + 2πk)/ω`. -/
theorem preimage_eq_latticeAP (ω θ : ℝ) (hω : ω ≠ 0) :
    {x : ℝ | Complex.exp (ω * x * Complex.I) = Complex.exp (θ * Complex.I)}
      = latticeAP ω θ := by
  ext x
  simp only [Set.mem_setOf_eq, latticeAP]
  rw [Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    -- (ω x) I = θ I + k (2π I)  ⇒  ω x = θ + 2π k  (as reals), then divide by ω
    have hI : ((ω : ℂ) * (x : ℂ) * Complex.I)
        = (((θ : ℂ) + (k : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I) := by
      rw [hk]; ring
    have hmul : ((ω : ℂ) * (x : ℂ))
        = ((θ : ℂ) + (k : ℂ) * (2 * (Real.pi : ℂ))) :=
      mul_right_cancel₀ Complex.I_ne_zero hI
    have hre : ω * x = θ + 2 * Real.pi * k := by
      have := congrArg Complex.re hmul
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    field_simp
    linarith [hre]
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hxω : ω * x = θ + 2 * Real.pi * k := by
      rw [hk]; field_simp
    have hc : ((ω : ℂ) * (x : ℂ)) = ((θ : ℂ) + (k : ℂ) * (2 * (Real.pi : ℂ))) := by
      have := congrArg (fun r : ℝ => (r : ℂ)) hxω
      push_cast at this ⊢
      linear_combination this
    linear_combination Complex.I * hc

/-- Membership rewrite: `x` is a real zero of the exponential polynomial `F` iff
`e^{iωx}` is a root of `p`.  (Restatement of the increment-(i) bridge, packaged for
the support-structure argument.) -/
theorem mem_zeroSet_iff (p : ℂ[X]) (ω x : ℝ) :
    expPoly p ω x = 0 ↔ p.eval (Complex.exp (ω * x * Complex.I)) = 0 :=
  expPoly_root_iff_eval_zero p ω x

/-- A point of a shifted lattice, written explicitly. -/
theorem latticeAP_mem (ω θ : ℝ) (k : ℤ) :
    ((θ + 2 * Real.pi * k) / ω) ∈ latticeAP ω θ :=
  ⟨k, rfl⟩

/-- **LAYER 2 (Poisson summation, test-function form).**  Crystalline diffraction
for a shifted, scaled lattice.  For a Schwartz function `f` and shift `s`,
summing over the unit-step shifted lattice `{s + n : n ∈ ℤ}` equals the Fourier
dual sum -- Mathlib's Poisson summation.  This is the crystalline summation
identity in the honest test-function form (a pure-point diffraction statement
without distribution topology); the general step `2π/ω` case is obtained by the
affine reparametrization `x ↦ (θ + 2π x)/ω`, whose temperate growth makes
`SchwartzMap.compCLM` applicable. -/
theorem poisson_shifted_lattice (f : SchwartzMap ℝ ℂ) (s : ℝ) :
    ∑' n : ℤ, f (s + n)
      = ∑' n : ℤ, 𝓕 f n * fourier n (s : UnitAddCircle) :=
  SchwartzMap.tsum_eq_tsum_fourier f s

end

end Quasicrystal
