/-  AUDIT PROBE A2 (2026-09-22), node MM_torus_section_dictionary: what closes the dictionary
    identity and what does not.  NOT a lean_lib, NOT a default target.  Run by hand with

        cd telperion/examples/quasicrystal/lean && lake env lean Probes/AuditTorusDict_Probes.lean

    This file is EXPECTED TO FAIL to compile at exactly two places, P3a and P3f (see below);
    every other probe must elaborate.  The mirror definitions are re-declared with the
    artifact's bodies so the probes need no olean of the artifact.

    conjecture1_proved = False.  Nothing here proves, or approaches, RH. -/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import TwoFreqRigidity

open Complex

namespace Quasicrystal

noncomputable section

noncomputable def torusOrbit (N : ℕ) (lam : Fin N → ℝ) (x : ℂ) : Fin N → ℂ :=
  fun j => Complex.exp ((lam j : ℂ) * x * Complex.I)

def linearTorusForm (N : ℕ) (c : Fin N → ℂ) (z : Fin N → ℂ) : ℂ :=
  ∑ j, c j * z j

-- P3a  bare rfl.  EXPECTED TO FAIL: the Finset fold's trailing `+ 0` on ℂ is not
-- definitional (real addition is a quotient of Cauchy sequences), which is the readback's
-- reason and the reason Mathlib proves Fin.sum_univ_two by simp.
example (c₁ c₂ : ℂ) (lam₁ lam₂ : ℝ) (x : ℂ) :
    twoFreq c₁ c₂ lam₁ lam₂ x
      = linearTorusForm 2 ![c₁, c₂] (torusOrbit 2 ![lam₁, lam₂] x) := rfl

-- P3b  after the ONE sum unfolding, everything else is definitional: the four ![.,.]
-- projections, the real-to-complex casts and the delta-unfolding of twoFreq/torusOrbit
-- all close by rfl.  So the whole gap between the two sides is one rewrite.
example (c₁ c₂ : ℂ) (lam₁ lam₂ : ℝ) (x : ℂ) :
    twoFreq c₁ c₂ lam₁ lam₂ x
      = linearTorusForm 2 ![c₁, c₂] (torusOrbit 2 ![lam₁, lam₂] x) := by
  rw [linearTorusForm, Fin.sum_univ_two]; rfl

-- P3c  the explicit simp set the artifact header names (no simp-set search).  The linter
-- reports Matrix.head_cons unused: cons_val_one already lands on `u 0`, closed by cons_val_zero.
example (c₁ c₂ : ℂ) (lam₁ lam₂ : ℝ) (x : ℂ) :
    twoFreq c₁ c₂ lam₁ lam₂ x
      = linearTorusForm 2 ![c₁, c₂] (torusOrbit 2 ![lam₁, lam₂] x) := by
  simp only [twoFreq, linearTorusForm, torusOrbit, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

-- P3d  the artifact's exact tactic line (control)
example (c₁ c₂ : ℂ) (lam₁ lam₂ : ℝ) (x : ℂ) :
    twoFreq c₁ c₂ lam₁ lam₂ x
      = linearTorusForm 2 ![c₁, c₂] (torusOrbit 2 ![lam₁, lam₂] x) := by
  simp [twoFreq, linearTorusForm, torusOrbit, Fin.sum_univ_two]

-- P3e  Fin.sum_univ_two is @[simp] in this Mathlib, so naming it in the artifact is redundant.
example (c₁ c₂ : ℂ) (lam₁ lam₂ : ℝ) (x : ℂ) :
    twoFreq c₁ c₂ lam₁ lam₂ x
      = linearTorusForm 2 ![c₁, c₂] (torusOrbit 2 ![lam₁, lam₂] x) := by
  simp [twoFreq, linearTorusForm, torusOrbit]

-- P3f  NEGATIVE CONTROL, EXPECTED TO FAIL: with the coefficient literal reversed the same
-- tactic is left with c₁ e^{iλ₁x} + c₂ e^{iλ₂x} = c₂ e^{iλ₁x} + c₁ e^{iλ₂x}, so the
-- projections really are evaluated and the probe battery is discriminating.
example (c₁ c₂ : ℂ) (lam₁ lam₂ : ℝ) (x : ℂ) :
    twoFreq c₁ c₂ lam₁ lam₂ x
      = linearTorusForm 2 ![c₂, c₁] (torusOrbit 2 ![lam₁, lam₂] x) := by
  simp [twoFreq, linearTorusForm, torusOrbit, Fin.sum_univ_two]

end

end Quasicrystal
