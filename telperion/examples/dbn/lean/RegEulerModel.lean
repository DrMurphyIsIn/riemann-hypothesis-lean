import DBNEulerModelRH

/-!
# Registry-shape statement: the finite Euler-product model is zero-free near the line (2026-10-14)

One root-namespace theorem whose statement is the registry statement of `RH_dbn_euler_model_zero_free`
VERBATIM (fully qualified; the vocabulary `primesUpTo`, `eulerX`, `chiM`, `ZX`, `LamX` is mirrored verbatim
into missions/rh/lean/Statements/RHDefs.lean), proved from `DBNEulerModel.ZX_ne_zero`:
* `euler_model_ZX_ne_zero` : for the MODEL Z_X(s) = E_X(s) + χ(s) E_X(1-s), E_X the Euler product over
                             p <= X and χ the functional-equation factor, Z_X(σ + it) ≠ 0 whenever
                             0 < |σ - 1/2| <= y < 1/2 and log(t/2π) - 1/t - 2/t² > Λ_X(y).
A statement about a MODEL (finite Euler product + χ), NOT about ζ: a folklore-grade companion to
Gonek (2012), Theorem 6.2.  Nothing here bears on RH.  conjecture1_proved = False.
-/

/-- Registry shape of `RH_dbn_euler_model_zero_free`. -/
theorem euler_model_ZX_ne_zero (X : ℕ) {y t : ℝ} (hy : y < 1 / 2) (ht : 0 < t)
    (hK : Real.log (t / (2 * Real.pi)) - 1 / t - 2 / t ^ 2 > DBNEulerModel.LamX X y)
    {σ : ℝ} (hσ : 0 < |σ - 1 / 2|) (hσy : |σ - 1 / 2| ≤ y) :
    DBNEulerModel.ZX X ((σ : ℂ) + t * Complex.I) ≠ 0 :=
  DBNEulerModel.ZX_ne_zero X hy ht hK hσ hσy
