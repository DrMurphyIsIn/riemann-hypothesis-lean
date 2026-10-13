/-
  DBNM4P15Defs -- lane m4 (Route C milestone M4, synthesis
  telperion/docs/ROUTE_C_SYNTHESIS_2026-09-23.md sections 5.2 and 7.2): vocabulary only.

  * The three hypotheses of Polymath15's zero-free region criterion, Proposition 3.3 of
    D.H.J. Polymath, "Effective approximation of heat flow evolution of the Riemann xi function,
    and a new upper bound for the de Bruijn-Newman constant", Res. Math. Sci. 6 (2019) art. 31,
    arXiv:1904.12438v2, p.15, transcribed verbatim in `H_t` form (z = x + iy):

      (i)   There are no zeroes H_0(x + iy) = 0 with 0 ≤ x ≤ X and √(y0² + 2t0) ≤ y ≤ 1.
      (ii)  There are no zeroes H_{t0}(x + iy) = 0 with x ≥ X + √(1 − y0²) and
            y0 ≤ y ≤ √(1 − 2t0).
      (iii) There are no zeroes H_t(x + iy) = 0 with X ≤ x ≤ X + √(1 − y0²),
            √(y0² + 2(t0 − t)) ≤ y ≤ √(1 − 2t), and 0 ≤ t ≤ t0.

    The side conditions of Prop 3.3 ("t0, X > 0 and 0 < y0 ≤ 1") are NOT folded into the Props;
    they are explicit hypotheses of the theorems that consume them (`DBNM4P15Criterion`), as in
    the synthesis sketch of `RH_dbn_p15_criterion`.  `Real.sqrt` of a negative number is `0` in
    Mathlib; in each such case the transcribed `y`-range is empty (its lower end is `≥ y0 > 0`),
    matching the paper, where those ranges are empty.

  * `M1aStep`: the parametric de Bruijn step (P15 Thm 3.2 / de Bruijn 1950 Thm 13), statement
    verbatim from synthesis section 7.2 node `RH_dbn_debruijn_parametric` (M1a, lane m1).  It is a
    named HYPOTHESIS here; this module does not prove it.

  Definitions only.  Nothing here proves RH or bounds the de Bruijn-Newman constant (which is not
  defined on this island).  conjecture1_proved = False.
-/
import DBNDefs

namespace DBN

/-- **P15 Prop 3.3 (i)**, verbatim: "There are no zeroes `H_0(x + iy) = 0` with `0 ≤ x ≤ X` and
`√(y0² + 2t0) ≤ y ≤ 1`." -/
def P15ZeroFreeRect (X y0 t0 : ℝ) : Prop :=
  ∀ x y : ℝ, 0 ≤ x → x ≤ X → Real.sqrt (y0 ^ 2 + 2 * t0) ≤ y → y ≤ 1 →
    H 0 ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0

/-- **P15 Prop 3.3 (ii)**, verbatim: "There are no zeroes `H_{t0}(x + iy) = 0` with
`x ≥ X + √(1 − y0²)` and `y0 ≤ y ≤ √(1 − 2t0)`." -/
def P15Canopy (X y0 t0 : ℝ) : Prop :=
  ∀ x y : ℝ, X + Real.sqrt (1 - y0 ^ 2) ≤ x → y0 ≤ y → y ≤ Real.sqrt (1 - 2 * t0) →
    H t0 ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0

/-- **P15 Prop 3.3 (iii)**, verbatim: "There are no zeroes `H_t(x + iy) = 0` with
`X ≤ x ≤ X + √(1 − y0²)`, `√(y0² + 2(t0 − t)) ≤ y ≤ √(1 − 2t)`, and `0 ≤ t ≤ t0`." -/
def P15Barrier (X y0 t0 : ℝ) : Prop :=
  ∀ t x y : ℝ, X ≤ x → x ≤ X + Real.sqrt (1 - y0 ^ 2) →
    Real.sqrt (y0 ^ 2 + 2 * (t0 - t)) ≤ y → y ≤ Real.sqrt (1 - 2 * t) → 0 ≤ t → t ≤ t0 →
    H t ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0

/-- **The parametric de Bruijn step (M1a), as a named hypothesis.**  Statement verbatim from
synthesis section 7.2 (`RH_dbn_debruijn_parametric`): if every zero of `H_{t0}` has
`(Im z)² ≤ Y`, then for `t ≥ t0` every zero of `H_t` has `(Im z)² ≤ max (Y − 2(t − t0)) 0`.
NOT proved in lane m4 (lane m1 proves it). -/
def M1aStep : Prop :=
  ∀ t0 Y : ℝ, (∀ z : ℂ, H t0 z = 0 → z.im ^ 2 ≤ Y) →
    ∀ t : ℝ, t0 ≤ t → ∀ z : ℂ, H t z = 0 → z.im ^ 2 ≤ max (Y - 2 * (t - t0)) 0

end DBN
