import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Lemma S step 1, abstract core (e9, 2026-10-13)

Model: gradients of a continuous piecewise-affine function in the four sectors around a crossing of a graph ray
(direction `(1, μ)`) with a vertical fibre (direction `(0, 1)`). Continuity across each boundary ray `d` says the
gradient jump across it is orthogonal to `d`. The jump of the graph crease is measured along its normal `(μ, -1)`.

* `ray_jump_preserved_vertical` / `_horizontal`: a fibre crossing does not change the graph's normal jump.
* `jump_zero_of_monodromy`: a jump equal to itself divided by `p > 1` (the diagonal-loop monodromy) is zero.
* `graph_coefficient_zero`: along a loop of fibre crossings with monodromy `1/p`, the graph coefficient vanishes.

conjecture1_proved = False; this is about the single-orbit square only.
-/

namespace LemmaSCore

/-- Dot product on `ℝ × ℝ`. -/
def dot (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2

/-- Normal jump of the graph crease across a vertical-fibre crossing is preserved. Sectors in counterclockwise
order: `g4 | ray-out (1,μ) | g1 | fibre-up (0,1) | g2 | ray-in (-1,-μ) | g3 | fibre-down (0,-1) | g4`. -/
theorem ray_jump_preserved_vertical (μ : ℝ) (g1 g2 g3 g4 : ℝ × ℝ)
    (h1 : dot (g1 - g4) (1, μ) = 0) (h2 : dot (g2 - g1) (0, 1) = 0)
    (h3 : dot (g3 - g2) (-1, -μ) = 0) (h4 : dot (g4 - g3) (0, -1) = 0) :
    dot (g1 - g4) (μ, -1) = dot (g2 - g3) (μ, -1) := by
  simp only [dot, Prod.fst_sub, Prod.snd_sub] at *
  linear_combination μ * h1 - μ * h3 + (1 + μ ^ 2) * h2 - (1 + μ ^ 2) * h4

/-- Same for a horizontal fibre (direction `(1, 0)`): sectors
`g4 | ray-out (1,μ) | g1 | fibre-left (-1,0) | g2 | ray-in (-1,-μ) | g3 | fibre-right (1,0) | g4`. -/
theorem ray_jump_preserved_horizontal (μ : ℝ) (hμ : μ ≠ 0) (g1 g2 g3 g4 : ℝ × ℝ)
    (h1 : dot (g1 - g4) (1, μ) = 0) (h2 : dot (g2 - g1) (-1, 0) = 0)
    (h3 : dot (g3 - g2) (-1, -μ) = 0) (h4 : dot (g4 - g3) (1, 0) = 0) :
    dot (g1 - g4) (μ, -1) = dot (g2 - g3) (μ, -1) := by
  simp only [dot, Prod.fst_sub, Prod.snd_sub] at *
  have e1 : g2.1 = g1.1 := by linarith
  have e2 : g4.1 = g3.1 := by linarith
  have e5 : μ * ((g1.2 - g4.2) - (g2.2 - g3.2)) = 0 := by
    linear_combination h1 - h3 - h2 + h4
  have e6 : (g1.2 - g4.2) - (g2.2 - g3.2) = 0 := by
    rcases mul_eq_zero.mp e5 with h | h
    · exact absurd h hμ
    · exact h
  have e7 : (g1.1 - g4.1) - (g2.1 - g3.1) = 0 := by
    linear_combination h2 - h4
  linear_combination μ * e7 - e6

/-- Monodromy: a jump equal to itself divided by `p > 1` is zero. -/
theorem jump_zero_of_monodromy {p c : ℝ} (hp : 1 < p) (h : c = c / p) : c = 0 := by
  have hp0 : (0 : ℝ) < p := by linarith
  have : c * p = c := by
    calc c * p = (c / p) * p := by rw [← h]
      _ = c := by field_simp
  have : c * (p - 1) = 0 := by linarith
  rcases mul_eq_zero.mp this with h' | h'
  · exact h'
  · linarith

/-- Along a loop of fibre crossings the graph's normal jump is a constant `c` (each crossing preserves it); the
diagonal loop returns it as `c / p`. Hence the graph coefficient is zero. -/
theorem graph_coefficient_zero {p : ℝ} (hp : 1 < p) (c : ℕ → ℝ) (n : ℕ)
    (hstep : ∀ k < n, c (k + 1) = c k) (hloop : c n = c 0 / p) : c 0 = 0 := by
  have hconst : ∀ k ≤ n, c k = c 0 := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih => rw [hstep k (by omega), ih (by omega)]
  have hn := hconst n le_rfl
  rw [hn] at hloop
  exact jump_zero_of_monodromy hp hloop

end LemmaSCore
