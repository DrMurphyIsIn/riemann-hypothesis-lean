/-
  ProbeSatake.lean -- ANTI-TRIVIALITY PROBES for SatakeDegreeTwo (A1b).

  NOT a `lean_lib`, NOT part of the build.  Scratch harness: every `example`
  below is EXPECTED TO FAIL, and the failures are the evidence that the node's
  statements are not rfl/simp/decide-grade.  Run with

      lake env lean ProbeSatake.lean

  and read the error list.  A probe that SUCCEEDS is a finding against the node.

  The one probe expected to SUCCEED is the degenerate-specialization probe at the
  bottom: it proves the hypothesis-free version of the headline is FALSE, i.e. the
  `a * b = 1` hypothesis is load-bearing and the refutation is not vacuous.
-/
import SatakeDegreeTwo

namespace SatakeDegreeTwo

/-! ### Probe 1 -- the headline iff -/
example (a b : ℂ) : ScalarGenerated (powerSum a b) ↔ a * b = 0 := by rfl
example (a b : ℂ) : ScalarGenerated (powerSum a b) ↔ a * b = 0 := by simp
example (a b : ℂ) : ScalarGenerated (powerSum a b) ↔ a * b = 0 := by decide

/-! ### Probe 2 -- the GL(2) rejection -/
example (a b : ℂ) (h : a * b = 1) : ¬ ScalarGenerated (powerSum a b) := by rfl
example (a b : ℂ) (h : a * b = 1) : ¬ ScalarGenerated (powerSum a b) := by simp
example (a b : ℂ) (h : a * b = 1) : ¬ ScalarGenerated (powerSum a b) := by decide

/-! ### Probe 3 -- the Delta headline -/
example (a b : ℂ) (h : a * b = (satakeDetTwo : ℚ)) :
    ¬ ScalarGenerated (powerSum a b) := by rfl
example (a b : ℂ) (h : a * b = (satakeDetTwo : ℚ)) :
    ¬ ScalarGenerated (powerSum a b) := by simp
example (a b : ℂ) (h : a * b = (satakeDetTwo : ℚ)) :
    ¬ ScalarGenerated (powerSum a b) := by decide

/-! ### Probe 4 -- the re-derived Satake determinant (a computation, but Rat does
not kernel-reduce: `decide` and `rfl` must both fail; it is closed by `norm_num`
over the `decide`-proved integer facts `tau_two`/`tau_four`). -/
example : satakeDetTwo = 1 := by rfl
example : satakeDetTwo = 1 := by decide
example : satakeDetTwo = 1 := by simp

/-! ### Probe 5 -- non-vacuity existence -/
example (tr : ℂ) : ∃ a b : ℂ, a * b = 1 ∧ a + b = tr := by simp
example (tr : ℂ) : ∃ a b : ℂ, a * b = 1 ∧ a + b = tr := by decide

/-! ### Probe 6 -- DEGENERATE SPECIALIZATION (expected to SUCCEED).

Dropping the `a * b = 1` hypothesis makes the headline FALSE.  So the hypothesis
is load-bearing: the node does not refute `ScalarGenerated` for every layer, only
for the genuinely-degree-2 ones.  This is the anti-vacuity certificate. -/
theorem probe_hypothesis_is_load_bearing :
    ¬ (∀ a b : ℂ, ¬ ScalarGenerated (powerSum a b)) := by
  intro h
  exact h 1 0 (deg1_scalarGenerated 1)

/-- And the clause is not trivially satisfied either: it genuinely fails somewhere. -/
theorem probe_clause_not_universally_true :
    ¬ (∀ a b : ℂ, ScalarGenerated (powerSum a b)) := by
  intro h
  exact unitary_deg2_not_scalarGenerated 1 1 (by norm_num) (h 1 1)

end SatakeDegreeTwo
