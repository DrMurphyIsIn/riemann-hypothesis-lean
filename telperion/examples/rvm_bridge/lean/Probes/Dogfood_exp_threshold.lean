/-
  Dogfood_exp_threshold -- the Telperion `exp_threshold` kind (SHAPES_AUDIT_48H_2026-09-22.md
  section 2 rank 5; B N2) regenerating two hand-proof sites of this island, 2026-09-22:

    E6Bridge7.lean:554-590   the threshold lam0 = max 1 (max (A/(2 eta K)) (B/(2 M K))) and its two
                             exponential consequences hexpeta / hexpM, as ONE guarded linear bundle
                             (`gaussian_dominance_thresholds`; the eventual_threshold guard fold-in);
    E6Bridge14.lean:66-86    `le_exp_of_log_le` (log mode, `le_exp_of_log_le_regen`) and the two log
                             consequences of `effectiveThreshold` (`effectiveThreshold_consequences`).

  The block between the telperion provenance header and `end DogfoodExpThreshold` is the FROZEN
  emitter output (examples/rvm_bridge/dogfood_exp_threshold.py regenerates it; a test pins the
  bytes).  The cross-checks after it apply each regenerated theorem to the ORIGINAL's statement, so
  the kernel confirms the regeneration is interchangeable with the hand proof.  Nothing in
  E6Bridge7 / E6Bridge14 is modified.

  Run: cd telperion/examples/rvm_bridge/lean && lake env lean Probes/Dogfood_exp_threshold.lean
  Expected axioms for every theorem: [propext, Classical.choice, Quot.sound].

  conjecture1_proved = False.  Nothing here bears on RH: every statement is an elementary real
  inequality (a threshold hypothesis on a real parameter implies an exponential bound).
-/
/- telperion 0.1.6 | family DogfoodExpThreshold | input-hash 456577dfaf2f48dc
   3 theorems, 8 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import E6Bridge7
import E6Bridge14

namespace DogfoodExpThreshold

/-- `gaussian_dominance_thresholds` -- exp_threshold: linear bundle, 2 step(s), guarded by `max 1`.
    step 1: linear; scale 2; K-cleared; symbolic; threshold A/(2*K*eta);
    step 2: linear; scale 2; K-cleared; strict; symbolic; threshold B/(2*K*M);
    Route: each conjunct extracted from the nested `max` by a `le_max` chain,
    then `div_le_iff0` + `Real.add_one_le_exp` + `linarith` (linear) or
    `Real.exp_log (lt_max_of_lt_left one_pos)` + `Real.exp_le_exp` (log).
    An elementary real inequality re-derived in the kernel; the generator REFUSES
    a non-positive rational `a`/`K`/scale and a declared threshold that does not
    match its exact recomputation.  Nothing about zeros; nothing about RH.
    conjecture1_proved = False. -/
theorem gaussian_dominance_thresholds (A eta K B M lam : ℝ)
    (heta0 : 0 < eta) (hK0 : 0 < K) (hM0 : 0 < M)
    (h : max 1 (max (A / (2 * eta * K)) (B / (2 * M * K))) ≤ lam) :
    1 ≤ lam ∧ A ≤ K * Real.exp (2 * lam * eta) ∧ B < K * Real.exp (2 * lam * M) := by
  have hlam1 : 1 ≤ lam := (le_max_left _ _).trans h
  have ht1 : A / (2 * eta * K) ≤ lam := ((le_max_left _ _).trans (le_max_right _ _)).trans h
  have ht2 : B / (2 * M * K) ≤ lam := ((le_max_right _ _).trans (le_max_right _ _)).trans h
  refine ⟨hlam1, ?_, ?_⟩
  · have h1 : A / K ≤ 2 * lam * eta := by
      rw [div_le_iff₀ hK0]
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * eta * K)).mp ht1
      linarith
    have h2 : 2 * lam * eta + 1 ≤ Real.exp (2 * lam * eta) := Real.add_one_le_exp _
    have h3 : A / K ≤ Real.exp (2 * lam * eta) := by linarith
    rwa [div_le_iff₀ hK0, mul_comm] at h3
  · have h1 : B / K ≤ 2 * lam * M := by
      rw [div_le_iff₀ hK0]
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * M * K)).mp ht2
      linarith
    have h2 : 2 * lam * M + 1 ≤ Real.exp (2 * lam * M) := Real.add_one_le_exp _
    have h3 : B / K < Real.exp (2 * lam * M) := by linarith
    rwa [div_lt_iff₀ hK0, mul_comm] at h3

/-- `le_exp_of_log_le_regen` -- exp_threshold: log bundle, 1 step(s).
    step 1: log; scale 2; no K; symbolic; threshold log(Max(1, Q))/(2*a);
    Route: the threshold read directly from `h`,
    then `div_le_iff0` + `Real.add_one_le_exp` + `linarith` (linear) or
    `Real.exp_log (lt_max_of_lt_left one_pos)` + `Real.exp_le_exp` (log).
    An elementary real inequality re-derived in the kernel; the generator REFUSES
    a non-positive rational `a`/`K`/scale and a declared threshold that does not
    match its exact recomputation.  Nothing about zeros; nothing about RH.
    conjecture1_proved = False. -/
theorem le_exp_of_log_le_regen (Q a lam : ℝ)
    (ha0 : 0 < a)
    (h : Real.log (max 1 Q) / (2 * a) ≤ lam) :
    Q ≤ Real.exp (2 * lam * a) := by
  have hmax : 0 < max 1 Q := lt_max_of_lt_left one_pos
  have h1 : Real.log (max 1 Q) ≤ 2 * lam * a := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * a)).mp h
    linarith
  calc Q ≤ max 1 Q := le_max_right _ _
    _ = Real.exp (Real.log (max 1 Q)) := (Real.exp_log hmax).symm
    _ ≤ Real.exp (2 * lam * a) := Real.exp_le_exp.mpr h1

/-- `effectiveThreshold_consequences` -- exp_threshold: log bundle, 2 step(s), guarded by `max 1`.
    step 1: log; scale 2; no K; symbolic; threshold log(Max(1, Q1))/(2*a1);
    step 2: log; scale 2; no K; symbolic; threshold log(Max(1, Q2))/(2*a2);
    Route: each conjunct extracted from the nested `max` by a `le_max` chain,
    then `div_le_iff0` + `Real.add_one_le_exp` + `linarith` (linear) or
    `Real.exp_log (lt_max_of_lt_left one_pos)` + `Real.exp_le_exp` (log).
    An elementary real inequality re-derived in the kernel; the generator REFUSES
    a non-positive rational `a`/`K`/scale and a declared threshold that does not
    match its exact recomputation.  Nothing about zeros; nothing about RH.
    conjecture1_proved = False. -/
theorem effectiveThreshold_consequences (Q1 a1 Q2 a2 lam : ℝ)
    (ha10 : 0 < a1) (ha20 : 0 < a2)
    (h : max 1 (max (Real.log (max 1 Q1) / (2 * a1)) (Real.log (max 1 Q2) / (2 * a2))) ≤ lam) :
    1 ≤ lam ∧ Q1 ≤ Real.exp (2 * lam * a1) ∧ Q2 ≤ Real.exp (2 * lam * a2) := by
  have hlam1 : 1 ≤ lam := (le_max_left _ _).trans h
  have ht1 : Real.log (max 1 Q1) / (2 * a1) ≤ lam :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans h
  have ht2 : Real.log (max 1 Q2) / (2 * a2) ≤ lam :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans h
  refine ⟨hlam1, ?_, ?_⟩
  · have hmax : 0 < max 1 Q1 := lt_max_of_lt_left one_pos
    have h1 : Real.log (max 1 Q1) ≤ 2 * lam * a1 := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * a1)).mp ht1
      linarith
    calc Q1 ≤ max 1 Q1 := le_max_right _ _
      _ = Real.exp (Real.log (max 1 Q1)) := (Real.exp_log hmax).symm
      _ ≤ Real.exp (2 * lam * a1) := Real.exp_le_exp.mpr h1
  · have hmax : 0 < max 1 Q2 := lt_max_of_lt_left one_pos
    have h1 : Real.log (max 1 Q2) ≤ 2 * lam * a2 := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * a2)).mp ht2
      linarith
    calc Q2 ≤ max 1 Q2 := le_max_right _ _
      _ = Real.exp (Real.log (max 1 Q2)) := (Real.exp_log hmax).symm
      _ ≤ Real.exp (2 * lam * a2) := Real.exp_le_exp.mpr h1

end DogfoodExpThreshold

/-! ## Kernel cross-checks against the hand-written originals (generator-appended; the block above
    is the frozen emitter output).  Each `example` is closed by applying one side to the other's
    statement, so a drift in either statement fails to elaborate. -/

section CrossChecks
open DogfoodExpThreshold

/-- The regenerated log step proves the ORIGINAL `RvMBridge14.le_exp_of_log_le` statement. -/
example {Q a lam : ℝ} (ha : 0 < a) (h : Real.log (max 1 Q) / (2 * a) ≤ lam) :
    Q ≤ Real.exp (2 * lam * a) :=
  le_exp_of_log_le_regen Q a lam ha h

/-- ... and the original proves the regenerated statement: the two are interchangeable. -/
example (Q a lam : ℝ) (ha0 : 0 < a) (h : Real.log (max 1 Q) / (2 * a) ≤ lam) :
    Q ≤ Real.exp (2 * lam * a) :=
  RvMBridge14.le_exp_of_log_le ha0 h

/-- The guarded log bundle consumes `RvMBridge14.effectiveThreshold` by definitional unfolding and
    returns E6Bridge14's `hlam1`, `hQ1`, `hQ2` (E6Bridge14.lean:281-291) in one stroke. -/
example (y0 xmin : ℝ) (N : ℕ) (B D lam : ℝ) (hy0 : 0 < y0) (hx : 0 < xmin)
    (hlam : RvMBridge14.effectiveThreshold y0 xmin N B D ≤ lam) :
    1 ≤ lam ∧ 4 * N * (D ^ 2 + 1 / 4) / y0 ^ 2 ≤ Real.exp (2 * lam * xmin ^ 2)
      ∧ 4 * B / y0 ^ 2 ≤ Real.exp (2 * lam * y0 ^ 2) :=
  effectiveThreshold_consequences (4 * N * (D ^ 2 + 1 / 4) / y0 ^ 2) (xmin ^ 2)
    (4 * B / y0 ^ 2) (y0 ^ 2) lam (by positivity) (by positivity) hlam

/-- The guarded linear bundle yields E6Bridge7's `hexpeta` and `hexpM` (E6Bridge7.lean:575-590)
    from the `lam0 <= lam` hypothesis its `exists_lam_re_gaussTest` phase choice provides. -/
example (A eta K B M lam : ℝ) (heta : 0 < eta) (hK : 0 < K) (hM : 0 < M)
    (hlam : max 1 (max (A / (2 * eta * K)) (B / (2 * M * K))) ≤ lam) :
    A ≤ K * Real.exp (2 * lam * eta) ∧ B < K * Real.exp (2 * lam * M) :=
  (gaussian_dominance_thresholds A eta K B M lam heta hK hM hlam).2

end CrossChecks

#print axioms DogfoodExpThreshold.gaussian_dominance_thresholds
#print axioms DogfoodExpThreshold.le_exp_of_log_le_regen
#print axioms DogfoodExpThreshold.effectiveThreshold_consequences
