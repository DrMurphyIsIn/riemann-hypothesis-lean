/-  LeakageNode.lean -- PROGRAM MIRRORMERE, ROUTE A item A2b: the registry node.

    Registry node: MM_leakage_composite_zero (telperion/missions/mirrormere).
    The statement is mirrored VERBATIM from
      telperion/missions/mirrormere/lean/Statements/MM_leakage_composite_zero.lean
    into this island's namespace, where `CompletelyMultiplicative`,
    `IsLogDerivCoeff` and `dhKappa` are the island's own definitions (character for
    character the statement module's) and `leak_dh_amp` is the emitter-generated
    Davenport-Heilbronn amplitude of `LeakageInstances.lean`.

    Four conjuncts:
      (i)   the dictionary -- completely multiplicative => zero COMPOSITE amplitude;
      (ii)  non-vacuity -- the hypothesis class is inhabited by a NON-zero functional;
      (iii) the certified DH instance -- the leak exists and is pinned to the
            published b(6) = +1.9364, and DH is refused complete multiplicativity;
      (iv)  the falsification twin -- (i) without its hypothesis is FALSE.

    Conjunct (iv) is what separates this node from the `rfl`-grade von Mangoldt
    support statement the roadmap flagged as a trap: a support-level reading admits
    no counterexample, and this one has an explicit kernel-checked counterexample.

    NOTHING is discharged from outside the kernel: no Arb enclosure, no hypothesis,
    no `sorry`.  conjecture1_proved = False (NOT a proof of RH).

    GATE ALIGNMENT (2026-09-22).  The registry's statement module is the ONLY
    mirrormere statement that inlines its vocabulary (`CompletelyMultiplicative`,
    `IsLogDerivCoeff`, `dhKappa`, `leak_dh_amp`) instead of importing
    `Statements.MMDefs`, so the grant gate's normalized-containment check sees
    "four definitions + theorem" as ONE contiguous blob.  The theorem inside
    `namespace Quasicrystal` below writes the qualified `LeakageInstances.leak_dh_amp`
    and therefore does not contain that blob.  The trailing
    `namespace MMLeakageStatement` restates the four definitions and the theorem
    CHARACTER FOR CHARACTER from the statement module (spliced mechanically from
    that file, not retyped) and discharges it by the island theorem
    `Quasicrystal.leakage_composite_zero`: each local definition is
    delta-definitionally equal to the island's (`Quasicrystal.CompletelyMultiplicative`,
    `Quasicrystal.IsLogDerivCoeff`, `Quasicrystal.dhKappa`,
    `LeakageInstances.leak_dh_amp`), so the discharge is a bare `exact`.  No new
    mathematics; the mirror exists only so that the registry text and the kernel
    term coincide.  Guarded in AxiomGuardLeakage.lean.
-/
import LeakageDictionary
import LeakageInstances

namespace Quasicrystal

/-- **MM_leakage_composite_zero** -- the leakage dictionary, its non-vacuity, the
    certified Davenport-Heilbronn instance, and the falsification twin. -/
theorem leakage_composite_zero :
    (∀ a b : ℕ → ℝ, CompletelyMultiplicative a → IsLogDerivCoeff a b →
        ∀ n : ℕ, 0 < n → ¬ IsPrimePow n → b n = 0)
    ∧ (∃ a b : ℕ → ℝ, CompletelyMultiplicative a ∧ IsLogDerivCoeff a b ∧
        b 2 ≠ 0 ∧ b 6 = 0)
    ∧ (∃ b : ℕ → ℝ, IsLogDerivCoeff LeakageInstances.leak_dh_amp b ∧
        (1.93635 : ℝ) < b 6 ∧ b 6 < (1.93636 : ℝ) ∧
        ¬ CompletelyMultiplicative LeakageInstances.leak_dh_amp)
    ∧ ¬ (∀ a b : ℕ → ℝ, a 1 = 1 → IsLogDerivCoeff a b →
        ∀ n : ℕ, 0 < n → ¬ IsPrimePow n → b n = 0) := by
  refine ⟨fun a b ha hb n hn hcomp => composite_bragg_amplitude_zero ha hb hn hcomp,
    exists_nondegenerate_cm_logDerivCoeff, ?_,
    LeakageInstances.leak_dh_multiplicativity_is_necessary⟩
  obtain ⟨b, hb⟩ := exists_logDerivCoeff (a := LeakageInstances.leak_dh_amp)
    (by norm_num [LeakageInstances.leak_dh_amp])
  obtain ⟨h1, h2⟩ := LeakageInstances.leak_dh_enclosure_decimal hb
  exact ⟨b, hb, by norm_num at h1 ⊢; linarith, by norm_num at h2 ⊢; linarith,
    LeakageInstances.leak_dh_not_completelyMultiplicative hb⟩

end Quasicrystal

/-! ## Registry gate mirror

    Everything from here to `end MMLeakageStatement` is the statement module
    `telperion/missions/mirrormere/lean/Statements/MM_leakage_composite_zero.lean`
    (node sha256 cad2aacc0c051f38) with its `import`/`open` header removed and its
    placeholder proof replaced by the island theorem.  Do not edit the definitions
    or the theorem statement: the grant gate is normalized-text containment, so any
    character-level drift from the statement module breaks the match.
    conjecture1_proved = False. -/

open Finset

namespace MMLeakageStatement

-- ===== MIRROR of Statements/MM_leakage_composite_zero.lean (four inlined
-- definitions + theorem), VERBATIM.  The proof is the only change. =====

/-- A completely multiplicative amplitude sequence (the Dirichlet-coefficient form
    of "the series has an Euler product with degree-1 local factors"). -/
def CompletelyMultiplicative (a : ℕ → ℝ) : Prop :=
  a 1 = 1 ∧ ∀ m n : ℕ, a (m * n) = a m * a n

/-- `b` is THE log-derivative coefficient functional of `a`: the Dirichlet
    coefficients of `-F'/F` for `F (s) = ∑ a n * n ^ (-s)`, pinned by the divisor
    recursion.  These are the Bragg amplitudes of the comb. -/
def IsLogDerivCoeff (a b : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → a n * Real.log n = ∑ d ∈ n.divisors, b d * a (n / d)

/-- The exact Davenport-Heilbronn constant `κ = (√(10 − 2√5) − 2)/(√5 − 1)`. -/
noncomputable def dhKappa : ℝ := (Real.sqrt (10 - 2 * Real.sqrt 5) - 2) / (Real.sqrt 5 - 1)

/-- The Davenport-Heilbronn amplitude: period 5, `[1, κ, −κ, −1, 0]`.  DH satisfies a
    Riemann-type functional equation but has NO Euler product, and has zeros off the
    critical line: this program's standing negative control. -/
noncomputable def leak_dh_amp : ℕ → ℝ := fun n =>
  if n % 5 = 1 then 1 else
  if n % 5 = 2 then dhKappa else
  if n % 5 = 3 then -dhKappa else
  if n % 5 = 4 then -1 else 0

theorem leakage_composite_zero :
    -- (i) THE DICTIONARY.  A completely multiplicative amplitude has ZERO Bragg
    --     amplitude at every COMPOSITE (non-prime-power) frequency `log n`.
    (∀ a b : ℕ → ℝ, CompletelyMultiplicative a → IsLogDerivCoeff a b →
        ∀ n : ℕ, 0 < n → ¬ IsPrimePow n → b n = 0)
    -- (ii) NON-VACUITY.  The hypotheses of (i) are inhabited by a functional that is
    --      NOT identically zero, so its conclusion is not the trivial `b = 0`.
    ∧ (∃ a b : ℕ → ℝ, CompletelyMultiplicative a ∧ IsLogDerivCoeff a b ∧
        b 2 ≠ 0 ∧ b 6 = 0)
    -- (iii) THE CERTIFIED DAVENPORT-HEILBRONN INSTANCE.  The DH amplitude LEAKS at
    --       the first composite frequency `log 6` -- its functional exists and is
    --       pinned to the published `b(6) = +1.9364` -- and DH is thereby REFUSED
    --       complete multiplicativity.
    ∧ (∃ b : ℕ → ℝ, IsLogDerivCoeff leak_dh_amp b ∧
        (1.93635 : ℝ) < b 6 ∧ b 6 < (1.93636 : ℝ) ∧
        ¬ CompletelyMultiplicative leak_dh_amp)
    -- (iv) THE FALSIFICATION TWIN.  Statement (i) WITHOUT its multiplicativity
    --      hypothesis is FALSE.  So the hypothesis is load-bearing, and (i) is not
    --      the `rfl`-grade von Mangoldt support fact in disguise: a support-level
    --      reading admits no counterexample.
    ∧ ¬ (∀ a b : ℕ → ℝ, a 1 = 1 → IsLogDerivCoeff a b →
        ∀ n : ℕ, 0 < n → ¬ IsPrimePow n → b n = 0) :=
  Quasicrystal.leakage_composite_zero

end MMLeakageStatement
