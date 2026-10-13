/-  LeakageDictionary.lean -- PROGRAM MIRRORMERE, ROUTE A item A2b.

    HAND-WRITTEN island theory.  The certified INSTANCES live in the emitted
    `LeakageInstances.lean` (telperion/examples/leakage_dictionary/generate.py,
    kind `leakage_dictionary`, drift-gated by `--check`).

    Registry node: MM_leakage_composite_zero_dh (campaign mirrormere).

    THE LEAKAGE DICTIONARY, as kernel lemmas:

        completely-multiplicative amplitude  ==>  zero COMPOSITE Bragg amplitude

    WHAT IS BEING CLAIMED -- and the trivial-direction trap.  The roadmap
    (RH_ROUTES_ROADMAP_2026-09-16.md, item A2b) flags that one direction of this
    dictionary is `rfl`-grade: that the von Mangoldt function is supported on
    prime powers is, in Mathlib, `vonMangoldt_eq_zero_iff`, an unfolding of the
    definitional body `if IsPrimePow n then Real.log (minFac n) else 0`.  That is
    NOT the content here, and it is deliberately isolated below as
    `vonMangoldt_support_is_definitional` so that a reader can see exactly which
    half is free.

    The content is the LOG-DERIVATIVE COEFFICIENT FUNCTIONAL.  For an amplitude
    sequence `a : N -> R` the Bragg amplitudes of the associated comb are the
    Dirichlet coefficients `b` of `-F'/F`, `F(s) = sum_n a n * n^(-s)`, pinned by
    the exact divisor recursion

        `IsLogDerivCoeff a b  :  a n * log n = sum_{d in n.divisors} b d * a (n/d)`

    for every `n >= 1`.  `b` is specified only IMPLICITLY: its support is not
    visible in the definition, and for a general `a` it is supported at composites
    (the Davenport-Heilbronn instance has `b 6 > 0`).  The theorem
    `composite_bragg_amplitude_zero` says that complete multiplicativity of `a`
    forces `b = Lambda * a`, hence `b n = 0` at every non-prime-power `n`.  Its
    proof consumes (i) uniqueness for the recursion (strong induction, peeling the
    `d = n` term, `logDerivCoeff_unique`) and (ii) `sum_{d|n} Lambda d = log n`
    routed through `a d * a (n/d) = a n` (`vonMangoldt_mul_isLogDerivCoeff`).

    NON-VACUITY, both directions.  `exists_logDerivCoeff` constructs the functional
    by strong recursion, so every conditional theorem here and in the instances file
    has inhabited hypotheses.  `exists_nondegenerate_cm_logDerivCoeff` exhibits a
    completely-multiplicative amplitude whose functional is NOT identically zero
    (`b 2 = log 2 != 0`), so the conclusion is not the trivial `b = 0`.  And the
    emitted instances file refutes the hypothesis-free statement in-kernel with the
    Davenport-Heilbronn amplitude -- this program's standing NEGATIVE CONTROL
    (functional equation, no Euler product, zeros off the critical line).

    SECTION 5 carries the algebraic and transcendental CONSTANTS the certified
    instances consume: the exact DH constant `kappa` with a kernel-proved rational
    enclosure, and rational enclosures of `log 2`, `log 3`.

    SCOPE.  This is a statement about Dirichlet coefficients of a logarithmic
    derivative.  It says NOTHING about zeros, about temperedness, or about the
    membership wall (A5).  `conjecture1_proved = False`.
-/
import Mathlib

open Finset ArithmeticFunction
open scoped ArithmeticFunction

namespace Quasicrystal

/-! ## 1.  The two vocabularies -/

/-- `a` is a **completely multiplicative** amplitude sequence: normalized at 1 and
    multiplicative across EVERY pair, not merely coprime pairs.  This is the
    Dirichlet-coefficient form of "the series has an Euler product with degree-1
    local factors". -/
def CompletelyMultiplicative (a : ℕ → ℝ) : Prop :=
  a 1 = 1 ∧ ∀ m n : ℕ, a (m * n) = a m * a n

/-- `b` is **the log-derivative coefficient functional** of the amplitude `a`:
    the Dirichlet coefficient sequence of `-F'/F` for `F (s) = ∑ a n * n ^ (-s)`,
    pinned by the exact divisor recursion obtained from `F' = -F * (-F'/F)` by
    comparing coefficients.  These are the Bragg amplitudes of the comb, before
    the archimedean weight.

    NOTE the shape of the definition: `b` is specified only IMPLICITLY, and
    nothing about its support is readable off it. -/
def IsLogDerivCoeff (a b : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → a n * Real.log n = ∑ d ∈ n.divisors, b d * a (n / d)

/-- The archimedean-weighted Bragg amplitude at frequency `log n`. -/
noncomputable def braggAmplitude (b : ℕ → ℝ) (n : ℕ) : ℝ := b n / Real.sqrt n

/-! ## 2.  The trivial half, isolated on purpose

    This is the `rfl`-grade direction the roadmap warns about.  It is recorded
    here ONLY so that the reader can see that the theorems of section 3 do not
    live on it: it is a fact about `Λ`'s definitional body, with no reference to
    the recursion, to `a`, or to multiplicativity. -/

/-- The trivial-direction trap, named and quarantined: von Mangoldt's support is
    definitional (`Λ n = if IsPrimePow n then Real.log (minFac n) else 0`), so
    this closes by `simp` on the defining `if`.  It carries NO information about
    the log-derivative coefficient functional. -/
theorem vonMangoldt_support_is_definitional {n : ℕ} (h : ¬ IsPrimePow n) : Λ n = 0 := by
  simp [ArithmeticFunction.vonMangoldt_apply, h]

/-! ## 3.  The content: the log-derivative coefficient functional -/

/-- Peel the `d = n` term off the recursion.  Uses `a 1 = 1`. -/
theorem logDerivCoeff_peel {a c : ℕ → ℝ} (ha : a 1 = 1) (hc : IsLogDerivCoeff a c)
    {n : ℕ} (hn : 0 < n) :
    a n * Real.log n = c n + ∑ d ∈ n.divisors.erase n, c d * a (n / d) := by
  have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hn.ne'
  have h := hc n hn
  rw [← Finset.add_sum_erase _ _ hmem] at h
  rw [h, Nat.div_self hn, ha, mul_one]

/-- **Uniqueness of the functional.**  The divisor recursion determines `b` on the
    positives: every proper divisor `d` of `n` is `< n`, so the peeled recursion is
    a strong-induction definition of `b n`.  This is the step that makes the
    dictionary a statement about a FUNCTIONAL rather than about a formula. -/
theorem logDerivCoeff_unique {a b b' : ℕ → ℝ} (ha : a 1 = 1)
    (hb : IsLogDerivCoeff a b) (hb' : IsLogDerivCoeff a b') :
    ∀ n : ℕ, 0 < n → b n = b' n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have h1 := logDerivCoeff_peel ha hb hn
    have h2 := logDerivCoeff_peel ha hb' hn
    have hsum : ∑ d ∈ n.divisors.erase n, b d * a (n / d)
        = ∑ d ∈ n.divisors.erase n, b' d * a (n / d) := by
      refine Finset.sum_congr rfl ?_
      intro d hd
      have hdne : d ≠ n := (Finset.mem_erase.mp hd).1
      obtain ⟨hdvd, _⟩ := Nat.mem_divisors.mp (Finset.mem_erase.mp hd).2
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
      have hdlt : d < n := lt_of_le_of_ne (Nat.le_of_dvd hn hdvd) hdne
      rw [ih d hdlt hdpos]
    rw [hsum] at h1
    linarith [h1, h2]

/-! ### The functional EXISTS (the vacuity gate)

    Every theorem below is of the form "for any `b` satisfying the recursion ...".
    Such statements are worthless if no `b` satisfies it.  The recursion is
    solvable by strong recursion whenever `a 1 = 1`, and the construction is
    recorded here so that the conditional theorems are demonstrably non-vacuous. -/

/-- The log-derivative coefficient functional, constructed by strong recursion:
    `b n = a n log n - ∑_{d ∣ n, d ≠ n} b d * a (n / d)`. -/
noncomputable def logDerivCoeffOf (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  a n * Real.log n - ∑ d ∈ (n.divisors.erase n).attach,
    logDerivCoeffOf a d.1 * a (n / d.1)
decreasing_by
  have hd := d.2
  have hdne : (d : ℕ) ≠ n := (Finset.mem_erase.mp hd).1
  obtain ⟨hdvd, hn0⟩ := Nat.mem_divisors.mp (Finset.mem_erase.mp hd).2
  exact lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd) hdne

theorem logDerivCoeffOf_spec {a : ℕ → ℝ} (ha : a 1 = 1) :
    IsLogDerivCoeff a (logDerivCoeffOf a) := by
  intro n hn
  have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hn.ne'
  rw [← Finset.add_sum_erase _ _ hmem, Nat.div_self hn, ha, mul_one]
  rw [show logDerivCoeffOf a n = a n * Real.log n - ∑ d ∈ (n.divisors.erase n).attach,
      logDerivCoeffOf a d.1 * a (n / d.1) from by rw [logDerivCoeffOf]]
  rw [Finset.sum_attach (n.divisors.erase n) (fun d => logDerivCoeffOf a d * a (n / d))]
  ring

/-- **The vacuity gate.**  Normalization `a 1 = 1` alone makes the recursion
    solvable, so every conditional theorem below has inhabited hypotheses. -/
theorem exists_logDerivCoeff {a : ℕ → ℝ} (ha : a 1 = 1) : ∃ b, IsLogDerivCoeff a b :=
  ⟨_, logDerivCoeffOf_spec ha⟩

/-- **Complete multiplicativity solves the recursion.**  The candidate `Λ · a`
    satisfies the divisor recursion, because `a d * a (n / d) = a n` collapses the
    convolution onto `∑_{d ∣ n} Λ d = log n` (`ArithmeticFunction.vonMangoldt_sum`).
    This is where multiplicativity is actually spent. -/
theorem vonMangoldt_mul_isLogDerivCoeff {a : ℕ → ℝ} (ha : CompletelyMultiplicative a) :
    IsLogDerivCoeff a (fun n => Λ n * a n) := by
  intro n hn
  have hcong : ∀ d ∈ n.divisors, Λ d * a d * a (n / d) = Λ d * a n := by
    intro d hd
    obtain ⟨hdvd, _⟩ := Nat.mem_divisors.mp hd
    have hmul : a d * a (n / d) = a n := by
      rw [← ha.2, Nat.mul_div_cancel' hdvd]
    rw [mul_assoc, hmul]
  simp only []
  rw [Finset.sum_congr rfl hcong, ← Finset.sum_mul, ArithmeticFunction.vonMangoldt_sum]
  ring

/-- The dictionary in its sharp form: for a completely multiplicative amplitude the
    log-derivative coefficient functional IS `Λ · a`. -/
theorem logDerivCoeff_eq_vonMangoldt_mul {a b : ℕ → ℝ}
    (ha : CompletelyMultiplicative a) (hb : IsLogDerivCoeff a b) {n : ℕ} (hn : 0 < n) :
    b n = Λ n * a n :=
  logDerivCoeff_unique ha.1 hb (vonMangoldt_mul_isLogDerivCoeff ha) n hn

/-- **THE LEAKAGE DICTIONARY.**  A completely multiplicative amplitude has ZERO
    Bragg amplitude at every composite (non-prime-power) frequency `log n`.

    This is NOT the `Λ`-support statement of section 2: the hypothesis is about
    `a`, the conclusion is about the implicitly-defined functional `b`, and the
    proof routes through uniqueness of the recursion.  Dropping `ha` makes the
    statement false -- see `dh_b_six_pos`. -/
theorem composite_bragg_amplitude_zero {a b : ℕ → ℝ}
    (ha : CompletelyMultiplicative a) (hb : IsLogDerivCoeff a b)
    {n : ℕ} (hn : 0 < n) (hcomp : ¬ IsPrimePow n) : b n = 0 := by
  rw [logDerivCoeff_eq_vonMangoldt_mul ha hb hn,
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hcomp, zero_mul]

/-- The same statement in archimedean-weighted (diffraction) coordinates. -/
theorem composite_braggAmplitude_zero {a b : ℕ → ℝ}
    (ha : CompletelyMultiplicative a) (hb : IsLogDerivCoeff a b)
    {n : ℕ} (hn : 0 < n) (hcomp : ¬ IsPrimePow n) : braggAmplitude b n = 0 := by
  rw [braggAmplitude, composite_bragg_amplitude_zero ha hb hn hcomp, zero_div]

/-- **The instrument, contrapositive.**  A nonzero composite Bragg amplitude
    REFUSES complete multiplicativity of the amplitude sequence.  This is the
    direction the falsification zoo consumes. -/
theorem not_completelyMultiplicative_of_composite_leak {a b : ℕ → ℝ}
    (hb : IsLogDerivCoeff a b) {n : ℕ} (hn : 0 < n) (hcomp : ¬ IsPrimePow n)
    (hleak : b n ≠ 0) : ¬ CompletelyMultiplicative a := by
  intro ha
  exact hleak (composite_bragg_amplitude_zero ha hb hn hcomp)

/-! ## 4.  Positive control: the completely-multiplicative (zeta) fiber

    `a ≡ 1` is the zeta fiber of the dictionary: `F = ζ`, `-ζ'/ζ = ∑ Λ n n^(-s)`.
    It witnesses that the hypothesis class of section 3 is INHABITED and that the
    conclusion is not the trivial `b ≡ 0`. -/

/-- The zeta-fiber amplitude. -/
def zetaAmp : ℕ → ℝ := fun _ => 1

theorem zetaAmp_completelyMultiplicative : CompletelyMultiplicative zetaAmp :=
  ⟨rfl, fun _ _ => by simp [zetaAmp]⟩

theorem zetaAmp_logDerivCoeff : IsLogDerivCoeff zetaAmp (fun n => Λ n) := by
  have h := vonMangoldt_mul_isLogDerivCoeff zetaAmp_completelyMultiplicative
  simpa [zetaAmp] using h

/-- Positive control, first direction: a completely multiplicative input certifies
    a ZERO composite amplitude.  `6` is the first composite frequency. -/
theorem zeta_composite_amplitude_zero {b : ℕ → ℝ} (hb : IsLogDerivCoeff zetaAmp b) :
    b 6 = 0 :=
  composite_bragg_amplitude_zero zetaAmp_completelyMultiplicative hb (by norm_num)
    (by decide)

/-- ... and the functional is NOT identically zero, so the vanishing above has
    content: at the prime frequency `log 2` the amplitude is `log 2 > 0`. -/
theorem zeta_prime_amplitude_ne_zero {b : ℕ → ℝ} (hb : IsLogDerivCoeff zetaAmp b) :
    b 2 ≠ 0 := by
  have h : b 2 = Λ 2 * zetaAmp 2 :=
    logDerivCoeff_eq_vonMangoldt_mul zetaAmp_completelyMultiplicative hb (by norm_num)
  rw [h, zetaAmp, mul_one, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  exact ne_of_gt (Real.log_pos (by norm_num))

/-- **Non-vacuity witness.**  The hypotheses of `composite_bragg_amplitude_zero`
    are satisfiable by a functional that is not identically zero, so the theorem
    is not vacuous and its conclusion is not the trivial `b = 0`. -/
theorem exists_nondegenerate_cm_logDerivCoeff :
    ∃ a b : ℕ → ℝ, CompletelyMultiplicative a ∧ IsLogDerivCoeff a b ∧ b 2 ≠ 0 ∧ b 6 = 0 :=
  ⟨zetaAmp, fun n => Λ n, zetaAmp_completelyMultiplicative, zetaAmp_logDerivCoeff,
    zeta_prime_amplitude_ne_zero zetaAmp_logDerivCoeff,
    zeta_composite_amplitude_zero zetaAmp_logDerivCoeff⟩


/-! ## 5.  Constants for the certified instances

    Everything below is kernel arithmetic from `Real.sq_sqrt`,
    `Real.log_two_{gt,lt}_d9` and Mathlib's log Taylor estimate
    `Real.abs_log_sub_add_sum_range_le`.  No Arb input, no discharged hypothesis.

    The Davenport-Heilbronn constant (QC_DH_SCOUT.md section 1, cross-checked
    against Franca-LeClair eq. (245)-(247) and Ferry-Isaila-Pantazi section 2) is
    the only algebraic constant the instances need. -/

/-- The exact DH constant `kappa = (sqrt(10 - 2 sqrt 5) - 2)/(sqrt 5 - 1)`. -/
noncomputable def dhKappa : ℝ := (Real.sqrt (10 - 2 * Real.sqrt 5) - 2) / (Real.sqrt 5 - 1)

/-- `sqrt 5` enclosed on a 1e-12 grid, from `Real.sq_sqrt`. -/
theorem sqrt_five_bounds : (1118033988749 / 500000000000 : ℝ) < Real.sqrt 5 ∧ Real.sqrt 5 < (2236067977501 / 1000000000000 : ℝ) := by
  have h2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hn : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  constructor <;> nlinarith [h2, hn]

/-- `sqrt (10 - 2 sqrt 5)` enclosed, propagating the `sqrt 5` box. -/
theorem sqrt_inner_bounds :
    (1175570504583 / 500000000000 : ℝ) < Real.sqrt (10 - 2 * Real.sqrt 5) ∧
    Real.sqrt (10 - 2 * Real.sqrt 5) < (2351141009173 / 1000000000000 : ℝ) := by
  obtain ⟨hslo, hshi⟩ := sqrt_five_bounds
  have harg : (0:ℝ) ≤ 10 - 2 * Real.sqrt 5 := by linarith
  have h2 : Real.sqrt (10 - 2 * Real.sqrt 5) ^ 2 = 10 - 2 * Real.sqrt 5 :=
    Real.sq_sqrt harg
  have hn : 0 ≤ Real.sqrt (10 - 2 * Real.sqrt 5) := Real.sqrt_nonneg _
  constructor
  · nlinarith [h2, hn, hshi]
  · nlinarith [h2, hn, hslo]

/-- The DH constant enclosed: `κ ∈ (0.284079041, 0.284079046)`
    (QC_DH_SCOUT.md quotes `κ = 0.284079043840412...`). -/
theorem dhKappa_gt : (284079041 / 1000000000 : ℝ) < dhKappa := by
  obtain ⟨hslo, hshi⟩ := sqrt_five_bounds
  obtain ⟨htlo, hthi⟩ := sqrt_inner_bounds
  have hden : (0:ℝ) < Real.sqrt 5 - 1 := by linarith
  rw [dhKappa, lt_div_iff₀ hden]
  nlinarith [htlo, hshi]

theorem dhKappa_lt : dhKappa < (142039523 / 500000000 : ℝ) := by
  obtain ⟨hslo, hshi⟩ := sqrt_five_bounds
  obtain ⟨htlo, hthi⟩ := sqrt_inner_bounds
  have hden : (0:ℝ) < Real.sqrt 5 - 1 := by linarith
  rw [dhKappa, div_lt_iff₀ hden]
  nlinarith [hthi, hslo]

/-- The DH constant's two-sided enclosure, packaged for the emitted instances. -/
theorem dhKappa_bounds :
    (284079041 / 1000000000 : ℝ) < dhKappa ∧ dhKappa < (142039523 / 500000000 : ℝ) :=
  ⟨dhKappa_gt, dhKappa_lt⟩

/-- `log (3/2)` enclosed by Mathlib's log Taylor estimate at `x = -1/2`,
    order 24: `|S + log (3/2)| ≤ (1/2)^25/(1/2)`. -/
theorem log_three_halves_bounds :
    (6070423640075591 / 14971509072199680 : ℝ) ≤ Real.log (3 / 2) ∧ Real.log (3 / 2) ≤ (6070425424818551 / 14971509072199680 : ℝ) := by
  have hx : |(-(1:ℝ) / 2)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 24
  rw [show (1:ℝ) - -(1:ℝ) / 2 = 3 / 2 by norm_num] at h
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `log 6 = 2 log 2 + log (3/2)`, enclosed. -/
theorem log_six_bounds : (52393246555737784416259 / 29241228656640000000000 : ℝ) < Real.log 6 ∧ Real.log 6 < (52393250070805106822899 / 29241228656640000000000 : ℝ) := by
  have h6 : Real.log 6 = Real.log 2 + Real.log 2 + Real.log (3 / 2) := by
    rw [show (6:ℝ) = 2 * 2 * (3 / 2) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  obtain ⟨hlo, hhi⟩ := log_three_halves_bounds
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  rw [h6]
  norm_num at h2lo h2hi
  constructor <;> linarith [hlo, hhi, h2lo, h2hi]


/-- `log 2` in rational form (Mathlib's `Real.log_two_{gt,lt}_d9`). -/
theorem log_two_bounds :
    (6931471803 / 10000000000 : ℝ) < Real.log 2 ∧
    Real.log 2 < (6931471808 / 10000000000 : ℝ) := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  norm_num at h1 h2
  exact ⟨by linarith, by linarith⟩

/-- `log 3 = log 2 + log (3/2)`, enclosed. -/
theorem log_three_bounds :
    (32124771363880211544067 / 29241228656640000000000 : ℝ) < Real.log 3 ∧
    Real.log 3 < (32124774864326919622387 / 29241228656640000000000 : ℝ) := by
  have h3 : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (3/2:ℝ) ≠ 0)]
    norm_num
  obtain ⟨hlo, hhi⟩ := log_three_halves_bounds
  obtain ⟨h2lo, h2hi⟩ := log_two_bounds
  rw [h3]
  constructor <;> linarith [hlo, hhi, h2lo, h2hi]

end Quasicrystal
