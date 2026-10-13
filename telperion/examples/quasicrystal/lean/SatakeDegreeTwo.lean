/-
  SatakeDegreeTwo.lean -- PROGRAM MIRRORMERE, ROUTE A milestone A1b.

  THE FALSIFICATION INSTRUMENT for clause (B-mult-twisted), QC_AXIOMS_DRAFT.md
  section W3c.2.  This file does NOT extend the clause to GL(2); it PROVES THE
  CLAUSE FALSE, exhibiting `L(s, Delta)` -- Ramanujan's modular discriminant, a
  bona-fide degree-2 element of the Selberg class -- as a member of the arithmetic
  class the clause purports to characterize which the clause REJECTS.

  ## The clause, verbatim (QC_AXIOMS_DRAFT.md W3c.2)

      (B-mult-twisted) -- Multiplicative amplitude generation with a unimodular
      twist.  The atomic support of mu-hat is contained in the prime log-lattice
      {+- m log p} with no atoms at composite frequencies, and there is a
      per-prime twist t : {primes} -> S^1 u {0} such that for every unramified
      prime p and every m >= 1
              c(m log p) = (log p) t(p)^m p^{-m/2},    |t(p)| = 1.

  ## Where L(s, Delta) fails it

  For a degree-2 Euler factor with Satake parameters (alpha_p, beta_p) the
  prime-layer amplitude is the POWER SUM
              c(m log p) = (log p) (alpha_p^m + beta_p^m) p^{-m/2},
  because -L'/L has von-Mangoldt coefficients b(p^m) = (log p) * p_m(alpha,beta).
  The clause demands that this power sum be a GEOMETRIC sequence t(p)^m in a single
  scalar.  For a Newton power sum in two parameters that is false as soon as the
  factor is genuinely of degree 2:

      alpha^m + beta^m = t^m for all m >= 1   <->   alpha * beta = 0.

  That is `scalarGenerated_powerSum_iff` below, and it is an IFF: the clause admits
  EXACTLY the degenerate (degree <= 1) local factors.  zeta (t(p) = 1) and
  L(s, chi) (t(p) = chi(p)) pass precisely because their Satake data is the
  one-parameter fiber beta = 0 -- see `deg1_scalarGenerated`, the anti-vacuity
  witness.  Every unitarily-normalized GL(2) factor has alpha * beta = 1 /= 0 and
  is therefore rejected, with the m = 2 datum as the witness:
              demanded  alpha^2 + beta^2 = (alpha+beta)^2
              actual    alpha^2 + beta^2 = (alpha+beta)^2 - 2 alpha beta,
  a defect of exactly 2 * (Satake determinant).

  NOTE the strengthening: `ScalarGenerated` below DROPS the clause's own |t| = 1
  demand.  Refuting the weaker predicate refutes the clause a fortiori -- the
  rejection is not an artifact of unimodularity bookkeeping.

  ## Scope honesty -- what is used, and where

  * The REJECTION half (this file's theorems) is UNCONDITIONAL and uses no input
    beyond the definition of a degree-2 Euler factor in unitary normalization
    (alpha_p beta_p = 1), which for Delta is RE-DERIVED here from the q-expansion
    rather than assumed (`delta_satakeDet_two`).
  * The MEMBERSHIP half -- that Delta deserves to be in the class at all, i.e.
    that its comb has the same temperedness/decay profile as zeta's -- is
    RAMANUJAN-PETERSSON, a THEOREM OF DELIGNE (Weil I, Publ. IHES 43, 1974):
    |alpha_p| = |beta_p| = 1.  It is NAMED as an input, NOT formalized here, and
    NOT used by any theorem below.  It is what makes the falsification bite: the
    rejected object is tempered, arithmetic, and automorphic.

  ## Anti-phantom face

  Nothing numeric is quoted.  `tau` is COMPUTED in-kernel from the definition
  Delta = q * prod_{n>=1} (1 - q^n)^24 by truncated integer power series, and the
  Satake determinant is RE-DERIVED from that computation via
  alpha beta = a(p)^2 - a(p^2).  Two structurally independent arithmetic laws --
  the Hecke recursion tau(p^2) = tau(p)^2 - p^11 and coprime multiplicativity
  tau(6) = tau(2) tau(3) -- are asserted as kernel cross-checks
  (`tau_hecke_p2`, `tau_mult_six`); a mis-implemented q-expansion fails them and
  the file REFUSES to compile.

  conjecture1_proved = False.  This proves nothing about RH.  It falsifies a
  clause in this program's own working definition of "arithmetic Fourier
  quasicrystal", which is exactly its value.
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

namespace SatakeDegreeTwo

/-! ## Part 1 -- the structural refutation (unconditional, no arithmetic input) -/

/-- The prime-layer amplitude sequence of a local Euler factor of degree at most 2
with Satake parameters `a, b`, stripped of the common factor `(log p) p^{-m/2}`:
the Newton power sum `p_m = a^m + b^m`.  This is `b(p^m) / log p` for
`-L'/L`.  Degree 1 is the degenerate fiber `b = 0`. -/
def powerSum (a b : ℂ) (m : ℕ) : ℂ := a ^ m + b ^ m

/-- The amplitude-generation law of clause (B-mult-twisted), restricted to one
prime and stripped of the `(log p) p^{-m/2}` normalization: SOME single scalar
twist `t` generates the entire layer, `c m = t ^ m` for all `m >= 1`.

The clause further demands `|t| = 1`.  This predicate omits that demand, so it is
WEAKER than the clause; refuting it refutes the clause. -/
def ScalarGenerated (c : ℕ → ℂ) : Prop := ∃ t : ℂ, ∀ m : ℕ, 1 ≤ m → c m = t ^ m

/-- **The falsification, in its sharpest form.**  A degree-2 prime layer satisfies
the (B-mult-twisted) generation law **if and only if** its Satake determinant
vanishes, i.e. if and only if the local factor degenerates to degree at most 1.

Forward: the `m = 1` datum forces `t = a + b`, and then the `m = 2` datum forces
`a^2 + b^2 = (a+b)^2`, i.e. `2ab = 0`.  Backward: with one parameter zero the
power sum IS geometric.

So the clause is not an "arithmetic class" predicate at all -- it is a predicate
that holds exactly on the GL(1) fiber. -/
theorem scalarGenerated_powerSum_iff (a b : ℂ) :
    ScalarGenerated (powerSum a b) ↔ a * b = 0 := by
  constructor
  · rintro ⟨t, h⟩
    have h1 := h 1 (by norm_num)
    have h2 := h 2 (by norm_num)
    simp only [powerSum, pow_one] at h1
    simp only [powerSum] at h2
    rw [← h1] at h2
    linear_combination (-(1 : ℂ) / 2) * h2
  · intro h
    rcases mul_eq_zero.mp h with ha | hb
    · refine ⟨b, fun m hm => ?_⟩
      simp [powerSum, ha, zero_pow (Nat.one_le_iff_ne_zero.mp hm)]
    · refine ⟨a, fun m hm => ?_⟩
      simp [powerSum, hb, zero_pow (Nat.one_le_iff_ne_zero.mp hm)]

/-- **Anti-vacuity witness (the degree-1 fiber PASSES).**  The refuted predicate is
not vacuously false: on the one-parameter shape `b = 0` it HOLDS, with twist
`t = a`.  This is exactly why zeta (`a = 1`) and `L(s, chi)` (`a = chi(p)`) pass
the clause, and it localizes the clause's defect precisely at the jump from
degree 1 to degree 2 -- not at unimodularity, not at positivity. -/
theorem deg1_scalarGenerated (a : ℂ) : ScalarGenerated (powerSum a 0) := by
  rw [scalarGenerated_powerSum_iff]; simp

/-- zeta's prime layer: trivial twist `t(p) = 1`, degree 1.  PASSES. -/
theorem zeta_layer_scalarGenerated : ScalarGenerated (powerSum 1 0) :=
  deg1_scalarGenerated 1

/-- `L(s, chi)`'s prime layer: unimodular character twist `t(p) = chi(p)`,
degree 1.  PASSES for every value of `chi(p)`. -/
theorem lchi_layer_scalarGenerated (chip : ℂ) : ScalarGenerated (powerSum chip 0) :=
  deg1_scalarGenerated chip

/-- **Every unitarily-normalized GL(2) local factor is rejected.**  Unitary
normalization of a degree-2 Euler factor means `alpha beta = 1` (the local factor
is `(1 - alpha X)(1 - beta X)` with constant term-normalized determinant 1); the
clause rejects it.  Ramanujan-Petersson (Deligne) additionally puts both
parameters ON the unit circle, which is what makes such a factor a legitimate
tempered member of the class -- but temperedness is not needed for the rejection. -/
theorem unitary_deg2_not_scalarGenerated (a b : ℂ) (hdet : a * b = 1) :
    ¬ ScalarGenerated (powerSum a b) := by
  rw [scalarGenerated_powerSum_iff, hdet]
  exact one_ne_zero

/-- **Non-vacuity of the rejected hypothesis class.**  For EVERY prescribed trace
`tr` there is a unitarily-normalized Satake pair realizing it (the roots of
`X^2 - tr X + 1` over the algebraically closed field `ℂ`).  So
`unitary_deg2_not_scalarGenerated` does not refute an empty hypothesis: it refutes
a class inhabited at every trace, `Delta`'s included. -/
theorem satake_pair_exists (tr : ℂ) : ∃ a b : ℂ, a * b = 1 ∧ a + b = tr := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (tr ^ 2 - 4) (n := 2) (by norm_num)
  refine ⟨(tr + r) / 2, (tr - r) / 2, ?_, by ring⟩
  have hr2 : r ^ 2 = tr ^ 2 - 4 := hr
  field_simp
  linear_combination -hr2

/-- The quantitative witness: at `m = 2` the amplitude the clause DEMANDS and the
amplitude a degree-2 layer HAS differ by exactly twice the Satake determinant.
For a unitarily-normalized factor the gap is the constant `2` -- it does not
shrink, at any prime, for any form. -/
theorem deg2_amplitude_defect (a b : ℂ) :
    (a + b) ^ 2 - powerSum a b 2 = 2 * (a * b) := by
  simp only [powerSum]; ring

/-! ## Part 2 -- the Delta instance, re-derived (anti-phantom face)

`Delta = q * prod_{n>=1} (1 - q^n)^24`.  We compute the q-expansion in-kernel over
`ℤ` with truncated power-series arithmetic on coefficient lists (index = power of
`q`), then read `tau` off it.  No tau value is quoted. -/

/-- Truncated power-series product of coefficient lists, to order `N`. -/
def cmul (N : ℕ) (u v : List ℤ) : List ℤ :=
  (List.range (N + 1)).map fun k =>
    ((List.range (k + 1)).map fun i => u.getD i 0 * v.getD (k - i) 0).sum

/-- The truncated constant series `1`. -/
def cone (N : ℕ) : List ℤ := (List.range (N + 1)).map fun k => if k = 0 then 1 else 0

/-- Truncated `u ^ e`, naive `e`-fold product (no clever exponentiation: the
exponent 24 must be visibly the exponent 24). -/
def cpow (N : ℕ) (u : List ℤ) : ℕ → List ℤ
  | 0 => cone N
  | e + 1 => cmul N (cpow N u e) u

/-- The truncated series `1 - q^n`. -/
def oneSubQPow (N n : ℕ) : List ℤ :=
  (List.range (N + 1)).map fun k => if k = 0 then 1 else if k = n then -1 else 0

/-- `prod_{n=1}^{j} (1 - q^n)^24`, truncated to order `N`.  For `j >= N` this is
the full eta-product to that order, since `(1 - q^n)^24 = 1` modulo `q^{N+1}`
whenever `n > N`. -/
def etaAux (N : ℕ) : ℕ → List ℤ
  | 0 => cone N
  | j + 1 => cmul N (etaAux N j) (cpow N (oneSubQPow N (j + 1)) 24)

-- The q-expansion is a closed integer computation; the kernel needs headroom to
-- unfold the nested truncated products.
set_option maxRecDepth 100000

/-- Order to which the q-expansion is carried. -/
def tauOrder : ℕ := 6

/-- Ramanujan's `tau`, COMPUTED: `Delta = q * prod (1 - q^n)^24`, so
`tau k` is the coefficient of `q^{k-1}` in the eta product. -/
def tau (k : ℕ) : ℤ := (etaAux tauOrder tauOrder).getD (k - 1) 0

/-- Normalization anchor: `Delta` is normalized, `tau 1 = 1`. -/
theorem tau_one : tau 1 = 1 := by decide

theorem tau_two : tau 2 = -24 := by decide

theorem tau_three : tau 3 = 252 := by decide

theorem tau_four : tau 4 = -1472 := by decide

theorem tau_six : tau 6 = -6048 := by decide

/-! ### Anti-phantom cross-checks

Two arithmetic laws of `tau` that are structurally independent of the q-expansion
recursion used to compute it.  If the computation above were wrong, these would
fail and the file would not compile -- this is the "REFUSE on disagreement"
requirement, discharged in the kernel rather than asserted in a comment. -/

/-- Hecke recursion at `p = 2`: `tau(p^2) = tau(p)^2 - p^11`.  Equivalently, the
Satake determinant at `p = 2` is `p^11` before unitary normalization. -/
theorem tau_hecke_p2 : tau 4 = tau 2 ^ 2 - 2 ^ 11 := by decide

/-- Multiplicativity at coprime arguments: `tau(6) = tau(2) tau(3)`. -/
theorem tau_mult_six : tau 6 = tau 2 * tau 3 := by decide

/-! ### The analytically-normalized Hecke data at p = 2, in exact rationals

`lambda(n) = tau(n) / n^{11/2}` is the analytic normalization.  `lambda(2)` itself
is irrational, but `lambda(2)^2 = tau(2)^2 / 2^11` and `lambda(4) = tau(4) / 2^11`
both are, so the entire Satake computation stays inside `ℚ` and is kernel-decidable. -/

/-- `lambda(2)^2`, from the computed `tau 2`. -/
def lamSqTwo : ℚ := (tau 2 : ℚ) ^ 2 / 2 ^ 11

/-- `lambda(4)`, from the computed `tau 4`.  (`4^{11/2} = 2^11`.) -/
def lamFour : ℚ := (tau 4 : ℚ) / 2 ^ 11

/-- The Satake determinant `alpha_2 * beta_2`, RE-DERIVED from the q-expansion.
For a degree-2 Euler factor the Dirichlet coefficients are the COMPLETE HOMOGENEOUS
symmetric functions, `a(p) = alpha + beta` and `a(p^2) = alpha^2 + alpha beta + beta^2`,
whence `alpha beta = a(p)^2 - a(p^2)`.  Nothing here assumes the value 1. -/
def satakeDetTwo : ℚ := lamSqTwo - lamFour

/-- The re-derivation lands on `1`: `Delta`'s Satake pair at `p = 2` is unitarily
normalized.  This is a COMPUTED consequence of `tau 2` and `tau 4`, not an input. -/
theorem delta_satakeDet_two : satakeDetTwo = 1 := by
  simp only [satakeDetTwo, lamSqTwo, lamFour, tau_two, tau_four]
  norm_num

/-- The clause's OWN unimodularity demand also fails, independently of the
generation law: the only candidate twist is `t(2) = lambda(2)`, whose squared
modulus is `9/32`, not `1`.  (Recorded for completeness; the generation-law
refutation above is the stronger and normalization-independent one.) -/
theorem delta_twist_not_unimodular : lamSqTwo = 9 / 32 ∧ lamSqTwo ≠ 1 := by
  have h : lamSqTwo = 9 / 32 := by
    simp only [lamSqTwo, tau_two]; norm_num
  exact ⟨h, by rw [h]; norm_num⟩

/-- The `m = 2` amplitude gap for `Delta` at `p = 2`, in exact rationals:
the clause demands `9/32`, `Delta` has `-55/32`, the defect is exactly `2`. -/
theorem delta_amplitude_defect_two :
    lamSqTwo - 2 * satakeDetTwo = -55 / 32 ∧
      lamSqTwo - (lamSqTwo - 2 * satakeDetTwo) = 2 := by
  have hl : lamSqTwo = 9 / 32 := by simp only [lamSqTwo, tau_two]; norm_num
  have hd : satakeDetTwo = 1 := delta_satakeDet_two
  rw [hl, hd]; norm_num

/-- **A1b, the headline.**  `L(s, Delta)` is rejected by clause (B-mult-twisted).

Stated against the RE-DERIVED determinant: any Satake pair at `p = 2` whose
determinant is the value the q-expansion actually produces fails the clause's
amplitude-generation law.  Had the q-expansion produced `0` the hypothesis would be
satisfiable and this theorem would say nothing -- the refusal is structural. -/
theorem delta_rejected_by_B_mult_twisted (a b : ℂ)
    (hdet : a * b = (satakeDetTwo : ℚ)) : ¬ ScalarGenerated (powerSum a b) := by
  rw [delta_satakeDet_two] at hdet
  norm_num at hdet
  exact unitary_deg2_not_scalarGenerated a b hdet

/-- **A1b, complete and non-vacuous.**  At `p = 2` with `Delta`'s RE-DERIVED Satake
determinant, the hypothesis class is inhabited AND every member of it is rejected by
clause (B-mult-twisted).  This is the falsification: `L(s, Delta)` is a degree-2
Selberg element, tempered by Deligne's theorem (named input, not used here), and the
clause list excludes it. -/
theorem delta_rejected_nonvacuous :
    (∃ a b : ℂ, a * b = (satakeDetTwo : ℚ)) ∧
      (∀ a b : ℂ, a * b = (satakeDetTwo : ℚ) → ¬ ScalarGenerated (powerSum a b)) := by
  refine ⟨?_, fun a b h => delta_rejected_by_B_mult_twisted a b h⟩
  obtain ⟨a, b, hab, -⟩ := satake_pair_exists 0
  exact ⟨a, b, by rw [hab, delta_satakeDet_two]; norm_num⟩

end SatakeDegreeTwo
