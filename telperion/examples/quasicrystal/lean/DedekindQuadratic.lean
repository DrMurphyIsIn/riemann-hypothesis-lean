/-
  DedekindQuadratic.lean -- the PRODUCT-CLOSURE control for clause (B-mult-twisted).

  zeta_K for K = Q(sqrt(-5)) (discriminant D = -20, class number 2) is the product
  zeta(s) * L(s, chi_D).  Its local Euler factor at a prime p has Satake pair
  {1, chi_D(p)}: degree 2 at every unramified prime (chi_D(p) = +1 split, -1 inert),
  degree 1 at the ramified primes 2 and 5 (chi_D(p) = 0).  Both parameters are
  unimodular BY CONSTRUCTION -- no Deligne / Ramanujan-Petersson input is needed, in
  contrast to the A1b instance L(s, Delta) in SatakeDegreeTwo.lean.

  What is proved here, on top of `SatakeDegreeTwo.scalarGenerated_powerSum_iff`:

    * the prime layer of zeta_K at a split prime (pair {1, 1}) and at an inert prime
      (pair {1, -1}) is NOT scalar-generated; at a ramified prime (pair {1, 0}) it IS;
    * the layer of the PRODUCT is the SUM of the two factors' layers (the log-derivative
      is additive), each of which IS scalar-generated: so the predicate is not closed
      under the operation that the Selberg class is closed under;
    * the inert layer vanishes at every odd power and equals 2 at every even power,
      which is why bare (B-iii) also fails zeta_K, for a third reason (missing atoms),
      never for sign variation;
    * chi_{-20}(3) = +1 and chi_{-20}(11) = -1 by `norm_num` on the Jacobi symbol, so
      the split and inert instances above are the ACTUAL local data of zeta_K at 3
      and 11, not abstract pairs.

  Python twin: examples/quasicrystal/zoo.py (`_load_dedekind`, the `DEDEKIND` block of
  `run_asserts`), which re-derives the ideal counts against the representation numbers
  of the two reduced forms of discriminant -20 before emitting any verdict.

  conjecture1_proved = False.  Nothing here bears on RH; it falsifies a clause of the
  program's own working definition of an arithmetic Fourier quasicrystal.
-/
import Mathlib
import SatakeDegreeTwo

namespace SatakeDegreeTwo

/-! ## Part 1 -- the abstract layers of a quadratic Dedekind zeta -/

/-- A split prime of a quadratic field (`chi(p) = 1`, Satake pair `{1, 1}`) is rejected
by the clause: the layer is `2` at every power, not a geometric law. -/
theorem dedekind_split_rejected : ¬ ScalarGenerated (powerSum 1 1) := by
  rw [scalarGenerated_powerSum_iff]; norm_num

/-- An inert prime (`chi(p) = -1`, Satake pair `{1, -1}`) is rejected as well. -/
theorem dedekind_inert_rejected : ¬ ScalarGenerated (powerSum 1 (-1)) := by
  rw [scalarGenerated_powerSum_iff]; norm_num

/-- A ramified prime (`chi(p) = 0`, the local factor degenerates to degree 1) is
admitted: this is the anti-vacuity face, exactly the `deg1_scalarGenerated` fiber. -/
theorem dedekind_ramified_admitted : ScalarGenerated (powerSum 1 0) :=
  deg1_scalarGenerated 1

/-- The inert layer vanishes at every odd power: `1^m + (-1)^m = 0` for odd `m`.  This is
the missing-atom phenomenon behind zeta_K's failure of bare (B-iii). -/
theorem dedekind_inert_layer_odd {m : ℕ} (hm : Odd m) : powerSum 1 (-1) m = 0 := by
  simp [powerSum, hm.neg_one_pow]

/-- ... and equals `2` at every even power. -/
theorem dedekind_inert_layer_even {m : ℕ} (hm : Even m) : powerSum 1 (-1) m = 2 := by
  simp [powerSum, hm.neg_one_pow]; norm_num

/-! ## Part 2 -- the predicate is not closed under products -/

/-- `ScalarGenerated` only looks at `m ≥ 1`, so two layers that agree from `m = 1` on
are scalar-generated together. -/
theorem scalarGenerated_congr {f g : ℕ → ℂ} (h : ∀ m : ℕ, 1 ≤ m → f m = g m) :
    ScalarGenerated f ↔ ScalarGenerated g := by
  constructor
  · rintro ⟨t, ht⟩; exact ⟨t, fun m hm => (h m hm).symm.trans (ht m hm)⟩
  · rintro ⟨t, ht⟩; exact ⟨t, fun m hm => (h m hm).trans (ht m hm)⟩

/-- The prime layer of a PRODUCT of L-functions is the SUM of the factors' layers
(`-(fg)'/(fg) = -f'/f - g'/g`).  For zeta * L(chi) at an unramified prime the two
degree-1 layers `powerSum 1 0` and `powerSum chi(p) 0` add up to the degree-2 layer
`powerSum 1 chi(p)`, for every `m ≥ 1` (at `m = 0` the convention `0 ^ 0 = 1` makes
the degree-1 layers carry a spurious constant, which the clause never sees). -/
theorem layer_of_product (c : ℂ) {m : ℕ} (hm : 1 ≤ m) :
    powerSum 1 0 m + powerSum c 0 m = powerSum 1 c m := by
  simp [powerSum, zero_pow (Nat.one_le_iff_ne_zero.mp hm)]

/-- **Product non-closure.**  Both factors' layers are scalar-generated (zeta with twist
`1`, `L(chi)` with twist `chi(p)`), and the layer of their product is not, at every
unramified prime (`chi(p) ≠ 0`).  A predicate that is meant to cut out a class closed
under products cannot fail closure under products. -/
theorem scalarGenerated_not_closed_under_product (c : ℂ) (hc : c ≠ 0) :
    ScalarGenerated (powerSum 1 0) ∧ ScalarGenerated (powerSum c 0) ∧
      ¬ ScalarGenerated (fun m => powerSum 1 0 m + powerSum c 0 m) := by
  refine ⟨deg1_scalarGenerated 1, deg1_scalarGenerated c, ?_⟩
  rw [scalarGenerated_congr (g := powerSum 1 c) (fun m hm => layer_of_product c hm),
    scalarGenerated_powerSum_iff]
  simpa using hc

/-! ## Part 3 -- the actual local data of zeta_K at 3 and 11 (anti-phantom face) -/

/-- `chi_{-20}(3) = +1`: the prime 3 splits in `Q(sqrt(-5))`. -/
theorem chi_m20_three : jacobiSym (-20) 3 = 1 := by norm_num

/-- `chi_{-20}(11) = -1`: the prime 11 is inert in `Q(sqrt(-5))`. -/
theorem chi_m20_eleven : jacobiSym (-20) 11 = -1 := by norm_num

/-- zeta_K's layer at the split prime 3, with the character value COMPUTED in-kernel,
is rejected. -/
theorem dedekind_at_three_rejected :
    ¬ ScalarGenerated (powerSum 1 ((jacobiSym (-20) 3 : ℤ) : ℂ)) := by
  rw [chi_m20_three]; exact_mod_cast dedekind_split_rejected

/-- zeta_K's layer at the inert prime 11, with the character value COMPUTED in-kernel,
is rejected. -/
theorem dedekind_at_eleven_rejected :
    ¬ ScalarGenerated (powerSum 1 ((jacobiSym (-20) 11 : ℤ) : ℂ)) := by
  rw [chi_m20_eleven]; exact_mod_cast dedekind_inert_rejected

end SatakeDegreeTwo
