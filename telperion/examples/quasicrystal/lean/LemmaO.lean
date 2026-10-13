/-
  LemmaO.lean -- LEMMA O: the log-derivative coefficients of a Dirichlet series are
  supported on prime powers IF AND ONLY IF the coefficient sequence is multiplicative.

  This is the kernel justification of the falsification zoo's multiplicativity clause
  (examples/quasicrystal/zoo.py `check_multiplicativity`, QC_AXIOMS_DRAFT.md appendices
  v2 W3a / v3 W3c / v4 A1b / v5 Dedekind).  The zoo builds, for every object, the
  coefficient sequence `b` of `-F'/F` from the Dirichlet coefficients `a` of
  `F(s) = sum a(n) n^{-s}` by the divisor recursion

        a(n) log n  =  sum_{d | n} b(d) a(n/d)          (n >= 1),

  and then reads two things off `b`: whether it vanishes at every composite
  (non-prime-power) `n`, and whether the prime layer `b(p^m)` obeys the geometric
  generation law `b(p^m) = (log p) t(p)^m`.  LEMMA O says exactly what those two
  readings certify:

    (O)   b supported on prime powers   <->   a multiplicative (on coprime pairs)
    (O')  for multiplicative a:
          b(p^k) = (log p) a(p)^k for all p, k   <->   a COMPLETELY multiplicative

  so a composite leak `b(6) != 0` refutes multiplicativity (the Davenport-Heilbronn and
  Epstein witnesses, `LemmaOWitnesses.lean`), and a prime layer that is not geometric
  in `a(p)` refutes COMPLETE multiplicativity even when `b(6) = 0` (the GL(2) Satake
  instance, `SatakeDegreeTwo.lean`).

  ## Form

  Everything is stated in Mathlib `ArithmeticFunction` form over a commutative ring `R`:
  the recursion is the Dirichlet-convolution identity `(b * a) n = a n * l n`, the
  multiplicativity clause is Mathlib's `ArithmeticFunction.IsMultiplicative`, and "log"
  is an abstract COMPLETELY ADDITIVE weight `l : N -> R` (`l (m n) = l m + l n` on
  positives).  Only the forward direction of (O) and the converse of (O') need more
  than the ring structure: cancellation (`IsDomain R`) and non-vanishing of the weight
  at every `n >= 2`.  Both hold for `l = Real.log` over `R = ℝ` and `R = ℂ`, which
  are instantiated in section 8.  The weight hypotheses are NOT decorative: with
  `l = 0` the recursion is solved by `b = 0` for EVERY `a`, so the forward direction is
  false without them.

  ## What is proved (headline names)

    * `logDerivCoeff_unique`, `logDerivCoeffOf_spec`: `b` exists and is unique (`a 1 = 1`);
    * `primePow_support_of_isMultiplicative`: multiplicative => prime-power support;
    * `isMultiplicative_of_primePow_support`: prime-power support => multiplicative;
    * `lemmaO`: the iff;
    * `generation_law_of_completelyMultiplicative`: completely multiplicative =>
      `b (p^k) = l p * a p ^ k`;
    * `completelyMultiplicative_of_generation_law`: multiplicative + generation law =>
      completely multiplicative;  `generation_law_iff_completelyMultiplicative`: the iff;
    * `lemmaO_real`, `lemmaO_complex`: the instances at `Real.log`.

  conjecture1_proved = False.  Nothing here bears on the zeros of anything; it is a
  statement about Dirichlet coefficients of a logarithmic derivative.
-/
import Mathlib

open Finset ArithmeticFunction
open scoped ArithmeticFunction

namespace LemmaO

variable {R : Type*} [CommRing R]

/-! ## 1.  Completely additive weights -/

/-- `l` is **completely additive** on the positive integers: `l (m n) = l m + l n` for all
`m, n >= 1`.  `Real.log` composed with the cast is the intended instance; any such weight
plays the role of "log" in the divisor recursion. -/
def IsCompletelyAdditive (l : ℕ → R) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → l (m * n) = l m + l n

theorem IsCompletelyAdditive.map_one {l : ℕ → R} (hl : IsCompletelyAdditive l) : l 1 = 0 := by
  have h := hl 1 1 one_pos one_pos
  rw [mul_one] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

theorem IsCompletelyAdditive.map_pow {l : ℕ → R} (hl : IsCompletelyAdditive l) {p : ℕ}
    (hp : 0 < p) (k : ℕ) : l (p ^ k) = (k : R) * l p := by
  induction k with
  | zero => simp [hl.map_one]
  | succ k ih =>
    rw [pow_succ, hl _ _ (pow_pos hp k) hp, ih]
    push_cast
    ring

/-! ## 2.  The log-derivative coefficient functional -/

/-- `b` is the **log-derivative coefficient functional** of the amplitude `a` with respect
to the weight `l`: the Dirichlet-convolution identity `b * a = a · l` on the positives,
i.e. the divisor recursion `a n * l n = sum_{d | n} b d * a (n / d)`.  With `l = log` this
is `-F'/F · F = -F'` for `F = sum a n n^{-s}`, coefficient by coefficient. -/
def IsLogDerivCoeff (l : ℕ → R) (a b : ArithmeticFunction R) : Prop :=
  ∀ n : ℕ, 0 < n → a n * l n = (b * a) n

/-- Dirichlet convolution as a sum over divisors. -/
theorem mul_apply_divisors (b a : ArithmeticFunction R) (n : ℕ) :
    (b * a) n = ∑ d ∈ n.divisors, b d * a (n / d) := by
  rw [mul_apply]
  exact Nat.sum_divisorsAntidiagonal (fun x y => b x * a y)

theorem IsLogDerivCoeff.sum {l : ℕ → R} {a b : ArithmeticFunction R}
    (h : IsLogDerivCoeff l a b) {n : ℕ} (hn : 0 < n) :
    a n * l n = ∑ d ∈ n.divisors, b d * a (n / d) := by
  rw [h n hn, mul_apply_divisors]

/-- Peel the `d = n` term off the recursion (uses `a 1 = 1`). -/
theorem IsLogDerivCoeff.peel {l : ℕ → R} {a b : ArithmeticFunction R} (ha : a 1 = 1)
    (h : IsLogDerivCoeff l a b) {n : ℕ} (hn : 0 < n) :
    a n * l n = b n + ∑ d ∈ n.divisors.erase n, b d * a (n / d) := by
  rw [h.sum hn, ← Finset.add_sum_erase _ _ (Nat.mem_divisors_self n hn.ne'), Nat.div_self hn,
    ha, mul_one]

/-- `b 1 = 0`: the recursion at `n = 1` reads `a 1 * l 1 = b 1 * a 1`. -/
theorem IsLogDerivCoeff.one {l : ℕ → R} {a b : ArithmeticFunction R}
    (hl : IsCompletelyAdditive l) (ha : a 1 = 1) (h : IsLogDerivCoeff l a b) : b 1 = 0 := by
  have h1 := h.peel ha one_pos
  simp only [Nat.divisors_one, Finset.erase_singleton, Finset.sum_empty, add_zero, ha, one_mul,
    hl.map_one] at h1
  exact h1.symm

/-- **Uniqueness.**  The recursion determines `b` (strong induction: every proper divisor
is smaller). -/
theorem logDerivCoeff_unique {l : ℕ → R} {a b b' : ArithmeticFunction R} (ha : a 1 = 1)
    (hb : IsLogDerivCoeff l a b) (hb' : IsLogDerivCoeff l a b') : b = b' := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have h1 := hb.peel ha hn
    have h2 := hb'.peel ha hn
    have hsum : ∑ d ∈ n.divisors.erase n, b d * a (n / d)
        = ∑ d ∈ n.divisors.erase n, b' d * a (n / d) := by
      refine Finset.sum_congr rfl fun d hd => ?_
      have hdne : d ≠ n := (Finset.mem_erase.mp hd).1
      obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp (Finset.mem_erase.mp hd).2
      rw [ih d (lt_of_le_of_ne (Nat.le_of_dvd hn hdvd) hdne)]
    rw [hsum] at h1
    exact add_right_cancel (h1.symm.trans h2)

/-- The functional, constructed by strong recursion (the vacuity gate: every conditional
theorem below has inhabited hypotheses).  Returns `0` at `n = 0` because `a 0 = 0`. -/
noncomputable def logDerivCoeffFun (l : ℕ → R) (a : ArithmeticFunction R) (n : ℕ) : R :=
  a n * l n - ∑ d ∈ (n.divisors.erase n).attach, logDerivCoeffFun l a d.1 * a (n / d.1)
decreasing_by
  have hd := d.2
  have hdne : (d : ℕ) ≠ n := (Finset.mem_erase.mp hd).1
  obtain ⟨hdvd, hn0⟩ := Nat.mem_divisors.mp (Finset.mem_erase.mp hd).2
  exact lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd) hdne

/-- The functional as an arithmetic function. -/
noncomputable def logDerivCoeffOf (l : ℕ → R) (a : ArithmeticFunction R) :
    ArithmeticFunction R :=
  ⟨logDerivCoeffFun l a, by rw [logDerivCoeffFun]; simp⟩

theorem logDerivCoeffOf_apply (l : ℕ → R) (a : ArithmeticFunction R) (n : ℕ) :
    logDerivCoeffOf l a n = logDerivCoeffFun l a n := rfl

theorem logDerivCoeffOf_spec {l : ℕ → R} {a : ArithmeticFunction R} (ha : a 1 = 1) :
    IsLogDerivCoeff l a (logDerivCoeffOf l a) := by
  intro n hn
  rw [mul_apply_divisors, ← Finset.add_sum_erase _ _ (Nat.mem_divisors_self n hn.ne'),
    Nat.div_self hn, ha, mul_one]
  simp only [logDerivCoeffOf_apply]
  rw [show logDerivCoeffFun l a n = a n * l n - ∑ d ∈ (n.divisors.erase n).attach,
      logDerivCoeffFun l a d.1 * a (n / d.1) from by rw [logDerivCoeffFun]]
  rw [Finset.sum_attach (n.divisors.erase n) (fun d => logDerivCoeffFun l a d * a (n / d))]
  ring

/-- **Existence.** -/
theorem exists_logDerivCoeff (l : ℕ → R) {a : ArithmeticFunction R} (ha : a 1 = 1) :
    ∃ b, IsLogDerivCoeff l a b :=
  ⟨_, logDerivCoeffOf_spec ha⟩

/-! ## 3.  Coprime splitting of a divisor sum

The engine behind both directions of Lemma O.  For coprime `m, k >= 2` and a summand
vanishing at `1` and at every proper non-prime-power divisor of `m k`, the sum over the
divisors of `m k` collapses to the `d = m k` term plus the sums over the divisors of `m`
and of `k`: every remaining divisor is a prime power, and a prime power dividing a
coprime product divides one of the factors (`Nat.Coprime.isPrimePow_dvd_mul`). -/

theorem sum_divisors_coprime_split (f : ℕ → R) {m k : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k)
    (hmk : m.Coprime k) (h1 : f 1 = 0)
    (hvan : ∀ d, d ∣ m * k → d ≠ m * k → ¬ IsPrimePow d → f d = 0) :
    ∑ d ∈ (m * k).divisors, f d = f (m * k) + ∑ d ∈ m.divisors, f d + ∑ d ∈ k.divisors, f d := by
  have hm0 : m ≠ 0 := by omega
  have hk0 : k ≠ 0 := by omega
  have hn0 : m * k ≠ 0 := mul_ne_zero hm0 hk0
  have hmlt : m < m * k := lt_mul_of_one_lt_right (by omega) (by omega)
  have hklt : k < m * k := lt_mul_of_one_lt_left (by omega) (by omega)
  rw [← Finset.add_sum_erase _ _ (Nat.mem_divisors_self _ hn0), add_assoc]
  congr 1
  set T := (m * k).divisors.erase (m * k) with hT
  rw [← Finset.sum_filter_add_sum_filter_not T (· ∣ m)]
  have hA : T.filter (· ∣ m) = m.divisors := by
    ext d
    simp only [hT, Finset.mem_filter, Finset.mem_erase, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨-, -, -⟩, hdm⟩
      exact ⟨hdm, hm0⟩
    · rintro ⟨hdm, -⟩
      refine ⟨⟨?_, Dvd.dvd.mul_right hdm k, hn0⟩, hdm⟩
      rintro rfl
      exact absurd (Nat.le_of_dvd (by omega) hdm) (not_le.mpr hmlt)
  rw [hA]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not (T.filter (¬ · ∣ m)) (· ∣ k)]
  have hB : (T.filter (¬ · ∣ m)).filter (· ∣ k) = k.divisors.erase 1 := by
    ext d
    simp only [hT, Finset.mem_filter, Finset.mem_erase, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨-, hdm⟩, hdk⟩
      refine ⟨?_, hdk, hk0⟩
      rintro rfl
      exact hdm (one_dvd m)
    · rintro ⟨hd1, hdk, -⟩
      refine ⟨⟨⟨?_, Dvd.dvd.mul_left hdk m, hn0⟩, fun hdm => hd1 ?_⟩, hdk⟩
      · rintro rfl
        exact absurd (Nat.le_of_dvd (by omega) hdk) (not_le.mpr hklt)
      · exact Nat.eq_one_of_dvd_coprimes hmk hdm hdk
  have hC : ∑ d ∈ (T.filter (¬ · ∣ m)).filter (¬ · ∣ k), f d = 0 := by
    refine Finset.sum_eq_zero fun d hd => ?_
    simp only [hT, Finset.mem_filter, Finset.mem_erase, Nat.mem_divisors] at hd
    obtain ⟨⟨⟨hdne, hdvd, -⟩, hdm⟩, hdk⟩ := hd
    refine hvan d hdvd hdne fun hp => ?_
    rcases (hmk.isPrimePow_dvd_mul hp).mp hdvd with h | h
    · exact hdm h
    · exact hdk h
  rw [hB, hC, add_zero, Finset.sum_erase _ h1]

/-! ## 4.  Lemma O, backward: multiplicative  =>  prime-power support -/

/-- A non-prime-power `n >= 2` splits as a coprime product of two factors `>= 2`
(`ordProj[p] n * ordCompl[p] n` for `p = n.minFac`). -/
theorem exists_coprime_factorization {n : ℕ} (hn : 2 ≤ n) (h : ¬ IsPrimePow n) :
    ∃ m k : ℕ, 2 ≤ m ∧ 2 ≤ k ∧ m.Coprime k ∧ n = m * k := by
  have hn0 : n ≠ 0 := by omega
  have hpp : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hpd : n.minFac ∣ n := Nat.minFac_dvd n
  have hv : 0 < n.factorization n.minFac := hpp.factorization_pos_of_dvd hn0 hpd
  refine ⟨ordProj[n.minFac] n, ordCompl[n.minFac] n, ?_, ?_, ?_,
    (Nat.ordProj_mul_ordCompl_eq_self n n.minFac).symm⟩
  · exact le_trans hpp.two_le (Nat.le_self_pow hv.ne' _)
  · have hpos := Nat.ordCompl_pos n.minFac hn0
    by_contra hlt
    have h1 : ordCompl[n.minFac] n = 1 := by omega
    apply h
    have hself := Nat.ordProj_mul_ordCompl_eq_self n n.minFac
    rw [h1, mul_one] at hself
    rw [← hself]
    exact hpp.isPrimePow.pow hv.ne'
  · exact (Nat.coprime_ordCompl hpp hn0).pow_left _

/-- **Lemma O, backward direction.**  If `a` is multiplicative then its log-derivative
coefficient functional vanishes at every non-prime-power.  No cancellation and no
hypothesis on the weight beyond complete additivity: this direction holds over any
commutative ring. -/
theorem primePow_support_of_isMultiplicative {l : ℕ → R} {a b : ArithmeticFunction R}
    (hl : IsCompletelyAdditive l) (ha : a.IsMultiplicative) (hb : IsLogDerivCoeff l a b) :
    ∀ n, ¬ IsPrimePow n → b n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases lt_or_ge n 2 with h2 | h2
    · interval_cases n
      · simp
      · exact hb.one hl ha.1
    obtain ⟨m, k, hm, hk, hmk, rfl⟩ := exists_coprime_factorization h2 hn
    have hm0 : 0 < m := by omega
    have hk0 : 0 < k := by omega
    have hpos : 0 < m * k := by positivity
    have hrec := hb.sum hpos
    rw [sum_divisors_coprime_split (fun d => b d * a (m * k / d)) hm hk hmk
      (by simp [hb.one hl ha.1])
      (fun d hd hdne hdp => by
        simp [ih d (lt_of_le_of_ne (Nat.le_of_dvd hpos hd) hdne) hdp])] at hrec
    have hSm : ∑ d ∈ m.divisors, b d * a (m * k / d) = (a m * l m) * a k := by
      rw [hb.sum hm0, Finset.sum_mul]
      refine Finset.sum_congr rfl fun d hd => ?_
      obtain ⟨hdm, -⟩ := Nat.mem_divisors.mp hd
      rw [mul_comm m k, Nat.mul_div_assoc k hdm,
        ha.2 (hmk.symm.coprime_dvd_right (Nat.div_dvd_of_dvd hdm))]
      ring
    have hSk : ∑ d ∈ k.divisors, b d * a (m * k / d) = a m * (a k * l k) := by
      rw [hb.sum hk0, Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      obtain ⟨hdk, -⟩ := Nat.mem_divisors.mp hd
      rw [Nat.mul_div_assoc m hdk, ha.2 (hmk.coprime_dvd_right (Nat.div_dvd_of_dvd hdk))]
      ring
    rw [hSm, hSk, ha.2 hmk, hl m k hm0 hk0, Nat.div_self hpos, ha.1, mul_one] at hrec
    linear_combination -hrec

/-! ## 5.  Lemma O, forward: prime-power support  =>  multiplicative

This direction needs to CANCEL the weight: the recursion at a coprime product `m k` gives
`a (m k) * l (m k) = a m * a k * l (m k)`, and `l (m k) ≠ 0` is what turns that into
multiplicativity.  With `l = 0` the statement is false (`b = 0` solves the recursion for
every `a`), so the non-vanishing hypothesis is essential, not bookkeeping. -/

/-- A coprime product of two factors `>= 2` is not a prime power. -/
theorem not_isPrimePow_mul_of_coprime {m k : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k)
    (hmk : m.Coprime k) : ¬ IsPrimePow (m * k) := by
  intro hp
  rcases (hmk.isPrimePow_dvd_mul hp).mp (dvd_refl _) with h | h
  · exact absurd (Nat.le_of_dvd (by omega) h)
      (not_le.mpr (lt_mul_of_one_lt_right (by omega) (by omega)))
  · exact absurd (Nat.le_of_dvd (by omega) h)
      (not_le.mpr (lt_mul_of_one_lt_left (by omega) (by omega)))

/-- **Lemma O, forward direction.**  If the log-derivative coefficient functional of `a`
vanishes at every non-prime-power, then `a` is multiplicative.  Hypotheses: `a 1 = 1`,
`R` a domain, and the weight non-vanishing at every `n >= 2`. -/
theorem isMultiplicative_of_primePow_support [IsDomain R] {l : ℕ → R}
    {a b : ArithmeticFunction R} (hl : IsCompletelyAdditive l)
    (hl0 : ∀ n, 2 ≤ n → l n ≠ 0) (ha : a 1 = 1) (hb : IsLogDerivCoeff l a b)
    (hsupp : ∀ n, ¬ IsPrimePow n → b n = 0) : a.IsMultiplicative := by
  refine ⟨ha, ?_⟩
  suffices H : ∀ N, ∀ m k, m * k = N → m.Coprime k → a (m * k) = a m * a k by
    intro m k hmk
    exact H _ m k rfl hmk
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro m k hN hmk
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    rcases eq_or_ne m 1 with rfl | hm1
    · simp [ha]
    rcases eq_or_ne k 1 with rfl | hk1
    · simp [ha]
    have hm : 2 ≤ m := by omega
    have hk : 2 ≤ k := by omega
    have hpos : 0 < m * k := by positivity
    have hrec := hb.sum hpos
    rw [sum_divisors_coprime_split (fun d => b d * a (m * k / d)) hm hk hmk
      (by simp [hb.one hl ha]) (fun d _ _ hdp => by simp [hsupp d hdp])] at hrec
    have hSm : ∑ d ∈ m.divisors, b d * a (m * k / d) = (a m * l m) * a k := by
      rw [hb.sum hm0, Finset.sum_mul]
      refine Finset.sum_congr rfl fun d hd => ?_
      obtain ⟨hdm, -⟩ := Nat.mem_divisors.mp hd
      rcases eq_or_ne d 1 with rfl | hd1
      · simp [hb.one hl ha]
      have hdlt : m / d < m :=
        Nat.div_lt_self hm0 (by have := Nat.pos_of_dvd_of_pos hdm hm0; omega)
      rw [mul_comm m k, Nat.mul_div_assoc k hdm,
        ih (k * (m / d)) (by rw [← hN, mul_comm m k]; exact Nat.mul_lt_mul_of_pos_left hdlt hk0)
          k (m / d) rfl (hmk.symm.coprime_dvd_right (Nat.div_dvd_of_dvd hdm))]
      ring
    have hSk : ∑ d ∈ k.divisors, b d * a (m * k / d) = a m * (a k * l k) := by
      rw [hb.sum hk0, Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      obtain ⟨hdk, -⟩ := Nat.mem_divisors.mp hd
      rcases eq_or_ne d 1 with rfl | hd1
      · simp [hb.one hl ha]
      have hdlt : k / d < k :=
        Nat.div_lt_self hk0 (by have := Nat.pos_of_dvd_of_pos hdk hk0; omega)
      rw [Nat.mul_div_assoc m hdk,
        ih (m * (k / d)) (by rw [← hN]; exact Nat.mul_lt_mul_of_pos_left hdlt hm0)
          m (k / d) rfl (hmk.coprime_dvd_right (Nat.div_dvd_of_dvd hdk))]
      ring
    rw [hSm, hSk, hsupp _ (not_isPrimePow_mul_of_coprime hm hk hmk), zero_mul,
      hl m k hm0 hk0] at hrec
    have hne : l (m * k) ≠ 0 := hl0 _ (le_trans hm (Nat.le_mul_of_pos_right m hk0))
    have hkey : a (m * k) * l (m * k) = (a m * a k) * l (m * k) := by
      rw [hl m k hm0 hk0]
      linear_combination hrec
    exact mul_right_cancel₀ hne hkey

/-! ## 6.  LEMMA O -/

/-- **LEMMA O.**  For `a 1 = 1`, a completely additive weight `l` non-vanishing at every
`n >= 2`, and `b` the log-derivative coefficient functional of `a`: `b` is supported on
prime powers if and only if `a` is multiplicative. -/
theorem lemmaO [IsDomain R] {l : ℕ → R} {a b : ArithmeticFunction R}
    (hl : IsCompletelyAdditive l) (hl0 : ∀ n, 2 ≤ n → l n ≠ 0) (ha : a 1 = 1)
    (hb : IsLogDerivCoeff l a b) :
    (∀ n, ¬ IsPrimePow n → b n = 0) ↔ a.IsMultiplicative :=
  ⟨isMultiplicative_of_primePow_support hl hl0 ha hb,
    fun hm => primePow_support_of_isMultiplicative hl hm hb⟩

/-- **The instrument the zoo consumes, contrapositive.**  A single composite leak
`b n ≠ 0` (`n` not a prime power) refutes multiplicativity.  Holds over any commutative
ring: only the backward direction is used. -/
theorem not_isMultiplicative_of_composite_leak {l : ℕ → R} {a b : ArithmeticFunction R}
    (hl : IsCompletelyAdditive l) (hb : IsLogDerivCoeff l a b) {n : ℕ}
    (hcomp : ¬ IsPrimePow n) (hleak : b n ≠ 0) : ¬ a.IsMultiplicative :=
  fun ha => hleak (primePow_support_of_isMultiplicative hl ha hb n hcomp)

/-! ## 7.  Refinement: the generation law  <->  complete multiplicativity

The zoo's second reading of `b` is the prime-layer law `b (p^k) = (log p) a(p)^k`.  That
law holds for COMPLETELY multiplicative `a` and characterizes it among multiplicative
`a`: a multiplicative `a` that is not completely multiplicative has a prime power where
the law fails (the GL(2) Satake instance is `SatakeDegreeTwo.scalarGenerated_powerSum_iff`:
`b(p^m) = (log p)(alpha^m + beta^m)` is geometric iff `alpha beta = 0`). -/

/-- Complete multiplicativity: `a 1 = 1` and `a (m n) = a m * a n` for ALL `m, n`. -/
def IsCompletelyMultiplicative (a : ArithmeticFunction R) : Prop :=
  a 1 = 1 ∧ ∀ m n : ℕ, a (m * n) = a m * a n

theorem IsCompletelyMultiplicative.isMultiplicative {a : ArithmeticFunction R}
    (h : IsCompletelyMultiplicative a) : a.IsMultiplicative :=
  ⟨h.1, fun _ => h.2 _ _⟩

theorem IsCompletelyMultiplicative.map_pow {a : ArithmeticFunction R}
    (h : IsCompletelyMultiplicative a) (p k : ℕ) : a (p ^ k) = a p ^ k := by
  induction k with
  | zero => simp [h.1]
  | succ k ih => rw [pow_succ, h.2, ih, pow_succ]

/-- The recursion at a prime power, indexed by the exponent. -/
theorem IsLogDerivCoeff.primePow_sum {l : ℕ → R} {a b : ArithmeticFunction R}
    (hb : IsLogDerivCoeff l a b) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    a (p ^ k) * l (p ^ k) = ∑ j ∈ Finset.range (k + 1), b (p ^ j) * a (p ^ (k - j)) := by
  rw [hb.sum (pow_pos hp.pos k), Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Nat.pow_div (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hp.pos]

/-- **The generation law.**  For completely multiplicative `a` the prime layer of `b` is
geometric: `b (p^k) = l p * a p ^ k` for every prime `p` and `k >= 1`.  (Over `ℝ` with
`l = log` and `a = 1` this is `Λ (p^k) = log p`.)  Any commutative ring. -/
theorem generation_law_of_completelyMultiplicative {l : ℕ → R} {a b : ArithmeticFunction R}
    (hl : IsCompletelyAdditive l) (ha : IsCompletelyMultiplicative a)
    (hb : IsLogDerivCoeff l a b) {p : ℕ} (hp : p.Prime) :
    ∀ k, 1 ≤ k → b (p ^ k) = l p * a p ^ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hrec := hb.primePow_sum hp (k' + 1)
    rw [Finset.sum_range_succ, Finset.sum_range_succ'] at hrec
    simp only [pow_zero, Nat.sub_zero, Nat.sub_self, hb.one hl ha.1, zero_mul, ha.1,
      mul_one] at hrec
    have hmid : ∑ j ∈ Finset.range k', b (p ^ (j + 1)) * a (p ^ (k' + 1 - (j + 1)))
        = ∑ _j ∈ Finset.range k', l p * a p ^ (k' + 1) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjlt := Finset.mem_range.mp hj
      rw [ih (j + 1) (by omega) (by omega), ha.map_pow, mul_assoc, ← pow_add]
      congr 2
      omega
    rw [hmid, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ha.map_pow,
      hl.map_pow hp.pos] at hrec
    push_cast at hrec
    linear_combination -hrec

/-- **Converse of the generation law.**  A multiplicative `a` whose prime layer obeys the
generation law is completely multiplicative.  Needs cancellation of `l (p^k) ≠ 0`. -/
theorem completelyMultiplicative_of_generation_law [IsDomain R] {l : ℕ → R}
    {a b : ArithmeticFunction R} (hl : IsCompletelyAdditive l) (hl0 : ∀ n, 2 ≤ n → l n ≠ 0)
    (ha : a.IsMultiplicative) (hb : IsLogDerivCoeff l a b)
    (hgen : ∀ p, p.Prime → ∀ k, 1 ≤ k → b (p ^ k) = l p * a p ^ k) :
    IsCompletelyMultiplicative a := by
  have hpow : ∀ p, p.Prime → ∀ k, a (p ^ k) = a p ^ k := by
    intro p hp k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [ha.1]
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hrec := hb.primePow_sum hp (k' + 1)
      rw [Finset.sum_range_succ'] at hrec
      simp only [pow_zero, Nat.sub_zero, hb.one hl ha.1, zero_mul, add_zero] at hrec
      have hmid : ∑ j ∈ Finset.range (k' + 1), b (p ^ (j + 1)) * a (p ^ (k' + 1 - (j + 1)))
          = ∑ _j ∈ Finset.range (k' + 1), l p * a p ^ (k' + 1) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjlt := Finset.mem_range.mp hj
        rw [hgen p hp (j + 1) (by omega), ih (k' + 1 - (j + 1)) (by omega), mul_assoc,
          ← pow_add]
        congr 2
        omega
      rw [hmid, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hl.map_pow hp.pos] at hrec
      have hne : ((k' + 1 : ℕ) : R) * l p ≠ 0 := by
        rw [← hl.map_pow hp.pos]
        exact hl0 _ (le_trans hp.two_le (Nat.le_self_pow (by omega) p))
      have hkey : a (p ^ (k' + 1)) * (((k' + 1 : ℕ) : R) * l p)
          = a p ^ (k' + 1) * (((k' + 1 : ℕ) : R) * l p) := by
        rw [hrec]
        ring
      exact mul_right_cancel₀ hne hkey
  have hfac : ∀ N : ℕ, N ≠ 0 → a N = N.factorization.prod (fun p k => a p ^ k) := by
    intro N hN
    rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization a ha hN]
    exact Finsupp.prod_congr fun p hp => hpow p (Nat.prime_of_mem_primeFactors hp) _
  refine ⟨ha.1, fun m n => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [hfac _ (mul_ne_zero hm hn), hfac _ hm, hfac _ hn, Nat.factorization_mul hm hn,
    Finsupp.prod_add_index' (fun p => pow_zero (a p)) (fun p k1 k2 => pow_add (a p) k1 k2)]

/-- **Refinement, packaged.**  Among multiplicative `a`, the generation law characterizes
complete multiplicativity. -/
theorem generation_law_iff_completelyMultiplicative [IsDomain R] {l : ℕ → R}
    {a b : ArithmeticFunction R} (hl : IsCompletelyAdditive l) (hl0 : ∀ n, 2 ≤ n → l n ≠ 0)
    (ha : a.IsMultiplicative) (hb : IsLogDerivCoeff l a b) :
    (∀ p, p.Prime → ∀ k, 1 ≤ k → b (p ^ k) = l p * a p ^ k) ↔ IsCompletelyMultiplicative a :=
  ⟨completelyMultiplicative_of_generation_law hl hl0 ha hb,
    fun hcm _ hp => generation_law_of_completelyMultiplicative hl hcm hb hp⟩

/-- **The second instrument, contrapositive.**  A multiplicative `a` with a prime power
where the generation law fails is NOT completely multiplicative.  (This is the shape of
the GL(2) Satake rejection: `b(6) = 0` but the layer at `p = 2` is not geometric.) -/
theorem not_completelyMultiplicative_of_generation_law_fails {l : ℕ → R}
    {a b : ArithmeticFunction R} (hl : IsCompletelyAdditive l) (hb : IsLogDerivCoeff l a b)
    {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hfail : b (p ^ k) ≠ l p * a p ^ k) :
    ¬ IsCompletelyMultiplicative a :=
  fun hcm => hfail (generation_law_of_completelyMultiplicative hl hcm hb hp k hk)

/-! ## 8.  Instances: the weight `log` over `ℝ` and `ℂ` -/

/-- The real logarithmic weight `n ↦ log n`. -/
noncomputable def logWeight : ℕ → ℝ := fun n => Real.log n

theorem logWeight_completelyAdditive : IsCompletelyAdditive logWeight := by
  intro m n hm hn
  simp only [logWeight]
  push_cast
  exact Real.log_mul (by positivity) (by positivity)

theorem logWeight_ne_zero : ∀ n, 2 ≤ n → logWeight n ≠ 0 := fun n hn =>
  ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < n)))

/-- The same weight, viewed in `ℂ`. -/
noncomputable def logWeightC : ℕ → ℂ := fun n => (Real.log n : ℂ)

theorem logWeightC_completelyAdditive : IsCompletelyAdditive logWeightC := by
  intro m n hm hn
  simp only [logWeightC]
  push_cast
  rw [Real.log_mul (by positivity) (by positivity)]
  push_cast
  ring

theorem logWeightC_ne_zero : ∀ n, 2 ≤ n → logWeightC n ≠ 0 := fun n hn =>
  Complex.ofReal_ne_zero.mpr (logWeight_ne_zero n hn)

/-- **Lemma O over `ℝ`** with `l = log`: `a n * log n = (b * a) n` for `n >= 1`; then `b`
is supported on prime powers iff `a` is multiplicative. -/
theorem lemmaO_real {a b : ArithmeticFunction ℝ} (ha : a 1 = 1)
    (hb : IsLogDerivCoeff logWeight a b) :
    (∀ n, ¬ IsPrimePow n → b n = 0) ↔ a.IsMultiplicative :=
  lemmaO logWeight_completelyAdditive logWeight_ne_zero ha hb

/-- **Lemma O over `ℂ`** with `l = log`. -/
theorem lemmaO_complex {a b : ArithmeticFunction ℂ} (ha : a 1 = 1)
    (hb : IsLogDerivCoeff logWeightC a b) :
    (∀ n, ¬ IsPrimePow n → b n = 0) ↔ a.IsMultiplicative :=
  lemmaO logWeightC_completelyAdditive logWeightC_ne_zero ha hb

/-- **The refinement over `ℝ`**: among multiplicative `a`, `b (p^k) = log p * a p ^ k` for
all `p, k >= 1` iff `a` is completely multiplicative. -/
theorem generation_law_iff_completelyMultiplicative_real {a b : ArithmeticFunction ℝ}
    (ha : a.IsMultiplicative) (hb : IsLogDerivCoeff logWeight a b) :
    (∀ p, p.Prime → ∀ k, 1 ≤ k → b (p ^ k) = Real.log p * a p ^ k) ↔
      IsCompletelyMultiplicative a :=
  generation_law_iff_completelyMultiplicative logWeight_completelyAdditive logWeight_ne_zero
    ha hb

/-- **The refinement over `ℂ`.** -/
theorem generation_law_iff_completelyMultiplicative_complex {a b : ArithmeticFunction ℂ}
    (ha : a.IsMultiplicative) (hb : IsLogDerivCoeff logWeightC a b) :
    (∀ p, p.Prime → ∀ k, 1 ≤ k → b (p ^ k) = (Real.log p : ℂ) * a p ^ k) ↔
      IsCompletelyMultiplicative a :=
  generation_law_iff_completelyMultiplicative logWeightC_completelyAdditive
    logWeightC_ne_zero ha hb

end LemmaO
