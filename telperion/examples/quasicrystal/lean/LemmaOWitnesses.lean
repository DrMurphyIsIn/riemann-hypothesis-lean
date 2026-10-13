/-
  LemmaOWitnesses.lean -- the composite frequency `n = 6`, three ways, in the kernel.

  Lemma O (`LemmaO.lean`) says: the log-derivative coefficient `b` of an amplitude `a` is
  supported on prime powers iff `a` is multiplicative.  `6 = 2 * 3` is the first composite
  (non-prime-power) integer, so `b 6` is the first place a non-multiplicative amplitude can
  LEAK.  This file evaluates `b 6` for three concrete amplitudes and draws the Lemma O
  verdict for each.  Every number is computed from the recursion; nothing is quoted.

    (i)   POSITIVE CONTROL, zeta.  `a = ζ` (all ones) is completely multiplicative.  Its
          functional is von Mangoldt's `Λ` (Mathlib's `vonMangoldt_mul_zeta`, read as the
          recursion), `b 6 = Λ 6 = 0`, and the generation law `b (p^k) = log p` holds.

    (ii)  DAVENPORT-HEILBRONN.  `a` periodic mod 5 with pattern `[1, κ, -κ, -1, 0]`,
          `κ = (sqrt(10 - 2 sqrt 5) - 2)/(sqrt 5 - 1)` (zoo.py `_DH_C`; the island's
          `Quasicrystal.dhKappa`).  The recursion gives `b 2 = κ log 2`, `b 3 = -κ log 3`,
          and `b 6 = (1 + κ²) log 6 > 0`: a strictly positive composite atom, so by Lemma O
          the DH amplitude is NOT multiplicative.  (Numerically `b 6 = 1.9364`, the value
          the leakage node certifies as a rational enclosure.)

    (iii) EPSTEIN `E`.  `a n = r(n) / 2` with `r(n) = #{(x, y) ∈ ℤ² : x² + 5y² = n}`, the
          Epstein zeta of the principal form of discriminant `-20`, normalized by
          `r(1) = 2`.  Representation numbers are COUNTED by `decide` over the lattice
          box `|x|, |y| ≤ n`, which is proved complete (`rep5_box_complete`).  `a 2 = a 3 = 0`
          and `a 6 = 2` (the four points `(±1, ±1)`), so `b 6 = 2 log 6 ≠ 0` and `E` is NOT
          multiplicative.  `E` is the counterfeit: it has the functional-equation profile of
          `zeta_K` for `Q(sqrt(-5))` (it is `(zeta_K + L_genus)/2`) but no Euler product,
          and Lemma O sees that at `n = 6` already.  The direct check `a 6 ≠ a 2 * a 3` is
          recorded alongside as the anti-phantom cross-check.

  NOTE on (iii): the natural normalization is `a 1 = r(1)/2 = 1`, which gives `a 6 = 2`,
  not `1` -- `x² + 5y² = 6` has four solutions.  Either value leaks; the file records the
  computed one.

  conjecture1_proved = False.
-/
import Mathlib
import LemmaO
import LeakageDictionary

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta

namespace LemmaO

/-! ## 0.  Shared arithmetic at `n = 2, 3, 6` -/

theorem divisors_two : Nat.divisors 2 = {1, 2} := by decide
theorem divisors_three : Nat.divisors 3 = {1, 3} := by decide
theorem divisors_six : Nat.divisors 6 = {1, 2, 3, 6} := by decide

theorem six_not_isPrimePow : ¬ IsPrimePow 6 :=
  not_isPrimePow_mul_of_coprime (m := 2) (k := 3) le_rfl (by norm_num) (by norm_num)

/-- The recursion at `n = 2`, `3`, `6` written out, for any real amplitude with `a 1 = 1`. -/
theorem b_two {a b : ArithmeticFunction ℝ} (ha : a 1 = 1) (hb : IsLogDerivCoeff logWeight a b) :
    b 2 = a 2 * Real.log 2 := by
  have h := hb.sum (n := 2) (by norm_num)
  rw [divisors_two, Finset.sum_insert (by decide), Finset.sum_singleton,
    hb.one logWeight_completelyAdditive ha, ha] at h
  simp only [logWeight, Nat.cast_ofNat] at h
  norm_num at h
  linarith

theorem b_three {a b : ArithmeticFunction ℝ} (ha : a 1 = 1)
    (hb : IsLogDerivCoeff logWeight a b) : b 3 = a 3 * Real.log 3 := by
  have h := hb.sum (n := 3) (by norm_num)
  rw [divisors_three, Finset.sum_insert (by decide), Finset.sum_singleton,
    hb.one logWeight_completelyAdditive ha, ha] at h
  simp only [logWeight, Nat.cast_ofNat] at h
  norm_num at h
  linarith

/-- `b 6 = a 6 log 6 - a 2 a 3 (log 2 + log 3)`: the composite coefficient in closed form. -/
theorem b_six {a b : ArithmeticFunction ℝ} (ha : a 1 = 1) (hb : IsLogDerivCoeff logWeight a b) :
    b 6 = a 6 * Real.log 6 - a 2 * a 3 * (Real.log 2 + Real.log 3) := by
  have h := hb.sum (n := 6) (by norm_num)
  rw [divisors_six, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    hb.one logWeight_completelyAdditive ha, ha, b_two ha hb, b_three ha hb] at h
  simp only [logWeight, Nat.cast_ofNat] at h
  norm_num at h
  linarith

/-! ## 1.  Positive control: zeta -/

/-- `ζ` (all ones, as a real arithmetic function) is completely multiplicative. -/
theorem zeta_completelyMultiplicative : IsCompletelyMultiplicative (ζ : ArithmeticFunction ℝ) := by
  refine ⟨by simp, fun m n => ?_⟩
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  simp [natCoe_apply, zeta_apply, hm, hn]

/-- Mathlib's `Λ * ζ = log`, read as the divisor recursion: von Mangoldt IS the
log-derivative coefficient functional of `ζ`. -/
theorem zeta_logDerivCoeff : IsLogDerivCoeff logWeight (ζ : ArithmeticFunction ℝ) Λ := by
  intro n hn
  rw [vonMangoldt_mul_zeta, log_apply]
  simp [natCoe_apply, zeta_apply, hn.ne', logWeight]

/-- **Positive control.**  Any functional of `ζ` vanishes at `6` -- by Lemma O, from
multiplicativity alone (not from `Λ`'s definition). -/
theorem zeta_b_six {b : ArithmeticFunction ℝ} (hb : IsLogDerivCoeff logWeight ζ b) : b 6 = 0 :=
  primePow_support_of_isMultiplicative logWeight_completelyAdditive
    zeta_completelyMultiplicative.isMultiplicative hb 6 six_not_isPrimePow

/-- ... and the functional is `Λ` (uniqueness), which is not identically zero. -/
theorem zeta_functional_eq_vonMangoldt {b : ArithmeticFunction ℝ}
    (hb : IsLogDerivCoeff logWeight ζ b) : b = Λ :=
  logDerivCoeff_unique (by simp) hb zeta_logDerivCoeff

/-- The generation law for `ζ`: `Λ (p^k) = log p`, derived from Lemma O's refinement
rather than from the definition of `Λ`. -/
theorem zeta_generation_law {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) :
    Λ (p ^ k) = Real.log p := by
  have h := generation_law_of_completelyMultiplicative logWeight_completelyAdditive
    zeta_completelyMultiplicative zeta_logDerivCoeff hp k hk
  rw [h]
  simp [natCoe_apply, zeta_apply, hp.ne_zero, logWeight]

/-! ## 2.  Davenport-Heilbronn -/

/-- The DH amplitude as an arithmetic function: period 5, pattern `[1, κ, -κ, -1, 0]`
indexed by `n mod 5` (so `a 0 = 0`, `a 1 = 1`, `a 2 = κ`, `a 3 = -κ`, `a 4 = -1`, `a 5 = 0`). -/
noncomputable def dhAmp : ArithmeticFunction ℝ :=
  ⟨fun n => if n % 5 = 1 then 1 else if n % 5 = 2 then Quasicrystal.dhKappa else
    if n % 5 = 3 then -Quasicrystal.dhKappa else if n % 5 = 4 then -1 else 0, by simp⟩

theorem dhAmp_one : dhAmp 1 = 1 := by simp [dhAmp]
theorem dhAmp_two : dhAmp 2 = Quasicrystal.dhKappa := by simp [dhAmp]
theorem dhAmp_three : dhAmp 3 = -Quasicrystal.dhKappa := by simp [dhAmp]
theorem dhAmp_six : dhAmp 6 = 1 := by simp [dhAmp]

/-- **DH leaks at 6**: `b 6 = (1 + κ²) log 6`. -/
theorem dh_b_six {b : ArithmeticFunction ℝ} (hb : IsLogDerivCoeff logWeight dhAmp b) :
    b 6 = (1 + Quasicrystal.dhKappa ^ 2) * Real.log 6 := by
  rw [b_six dhAmp_one hb, dhAmp_six, dhAmp_two, dhAmp_three,
    show Real.log 6 = Real.log 2 + Real.log 3 by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num]
  ring

theorem dh_b_six_pos {b : ArithmeticFunction ℝ} (hb : IsLogDerivCoeff logWeight dhAmp b) :
    0 < b 6 := by
  rw [dh_b_six hb]
  exact mul_pos (by positivity) (Real.log_pos (by norm_num))

/-- **Lemma O verdict on DH: not multiplicative**, from the composite leak alone. -/
theorem dhAmp_not_isMultiplicative {b : ArithmeticFunction ℝ}
    (hb : IsLogDerivCoeff logWeight dhAmp b) : ¬ dhAmp.IsMultiplicative :=
  not_isMultiplicative_of_composite_leak logWeight_completelyAdditive hb six_not_isPrimePow
    (ne_of_gt (dh_b_six_pos hb))

/-- The hypothesis is inhabited (the functional exists), so the verdict is unconditional. -/
theorem dhAmp_not_isMultiplicative_uncond : ¬ dhAmp.IsMultiplicative :=
  dhAmp_not_isMultiplicative (logDerivCoeffOf_spec dhAmp_one)

/-! ## 3.  Epstein `E` for `x² + 5y²` -/

/-- The shift `(i, j) ↦ (i - n, j - n)` from the `ℕ`-box `[0, 2n]²` onto the `ℤ`-box
`[-n, n]²`. -/
def boxShift (n : ℕ) (ij : ℕ × ℕ) : ℤ × ℤ := ((ij.1 : ℤ) - n, (ij.2 : ℤ) - n)

theorem boxShift_injective (n : ℕ) : Function.Injective (boxShift n) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  simp only [boxShift, Prod.mk.injEq] at h
  ext <;> simp <;> omega

/-- The representations of `n` by `x² + 5y²` with `|x|, |y| ≤ n`, enumerated through the
`ℕ`-box so that the count is a closed computation. -/
def rep5Set (n : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.range (2 * n + 1) ×ˢ Finset.range (2 * n + 1)).filter
    fun ij => ((ij.1 : ℤ) - n) ^ 2 + 5 * ((ij.2 : ℤ) - n) ^ 2 = n).image (boxShift n)

/-- `r(n) = #{(x, y) ∈ ℤ² : x² + 5y² = n}`, as the size of the `ℕ`-box filter. -/
def rep5 (n : ℕ) : ℕ :=
  ((Finset.range (2 * n + 1) ×ˢ Finset.range (2 * n + 1)).filter
    fun ij => ((ij.1 : ℤ) - n) ^ 2 + 5 * ((ij.2 : ℤ) - n) ^ 2 = n).card

theorem rep5_eq_card (n : ℕ) : rep5 n = (rep5Set n).card := by
  rw [rep5Set, Finset.card_image_of_injective _ (boxShift_injective n)]
  rfl

/-- Soundness: every element of `rep5Set n` is a representation of `n`. -/
theorem rep5Set_sound {n : ℕ} {x y : ℤ} (h : (x, y) ∈ rep5Set n) : x ^ 2 + 5 * y ^ 2 = n := by
  simp only [rep5Set, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range, boxShift, Prod.mk.injEq] at h
  obtain ⟨⟨i, j⟩, ⟨-, hij⟩, rfl, rfl⟩ := h
  exact hij

/-- **Completeness**: every integer representation of `n` lies in `rep5Set n` (the box
`|x|, |y| ≤ n` suffices since `x² ≤ n` and `5y² ≤ n`), so `rep5` is the true
representation number, not a truncation. -/
theorem rep5_box_complete {n : ℕ} {x y : ℤ} (h : x ^ 2 + 5 * y ^ 2 = n) :
    (x, y) ∈ rep5Set n := by
  have hn0 : (0 : ℤ) ≤ n := by positivity
  have hx1 : -(n : ℤ) ≤ x := by nlinarith [sq_nonneg y, sq_nonneg (x + 1)]
  have hx2 : x ≤ n := by nlinarith [sq_nonneg y, sq_nonneg (x - 1)]
  have hy1 : -(n : ℤ) ≤ y := by nlinarith [sq_nonneg x, sq_nonneg (y + 1)]
  have hy2 : y ≤ n := by nlinarith [sq_nonneg x, sq_nonneg (y - 1)]
  simp only [rep5Set, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range, boxShift, Prod.mk.injEq]
  refine ⟨((x + n).toNat, (y + n).toNat), ⟨⟨by omega, by omega⟩, ?_⟩, by omega, by omega⟩
  rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
  simpa using h

theorem rep5_one : rep5 1 = 2 := by decide
theorem rep5_two : rep5 2 = 0 := by decide
theorem rep5_three : rep5 3 = 0 := by decide
theorem rep5_six : rep5 6 = 4 := by decide

/-- The Epstein amplitude `a n = r(n) / 2` (`a 0 = 0`, `a 1 = 1`). -/
noncomputable def epsteinAmp : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else (rep5 n : ℝ) / 2, by simp⟩

theorem epsteinAmp_one : epsteinAmp 1 = 1 := by simp [epsteinAmp, rep5_one]
theorem epsteinAmp_two : epsteinAmp 2 = 0 := by simp [epsteinAmp, rep5_two]
theorem epsteinAmp_three : epsteinAmp 3 = 0 := by simp [epsteinAmp, rep5_three]
theorem epsteinAmp_six : epsteinAmp 6 = 2 := by norm_num [epsteinAmp, rep5_six]

/-- **E leaks at 6**: `b 6 = 2 log 6`. -/
theorem epstein_b_six {b : ArithmeticFunction ℝ} (hb : IsLogDerivCoeff logWeight epsteinAmp b) :
    b 6 = 2 * Real.log 6 := by
  rw [b_six epsteinAmp_one hb, epsteinAmp_six, epsteinAmp_two, epsteinAmp_three]
  ring

theorem epstein_b_six_ne_zero {b : ArithmeticFunction ℝ}
    (hb : IsLogDerivCoeff logWeight epsteinAmp b) : b 6 ≠ 0 := by
  rw [epstein_b_six hb]
  exact mul_ne_zero two_ne_zero (ne_of_gt (Real.log_pos (by norm_num)))

/-- **Lemma O verdict on E: not multiplicative**, from the composite leak. -/
theorem epsteinAmp_not_isMultiplicative {b : ArithmeticFunction ℝ}
    (hb : IsLogDerivCoeff logWeight epsteinAmp b) : ¬ epsteinAmp.IsMultiplicative :=
  not_isMultiplicative_of_composite_leak logWeight_completelyAdditive hb six_not_isPrimePow
    (epstein_b_six_ne_zero hb)

theorem epsteinAmp_not_isMultiplicative_uncond : ¬ epsteinAmp.IsMultiplicative :=
  epsteinAmp_not_isMultiplicative (logDerivCoeffOf_spec epsteinAmp_one)

/-- Anti-phantom cross-check, independent of the recursion: `a 6 = 2 ≠ 0 = a 2 * a 3`. -/
theorem epsteinAmp_not_isMultiplicative_direct : ¬ epsteinAmp.IsMultiplicative := by
  intro h
  have := h.2 (show Nat.Coprime 2 3 by norm_num)
  rw [epsteinAmp_six, epsteinAmp_two, epsteinAmp_three] at this
  norm_num at this

end LemmaO
