/- telperion 0.1.6 | family LeakageInstances | input-hash 511b72f4e0ce77a5
   23 theorems, 8 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib
import LeakageDictionary

namespace LeakageInstances

/-! ### Instance `leak_chi5` -- period 5, index n = 6: VANISHES (completely multiplicative)

    Amplitude vector `[a 1, ..., a 5] = [1, -1, -1, 1, 0]`.
    Re-derived coefficient row (exact symbolic divisor recursion):
      b 1 = 0
      b 2 = -Lg2
      b 3 = -Lg3
      b 6 = 0
    conjecture1_proved = False. -/

noncomputable def leak_chi5_amp : ℕ → ℝ := fun n =>
  if n % 5 = 1 then (1 : ℝ) else
  if n % 5 = 2 then -(1 : ℝ) else
  if n % 5 = 3 then -(1 : ℝ) else
  if n % 5 = 4 then (1 : ℝ) else
  (0 : ℝ)

@[simp] theorem leak_chi5_amp_1 : leak_chi5_amp 1 = (1 : ℝ) := by
  norm_num [leak_chi5_amp]
@[simp] theorem leak_chi5_amp_2 : leak_chi5_amp 2 = -(1 : ℝ) := by
  norm_num [leak_chi5_amp]
@[simp] theorem leak_chi5_amp_3 : leak_chi5_amp 3 = -(1 : ℝ) := by
  norm_num [leak_chi5_amp]
@[simp] theorem leak_chi5_amp_6 : leak_chi5_amp 6 = (1 : ℝ) := by
  norm_num [leak_chi5_amp]

theorem leak_chi5_b_1 {b : ℕ → ℝ} (hb : Quasicrystal.IsLogDerivCoeff leak_chi5_amp b) :
    b 1 = 0 := by
  have h := hb 1 (by norm_num)
  rw [show (1:ℕ).divisors = {1} from by decide] at h
  simpa using h.symm

theorem leak_chi5_b_2 {b : ℕ → ℝ} (hb : Quasicrystal.IsLogDerivCoeff leak_chi5_amp b) :
    b 2 = -Real.log 2 := by
  have h := hb 2 (by norm_num)
  push_cast at h
  rw [show (2:ℕ).divisors = {1, 2} from by decide] at h
  rw [Finset.sum_insert (by decide), Finset.sum_singleton] at h
  rw [leak_chi5_b_1 hb] at h
  norm_num [leak_chi5_amp] at h
  linarith [h]

theorem leak_chi5_b_3 {b : ℕ → ℝ} (hb : Quasicrystal.IsLogDerivCoeff leak_chi5_amp b) :
    b 3 = -Real.log 3 := by
  have h := hb 3 (by norm_num)
  push_cast at h
  rw [show (3:ℕ).divisors = {1, 3} from by decide] at h
  rw [Finset.sum_insert (by decide), Finset.sum_singleton] at h
  rw [leak_chi5_b_1 hb] at h
  norm_num [leak_chi5_amp] at h
  linarith [h]

theorem leak_chi5_b_6 {b : ℕ → ℝ} (hb : Quasicrystal.IsLogDerivCoeff leak_chi5_amp b) :
    b 6 = (0 : ℝ) := by
  have h := hb 6 (by norm_num)
  push_cast at h
  have hlog : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = (2 : ℝ) * ((3 : ℝ)) by norm_num]
    rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [hlog] at h
  rw [show (6:ℕ).divisors = {1, 2, 3, 6} from by decide] at h
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton] at h
  rw [leak_chi5_b_1 hb, leak_chi5_b_2 hb, leak_chi5_b_3 hb] at h
  norm_num [leak_chi5_amp] at h
  linarith [h]

/-- **Composite amplitude VANISHES** at `n = 6`, RE-DERIVED from the divisor
    recursion (not imported from the general dictionary): the coefficient row
    cancels exactly.  The amplitude is completely multiplicative, so this is the
    POSITIVE control of `Quasicrystal.composite_bragg_amplitude_zero`. -/
theorem leak_chi5_composite_vanishes {b : ℕ → ℝ}
    (hb : Quasicrystal.IsLogDerivCoeff leak_chi5_amp b) : b 6 = 0 :=
  leak_chi5_b_6 hb

/-! ### Instance `leak_dh` -- period 5, index n = 6: LEAKS (not completely multiplicative)

    Amplitude vector `[a 1, ..., a 5] = [1, K, -K, -1, 0]`.
    Re-derived coefficient row (exact symbolic divisor recursion):
      b 1 = 0
      b 2 = K*Lg2
      b 3 = -K*Lg3
      b 6 = K**2*Lg2 + K**2*Lg3 + Lg2 + Lg3
    conjecture1_proved = False. -/

noncomputable def leak_dh_amp : ℕ → ℝ := fun n =>
  if n % 5 = 1 then (1 : ℝ) else
  if n % 5 = 2 then Quasicrystal.dhKappa else
  if n % 5 = 3 then -Quasicrystal.dhKappa else
  if n % 5 = 4 then -(1 : ℝ) else
  (0 : ℝ)

@[simp] theorem leak_dh_amp_1 : leak_dh_amp 1 = (1 : ℝ) := by
  norm_num [leak_dh_amp]
@[simp] theorem leak_dh_amp_2 : leak_dh_amp 2 = Quasicrystal.dhKappa := by
  norm_num [leak_dh_amp]
@[simp] theorem leak_dh_amp_3 : leak_dh_amp 3 = -Quasicrystal.dhKappa := by
  norm_num [leak_dh_amp]
@[simp] theorem leak_dh_amp_6 : leak_dh_amp 6 = (1 : ℝ) := by
  norm_num [leak_dh_amp]

theorem leak_dh_b_1 {b : ℕ → ℝ} (hb : Quasicrystal.IsLogDerivCoeff leak_dh_amp b) :
    b 1 = 0 := by
  have h := hb 1 (by norm_num)
  rw [show (1:ℕ).divisors = {1} from by decide] at h
  simpa using h.symm

theorem leak_dh_b_2 {b : ℕ → ℝ} (hb : Quasicrystal.IsLogDerivCoeff leak_dh_amp b) :
    b 2 = Real.log 2 * Quasicrystal.dhKappa := by
  have h := hb 2 (by norm_num)
  push_cast at h
  rw [show (2:ℕ).divisors = {1, 2} from by decide] at h
  rw [Finset.sum_insert (by decide), Finset.sum_singleton] at h
  rw [leak_dh_b_1 hb] at h
  norm_num [leak_dh_amp] at h
  linarith [h]

theorem leak_dh_b_3 {b : ℕ → ℝ} (hb : Quasicrystal.IsLogDerivCoeff leak_dh_amp b) :
    b 3 = -Real.log 3 * Quasicrystal.dhKappa := by
  have h := hb 3 (by norm_num)
  push_cast at h
  rw [show (3:ℕ).divisors = {1, 3} from by decide] at h
  rw [Finset.sum_insert (by decide), Finset.sum_singleton] at h
  rw [leak_dh_b_1 hb] at h
  norm_num [leak_dh_amp] at h
  linarith [h]

theorem leak_dh_b_6 {b : ℕ → ℝ} (hb : Quasicrystal.IsLogDerivCoeff leak_dh_amp b) :
    b 6 = Real.log 2 * Quasicrystal.dhKappa ^ 2 + Real.log 3 * Quasicrystal.dhKappa ^ 2 + Real.log 2 + Real.log 3 := by
  have h := hb 6 (by norm_num)
  push_cast at h
  have hlog : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = (2 : ℝ) * ((3 : ℝ)) by norm_num]
    rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [hlog] at h
  rw [show (6:ℕ).divisors = {1, 2, 3, 6} from by decide] at h
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton] at h
  rw [leak_dh_b_1 hb, leak_dh_b_2 hb, leak_dh_b_3 hb] at h
  norm_num [leak_dh_amp] at h
  linarith [h]

/-- **Composite amplitude LEAKS** at `n = 6`: the re-derived coefficient is
    strictly positive, so the Bragg amplitude at the composite frequency
    `log 6` does NOT vanish. -/
theorem leak_dh_composite_leak_pos {b : ℕ → ℝ}
    (hb : Quasicrystal.IsLogDerivCoeff leak_dh_amp b) : 0 < b 6 := by
  rw [leak_dh_b_6 hb]
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  nlinarith [hl2, hl3, sq_nonneg Quasicrystal.dhKappa]

/-- **The negative control bites.**  A nonzero COMPOSITE Bragg amplitude refuses
    complete multiplicativity of the amplitude sequence, through the island's
    contrapositive instrument.  Nothing but the recursion is consumed. -/
theorem leak_dh_not_completelyMultiplicative {b : ℕ → ℝ}
    (hb : Quasicrystal.IsLogDerivCoeff leak_dh_amp b) :
    ¬ Quasicrystal.CompletelyMultiplicative leak_dh_amp :=
  Quasicrystal.not_completelyMultiplicative_of_composite_leak hb (by norm_num)
    (by decide) (ne_of_gt (leak_dh_composite_leak_pos hb))

/-- **The certified number.**  The re-derived composite amplitude at `n = 6`,
    pinned to a rational interval of width ~1.35e-07 from the island's
    kernel-proved atom enclosures.  Roadmap value: `b(6) = +1.9364`. -/
theorem leak_dh_enclosure {b : ℕ → ℝ}
    (hb : Quasicrystal.IsLogDerivCoeff leak_dh_amp b) :
    (56621428787156489290615677868224140533379 / 29241228656640000000000000000000000000000 : ℝ) < b 6 ∧ b 6 < (14155358183682789308270590739585149546571 / 7310307164160000000000000000000000000000 : ℝ) := by
  rw [leak_dh_b_6 hb]
  obtain ⟨hb0lo, hb0hi⟩ := Quasicrystal.dhKappa_bounds
  obtain ⟨hb1lo, hb1hi⟩ := Quasicrystal.log_two_bounds
  obtain ⟨hb2lo, hb2hi⟩ := Quasicrystal.log_three_bounds
  constructor <;> nlinarith [hb0lo, hb0hi, hb1lo, hb1hi, hb2lo, hb2hi, sq_nonneg Quasicrystal.dhKappa]

/-- The same enclosure at five decimals -- the human-readable form the registry
    node quotes, and the form that pins the published four-decimal value. -/
theorem leak_dh_enclosure_decimal {b : ℕ → ℝ}
    (hb : Quasicrystal.IsLogDerivCoeff leak_dh_amp b) :
    (38727/20000 : ℝ) < b 6 ∧ b 6 < (48409/25000 : ℝ) := by
  obtain ⟨h1, h2⟩ := leak_dh_enclosure hb
  exact ⟨by norm_num at h1 ⊢; linarith, by norm_num at h2 ⊢; linarith⟩

/-- **Non-vacuity.**  The functional exists for this amplitude, so the conditional
    theorems above are not empty: the leak is an unconditional theorem. -/
theorem leak_dh_leak_exists :
    ∃ b : ℕ → ℝ, Quasicrystal.IsLogDerivCoeff leak_dh_amp b ∧ 0 < b 6 := by
  obtain ⟨b, hb⟩ := Quasicrystal.exists_logDerivCoeff (a := leak_dh_amp)
    (by norm_num [leak_dh_amp])
  exact ⟨b, hb, leak_dh_composite_leak_pos hb⟩

/-- **THE FALSIFICATION TWIN.**  Delete the multiplicativity hypothesis from
    `Quasicrystal.composite_bragg_amplitude_zero` and the statement is FALSE --
    refuted in-kernel by THIS amplitude at `n = 6`.

    This is the probe that would fail if the dictionary were the `rfl`-grade von
    Mangoldt-support statement in disguise: a support-level reading admits no
    counterexample, because `Λ` vanishes off prime powers unconditionally.  The
    log-derivative coefficient functional does not. -/
theorem leak_dh_multiplicativity_is_necessary :
    ¬ (∀ a b : ℕ → ℝ, a 1 = 1 → Quasicrystal.IsLogDerivCoeff a b →
        ∀ m : ℕ, 0 < m → ¬ IsPrimePow m → b m = 0) := by
  intro H
  obtain ⟨b, hb, hpos⟩ := leak_dh_leak_exists
  have := H leak_dh_amp b (by norm_num [leak_dh_amp]) hb 6 (by norm_num) (by decide)
  linarith

end LeakageInstances
