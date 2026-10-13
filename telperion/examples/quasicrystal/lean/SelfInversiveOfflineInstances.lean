/- telperion 0.1.6 | family SelfInversiveOfflineInstances | input-hash d198bd17e6d2864e
   18 theorems, 3 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib
import TwoFreqRigidity

namespace SelfInversiveOfflineInstances

/-- Concrete two-frequency sum `F(x) = c₁·e^{iλ₁x} + c₂·e^{iλ₂x}` with REAL radical
    coefficients `c₁ = 1·√1`, `c₂ = (-(1 / 2))·√2` (so `|c₁|² = 1`,
    `|c₂|² = 1/2`, EXACT) and frequencies `λ₁ = (0)`, `λ₂ = (-(Real.log 2))`. -/
noncomputable def euler_factor_p2_offline_c1 : ℂ := ((1 * Real.sqrt 1 : ℝ) : ℂ)
noncomputable def euler_factor_p2_offline_c2 : ℂ := (((-(1 / 2)) * Real.sqrt 2 : ℝ) : ℂ)

/-- **Off-line refutation** (euler_factor_p2_offline): since `|c₁|² = 1 ≠ 1/2 = |c₂|²`
    EXACTLY, `‖c₁‖ ≠ ‖c₂‖`, so by the `.mp` direction of `Quasicrystal.twoFreq_realRooted_iff`
    the two-frequency sum is NOT real-rooted — some zero has nonzero imaginary part (in
    fact every zero sits on the single line `Im x = −(1/w)·log|c₁/c₂| ≠ 0`).  Reverse-Dyson
    R3(n=2) negative control: unequal modulus is exactly the off-line signature.
    conjecture1_proved = False. -/
theorem euler_factor_p2_offline :
    ¬ (∀ x : ℂ, Quasicrystal.twoFreq euler_factor_p2_offline_c1 euler_factor_p2_offline_c2 (0) (-(Real.log 2)) x = 0 → x.im = 0) := by
  intro hall
  have hq1 : (0 : ℝ) < 1 := by norm_num
  have hq2 : (0 : ℝ) < 2 := by norm_num
  have hc1 : euler_factor_p2_offline_c1 ≠ 0 := Complex.ofReal_ne_zero.mpr
    (mul_ne_zero (by norm_num) (Real.sqrt_ne_zero'.mpr hq1))
  have hc2 : euler_factor_p2_offline_c2 ≠ 0 := Complex.ofReal_ne_zero.mpr
    (mul_ne_zero (by norm_num) (Real.sqrt_ne_zero'.mpr hq2))
  have hlam : ((0) : ℝ) ≠ (-(Real.log 2)) := by
    have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    intro h
    linarith
  have hn := (Quasicrystal.twoFreq_realRooted_iff euler_factor_p2_offline_c1 euler_factor_p2_offline_c2 (0) (-(Real.log 2))
    hc1 hc2 hlam).mp hall
  -- the kernel checks the EXACT normSq inequality 1 ≠ 1/2
  have hsq : ‖euler_factor_p2_offline_c1‖ ^ 2 ≠ ‖euler_factor_p2_offline_c2‖ ^ 2 := by
    unfold euler_factor_p2_offline_c1 euler_factor_p2_offline_c2
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      sq_abs, sq_abs, mul_pow, mul_pow, Real.sq_sqrt hq1.le, Real.sq_sqrt hq2.le]
    norm_num
  exact hsq (by rw [hn])

/-- **Explicit off-line witness** (euler_factor_p2_offline_witness): `x = i/2` is a zero of the p = 2
    Euler-factor section `1 − (1/√2)·e^{−i (log 2) x}`, since
    `e^{−i (log 2) (i/2)} = e^{(log 2)/2} = √2`.  `Im (i/2) = 1/2`: the uniform
    off-line displacement (the zeros are `s = 2πik/log 2`, i.e. `Re s = 0`).
    conjecture1_proved = False. -/
theorem euler_factor_p2_offline_witness :
    Quasicrystal.twoFreq euler_factor_p2_offline_c1 euler_factor_p2_offline_c2 (0) (-(Real.log 2)) (Complex.I / 2) = 0 := by
  have hq1 : (0 : ℝ) < 1 := by norm_num
  have hq2 : (0 : ℝ) < 2 := by norm_num
  have hc1 : euler_factor_p2_offline_c1 ≠ 0 := Complex.ofReal_ne_zero.mpr
    (mul_ne_zero (by norm_num) (Real.sqrt_ne_zero'.mpr hq1))
  have hc2 : euler_factor_p2_offline_c2 ≠ 0 := Complex.ofReal_ne_zero.mpr
    (mul_ne_zero (by norm_num) (Real.sqrt_ne_zero'.mpr hq2))
  rw [Quasicrystal.twoFreq_eq_zero_iff _ _ _ _ _ hc1 hc2]
  have harg : (((-(Real.log 2)) - 0 : ℝ) : ℂ) * (Complex.I / 2) * Complex.I
      = ((Real.log 2 / 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [harg, ← Complex.ofReal_exp, Real.exp_half, Real.exp_log hq2]
  unfold euler_factor_p2_offline_c1 euler_factor_p2_offline_c2
  rw [← Complex.ofReal_neg, ← Complex.ofReal_div, Complex.ofReal_inj, Real.sqrt_one]
  have hs : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr hq2
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt hq2.le
  field_simp
  linarith [hsq]

/-- The witness is off the real line: `Im (i/2) = 1/2 ≠ 0`, so `euler_factor_p2_offline` also follows
    directly from `euler_factor_p2_offline_witness` (second, independent route). -/
theorem euler_factor_p2_offline_of_witness :
    ¬ (∀ x : ℂ, Quasicrystal.twoFreq euler_factor_p2_offline_c1 euler_factor_p2_offline_c2 (0) (-(Real.log 2)) x = 0 → x.im = 0) := by
  intro hall
  have h := hall (Complex.I / 2) euler_factor_p2_offline_witness
  simp [Complex.div_ofNat_im] at h

/-- The p = 2 Euler-factor coefficients in the registry's spelling:
    `1·√1 = 1` and `(-(1 / 2))·√2 = -(1/√2)` (since `√2·√2 = 2`). -/
theorem euler_factor_p2_offline_c1_eq : euler_factor_p2_offline_c1 = 1 := by
  unfold euler_factor_p2_offline_c1
  rw [Real.sqrt_one]
  norm_num

theorem euler_factor_p2_offline_c2_eq : euler_factor_p2_offline_c2 = ((-(1 / Real.sqrt 2) : ℝ) : ℂ) := by
  unfold euler_factor_p2_offline_c2
  have hq : (0 : ℝ) < 2 := by norm_num
  have hs : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr hq
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt hq.le
  rw [Complex.ofReal_inj]
  field_simp
  linarith [hsq]

/-- **The registry-verbatim form** (euler_factor_p2_offline_node): the p = 2 Euler-factor section
    `twoFreq 1 (-(1/√2)) 0 (-log 2)` is NOT real-rooted.  Identical content to
    `euler_factor_p2_offline`, restated with the coefficients in the mission-registry spelling.
    conjecture1_proved = False. -/
theorem euler_factor_p2_offline_node :
    ¬ (∀ x : ℂ,
        Quasicrystal.twoFreq 1 ((-(1 / Real.sqrt 2) : ℝ) : ℂ) 0 (-(Real.log 2)) x = 0
          → x.im = 0) := by
  rw [← euler_factor_p2_offline_c1_eq, ← euler_factor_p2_offline_c2_eq]
  exact euler_factor_p2_offline

/-- Concrete two-frequency sum `F(x) = c₁·e^{iλ₁x} + c₂·e^{iλ₂x}` with REAL radical
    coefficients `c₁ = 1·√1`, `c₂ = (-(1 / 3))·√3` (so `|c₁|² = 1`,
    `|c₂|² = 1/3`, EXACT) and frequencies `λ₁ = (0)`, `λ₂ = (-(Real.log 3))`. -/
noncomputable def euler_factor_p3_offline_c1 : ℂ := ((1 * Real.sqrt 1 : ℝ) : ℂ)
noncomputable def euler_factor_p3_offline_c2 : ℂ := (((-(1 / 3)) * Real.sqrt 3 : ℝ) : ℂ)

/-- **Off-line refutation** (euler_factor_p3_offline): since `|c₁|² = 1 ≠ 1/3 = |c₂|²`
    EXACTLY, `‖c₁‖ ≠ ‖c₂‖`, so by the `.mp` direction of `Quasicrystal.twoFreq_realRooted_iff`
    the two-frequency sum is NOT real-rooted — some zero has nonzero imaginary part (in
    fact every zero sits on the single line `Im x = −(1/w)·log|c₁/c₂| ≠ 0`).  Reverse-Dyson
    R3(n=2) negative control: unequal modulus is exactly the off-line signature.
    conjecture1_proved = False. -/
theorem euler_factor_p3_offline :
    ¬ (∀ x : ℂ, Quasicrystal.twoFreq euler_factor_p3_offline_c1 euler_factor_p3_offline_c2 (0) (-(Real.log 3)) x = 0 → x.im = 0) := by
  intro hall
  have hq1 : (0 : ℝ) < 1 := by norm_num
  have hq2 : (0 : ℝ) < 3 := by norm_num
  have hc1 : euler_factor_p3_offline_c1 ≠ 0 := Complex.ofReal_ne_zero.mpr
    (mul_ne_zero (by norm_num) (Real.sqrt_ne_zero'.mpr hq1))
  have hc2 : euler_factor_p3_offline_c2 ≠ 0 := Complex.ofReal_ne_zero.mpr
    (mul_ne_zero (by norm_num) (Real.sqrt_ne_zero'.mpr hq2))
  have hlam : ((0) : ℝ) ≠ (-(Real.log 3)) := by
    have hlog3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
    intro h
    linarith
  have hn := (Quasicrystal.twoFreq_realRooted_iff euler_factor_p3_offline_c1 euler_factor_p3_offline_c2 (0) (-(Real.log 3))
    hc1 hc2 hlam).mp hall
  -- the kernel checks the EXACT normSq inequality 1 ≠ 1/3
  have hsq : ‖euler_factor_p3_offline_c1‖ ^ 2 ≠ ‖euler_factor_p3_offline_c2‖ ^ 2 := by
    unfold euler_factor_p3_offline_c1 euler_factor_p3_offline_c2
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      sq_abs, sq_abs, mul_pow, mul_pow, Real.sq_sqrt hq1.le, Real.sq_sqrt hq2.le]
    norm_num
  exact hsq (by rw [hn])

/-- **Explicit off-line witness** (euler_factor_p3_offline_witness): `x = i/2` is a zero of the p = 3
    Euler-factor section `1 − (1/√3)·e^{−i (log 3) x}`, since
    `e^{−i (log 3) (i/2)} = e^{(log 3)/2} = √3`.  `Im (i/2) = 1/2`: the uniform
    off-line displacement (the zeros are `s = 2πik/log 3`, i.e. `Re s = 0`).
    conjecture1_proved = False. -/
theorem euler_factor_p3_offline_witness :
    Quasicrystal.twoFreq euler_factor_p3_offline_c1 euler_factor_p3_offline_c2 (0) (-(Real.log 3)) (Complex.I / 2) = 0 := by
  have hq1 : (0 : ℝ) < 1 := by norm_num
  have hq2 : (0 : ℝ) < 3 := by norm_num
  have hc1 : euler_factor_p3_offline_c1 ≠ 0 := Complex.ofReal_ne_zero.mpr
    (mul_ne_zero (by norm_num) (Real.sqrt_ne_zero'.mpr hq1))
  have hc2 : euler_factor_p3_offline_c2 ≠ 0 := Complex.ofReal_ne_zero.mpr
    (mul_ne_zero (by norm_num) (Real.sqrt_ne_zero'.mpr hq2))
  rw [Quasicrystal.twoFreq_eq_zero_iff _ _ _ _ _ hc1 hc2]
  have harg : (((-(Real.log 3)) - 0 : ℝ) : ℂ) * (Complex.I / 2) * Complex.I
      = ((Real.log 3 / 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [harg, ← Complex.ofReal_exp, Real.exp_half, Real.exp_log hq2]
  unfold euler_factor_p3_offline_c1 euler_factor_p3_offline_c2
  rw [← Complex.ofReal_neg, ← Complex.ofReal_div, Complex.ofReal_inj, Real.sqrt_one]
  have hs : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.mpr hq2
  have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt hq2.le
  field_simp
  linarith [hsq]

/-- The witness is off the real line: `Im (i/2) = 1/2 ≠ 0`, so `euler_factor_p3_offline` also follows
    directly from `euler_factor_p3_offline_witness` (second, independent route). -/
theorem euler_factor_p3_offline_of_witness :
    ¬ (∀ x : ℂ, Quasicrystal.twoFreq euler_factor_p3_offline_c1 euler_factor_p3_offline_c2 (0) (-(Real.log 3)) x = 0 → x.im = 0) := by
  intro hall
  have h := hall (Complex.I / 2) euler_factor_p3_offline_witness
  simp [Complex.div_ofNat_im] at h

/-- The p = 3 Euler-factor coefficients in the registry's spelling:
    `1·√1 = 1` and `(-(1 / 3))·√3 = -(1/√3)` (since `√3·√3 = 3`). -/
theorem euler_factor_p3_offline_c1_eq : euler_factor_p3_offline_c1 = 1 := by
  unfold euler_factor_p3_offline_c1
  rw [Real.sqrt_one]
  norm_num

theorem euler_factor_p3_offline_c2_eq : euler_factor_p3_offline_c2 = ((-(1 / Real.sqrt 3) : ℝ) : ℂ) := by
  unfold euler_factor_p3_offline_c2
  have hq : (0 : ℝ) < 3 := by norm_num
  have hs : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.mpr hq
  have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt hq.le
  rw [Complex.ofReal_inj]
  field_simp
  linarith [hsq]

/-- **The registry-verbatim form** (euler_factor_p3_offline_node): the p = 3 Euler-factor section
    `twoFreq 1 (-(1/√3)) 0 (-log 3)` is NOT real-rooted.  Identical content to
    `euler_factor_p3_offline`, restated with the coefficients in the mission-registry spelling.
    conjecture1_proved = False. -/
theorem euler_factor_p3_offline_node :
    ¬ (∀ x : ℂ,
        Quasicrystal.twoFreq 1 ((-(1 / Real.sqrt 3) : ℝ) : ℂ) 0 (-(Real.log 3)) x = 0
          → x.im = 0) := by
  rw [← euler_factor_p3_offline_c1_eq, ← euler_factor_p3_offline_c2_eq]
  exact euler_factor_p3_offline

/-- Concrete two-frequency sum `F(x) = c₁·e^{iλ₁x} + c₂·e^{iλ₂x}` with REAL radical
    coefficients `c₁ = 1·√1`, `c₂ = (-(1 / 5))·√5` (so `|c₁|² = 1`,
    `|c₂|² = 1/5`, EXACT) and frequencies `λ₁ = (0)`, `λ₂ = (-(Real.log 5))`. -/
noncomputable def euler_factor_p5_offline_c1 : ℂ := ((1 * Real.sqrt 1 : ℝ) : ℂ)
noncomputable def euler_factor_p5_offline_c2 : ℂ := (((-(1 / 5)) * Real.sqrt 5 : ℝ) : ℂ)

/-- **Off-line refutation** (euler_factor_p5_offline): since `|c₁|² = 1 ≠ 1/5 = |c₂|²`
    EXACTLY, `‖c₁‖ ≠ ‖c₂‖`, so by the `.mp` direction of `Quasicrystal.twoFreq_realRooted_iff`
    the two-frequency sum is NOT real-rooted — some zero has nonzero imaginary part (in
    fact every zero sits on the single line `Im x = −(1/w)·log|c₁/c₂| ≠ 0`).  Reverse-Dyson
    R3(n=2) negative control: unequal modulus is exactly the off-line signature.
    conjecture1_proved = False. -/
theorem euler_factor_p5_offline :
    ¬ (∀ x : ℂ, Quasicrystal.twoFreq euler_factor_p5_offline_c1 euler_factor_p5_offline_c2 (0) (-(Real.log 5)) x = 0 → x.im = 0) := by
  intro hall
  have hq1 : (0 : ℝ) < 1 := by norm_num
  have hq2 : (0 : ℝ) < 5 := by norm_num
  have hc1 : euler_factor_p5_offline_c1 ≠ 0 := Complex.ofReal_ne_zero.mpr
    (mul_ne_zero (by norm_num) (Real.sqrt_ne_zero'.mpr hq1))
  have hc2 : euler_factor_p5_offline_c2 ≠ 0 := Complex.ofReal_ne_zero.mpr
    (mul_ne_zero (by norm_num) (Real.sqrt_ne_zero'.mpr hq2))
  have hlam : ((0) : ℝ) ≠ (-(Real.log 5)) := by
    have hlog5 := Real.log_pos (by norm_num : (1 : ℝ) < 5)
    intro h
    linarith
  have hn := (Quasicrystal.twoFreq_realRooted_iff euler_factor_p5_offline_c1 euler_factor_p5_offline_c2 (0) (-(Real.log 5))
    hc1 hc2 hlam).mp hall
  -- the kernel checks the EXACT normSq inequality 1 ≠ 1/5
  have hsq : ‖euler_factor_p5_offline_c1‖ ^ 2 ≠ ‖euler_factor_p5_offline_c2‖ ^ 2 := by
    unfold euler_factor_p5_offline_c1 euler_factor_p5_offline_c2
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      sq_abs, sq_abs, mul_pow, mul_pow, Real.sq_sqrt hq1.le, Real.sq_sqrt hq2.le]
    norm_num
  exact hsq (by rw [hn])

/-- **Explicit off-line witness** (euler_factor_p5_offline_witness): `x = i/2` is a zero of the p = 5
    Euler-factor section `1 − (1/√5)·e^{−i (log 5) x}`, since
    `e^{−i (log 5) (i/2)} = e^{(log 5)/2} = √5`.  `Im (i/2) = 1/2`: the uniform
    off-line displacement (the zeros are `s = 2πik/log 5`, i.e. `Re s = 0`).
    conjecture1_proved = False. -/
theorem euler_factor_p5_offline_witness :
    Quasicrystal.twoFreq euler_factor_p5_offline_c1 euler_factor_p5_offline_c2 (0) (-(Real.log 5)) (Complex.I / 2) = 0 := by
  have hq1 : (0 : ℝ) < 1 := by norm_num
  have hq2 : (0 : ℝ) < 5 := by norm_num
  have hc1 : euler_factor_p5_offline_c1 ≠ 0 := Complex.ofReal_ne_zero.mpr
    (mul_ne_zero (by norm_num) (Real.sqrt_ne_zero'.mpr hq1))
  have hc2 : euler_factor_p5_offline_c2 ≠ 0 := Complex.ofReal_ne_zero.mpr
    (mul_ne_zero (by norm_num) (Real.sqrt_ne_zero'.mpr hq2))
  rw [Quasicrystal.twoFreq_eq_zero_iff _ _ _ _ _ hc1 hc2]
  have harg : (((-(Real.log 5)) - 0 : ℝ) : ℂ) * (Complex.I / 2) * Complex.I
      = ((Real.log 5 / 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [harg, ← Complex.ofReal_exp, Real.exp_half, Real.exp_log hq2]
  unfold euler_factor_p5_offline_c1 euler_factor_p5_offline_c2
  rw [← Complex.ofReal_neg, ← Complex.ofReal_div, Complex.ofReal_inj, Real.sqrt_one]
  have hs : Real.sqrt 5 ≠ 0 := Real.sqrt_ne_zero'.mpr hq2
  have hsq : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt hq2.le
  field_simp
  linarith [hsq]

/-- The witness is off the real line: `Im (i/2) = 1/2 ≠ 0`, so `euler_factor_p5_offline` also follows
    directly from `euler_factor_p5_offline_witness` (second, independent route). -/
theorem euler_factor_p5_offline_of_witness :
    ¬ (∀ x : ℂ, Quasicrystal.twoFreq euler_factor_p5_offline_c1 euler_factor_p5_offline_c2 (0) (-(Real.log 5)) x = 0 → x.im = 0) := by
  intro hall
  have h := hall (Complex.I / 2) euler_factor_p5_offline_witness
  simp [Complex.div_ofNat_im] at h

/-- The p = 5 Euler-factor coefficients in the registry's spelling:
    `1·√1 = 1` and `(-(1 / 5))·√5 = -(1/√5)` (since `√5·√5 = 5`). -/
theorem euler_factor_p5_offline_c1_eq : euler_factor_p5_offline_c1 = 1 := by
  unfold euler_factor_p5_offline_c1
  rw [Real.sqrt_one]
  norm_num

theorem euler_factor_p5_offline_c2_eq : euler_factor_p5_offline_c2 = ((-(1 / Real.sqrt 5) : ℝ) : ℂ) := by
  unfold euler_factor_p5_offline_c2
  have hq : (0 : ℝ) < 5 := by norm_num
  have hs : Real.sqrt 5 ≠ 0 := Real.sqrt_ne_zero'.mpr hq
  have hsq : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt hq.le
  rw [Complex.ofReal_inj]
  field_simp
  linarith [hsq]

/-- **The registry-verbatim form** (euler_factor_p5_offline_node): the p = 5 Euler-factor section
    `twoFreq 1 (-(1/√5)) 0 (-log 5)` is NOT real-rooted.  Identical content to
    `euler_factor_p5_offline`, restated with the coefficients in the mission-registry spelling.
    conjecture1_proved = False. -/
theorem euler_factor_p5_offline_node :
    ¬ (∀ x : ℂ,
        Quasicrystal.twoFreq 1 ((-(1 / Real.sqrt 5) : ℝ) : ℂ) 0 (-(Real.log 5)) x = 0
          → x.im = 0) := by
  rw [← euler_factor_p5_offline_c1_eq, ← euler_factor_p5_offline_c2_eq]
  exact euler_factor_p5_offline

end SelfInversiveOfflineInstances
