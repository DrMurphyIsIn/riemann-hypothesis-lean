/- telperion 0.1.6 | family EulerFactorSectionOffline | input-hash a5a4a9c76c5bb5e5
   8 theorems, 3 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib
import TwoFreqRigidity

namespace EulerFactorSectionOffline

open Quasicrystal

/-- **Off-line displacement** (euler_factor_section_offline): the two-frequency sum
    `F(x) = c₁·e^{iλ₁x} + c₂·e^{iλ₂x}` with `|c₁|² = 1` and
    `|c₂|² = 1/2` is NOT real-rooted -- some zero lies strictly off the
    real line.  By `Quasicrystal.twoFreq_realRooted_iff` real-rootedness is
    EQUIVALENT to `‖c₁‖ = ‖c₂‖`, and the two moduli differ EXACTLY, so the
    universal statement is refuted.  Ladder rung T2 (p = 2).
    A finite section fact; nothing about ζ or RH.  conjecture1_proved = False. -/
theorem euler_factor_section_offline :
    ¬ (∀ x : ℂ, twoFreq 1 ((-(1 / Real.sqrt 2) : ℝ) : ℂ) 0 (-(Real.log 2)) x = 0 → x.im = 0) := by
  have hc1 : (1 : ℂ) ≠ 0 := by
    norm_num [Complex.ext_iff]
  have hc2 : (((-(1 / Real.sqrt 2) : ℝ) : ℂ) : ℂ) ≠ 0 := by
    have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    intro hzero
    have hre := Complex.ofReal_eq_zero.mp hzero
    have hp : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
    linarith
  have hlam : (0 : ℝ) ≠ ((-(Real.log 2))) := by
    have hlp := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    intro hlog
    linarith
  rw [twoFreq_realRooted_iff _ _ _ _ hc1 hc2 hlam]
  intro h
  have h2 : Complex.normSq (1) = Complex.normSq (((-(1 / Real.sqrt 2) : ℝ) : ℂ)) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, h]
  have hns1 : Complex.normSq (1) = (1 : ℝ) := by
    norm_num [Complex.normSq_apply]
  have hns2 : Complex.normSq (((-(1 / Real.sqrt 2) : ℝ) : ℂ)) = ((1 / 2) : ℝ) := by
    rw [Complex.normSq_ofReal, neg_mul_neg, div_mul_div_comm, one_mul,
      Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [hns1, hns2] at h2
  norm_num at h2

/-- Existence form of `euler_factor_section_offline`: an explicit zero off the real line.
    conjecture1_proved = False. -/
theorem euler_factor_section_offline_offline_zero :
    ∃ x : ℂ, twoFreq 1 ((-(1 / Real.sqrt 2) : ℝ) : ℂ) 0 (-(Real.log 2)) x = 0 ∧ x.im ≠ 0 := by
  obtain ⟨x, hx⟩ := not_forall.mp euler_factor_section_offline
  exact ⟨x, (Classical.not_imp.mp hx).1, (Classical.not_imp.mp hx).2⟩

/-- **Certified displacement** (euler_factor_section_offline_displacement): for the Euler factor
    `1 - 2^(-s)` read on `s = 1/2 + i x`, EVERY zero of the section sits at
    `Im x = 1/2` -- i.e. on `Re s = 0`, uniformly.  The ladder's negative control:
    the off-line displacement is 1/2 at this rung, for this prime, with no
    dependence on the truncation.  conjecture1_proved = False. -/
theorem euler_factor_section_offline_displacement :
    ∀ x : ℂ, twoFreq 1 ((-(1 / Real.sqrt 2) : ℝ) : ℂ) 0 (-(Real.log 2)) x = 0 → x.im = 1 / 2 := by
  intro x hz
  have hc1 : (1 : ℂ) ≠ 0 := by
    norm_num [Complex.ext_iff]
  have hc2 : (((-(1 / Real.sqrt 2) : ℝ) : ℂ) : ℂ) ≠ 0 := by
    have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    intro hzero
    have hre := Complex.ofReal_eq_zero.mp hzero
    have hp : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
    linarith
  have hn := twoFreq_zero_norm _ _ _ _ x hc1 hc2 hz
  rw [norm_one, Complex.norm_real, Real.norm_eq_abs, abs_neg,
    abs_of_pos (show (0 : ℝ) < 1 / Real.sqrt 2 by positivity), one_div_one_div] at hn
  have hlog := congrArg Real.log hn
  rw [Real.log_exp, Real.log_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] at hlog
  have hl : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hkey : Real.log 2 * x.im = Real.log 2 * (1 / 2) := by linarith
  exact mul_left_cancel₀ hl.ne' hkey

/-- **Off-line displacement** (euler_factor_section_offline_p3): the two-frequency sum
    `F(x) = c₁·e^{iλ₁x} + c₂·e^{iλ₂x}` with `|c₁|² = 1` and
    `|c₂|² = 1/3` is NOT real-rooted -- some zero lies strictly off the
    real line.  By `Quasicrystal.twoFreq_realRooted_iff` real-rootedness is
    EQUIVALENT to `‖c₁‖ = ‖c₂‖`, and the two moduli differ EXACTLY, so the
    universal statement is refuted.  Ladder rung T2 (p = 3).
    A finite section fact; nothing about ζ or RH.  conjecture1_proved = False. -/
theorem euler_factor_section_offline_p3 :
    ¬ (∀ x : ℂ, twoFreq 1 ((-(1 / Real.sqrt 3) : ℝ) : ℂ) 0 (-(Real.log 3)) x = 0 → x.im = 0) := by
  have hc1 : (1 : ℂ) ≠ 0 := by
    norm_num [Complex.ext_iff]
  have hc2 : (((-(1 / Real.sqrt 3) : ℝ) : ℂ) : ℂ) ≠ 0 := by
    have hs : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    intro hzero
    have hre := Complex.ofReal_eq_zero.mp hzero
    have hp : (0 : ℝ) < 1 / Real.sqrt 3 := by positivity
    linarith
  have hlam : (0 : ℝ) ≠ ((-(Real.log 3))) := by
    have hlp := Real.log_pos (show (1 : ℝ) < 3 by norm_num)
    intro hlog
    linarith
  rw [twoFreq_realRooted_iff _ _ _ _ hc1 hc2 hlam]
  intro h
  have h2 : Complex.normSq (1) = Complex.normSq (((-(1 / Real.sqrt 3) : ℝ) : ℂ)) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, h]
  have hns1 : Complex.normSq (1) = (1 : ℝ) := by
    norm_num [Complex.normSq_apply]
  have hns2 : Complex.normSq (((-(1 / Real.sqrt 3) : ℝ) : ℂ)) = ((1 / 3) : ℝ) := by
    rw [Complex.normSq_ofReal, neg_mul_neg, div_mul_div_comm, one_mul,
      Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  rw [hns1, hns2] at h2
  norm_num at h2

/-- Existence form of `euler_factor_section_offline_p3`: an explicit zero off the real line.
    conjecture1_proved = False. -/
theorem euler_factor_section_offline_p3_offline_zero :
    ∃ x : ℂ, twoFreq 1 ((-(1 / Real.sqrt 3) : ℝ) : ℂ) 0 (-(Real.log 3)) x = 0 ∧ x.im ≠ 0 := by
  obtain ⟨x, hx⟩ := not_forall.mp euler_factor_section_offline_p3
  exact ⟨x, (Classical.not_imp.mp hx).1, (Classical.not_imp.mp hx).2⟩

/-- **Certified displacement** (euler_factor_section_offline_p3_displacement): for the Euler factor
    `1 - 3^(-s)` read on `s = 1/2 + i x`, EVERY zero of the section sits at
    `Im x = 1/2` -- i.e. on `Re s = 0`, uniformly.  The ladder's negative control:
    the off-line displacement is 1/2 at this rung, for this prime, with no
    dependence on the truncation.  conjecture1_proved = False. -/
theorem euler_factor_section_offline_p3_displacement :
    ∀ x : ℂ, twoFreq 1 ((-(1 / Real.sqrt 3) : ℝ) : ℂ) 0 (-(Real.log 3)) x = 0 → x.im = 1 / 2 := by
  intro x hz
  have hc1 : (1 : ℂ) ≠ 0 := by
    norm_num [Complex.ext_iff]
  have hc2 : (((-(1 / Real.sqrt 3) : ℝ) : ℂ) : ℂ) ≠ 0 := by
    have hs : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    intro hzero
    have hre := Complex.ofReal_eq_zero.mp hzero
    have hp : (0 : ℝ) < 1 / Real.sqrt 3 := by positivity
    linarith
  have hn := twoFreq_zero_norm _ _ _ _ x hc1 hc2 hz
  rw [norm_one, Complex.norm_real, Real.norm_eq_abs, abs_neg,
    abs_of_pos (show (0 : ℝ) < 1 / Real.sqrt 3 by positivity), one_div_one_div] at hn
  have hlog := congrArg Real.log hn
  rw [Real.log_exp, Real.log_sqrt (show (0 : ℝ) ≤ 3 by norm_num)] at hlog
  have hl : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hkey : Real.log 3 * x.im = Real.log 3 * (1 / 2) := by linarith
  exact mul_left_cancel₀ hl.ne' hkey

/-- **Off-line displacement** (euler_factor_section_offline_p5): the two-frequency sum
    `F(x) = c₁·e^{iλ₁x} + c₂·e^{iλ₂x}` with `|c₁|² = 1` and
    `|c₂|² = 1/5` is NOT real-rooted -- some zero lies strictly off the
    real line.  By `Quasicrystal.twoFreq_realRooted_iff` real-rootedness is
    EQUIVALENT to `‖c₁‖ = ‖c₂‖`, and the two moduli differ EXACTLY, so the
    universal statement is refuted.  Ladder rung T2 (p = 5).
    A finite section fact; nothing about ζ or RH.  conjecture1_proved = False. -/
theorem euler_factor_section_offline_p5 :
    ¬ (∀ x : ℂ, twoFreq 1 ((-(1 / Real.sqrt 5) : ℝ) : ℂ) 0 (-(Real.log 5)) x = 0 → x.im = 0) := by
  have hc1 : (1 : ℂ) ≠ 0 := by
    norm_num [Complex.ext_iff]
  have hc2 : (((-(1 / Real.sqrt 5) : ℝ) : ℂ) : ℂ) ≠ 0 := by
    have hs : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
    intro hzero
    have hre := Complex.ofReal_eq_zero.mp hzero
    have hp : (0 : ℝ) < 1 / Real.sqrt 5 := by positivity
    linarith
  have hlam : (0 : ℝ) ≠ ((-(Real.log 5))) := by
    have hlp := Real.log_pos (show (1 : ℝ) < 5 by norm_num)
    intro hlog
    linarith
  rw [twoFreq_realRooted_iff _ _ _ _ hc1 hc2 hlam]
  intro h
  have h2 : Complex.normSq (1) = Complex.normSq (((-(1 / Real.sqrt 5) : ℝ) : ℂ)) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, h]
  have hns1 : Complex.normSq (1) = (1 : ℝ) := by
    norm_num [Complex.normSq_apply]
  have hns2 : Complex.normSq (((-(1 / Real.sqrt 5) : ℝ) : ℂ)) = ((1 / 5) : ℝ) := by
    rw [Complex.normSq_ofReal, neg_mul_neg, div_mul_div_comm, one_mul,
      Real.mul_self_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  rw [hns1, hns2] at h2
  norm_num at h2

/-- Existence form of `euler_factor_section_offline_p5`: an explicit zero off the real line.
    conjecture1_proved = False. -/
theorem euler_factor_section_offline_p5_offline_zero :
    ∃ x : ℂ, twoFreq 1 ((-(1 / Real.sqrt 5) : ℝ) : ℂ) 0 (-(Real.log 5)) x = 0 ∧ x.im ≠ 0 := by
  obtain ⟨x, hx⟩ := not_forall.mp euler_factor_section_offline_p5
  exact ⟨x, (Classical.not_imp.mp hx).1, (Classical.not_imp.mp hx).2⟩

end EulerFactorSectionOffline
