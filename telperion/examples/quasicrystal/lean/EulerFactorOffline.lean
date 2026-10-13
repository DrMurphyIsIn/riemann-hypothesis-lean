/-
  EulerFactorOffline.lean -- PROGRAM MIRRORMERE torus-section ladder, rung T2:
  THE NEGATIVE CONTROL (QC_TORUS_SECTION_LADDER memo section 4b).

  The p = 2 Euler factor 1 - 2^(-s), read on the critical line s = 1/2 + ix, is the
  two-frequency section
      twoFreq (1, -(1/sqrt 2); 0, -log 2) (x) = 1 - (1/sqrt 2) * e^{-i (log 2) x}.
  Its zeros sit UNIFORMLY at Im x = 1/2 (they are the points Re s = 0, s = 2 pi i k / log 2),
  so per-rung real-rootedness FAILS.  This is exactly what `twoFreq_realRooted_iff`
  (TwoFreqRigidity, R3(n=2)) predicts: the coefficient moduli are ||1|| = 1 and
  ||-(1/sqrt 2)|| = 1/sqrt 2 < 1, and unequal modulus puts every zero on the single
  off-line horizontal Im x = -(1/w) log|c1/c2| = (1/log 2) * log(sqrt 2) = 1/2.

  Registry node: MM_euler_factor_section_offline (statement mirrored VERBATIM below,
  name `euler_factor_section_offline`).  The `not` is the content: it certifies that no
  per-rung line-membership claim survives finite truncation (Turan/Montgomery
  obstruction, in-house); critical-line membership is an infinite-N continuation
  phenomenon.

  Companion (NOT a node): the explicit witness x = i/2, so the negative control carries
  a concrete off-line zero and not merely a refuted universal.

  Certificate shape: the Telperion SelfInversiveRigidityEmitter `mode="offline"`
  (examples/selfinversive_rigidity/generate.py) emits the same refutation for the
  p = 2, 3, 5 Euler-factor sections from an exact rational normSq inequality; this file
  is the hand-stated node so the registry statement text appears verbatim.

  MODULE NAME: the ladder's T1 (dictionary / N=2 rigidity) items live in a sibling
  `TorusSectionLadder` module authored in parallel; this rung is kept in its own module so
  the two can be built independently (the islands share one on-disk .lake olean cache, in
  which a same-named module would clobber).  Both declare into namespace `TorusSectionLadder`
  and merge into one file whenever the branches are reconciled.

  conjecture1_proved = False.  Unconditional finite fact; NOT a proof of RH, and NOT a
  step toward one (it is the obstruction, not the ladder).
-/
import TwoFreqRigidity

open Quasicrystal

namespace TorusSectionLadder

noncomputable section

/-- `-(1/sqrt 2)` is a nonzero real: the p = 2 Euler-factor coefficient. -/
theorem euler_factor_coeff_ne_zero : (-(1 / Real.sqrt 2) : ℝ) ≠ 0 :=
  neg_ne_zero.mpr (by positivity)

/-- The frequencies `0` and `-log 2` differ (`log 2 > 0`). -/
theorem euler_factor_freq_ne : (0 : ℝ) ≠ -(Real.log 2) := by
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  intro h
  linarith

/-- **MM_euler_factor_section_offline** (VERBATIM registry statement).  The p = 2
Euler-factor section is NOT real-rooted: the two-frequency sum
`twoFreq 1 (-(1/sqrt 2)) 0 (-log 2)` has a zero with nonzero imaginary part.
Proof: `.mp` of `twoFreq_realRooted_iff` would force `‖1‖ = ‖-(1/sqrt 2)‖`, i.e.
`1 = 1/sqrt 2`, contradicting `1 < sqrt 2`.  conjecture1_proved = False. -/
theorem euler_factor_section_offline :
    ¬ (∀ x : ℂ,
        twoFreq 1 ((-(1 / Real.sqrt 2) : ℝ) : ℂ) 0 (-(Real.log 2)) x = 0 → x.im = 0) := by
  intro hall
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hc₂ : ((-(1 / Real.sqrt 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr euler_factor_coeff_ne_zero
  have hn := (twoFreq_realRooted_iff 1 _ 0 _ one_ne_zero hc₂ euler_factor_freq_ne).mp hall
  rw [norm_one, Complex.norm_real, Real.norm_eq_abs, abs_neg,
    abs_of_pos (by positivity)] at hn
  -- hn : 1 = 1 / sqrt 2, but 1 / sqrt 2 < 1 since 1 < sqrt 2
  have hlt : 1 / Real.sqrt 2 < 1 := by
    rw [div_lt_one hs]
    exact Real.one_lt_sqrt_two
  linarith

/-- **Explicit off-line witness** (companion, NOT a node): `x = i/2` is a zero of the
p = 2 Euler-factor section.  Indeed `e^{-i (log 2) (i/2)} = e^{(log 2)/2} = sqrt 2`, so
`1 - (1/sqrt 2) * sqrt 2 = 0`.  Its imaginary part is `1/2`, the uniform off-line
displacement predicted by `twoFreq_zero_norm`.  conjecture1_proved = False. -/
theorem euler_factor_section_witness :
    twoFreq 1 ((-(1 / Real.sqrt 2) : ℝ) : ℂ) 0 (-(Real.log 2)) (Complex.I / 2) = 0 := by
  have hc₂ : ((-(1 / Real.sqrt 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr euler_factor_coeff_ne_zero
  rw [twoFreq_eq_zero_iff _ _ _ _ _ one_ne_zero hc₂]
  have harg : (((-(Real.log 2)) - 0 : ℝ) : ℂ) * (Complex.I / 2) * Complex.I
      = ((Real.log 2 / 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [harg, ← Complex.ofReal_exp, Real.exp_half, Real.exp_log (by norm_num)]
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)))
  push_cast
  rw [neg_div_neg_eq, one_div_one_div]

/-- The witness lies off the real line: `Im (i/2) = 1/2 ≠ 0`. -/
theorem euler_factor_section_witness_im : (Complex.I / 2 : ℂ).im = 1 / 2 := by
  simp [Complex.div_ofNat_im]

/-- **Refutation via the witness** (companion): the same node statement, discharged
directly from the explicit zero rather than through the `.mp` direction of the iff.
Two independent routes to the same negative control. -/
theorem euler_factor_section_offline_of_witness :
    ¬ (∀ x : ℂ,
        twoFreq 1 ((-(1 / Real.sqrt 2) : ℝ) : ℂ) 0 (-(Real.log 2)) x = 0 → x.im = 0) := by
  intro hall
  have h := hall (Complex.I / 2) euler_factor_section_witness
  rw [euler_factor_section_witness_im] at h
  norm_num at h

end

end TorusSectionLadder
