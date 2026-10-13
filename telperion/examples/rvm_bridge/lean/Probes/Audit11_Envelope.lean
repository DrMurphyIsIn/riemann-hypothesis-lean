/- Audit probes for the envelope section of E6Bridge11. -/
import E6Bridge13
open Zeta23 Complex MeasureTheory Filter Topology RvMBridge6 RvMBridge8 RvMBridge11 WeilExplicit

/- 1. Tail-mass constant: gaussA (lam/2) = 2√2 gaussA lam, and the pointwise tail bound
   bumpR c lam r ≤ e^{-4} bumpR c (lam/2) r for |r - c| ≥ 2/√lam (expected SUCCESS). -/
example {lam : ℝ} (h : 0 < lam) : gaussA (lam / 2) = 2 * Real.sqrt 2 * gaussA lam := gaussA_half h
theorem audit_tail_pointwise {c lam r : ℝ} (hlam : 0 < lam) (hr : 2 / Real.sqrt lam ≤ |r - c|) :
    bumpR c lam r ≤ Real.exp (-4) * bumpR c (lam / 2) r := by
  rw [bumpR_half]
  unfold bumpR
  have hsl : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsq : (2 / Real.sqrt lam) ^ 2 ≤ (r - c) ^ 2 := by
    rw [← sq_abs (r - c)]; exact pow_le_pow_left₀ (by positivity) hr 2
  have h4 : 4 ≤ lam * (r - c) ^ 2 := by
    have : (2 / Real.sqrt lam) ^ 2 = 4 / lam := by
      rw [div_pow, Real.sq_sqrt hlam.le]; norm_num
    rw [this] at hsq
    rwa [div_le_iff₀ hlam, mul_comm] at hsq
  have hexp : Real.exp (-(2 * lam) * (r - c) ^ 2) ≤ Real.exp (-4) * Real.exp (-lam * (r - c) ^ 2) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith
  calc (r - c) ^ 2 * Real.exp (-(2 * lam) * (r - c) ^ 2)
      ≤ (r - c) ^ 2 * (Real.exp (-4) * Real.exp (-lam * (r - c) ^ 2)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = Real.exp (-4) * ((r - c) ^ 2 * Real.exp (-lam * (r - c) ^ 2)) := by ring
#print axioms audit_tail_pointwise

/- 2. AM-GM prime bound direction: (log n)^2/(16 lam) ≥ 2 log n - 16 lam, hence
   e^{-(log n)^2/(16 lam)} ≤ e^{16 lam} n^{-2} for n ≥ 1 (expected SUCCESS). -/
theorem audit_amgm (x lam : ℝ) (hlam : 0 < lam) : 2 * x - 16 * lam ≤ x ^ 2 / (16 * lam) := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (x - 16 * lam)]
#print axioms audit_amgm

/- 3. re_digamma_quarter_ge_log needs |r| ≥ 2 (so that 5/t^2 ≤ 5 with t = r/2); at |r| = 1 the
   lemma does not apply (expected FAIL). -/
example : Real.log (|(1 : ℝ)| / 2) - 5 ≤ (Complex.digamma (((1 / 4 : ℝ) : ℂ) + I * (((1 : ℝ) / 2 : ℝ) : ℂ))).re :=
  re_digamma_quarter_ge_log (by norm_num)

/- 4. |c| - L > 0 is forced: envelopeC lam ≥ 2 + 2/√lam (expected SUCCESS). -/
theorem audit_envelopeC_ge {lam : ℝ} (hlam : 0 < lam) : 2 + 2 / Real.sqrt lam ≤ envelopeC lam := by
  unfold envelopeC
  have : (1 : ℝ) ≤ Real.exp (9 + 2 * envelopeX lam) := by
    rw [Real.one_le_exp_iff]; linarith [envelopeX_nonneg lam]
  linarith
#print axioms audit_envelopeC_ge

/- 5. Both signs of c: the primes-side envelope theorem at a large NEGATIVE centre, and the
   one-sided corollary is derived from the |c| form (expected SUCCESS). -/
example (lam : ℝ) (hlam : 0 < lam) (hc : envelopeC lam ≤ |(-(envelopeC lam + 7) : ℝ)|) :
    0 ≤ (archSide (autocorr (gaussPhi (-(envelopeC lam + 7)) lam))
        - primeSide (autocorr (gaussPhi (-(envelopeC lam + 7)) lam))).re :=
  re_weilForm_gauss_nonneg_of_large_c _ lam hlam hc
example (lam : ℝ) (hlam : 0 < lam) :
    envelopeC lam ≤ |(-(envelopeC lam + 7) : ℝ)| := by
  rw [abs_neg]
  exact le_trans (by linarith) (le_abs_self (envelopeC lam + 7))
example : ∀ lam : ℝ, 0 < lam → ∃ c₁ : ℝ, ∀ c : ℝ, c₁ ≤ c →
    0 ≤ (zeroSide (gaussTest c lam)).re := gaussian_positivity_envelope'

/- 6. The envelope threshold is load-bearing: at c = 0 the theorem does not apply
   (expected FAIL: envelopeC lam ≤ 0 is false). -/
example (lam : ℝ) (hlam : 0 < lam) : 0 ≤ (zeroSide (gaussTest 0 lam)).re :=
  gaussian_positivity_envelope 0 lam hlam (by simp [envelopeC]; positivity)
