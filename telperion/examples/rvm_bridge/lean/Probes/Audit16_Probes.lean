/- Audit probes for E6Bridge16. -/
import E6Bridge16
open Zeta23 Complex MeasureTheory Filter Topology RvMBridge6 RvMBridge11 RvMBridge16 WeilExplicit

/- 1. envelopeCsharp lam > 0 for every lam > 0 (expected SUCCESS). -/
theorem audit_envelopeCsharp_pos {lam : ℝ} (hlam : 0 < lam) : 0 < envelopeCsharp lam := by
  unfold envelopeCsharp
  have := tailRadius_nonneg lam
  have := Real.exp_pos (primeAbs lam + 1 / 2)
  have := Real.pi_pos
  have := Real.sqrt_pos.mpr hlam
  positivity
#print axioms audit_envelopeCsharp_pos

/- 2. The theorem is not applicable at c = 0 (expected FAIL: envelopeCsharp lam ≤ 0 is false). -/
example (lam : ℝ) (hlam : 0 < lam) : 0 ≤ (zeroSide (gaussTest 0 lam)).re :=
  gaussian_positivity_envelope_sharp 0 lam hlam (by simp; linarith [audit_envelopeCsharp_pos hlam])

/- 3. Height corollaries consume the sharp envelope; both signs of c (expected SUCCESS). -/
example {lam T : ℝ} (hlam : 0 < lam) (hT : envelopeCsharp lam ≤ T) (c : ℝ) (hc : T ≤ |c|) :
    0 ≤ (zeroSide (gaussTest c lam)).re :=
  gaussian_positivity_envelope_sharp c lam hlam (hT.trans hc)
example {lam T : ℝ} (hlam : 0 < lam) (hT : envelopeCsharp lam ≤ T) :
    0 ≤ (zeroSide (gaussTest (-(T + 5)) lam)).re :=
  gaussian_positivity_above_height hlam hT _ (by rw [abs_neg, abs_of_pos (by linarith [audit_envelopeCsharp_pos hlam])]; linarith)

/- 4. The log form's doubling step, re-proved abstractly: M + add ≤ 2M ≤ T from
   log(2M) ≤ log T, where 2M = 2π e^{P+1/2}·2 and log(2M) = log(2π) + P + 1/2 + log 2 (expected SUCCESS). -/
theorem audit_log_form (P T add : ℝ) (hT : 0 < T)
    (hlog : P + 1 / 2 + Real.log 2 ≤ Real.log (T / (2 * Real.pi)))
    (hadd : add ≤ 2 * Real.pi * Real.exp (P + 1 / 2)) :
    2 * Real.pi * Real.exp (P + 1 / 2) + add ≤ T := by
  set M := 2 * Real.pi * Real.exp (P + 1 / 2) with hM
  have hM0 : 0 < M := by positivity
  have e : Real.log (M * 2) = Real.log (2 * Real.pi) + (P + 1 / 2 + Real.log 2) := by
    rw [hM, Real.log_mul (by positivity) (by norm_num),
      Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hd : Real.log (T / (2 * Real.pi)) = Real.log T - Real.log (2 * Real.pi) :=
    Real.log_div hT.ne' (by positivity)
  have hle : Real.log (M * 2) ≤ Real.log T := by rw [e]; linarith
  have h2M : M * 2 ≤ T := (Real.log_le_log_iff (by positivity) hT).mp hle
  linarith
#print axioms audit_log_form

/- 5. primeAbs is a genuine (summable) series, and the crude closed-form bound consumes it
   (expected SUCCESS). -/
example {lam : ℝ} (hlam : 0 < lam) : Summable (primeAbsTerm lam) := summable_primeAbsTerm hlam
example {lam : ℝ} (hlam : 0 < lam) : primeAbs lam ≤ 16 * Real.exp (16 * lam) := primeAbs_le_crude hlam

/- 6. The complex-frequency transform specialises to the real line and to the pole points
   consistently with E6Bridge11's line formula (expected SUCCESS). -/
example {c lam : ℝ} (hlam : 0 < lam) (r : ℝ) :
    ∫ u : ℝ, autocorrGauss c lam u * Complex.exp (I * (r : ℂ) * u) = gaussTest c lam r :=
  fourier_autocorrGauss hlam r
example {c lam : ℝ} (hlam : 0 < lam) :
    weilKernel (autocorr (RvMBridge8.gaussPhi c lam)) 0 = gaussTest c lam (I / 2) :=
  weilKernel_zero_eq_gaussTest hlam
