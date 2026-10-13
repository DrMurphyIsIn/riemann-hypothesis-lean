/- Audit probes for E6Bridge30 (auditor-forward, 2026-09-22). -/
import E6Bridge30
open WeilExplicit RvMBridge11 RvMBridge16 RvMBridge30

#print axioms gaussian_positivity_small_lam_3e3

/- 1. Chain re-composed: zero-side form from the explicit formula and the primes-side theorem
   (expected SUCCESS). -/
example (c lam : ℝ) (hlam : 0 < lam) (hle : lam ≤ 3 / 2000) :
    0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re := by
  rw [gaussianExplicitFormula c lam hlam]; exact re_weilForm_gauss_nonneg_3e3 c lam hlam hle

/- 2. The 3/2000 theorem subsumes the 1/1000 one and E6Bridge11's existential (expected SUCCESS). -/
example (c lam : ℝ) (hlam : 0 < lam) (hle : lam ≤ 1 / 1000) :
    0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re :=
  gaussian_positivity_small_lam_3e3 c lam hlam (by linarith)
example : ∃ lam₀ > 0, ∀ c lam : ℝ, 0 < lam → lam ≤ lam₀ →
    0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re :=
  ⟨3 / 2000, by norm_num, fun c lam h1 h2 => gaussian_positivity_small_lam_3e3 c lam h1 h2⟩

/- 3. Pole floor, near case, abstractly: cos θ ≥ 0, c sin θ ≥ 0, E ≤ e^{lam/2} give ≥ -e^{lam/2}/2
   (expected SUCCESS). -/
example (c E e θ : ℝ) (hE0 : 0 < E) (hEe : E ≤ e) (hcos : 0 ≤ Real.cos θ) (hcos1 : Real.cos θ ≤ 1)
    (hsin : 0 ≤ c * Real.sin θ) :
    -(e / 2) ≤ E * ((c ^ 2 - 1 / 4) * Real.cos θ + c * Real.sin θ) := by
  nlinarith [mul_nonneg (sq_nonneg c) hcos, mul_nonneg hE0.le hcos]

/- 4. The far-case Taylor step: |c| ≥ 25 gives 8|c|² ≤ |c|⁴/24 (expected SUCCESS). -/
example (x : ℝ) (hx : 25 ≤ x) : 8 * x ^ 2 ≤ x ^ 4 / 24 := by nlinarith [sq_nonneg (x ^ 2 - 25 * x), sq_nonneg x]

/- 5. Cap algebra: e^{-1}/(2π lam) ≤ κ sqrt(lam) A with κ = 4 sqrt(2/π)/e, i.e. the cap constant is
   4 e^{-1} sqrt(2π) sqrt(lam)/π (expected SUCCESS, abstract identity). -/
example (lam : ℝ) (hlam : 0 < lam) :
    Real.exp (-1) / (2 * Real.pi * lam)
      = (4 * Real.exp (-1) * Real.sqrt (2 * Real.pi) * Real.sqrt lam / Real.pi) * gaussA lam := by
  unfold gaussA
  have hs : Real.sqrt lam * Real.sqrt lam = lam := Real.mul_self_sqrt hlam.le
  have hs0 : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hp0 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hp : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi := Real.mul_self_sqrt (by positivity)
  field_simp
  nlinarith [hs, hp, Real.pi_pos]

/- 6. Band-sum arithmetic recomputed from decimal floors and edges (expected SUCCESS). -/
example : (458103 / 20000 : ℝ)
    = (-2.1913 + 4.2315) * 0.5 + (-1.0532 + 2.1913) * 0.9 + (-0.3405 + 1.0532) * 1.5
      + (0.1691 + 0.3405) * 2.4 + (0.5804 - 0.1691) * 3.6 + (0.9303 - 0.5804) * 5.1
      + (1.2333 - 0.9303) * 6.9 + (1.4881 - 1.2333) * 8.9 + (1.7090 - 1.4881) * 11.1
      + (1.9046 - 1.7090) * 13.5 + (2.0804 - 1.9046) * 16.1 + (2.2403 - 2.0804) * 18.9 := by norm_num

/- 7. The two assembly margins are positive with the file's constants (expected SUCCESS). -/
example : (0 : ℝ) < -0.0006 + 2.2403 - 0.0455 * (458103 / 20000) - 1.1448 - 0.001 := by norm_num
example : (0 : ℝ) < -0.001 + 2.3499 - 0.0375 * (2744863 / 100000) - 1.1448 - 0.006 := by norm_num

/- 8. The margin SIGN FLIPS with the cap at lam = 1/500 (κ sqrt(1/500) = 0.0525): the same assembly
   is negative (expected SUCCESS; shows the 12-band data cannot reach 1/500). -/
example : -0.0006 + 2.2403 - 0.0525 * (458103 / 20000 : ℝ) - 1.1448 - 0.001 < 0 := by norm_num

/- 9. The tail comparison is a genuine nonnegative correction: serG t N - serG t (N+M) ≥ 0
   (expected SUCCESS via the antitone sum bound and serF ≥ 0). -/
example (t : ℝ) (N M : ℕ) : 0 ≤ ∑ n ∈ Finset.Ico N (N + M), serF t n :=
  Finset.sum_nonneg fun n _ => serF_nonneg t (Nat.cast_nonneg n)

/- 10. gamma bound consumed (expected SUCCESS). -/
example : Real.eulerMascheroniConstant < 0.6 := lt_of_le_of_lt eulerMascheroni_le (by norm_num)

/- 11. EXPECTED FAIL: the theorem at lam ≤ 1/500. -/
example (c lam : ℝ) (hlam : 0 < lam) (hle : lam ≤ 1 / 500) :
    0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re :=
  gaussian_positivity_small_lam_3e3 c lam hlam (by linarith)

/- 12. EXPECTED FAIL: a floor 0.001 above the file's at the outer edge 18.9 is not certified by the
   same N = 40 rational bound (the floors are tight to the method). -/
example : (22413 / 10000 : ℝ) ≤ psiR (189 / 10) := by
  refine le_trans ?_ (psiR_ge_rational (189 / 10) 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/- 13. EXPECTED FAIL: pole_floor outside its stated range lam ≤ 1/50. -/
example (c : ℝ) : -(Real.exp ((1 / 40 : ℝ) / 2) / 2)
    ≤ (RvMBridge6.gaussTest c (1 / 40) (Complex.I / 2)).re + (RvMBridge6.gaussTest c (1 / 40) (-Complex.I / 2)).re :=
  pole_floor (by norm_num) (by norm_num)
