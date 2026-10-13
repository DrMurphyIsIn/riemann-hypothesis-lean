/-  HeightFloorEM.lean -- brick H3 (AND_height_floor_kernel), part 3: the analytic reduction.

    M6GAP CROSS-PIN PORT (lane m6gap, 2026-09-23): a copy of
    telperion/examples/zeta_reflection/lean/HeightFloorEM.lean (Lean v4.32.0, Mathlib v4.32.0) onto the dbn
    island (Lean v4.34.0-rc1, Mathlib de5ce8a9).  The ONLY edits are: module names prefixed `M6gap`
    in the imports, every namespace prefixed `M6gap.` (so no declaration can clash with a sibling
    lane's port), and comment wording on this island's word-level placeholder scan.  No proof was
    changed.  Consumed by M6gapHeightFloor (the 55/16 height floor on this island).


    The island's order-3 Euler-Maclaurin enclosure (`EMZetaTail.em_zeta_strip3_enclosure`) at the
    SMALLEST cut `N = 2`, rewritten through `ZetaEMSum.emZetaFinite3_eq_dirichlet`, gives, for
    `0 < Re s < 1`, `s ≠ 0, 1`:

        (s - 1) * emZetaFinite3 s 2 = G2 s := (s - 1) + 2^(-s) (s² + 11 s + 36) / 24,
        ‖ζ(s) - emZetaFinite3 s 2‖ ≤ ‖s (s+1) (s+2)‖ 2^(-(σ+2)) / (72 (σ+2)).

    On the rectangle `1/2 ≤ σ ≤ 1`, `0 ≤ t ≤ 55/16` the second line times `‖s - 1‖` is at most
    `23/100` (`tail_le`).  Hence a zero of `ζ` there forces `‖G2 s‖ ≤ 23/100` (`G2_norm_le_of_zero`).

    `G2_re_im` writes `24 Re G2` and `24 Im G2` as the real polynomials `DI.realA`, `DI.realB` of
    `HeightFloorCheck` evaluated at `m = 2^(-σ)`, `C = cos (t log 2)`, `S = sin (t log 2)`, and
    `G2_norm_gt_of_AB` turns the box inequality `36 < A² + B²` into `1/4 < ‖G2‖`.

    conjecture1_proved = False.  A finite-height estimate; nothing here is about RH.
-/
import M6gapEMZetaTail
import M6gapZetaEMSum
import M6gapHeightFloorCheck

open Complex

namespace M6gap.HeightFloor

/-- The order-3 Euler-Maclaurin main part at `N = 2`, multiplied by `s - 1` (entire). -/
noncomputable def G2 (s : ℂ) : ℂ := (s - 1) + (2 : ℂ) ^ (-s) * (s ^ 2 + 11 * s + 36) / 24

/-- `(s - 1) · emZetaFinite3 s 2 = G2 s`. -/
theorem G2_eq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsre : s.re < 1) :
    (s - 1) * ZetaReflection.emZetaFinite3 s 2 = G2 s := by
  have hre : -1 < (-s).re := by rw [Complex.neg_re]; linarith
  rw [ZetaEMSum.emZetaFinite3_eq_dirichlet hs0 hs1 (by norm_num) hre]
  have hsum : (∑ n ∈ Finset.Ico 1 2, ((n : ℕ) : ℂ) ^ (-s)) = 1 := by
    simp
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hA : ((2 : ℕ) : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
    rw [show (1 - s : ℂ) = 1 + (-s) by ring, Nat.cast_ofNat, Complex.cpow_add _ _ h2,
      Complex.cpow_one]
  have hB : (((2 : ℕ) : ℝ) : ℂ) ^ (-s - 1) = (2 : ℂ) ^ (-s) / 2 := by
    rw [Nat.cast_ofNat, Complex.ofReal_ofNat, Complex.cpow_sub _ _ h2, Complex.cpow_one]
  have hC : ((2 : ℕ) : ℂ) ^ (-s) = (2 : ℂ) ^ (-s) := by rw [Nat.cast_ofNat]
  have hbern : ((bernoulli 2 : ℚ) : ℂ) = 1 / 6 := by
    rw [bernoulli_two]; push_cast; ring
  rw [hsum, hA, hB, hC, hbern]
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  unfold G2
  field_simp
  ring

/-- Norm bound from a bound on the squares of the real and imaginary parts. -/
theorem norm_le_of_sq {z : ℂ} {r : ℝ} (hr : 0 ≤ r) (h : z.re ^ 2 + z.im ^ 2 ≤ r ^ 2) :
    ‖z‖ ≤ r := by
  have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hn := norm_nonneg z
  nlinarith

/-- `2^(-5/2) ≤ 0.1768`. -/
theorem two_rpow_neg_five_halves_le : (2 : ℝ) ^ (-(5 / 2 : ℝ)) ≤ 1768 / 10000 := by
  have hy0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(5 / 2 : ℝ)) := by positivity
  have hsq : ((2 : ℝ) ^ (-(5 / 2 : ℝ))) ^ 2 = 1 / 32 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    rw [show (-(5 / 2 : ℝ) * ((2 : ℕ) : ℝ)) = -((5 : ℕ) : ℝ) by push_cast; ring]
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]; norm_num
  nlinarith

/-- **The tail on the rectangle.**  For `1/2 ≤ σ ≤ 1`, `0 ≤ t ≤ 55/16`, the order-3 remainder
    envelope at `N = 2`, times `‖s - 1‖`, is at most `23/100`. -/
theorem tail_le {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 1) (h3 : 0 ≤ s.im)
    (h4 : s.im ≤ 55 / 16) :
    ‖s - 1‖ * ((1 / 12) * ‖s * (s + 1) * (s + 2)‖ * ((2 : ℕ) : ℝ) ^ (-(s.re + 3 - 1))
      / (s.re + 3 - 1) / 6) ≤ 23 / 100 := by
  have ht2 : s.im ^ 2 ≤ (55 / 16) ^ 2 := by nlinarith
  have n1 : ‖s - 1‖ ≤ 7 / 2 := by
    apply norm_le_of_sq (by norm_num)
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
    nlinarith
  have n2 : ‖s‖ ≤ 18 / 5 := by
    apply norm_le_of_sq (by norm_num); nlinarith
  have n3 : ‖s + 1‖ ≤ 4 := by
    apply norm_le_of_sq (by norm_num)
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero]
    nlinarith
  have n4 : ‖s + 2‖ ≤ 23 / 5 := by
    apply norm_le_of_sq (by norm_num)
    simp only [Complex.add_re, Complex.add_im]
    norm_num
    nlinarith
  have hpow : ((2 : ℕ) : ℝ) ^ (-(s.re + 3 - 1)) ≤ 1768 / 10000 := by
    rw [Nat.cast_ofNat]
    refine le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith :
      -(s.re + 3 - 1) ≤ -(5 / 2 : ℝ))) two_rpow_neg_five_halves_le
  have hpow0 : (0 : ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(s.re + 3 - 1)) := by positivity
  have hden : (5 / 2 : ℝ) ≤ s.re + 3 - 1 := by linarith
  rw [norm_mul, norm_mul]
  calc ‖s - 1‖ * ((1 / 12) * (‖s‖ * ‖s + 1‖ * ‖s + 2‖) * ((2 : ℕ) : ℝ) ^ (-(s.re + 3 - 1))
        / (s.re + 3 - 1) / 6)
      ≤ (7 / 2) * ((1 / 12) * (18 / 5 * 4 * (23 / 5)) * (1768 / 10000) / (5 / 2) / 6) := by
        gcongr
    _ ≤ 23 / 100 := by norm_num

/-- **A zero of `ζ` on the rectangle forces `‖G2 s‖ ≤ 23/100`.** -/
theorem G2_norm_le_of_zero {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re < 1) (h3 : 0 < s.im)
    (h4 : s.im ≤ 55 / 16) (hz : riemannZeta s = 0) : ‖G2 s‖ ≤ 23 / 100 := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at h3; simp at h3
  have hs1 : s ≠ 1 := by intro h; rw [h] at h3; simp at h3
  have hsm1 : s ≠ -1 := by intro h; rw [h] at h3; simp at h3
  have hsm2 : s ≠ -2 := by intro h; rw [h] at h3; simp at h3
  have henc := ZetaReflection.em_zeta_strip3_enclosure (s := s) (by linarith) hs1 (N := 2)
    (by norm_num) hsm1 hsm2
  rw [hz, zero_sub, norm_neg] at henc
  rw [← G2_eq hs0 hs1 h2, norm_mul]
  calc ‖s - 1‖ * ‖ZetaReflection.emZetaFinite3 s 2‖
      ≤ ‖s - 1‖ * ((1 / 12) * ‖s * (s + 1) * (s + 2)‖ * ((2 : ℕ) : ℝ) ^ (-(s.re + 3 - 1))
          / (s.re + 3 - 1) / 6) := by
        gcongr
    _ ≤ 23 / 100 := tail_le h1 h2.le h3.le h4

/-! ### Real and imaginary parts of `G2` -/

/-- `2^(-(σ + t i)) = 2^(-σ) (cos (t log 2) - i sin (t log 2))`, componentwise. -/
theorem two_cpow_neg_re_im (σ t : ℝ) :
    ((2 : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))).re = (2 : ℝ) ^ (-σ) * Real.cos (t * Real.log 2) ∧
      ((2 : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))).im = -((2 : ℝ) ^ (-σ) * Real.sin (t * Real.log 2)) := by
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hlog : Complex.log (2 : ℂ) = ((Real.log 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by norm_num)]; norm_num
  rw [Complex.cpow_def_of_ne_zero h2, hlog]
  have hre : ((Real.log 2 : ℂ) * (-((σ : ℂ) + (t : ℂ) * I))).re = -(σ * Real.log 2) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]
    ring
  have him : ((Real.log 2 : ℂ) * (-((σ : ℂ) + (t : ℂ) * I))).im = -(t * Real.log 2) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]
    ring
  have hm : (2 : ℝ) ^ (-σ) = Real.exp (-(σ * Real.log 2)) := by
    rw [Real.rpow_def_of_pos (by norm_num)]; ring_nf
  rw [Complex.exp_re, Complex.exp_im, hre, him, hm, Real.cos_neg, Real.sin_neg]
  constructor
  · ring
  · ring

/-- `24 · Re G2 (σ + t i) = realA σ t (2^(-σ)) (cos (t log 2)) (sin (t log 2))`, and likewise `Im`. -/
theorem G2_re_im (σ t : ℝ) :
    24 * (G2 ((σ : ℂ) + (t : ℂ) * I)).re =
        DI.realA σ t ((2 : ℝ) ^ (-σ)) (Real.cos (t * Real.log 2)) (Real.sin (t * Real.log 2)) ∧
      24 * (G2 ((σ : ℂ) + (t : ℂ) * I)).im =
        DI.realB σ t ((2 : ℝ) ^ (-σ)) (Real.cos (t * Real.log 2)) (Real.sin (t * Real.log 2)) := by
  obtain ⟨hwr, hwi⟩ := two_cpow_neg_re_im σ t
  set w : ℂ := (2 : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) with hw
  set m : ℝ := (2 : ℝ) ^ (-σ)
  set C : ℝ := Real.cos (t * Real.log 2)
  set S : ℝ := Real.sin (t * Real.log 2)
  have hG : G2 ((σ : ℂ) + (t : ℂ) * I) =
      ((σ : ℂ) + (t : ℂ) * I - 1) + w * (((σ : ℂ) + (t : ℂ) * I) ^ 2
        + 11 * ((σ : ℂ) + (t : ℂ) * I) + 36) / 24 := by
    rw [G2]
  have hwe : w = ((m * C : ℝ) : ℂ) + ((-(m * S) : ℝ) : ℂ) * I := by
    apply Complex.ext
    · rw [hwr]; simp
    · rw [hwi]; simp
  rw [hG, hwe]
  constructor
  · unfold DI.realA
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.one_re, Complex.div_ofNat_re, pow_two]
    norm_num
    ring
  · unfold DI.realB
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.one_im, Complex.div_ofNat_im, pow_two]
    norm_num
    ring

/-- From the box inequality `36 < A² + B²` to `1/4 < ‖G2 s‖`. -/
theorem G2_norm_gt_of_AB {σ t : ℝ}
    (h : 36 < DI.realA σ t ((2 : ℝ) ^ (-σ)) (Real.cos (t * Real.log 2)) (Real.sin (t * Real.log 2))
      ^ 2 + DI.realB σ t ((2 : ℝ) ^ (-σ)) (Real.cos (t * Real.log 2))
        (Real.sin (t * Real.log 2)) ^ 2) :
    1 / 4 < ‖G2 ((σ : ℂ) + (t : ℂ) * I)‖ := by
  obtain ⟨hA, hB⟩ := G2_re_im σ t
  rw [← hA, ← hB] at h
  have hsq : ‖G2 ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 =
      (G2 ((σ : ℂ) + (t : ℂ) * I)).re ^ 2 + (G2 ((σ : ℂ) + (t : ℂ) * I)).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hn := norm_nonneg (G2 ((σ : ℂ) + (t : ℂ) * I))
  nlinarith

end M6gap.HeightFloor
