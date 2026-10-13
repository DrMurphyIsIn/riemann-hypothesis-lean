/-
  E6Bridge30 -- THE GAUSSIAN WINDOW (2026-09-22): the hypothesis-free small-width region of the
  Wall raised from lam0 = 10^-7 (E6Bridge11.gaussian_positivity_small_lam) to lam0 = 1/1000.

  The statement is the one of E6Bridge11 with the threshold replaced:

      0 <= Re zeroSide (gaussTest c lam)      for EVERY centre c and every 0 < lam <= 1/1000

  (gaussian_positivity_small_lam_1e3), through the Gaussian explicit formula of E6Bridge10, from
  the primes-side form re_weilForm_gauss_nonneg_1e3, which is an UNCONDITIONAL inequality about
  one explicit test function: archSide - primeSide of the autocorrelation of the Gaussian
  derivative phi(u) = K u e^{-u^2/(4 lam)} e^{-icu}.  No zeros are involved anywhere in this file.

  The design is method (a) of docs/GAUSS_WINDOW_DESIGN_2026-09-22.md, section 7 (the spec), with
  eight bands (section G repeats it with twelve bands for lam <= 3/2000, the registry node); every step below is the memo's step of the same number.

    1. pole_floor: the two pole terms are EVALUATED (E6Bridge16: weilKernel f 0 = gaussTest (i/2),
       weilKernel f 1 = gaussTest (-i/2)) and their sum P(c) = 2 e^{-2 lam (c^2 - 1/4)}
       [(c^2 - 1/4) cos(2 lam c) + c sin(2 lam c)] is bounded below by -e^{lam/2}/2 for all c
       (case split at 2 lam |c| <= 1; the far case via e^{2 lam c^2} >= e^{|c|} >= |c|^4/24).
       E6Bridge11's norm_weilKernel_zero_le is NOT used (it would cost 1.27 in units of A).
    2. prime side: E6Bridge11.norm_primeSide_le as is, with y^4/24 <= e^y for the numerics.
    3. bumpR_le': sup bumpR <= e^{-1}/(2 lam)  (y e^{-y} <= e^{-1}, from y <= e^{y-1}).
    4. setIntegral_bumpR_le': the window {|r| < rho} carries at most rho e^{-1}/lam of bump mass.
    5. psiR_mono: Re psi(1/4 + i r/2) is increasing in |r| (Zeta23.MuFields.re_digamma_mono, the
       termwise monotonicity of the vertical-line series; evenness from the same series).
    6. psiR_ge_rational: an explicit RATIONAL lower bound on psiR r at any rational r from the
       first N series terms, an integral-tail comparison for the rest (serF is decreasing in x,
       AntitoneOn.integral_le_sum_Ico + the FTC, the tail beyond N + M bounded by log X <= X - 1),
       log X >= 1 - 1/X for the tail integral, and gamma <= 0.58112 (Mathlib's
       eulerMascheroniConstant_lt_eulerMascheroniSeq' at n = 128, with log 128 = 7 log 2 and
       Real.log_two_gt_d9).  Nine instances (r = 0, 0.6, 1.4, 2.9, 5.1, 8.0, 11.6, 16.0, 21.1)
       by norm_num on 40 rationals each; the r = 0 instance replaces Gauss's digamma theorem.
    7. the LAYER CAKE: the invariant Cake (an explicit integrable minorant of psiR, constant
       beyond the current edge) with cake_base / cake_step / cake_integral, applied along the
       eight edges: int bumpR psiR >= phi_8 M - Sum_k (phi_k - phi_{k-1}) rho_k e^{-1}/lam,
       M = 2 pi A the bump mass.
    8. assembly: in units of A = 1/(8 sqrt(2 pi) lam^{3/2}), for 0 < lam <= 1/1000,
       F/A >= -0.001 + 2.3499 - 0.0375 * 27.44863 - 1.1448 - 0.006 = 0.168 > 0.
       Every cap is monotone in lam (sqrt lam, lam^{3/2}, e^{-(log 2)^2/(16 lam)} all decrease
       as lam decreases), so the single set of constants at lam0 covers the whole strip.

  Rigorous floors (rounded down to 4 decimals; exact values in the memo's table):
      r     0        0.6      1.4      2.9     5.1     8.0     11.6    16.0    21.1
      phi  -4.2315  -1.8138  -0.4233  0.3621  0.9303  1.3814  1.7530  2.0742  2.3499
  The memo's floors used gamma_up = 0.58221; ours is 0.58112, hence slightly better.

  STRETCH (section G): the same machinery with TWELVE bands (edges 0.5, 0.9, 1.5, 2.4, 3.6, 5.1,
  6.9, 8.9, 11.1, 13.5, 16.1, 18.9) certifies lam0 = 3/2000 with margin 0.052
  (gaussian_positivity_small_lam_3e3).  Deviations from the spec: pole_floor is stated for
  lam <= 1/50 (not 1/5; the far case uses a cruder e^{|c|} >= |c|^4/24, which is all the
  thresholds need); the sup cap is certified as 0.0375 (resp. 0.0455) rather than the exact
  kappa sqrt(lam0) = 0.037128 (resp. 0.045473); phi_0 comes from the series, not Gauss's theorem.

  Nothing here proves RH: the theorem is an unconditional statement about one explicit test
  function's prime-side functional; it involves no zeros.  conjecture1_proved = False.
-/
import E6Bridge11
import E6Bridge16

open Zeta23 Complex MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace RvMBridge30
open WeilExplicit RvMBridge11 RvMBridge16

/-! ## A. Step 1: the pole floor. -/

/-- Re gaussTest c lam (i/2) = e^{-2 lam (c^2 - 1/4)} [(c^2 - 1/4) cos(2 lam c) + c sin(2 lam c)]. -/
lemma re_gaussTest_I_half (c lam : ℝ) :
    (RvMBridge6.gaussTest c lam (I / 2)).re
      = Real.exp (-(2 * lam) * (c ^ 2 - 1 / 4))
        * ((c ^ 2 - 1 / 4) * Real.cos (2 * lam * c) + c * Real.sin (2 * lam * c)) := by
  unfold RvMBridge6.gaussTest
  have h1 : (I / 2 - (c : ℂ)) ^ 2 = ((c ^ 2 - 1 / 4 : ℝ) : ℂ) + ((-c : ℝ) : ℂ) * I := by
    push_cast
    linear_combination (1 / 4 : ℂ) * I_sq
  have h2 : -(2 * (lam : ℂ)) * (((c ^ 2 - 1 / 4 : ℝ) : ℂ) + ((-c : ℝ) : ℂ) * I)
      = ((-(2 * lam) * (c ^ 2 - 1 / 4) : ℝ) : ℂ) + ((2 * lam * c : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [h1, h2, Complex.mul_re, Complex.exp_re, Complex.exp_im]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero, sub_self]
  ring

/-- The other pole term is the conjugate: same real part. -/
lemma re_gaussTest_neg_I_half (c lam : ℝ) :
    (RvMBridge6.gaussTest c lam (-I / 2)).re = (RvMBridge6.gaussTest c lam (I / 2)).re := by
  have h : (-I / 2 : ℂ) = conj (I / 2) := by
    rw [map_div₀, Complex.conj_I, map_ofNat]
  rw [h, RvMBridge6.gaussTest_conj, Complex.conj_re]

/-- THE POLE FLOOR: P(c) = Re gaussTest (i/2) + Re gaussTest (-i/2) >= -e^{lam/2}/2 for every
centre c, once 0 < lam <= 1/50. -/
theorem pole_floor {c lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ 1 / 50) :
    -(Real.exp (lam / 2) / 2)
      ≤ (RvMBridge6.gaussTest c lam (I / 2)).re + (RvMBridge6.gaussTest c lam (-I / 2)).re := by
  rw [re_gaussTest_neg_I_half, re_gaussTest_I_half]
  set θ := 2 * lam * c with hθ
  set E := Real.exp (-(2 * lam) * (c ^ 2 - 1 / 4)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hEle : E ≤ Real.exp (lam / 2) := by
    rw [hE, Real.exp_le_exp]
    nlinarith [sq_nonneg c]
  rcases le_or_gt |θ| 1 with hθ1 | hθ1
  · -- near case: cos >= 0, c sin >= 0, so the bracket is >= -1/4
    have hpi := Real.pi_gt_three
    have hθl := (abs_le.mp hθ1).1
    have hθu := (abs_le.mp hθ1).2
    have hcos : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
    have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hsin : 0 ≤ c * Real.sin θ := by
      rcases le_or_gt 0 c with hc | hc
      · have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
        have := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith)
        positivity
      · have hθ0 : θ ≤ 0 := by rw [hθ]; nlinarith
        have := Real.sin_nonpos_of_nonpos_of_neg_pi_le hθ0 (by linarith)
        nlinarith
    have hbr : -(1 / 4) ≤ (c ^ 2 - 1 / 4) * Real.cos θ + c * Real.sin θ := by
      nlinarith [mul_nonneg (sq_nonneg c) hcos]
    have := mul_le_mul_of_nonneg_left hbr hE0.le
    linarith
  · -- far case: |c| > 1/(2 lam) >= 25, and the whole term is e^{lam/2} (4 c^2 e^{-2 lam c^2}) small
    have hc0 : 1 / (2 * lam) < |c| := by
      rw [hθ, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * lam)] at hθ1
      rw [div_lt_iff₀ (by positivity)]
      linarith
    have hc25 : 25 ≤ |c| := by
      have : (25 : ℝ) ≤ 1 / (2 * lam) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      linarith
    have hcsq : c ^ 2 = |c| ^ 2 := (sq_abs c).symm
    -- bracket >= -2 c^2
    have hbr : -(2 * c ^ 2) ≤ (c ^ 2 - 1 / 4) * Real.cos θ + c * Real.sin θ := by
      have h1 : -|c| ≤ c * Real.sin θ := by
        have := neg_abs_le (c * Real.sin θ)
        have h2 : |c * Real.sin θ| ≤ |c| := by
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg c) (Real.abs_sin_le_one θ)
        linarith
      have h2 : -(c ^ 2 + 1 / 4) ≤ (c ^ 2 - 1 / 4) * Real.cos θ := by
        have := neg_abs_le ((c ^ 2 - 1 / 4) * Real.cos θ)
        have h3 : |(c ^ 2 - 1 / 4) * Real.cos θ| ≤ c ^ 2 + 1 / 4 := by
          rw [abs_mul]
          calc |c ^ 2 - 1 / 4| * |Real.cos θ| ≤ |c ^ 2 - 1 / 4| * 1 :=
                mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ) (abs_nonneg _)
            _ ≤ c ^ 2 + 1 / 4 := by
                rw [mul_one, abs_le]
                constructor <;> nlinarith [sq_nonneg c]
        linarith
      nlinarith
    -- 8 c^2 <= e^{2 lam c^2}: e^{2 lam c^2} >= e^{|c|} >= |c|^4 / 24 >= 8 |c|^2
    have hexp : 8 * c ^ 2 ≤ Real.exp (2 * lam * c ^ 2) := by
      have h1 : |c| ≤ 2 * lam * c ^ 2 := by
        rw [hcsq]
        have h2 : 1 < 2 * lam * |c| := by
          rw [div_lt_iff₀ (by positivity)] at hc0
          linarith
        nlinarith [abs_nonneg c]
      have h2 : Real.exp |c| ≤ Real.exp (2 * lam * c ^ 2) := Real.exp_le_exp.mpr h1
      have h3 : |c| ^ 4 / (Nat.factorial 4 : ℝ) ≤ Real.exp |c| :=
        Real.pow_div_factorial_le_exp _ (abs_nonneg c) 4
      have h4 : 8 * |c| ^ 2 ≤ |c| ^ 4 / (Nat.factorial 4 : ℝ) := by
        rw [show (Nat.factorial 4 : ℝ) = 24 by norm_num [Nat.factorial]]
        nlinarith [sq_nonneg (|c| ^ 2 - 25 * |c|), sq_nonneg |c|]
      rw [hcsq] at h2 ⊢
      linarith
    -- assemble
    have hEeq : E = Real.exp (lam / 2) * Real.exp (-(2 * lam * c ^ 2)) := by
      rw [hE, ← Real.exp_add]
      congr 1
      ring
    have hsmall : 4 * c ^ 2 * Real.exp (-(2 * lam * c ^ 2)) ≤ 1 / 2 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
      linarith
    have hpos := Real.exp_pos (lam / 2)
    have := mul_le_mul_of_nonneg_left hbr hE0.le
    have hprod : E * (2 * c ^ 2) ≤ Real.exp (lam / 2) / 4 := by
      rw [hEeq]
      have := mul_le_mul_of_nonneg_left hsmall hpos.le
      nlinarith
    linarith

/-! ## B. Steps 3 and 4: the sup of the bump and the window mass. -/

/-- bumpR <= e^{-1} / (2 lam)  (y e^{-y} <= e^{-1}). -/
lemma bumpR_le' {c lam : ℝ} (hlam : 0 < lam) (r : ℝ) :
    bumpR c lam r ≤ Real.exp (-1) / (2 * lam) := by
  unfold bumpR
  set y := 2 * lam * (r - c) ^ 2 with hy
  have hy0 : 0 ≤ y := by positivity
  have h1 : y ≤ Real.exp (y - 1) := by linarith [Real.add_one_le_exp (y - 1)]
  have h2 : y * Real.exp (-y) ≤ Real.exp (-1) := by
    have h3 : Real.exp (y - 1) * Real.exp (-y) = Real.exp (-1) := by
      rw [← Real.exp_add]
      ring_nf
    calc y * Real.exp (-y) ≤ Real.exp (y - 1) * Real.exp (-y) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = Real.exp (-1) := h3
  have e0 : -(2 * lam) * (r - c) ^ 2 = -y := by rw [hy]; ring
  have e : (r - c) ^ 2 * Real.exp (-y) = (1 / (2 * lam)) * (y * Real.exp (-y)) := by
    rw [hy]
    field_simp
  rw [e0, e]
  calc (1 / (2 * lam)) * (y * Real.exp (-y)) ≤ (1 / (2 * lam)) * Real.exp (-1) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = Real.exp (-1) / (2 * lam) := by ring

/-- The window mass: ∫_{|r| < rho} bumpR <= rho e^{-1} / lam, for every centre c. -/
lemma setIntegral_bumpR_le' {c lam : ℝ} (hlam : 0 < lam) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∫ r in Set.Ioo (-ρ) ρ, bumpR c lam r ≤ ρ * (Real.exp (-1) / lam) := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioo (-ρ) ρ)
    (f := bumpR c lam) (C := Real.exp (-1) / (2 * lam))
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)
    (fun r _ => by rw [Real.norm_eq_abs, abs_of_nonneg (bumpR_nonneg c lam r)]; exact bumpR_le' hlam r)
  rw [Real.volume_real_Ioo_of_le (by linarith), Real.norm_eq_abs] at h
  calc ∫ r in Set.Ioo (-ρ) ρ, bumpR c lam r ≤ |∫ r in Set.Ioo (-ρ) ρ, bumpR c lam r| := le_abs_self _
    _ ≤ Real.exp (-1) / (2 * lam) * (ρ - -ρ) := h
    _ = ρ * (Real.exp (-1) / lam) := by field_simp; ring

/-! ## C. Step 5: psiR is even and increasing in |r|. -/

lemma psiR_neg (r : ℝ) : psiR (-r) = psiR r := by
  rw [psiR_eq, psiR_eq, Zeta23.MuFields.re_digamma_vertical (by norm_num) (by norm_num),
    Zeta23.MuFields.re_digamma_vertical (by norm_num) (by norm_num)]
  simp only [neg_div, neg_sq]

lemma psiR_abs (r : ℝ) : psiR |r| = psiR r := by
  rcases le_or_gt 0 r with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, psiR_neg]

/-- psiR is monotone in |r|: 0 <= s <= |r| gives psiR s <= psiR r. -/
theorem psiR_mono {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ |r|) : psiR s ≤ psiR r := by
  rw [← psiR_abs r, psiR_eq, psiR_eq]
  have h := Zeta23.MuFields.re_digamma_mono (a := 1 / 4) (by norm_num) (by norm_num)
    (Set.mem_Ici.mpr (by positivity : (0 : ℝ) ≤ s / 2))
    (Set.mem_Ici.mpr (by positivity : (0 : ℝ) ≤ |r| / 2)) (by linarith)
  exact h

/-! ## D. Step 6: the rational lower bound on psiR from the vertical-line series. -/

/-- The series integrand f(x) = 1/(x+1) - (x + 5/4)/((x + 5/4)^2 + t^2) (t = r/2). -/
def serF (t : ℝ) (x : ℝ) : ℝ := 1 / (x + 1) - (x + 1 + 1 / 4) / ((x + 1 + 1 / 4) ^ 2 + t ^ 2)

/-- Minus an antiderivative of serF: G(x) = (1/2) log((x + 5/4)^2 + t^2) - log(x + 1), G' = -f. -/
def serG (t : ℝ) (x : ℝ) : ℝ := (1 / 2) * Real.log ((x + 1 + 1 / 4) ^ 2 + t ^ 2) - Real.log (x + 1)

lemma serF_nonneg (t : ℝ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ serF t x := by
  unfold serF
  have hn : (0 : ℝ) < x + 1 + 1 / 4 := by positivity
  have h1 : (x + 1 + 1 / 4) / ((x + 1 + 1 / 4) ^ 2 + t ^ 2) ≤ 1 / (x + 1 + 1 / 4) := by
    rw [div_le_div_iff₀ (by positivity) hn]
    nlinarith [sq_nonneg t]
  have h2 : 1 / (x + 1 + 1 / 4) ≤ 1 / (x + 1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

/-- serF is decreasing on [0, ∞) (a direct algebraic identity for f(x) - f(y)). -/
lemma serF_antitoneOn (t : ℝ) : AntitoneOn (serF t) (Set.Ici 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  have hx1 : 0 < x + 1 := by linarith
  have hy1 : 0 < y + 1 := by linarith
  set p := x + 1 + 1 / 4 with hp
  set q := y + 1 + 1 / 4 with hq
  have hp0 : 0 < p := by rw [hp]; linarith
  have hq0 : 0 < q := by rw [hq]; linarith
  have hP : 0 < p ^ 2 + t ^ 2 := by positivity
  have hQ : 0 < q ^ 2 + t ^ 2 := by positivity
  have hnum : 0 ≤ (p ^ 2 + t ^ 2) * (q ^ 2 + t ^ 2) - (x + 1) * (y + 1) * (p * q - t ^ 2) := by
    rcases le_or_gt (p * q) (t ^ 2) with h | h
    · nlinarith [mul_pos hx1 hy1, mul_pos hP hQ]
    · have h1 : (x + 1) * (y + 1) ≤ p * q := by
        rw [hp, hq]
        nlinarith
      have h2 : (x + 1) * (y + 1) * (p * q - t ^ 2) ≤ p * q * (p * q - t ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (by linarith)
      nlinarith [mul_nonneg (sq_nonneg t) (sq_nonneg p), mul_nonneg (sq_nonneg t) (sq_nonneg q),
        mul_nonneg (sq_nonneg t) (mul_pos hp0 hq0).le, sq_nonneg (t ^ 2)]
  have hid : serF t x - serF t y
      = (y - x) * ((p ^ 2 + t ^ 2) * (q ^ 2 + t ^ 2) - (x + 1) * (y + 1) * (p * q - t ^ 2))
        / ((x + 1) * (y + 1) * ((p ^ 2 + t ^ 2) * (q ^ 2 + t ^ 2))) := by
    unfold serF
    rw [← hp, ← hq]
    field_simp
    ring
  have : 0 ≤ serF t x - serF t y := by
    rw [hid]
    apply div_nonneg (mul_nonneg (by linarith) hnum)
    positivity
  linarith

lemma hasDerivAt_neg_serG (t : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun x => -serG t x) (serF t x) x := by
  have hx1 : x + 1 ≠ 0 := by linarith
  have hq : (x + 1 + 1 / 4) ^ 2 + t ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun x : ℝ => x + 1 + 1 / 4) 1 x := by
    exact ((hasDerivAt_id x).add_const 1).add_const (1 / 4)
  have h2 : HasDerivAt (fun x : ℝ => (x + 1 + 1 / 4) ^ 2 + t ^ 2) (2 * (x + 1 + 1 / 4)) x := by
    have h := (h1.pow 2).add_const (t ^ 2)
    refine h.congr_deriv ?_
    norm_num
  have h3 : HasDerivAt (fun x : ℝ => Real.log ((x + 1 + 1 / 4) ^ 2 + t ^ 2))
      (2 * (x + 1 + 1 / 4) / ((x + 1 + 1 / 4) ^ 2 + t ^ 2)) x := h2.log hq
  have h4 : HasDerivAt (fun x : ℝ => Real.log (x + 1)) (1 / (x + 1)) x := by
    have := ((hasDerivAt_id x).add_const 1).log hx1
    simpa using this
  have h5 := ((h3.const_mul (1 / 2)).sub h4).neg
  have h6 : HasDerivAt (fun x => -serG t x)
      (-((1 / 2) * (2 * (x + 1 + 1 / 4) / ((x + 1 + 1 / 4) ^ 2 + t ^ 2)) - 1 / (x + 1))) x := by
    unfold serG
    exact h5
  refine h6.congr_deriv ?_
  unfold serF
  field_simp
  ring

/-- The tail comparison: Σ_{n ∈ [N, N+M)} serF t n >= G(N) - G(N + M). -/
lemma sum_serF_ge (t : ℝ) (N M : ℕ) :
    serG t N - serG t (N + M) ≤ ∑ n ∈ Finset.Ico N (N + M), serF t n := by
  have hNM : (N : ℝ) ≤ ((N + M : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have hanti : AntitoneOn (serF t) (Set.Icc (N : ℝ) ((N + M : ℕ) : ℝ)) :=
    (serF_antitoneOn t).mono fun x hx => by
      simp only [Set.mem_Icc] at hx
      simp only [Set.mem_Ici]
      linarith [hx.1, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have h1 := AntitoneOn.integral_le_sum_Ico (f := serF t) (a := N) (b := N + M) (by omega) hanti
  have hint : ∫ x in (N : ℝ)..((N + M : ℕ) : ℝ), serF t x = serG t N - serG t (N + M) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => -serG t x) (f' := serF t)
      (a := (N : ℝ)) (b := ((N + M : ℕ) : ℝ))
      (fun x hx => by
        rw [Set.uIcc_of_le hNM, Set.mem_Icc] at hx
        exact hasDerivAt_neg_serG t (by linarith [hx.1, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]))
      (by
        rw [← Set.uIcc_of_le hNM] at hanti
        exact hanti.intervalIntegrable)
    rw [h]
    push_cast
    ring
  rw [hint] at h1
  exact h1

/-- THE SERIES LOWER BOUND: for every r and all N, M,
psiR r >= -gamma - a/(a^2+t^2) + Σ_{n<N} f(n) + (G(N) - G(N+M)), a = 1/4, t = r/2. -/
theorem psiR_ge_series (r : ℝ) (N M : ℕ) :
    -Real.eulerMascheroniConstant - (1 / 4) / ((1 / 4) ^ 2 + (r / 2) ^ 2)
      + ∑ n ∈ Finset.range N, serF (r / 2) n
      + (serG (r / 2) N - serG (r / 2) (N + M)) ≤ psiR r := by
  rw [psiR_eq, Zeta23.MuFields.re_digamma_vertical (by norm_num) (by norm_num)]
  have hsum : Summable (fun n : ℕ => serF (r / 2) n) :=
    Zeta23.MuFields.summable_re_terms (a := 1 / 4) (by norm_num) (by norm_num) (r / 2)
  have hnn : ∀ n : ℕ, 0 ≤ serF (r / 2) n := fun n => serF_nonneg _ (Nat.cast_nonneg n)
  have h1 : ∑ n ∈ Finset.range (N + M), serF (r / 2) n ≤ ∑' n : ℕ, serF (r / 2) n :=
    hsum.sum_le_tsum _ (fun n _ => hnn n)
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le N) (Nat.le_add_right N M),
    ← Finset.range_eq_Ico] at h1
  have h2 := sum_serF_ge (r / 2) N M
  have h3 : (∑' n : ℕ, (1 / ((n : ℝ) + 1)
      - ((n : ℝ) + 1 + 1 / 4) / (((n : ℝ) + 1 + 1 / 4) ^ 2 + (r / 2) ^ 2)))
      = ∑' n : ℕ, serF (r / 2) n := rfl
  rw [h3]
  linarith

/-- The two log bounds on G: (1/2)(1 - (x+1)^2/((x+5/4)^2+t^2)) <= G(x) <= (1/2)(((x+5/4)^2+t^2)/(x+1)^2 - 1). -/
lemma serG_bounds (t : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    (1 / 2) * (1 - (x + 1) ^ 2 / ((x + 1 + 1 / 4) ^ 2 + t ^ 2)) ≤ serG t x
      ∧ serG t x ≤ (1 / 2) * (((x + 1 + 1 / 4) ^ 2 + t ^ 2) / (x + 1) ^ 2 - 1) := by
  unfold serG
  have hx1 : 0 < x + 1 := by linarith
  have hq : 0 < (x + 1 + 1 / 4) ^ 2 + t ^ 2 := by positivity
  have e : (1 / 2) * Real.log ((x + 1 + 1 / 4) ^ 2 + t ^ 2) - Real.log (x + 1)
      = (1 / 2) * Real.log (((x + 1 + 1 / 4) ^ 2 + t ^ 2) / (x + 1) ^ 2) := by
    rw [Real.log_div hq.ne' (by positivity), Real.log_pow]
    push_cast
    ring
  rw [e]
  have hpos : 0 < ((x + 1 + 1 / 4) ^ 2 + t ^ 2) / (x + 1) ^ 2 := by positivity
  constructor
  · have := Real.one_sub_inv_le_log_of_pos hpos
    rw [inv_div] at this
    linarith
  · have := Real.log_le_sub_one_of_pos hpos
    linarith

/-- THE RATIONAL LOWER BOUND: every quantity on the left is rational once r, N, M, gamma_up are. -/
theorem psiR_ge_rational (r : ℝ) (N M : ℕ) {γ : ℝ} (hγ : Real.eulerMascheroniConstant ≤ γ) :
    -γ - (1 / 4) / ((1 / 4) ^ 2 + (r / 2) ^ 2)
      + ∑ n ∈ Finset.range N, serF (r / 2) n
      + (1 / 2) * (1 - ((N : ℝ) + 1) ^ 2 / (((N : ℝ) + 1 + 1 / 4) ^ 2 + (r / 2) ^ 2))
      - (1 / 2) * (((((N : ℝ) + M) + 1 + 1 / 4) ^ 2 + (r / 2) ^ 2) / (((N : ℝ) + M + 1) ^ 2) - 1)
      ≤ psiR r := by
  have h := psiR_ge_series r N M
  have hN := (serG_bounds (r / 2) (x := (N : ℝ)) (Nat.cast_nonneg N)).1
  have hNM := (serG_bounds (r / 2) (x := ((N + M : ℕ) : ℝ)) (Nat.cast_nonneg _)).2
  push_cast at hNM
  linarith

/-- gamma <= 0.58112 (Mathlib: gamma < H_128 - log 128, log 128 = 7 log 2 > 4.85203). -/
lemma eulerMascheroni_le : Real.eulerMascheroniConstant ≤ 0.58112 := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 128
  have h2 : Real.eulerMascheroniSeq' 128 = (harmonic 128 : ℝ) - Real.log 128 := by
    rw [Real.eulerMascheroniSeq']
    simp
  have h3 : Real.log (128 : ℝ) = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
    push_cast
    ring
  have h4 : (harmonic 128 : ℝ) ≤ 5.4331471 := by
    have hq : harmonic 128 ≤ 54331471 / 10000000 := by
      simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    have hr : ((harmonic 128 : ℚ) : ℝ) ≤ ((54331471 / 10000000 : ℚ) : ℝ) := by exact_mod_cast hq
    push_cast at hr
    linarith
  have := Real.log_two_gt_d9
  linarith

/-! ### The nine edge floors (N = 40 terms, tail beyond N + M with M = 10^6). -/

/-- phi_0: psiR 0 >= -4.2315  (the exact value is psi(1/4) = -4.22745). -/
lemma psiR_floor_0 : (-8463 / 2000 : ℝ) ≤ psiR 0 := by
  refine le_trans ?_ (psiR_ge_rational 0 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiR_floor_1 : (-9069 / 5000 : ℝ) ≤ psiR (3 / 5) := by
  refine le_trans ?_ (psiR_ge_rational (3 / 5) 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiR_floor_2 : (-4233 / 10000 : ℝ) ≤ psiR (7 / 5) := by
  refine le_trans ?_ (psiR_ge_rational (7 / 5) 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiR_floor_3 : (3621 / 10000 : ℝ) ≤ psiR (29 / 10) := by
  refine le_trans ?_ (psiR_ge_rational (29 / 10) 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiR_floor_4 : (9303 / 10000 : ℝ) ≤ psiR (51 / 10) := by
  refine le_trans ?_ (psiR_ge_rational (51 / 10) 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiR_floor_5 : (6907 / 5000 : ℝ) ≤ psiR 8 := by
  refine le_trans ?_ (psiR_ge_rational 8 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiR_floor_6 : (1753 / 1000 : ℝ) ≤ psiR (58 / 5) := by
  refine le_trans ?_ (psiR_ge_rational (58 / 5) 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiR_floor_7 : (10371 / 5000 : ℝ) ≤ psiR 16 := by
  refine le_trans ?_ (psiR_ge_rational 16 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiR_floor_8 : (23499 / 10000 : ℝ) ≤ psiR (211 / 10) := by
  refine le_trans ?_ (psiR_ge_rational (211 / 10) 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-! ## E. Step 7: the layer cake. -/

lemma mem_Ioo_abs {ρ r : ℝ} : r ∈ Set.Ioo (-ρ) ρ ↔ |r| < ρ := by
  rw [Set.mem_Ioo, abs_lt]

/-- The layer-cake invariant: an integrable minorant ℓ of psiR that equals φ beyond |r| >= ρ,
with ∫ bumpR ℓ >= B. -/
def Cake (c lam φ ρ B : ℝ) : Prop :=
  ∃ ℓ : ℝ → ℝ, (∀ r, ℓ r ≤ psiR r) ∧ (∀ r, ρ ≤ |r| → ℓ r = φ)
    ∧ Integrable (fun r => bumpR c lam r * ℓ r) ∧ B ≤ ∫ r, bumpR c lam r * ℓ r

lemma cake_base {c lam : ℝ} (hlam : 0 < lam) {φ : ℝ} (hφ : ∀ r, φ ≤ psiR r) :
    Cake c lam φ 0 (φ * (2 * Real.pi * gaussA lam)) :=
  ⟨fun _ => φ, hφ, fun _ _ => rfl, (integrable_bumpR hlam).mul_const φ,
    by rw [integral_mul_const, integral_bumpR hlam]; linarith⟩

/-- One more band: a new edge ρ' >= ρ with a new floor φ' >= φ, φ' <= psiR ρ'. -/
lemma cake_step {c lam : ℝ} (hlam : 0 < lam) {φ ρ B φ' ρ' : ℝ} (h : Cake c lam φ ρ B)
    (hφ : φ ≤ φ') (hρ : ρ ≤ ρ') (hρ' : 0 ≤ ρ') (hψ : φ' ≤ psiR ρ') :
    Cake c lam φ' ρ' (B + (φ' - φ) * (2 * Real.pi * gaussA lam - ρ' * (Real.exp (-1) / lam))) := by
  obtain ⟨ℓ, hle, hconst, hint, hB⟩ := h
  have hbi : Integrable (bumpR c lam) := integrable_bumpR hlam
  have hind : Integrable ((Set.Ioo (-ρ') ρ').indicator (bumpR c lam)) :=
    hbi.indicator measurableSet_Ioo
  have hfun : (fun r => bumpR c lam r * (ℓ r + (φ' - φ) * (1 - (Set.Ioo (-ρ') ρ').indicator 1 r)))
      = fun r => bumpR c lam r * ℓ r + (φ' - φ) * bumpR c lam r
        - (φ' - φ) * (Set.Ioo (-ρ') ρ').indicator (bumpR c lam) r := by
    funext r
    by_cases hr : r ∈ Set.Ioo (-ρ') ρ'
    · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr, Pi.one_apply]
      ring
    · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr]
      ring
  have hint2 : Integrable (fun r => bumpR c lam r * ℓ r + (φ' - φ) * bumpR c lam r) :=
    hint.add (hbi.const_mul _)
  have hind2 : Integrable (fun r => (φ' - φ) * (Set.Ioo (-ρ') ρ').indicator (bumpR c lam) r) :=
    hind.const_mul _
  refine ⟨fun r => ℓ r + (φ' - φ) * (1 - (Set.Ioo (-ρ') ρ').indicator 1 r), ?_, ?_, ?_, ?_⟩
  · intro r
    show ℓ r + (φ' - φ) * (1 - (Set.Ioo (-ρ') ρ').indicator 1 r) ≤ psiR r
    by_cases hr : r ∈ Set.Ioo (-ρ') ρ'
    · rw [Set.indicator_of_mem hr, Pi.one_apply, sub_self, mul_zero, add_zero]
      exact hle r
    · rw [Set.indicator_of_notMem hr, sub_zero, mul_one]
      have hr' : ρ' ≤ |r| := by rwa [mem_Ioo_abs, not_lt] at hr
      have h1 := hconst r (hρ.trans hr')
      have h2 := psiR_mono hρ' hr'
      linarith
  · intro r hr
    show ℓ r + (φ' - φ) * (1 - (Set.Ioo (-ρ') ρ').indicator 1 r) = φ'
    have hnot : r ∉ Set.Ioo (-ρ') ρ' := by rw [mem_Ioo_abs]; exact not_lt.mpr hr
    rw [Set.indicator_of_notMem hnot, hconst r (hρ.trans hr)]
    ring
  · rw [hfun]
    exact hint2.sub hind2
  · rw [hfun, integral_sub hint2 hind2, integral_add hint (hbi.const_mul _), integral_const_mul,
      integral_const_mul, integral_indicator measurableSet_Ioo, integral_bumpR hlam]
    have hwin := setIntegral_bumpR_le' (c := c) hlam hρ'
    have hδ : 0 ≤ φ' - φ := by linarith
    have := mul_le_mul_of_nonneg_left hwin hδ
    linarith

lemma cake_integral {c lam φ ρ B : ℝ} (hlam : 0 < lam) (h : Cake c lam φ ρ B) :
    B ≤ ∫ r, bumpR c lam r * psiR r := by
  obtain ⟨ℓ, hle, -, hint, hB⟩ := h
  refine hB.trans (integral_mono hint (integrable_bumpR_mul_psiR hlam) fun r => ?_)
  exact mul_le_mul_of_nonneg_left (hle r) (bumpR_nonneg c lam r)

/-- The sum Σ_k (phi_k - phi_{k-1}) rho_k over the eight bands. -/
def bandSum : ℝ := 2744863 / 100000

lemma bandSum_eq : bandSum
    = (-9069 / 5000 - (-8463 / 2000)) * (3 / 5) + (-4233 / 10000 - (-9069 / 5000)) * (7 / 5)
      + (3621 / 10000 - (-4233 / 10000)) * (29 / 10) + (9303 / 10000 - 3621 / 10000) * (51 / 10)
      + (6907 / 5000 - 9303 / 10000) * 8 + (1753 / 1000 - 6907 / 5000) * (58 / 5)
      + (10371 / 5000 - 1753 / 1000) * 16 + (23499 / 10000 - 10371 / 5000) * (211 / 10) := by
  unfold bandSum
  norm_num

/-- THE EIGHT-BAND ARCHIMEDEAN LOWER BOUND:
∫ bumpR psiR >= phi_8 (2 pi A) - bandSum e^{-1} / lam, for every centre c. -/
theorem integral_bumpR_mul_psiR_ge_bands {c lam : ℝ} (hlam : 0 < lam) :
    (23499 / 10000) * (2 * Real.pi * gaussA lam) - bandSum * (Real.exp (-1) / lam)
      ≤ ∫ r : ℝ, bumpR c lam r * psiR r := by
  have h0 : Cake c lam (-8463 / 2000) 0 ((-8463 / 2000) * (2 * Real.pi * gaussA lam)) :=
    cake_base hlam fun r => (psiR_floor_0.trans (psiR_mono le_rfl (abs_nonneg r)))
  have h1 := cake_step hlam h0 (by norm_num) (by norm_num) (by norm_num) psiR_floor_1
  have h2 := cake_step hlam h1 (by norm_num) (by norm_num) (by norm_num) psiR_floor_2
  have h3 := cake_step hlam h2 (by norm_num) (by norm_num) (by norm_num) psiR_floor_3
  have h4 := cake_step hlam h3 (by norm_num) (by norm_num) (by norm_num) psiR_floor_4
  have h5 := cake_step hlam h4 (by norm_num) (by norm_num) (by norm_num) psiR_floor_5
  have h6 := cake_step hlam h5 (by norm_num) (by norm_num) (by norm_num) psiR_floor_6
  have h7 := cake_step hlam h6 (by norm_num) (by norm_num) (by norm_num) psiR_floor_7
  have h8 := cake_step hlam h7 (by norm_num) (by norm_num) (by norm_num) psiR_floor_8
  have h := cake_integral hlam h8
  rw [bandSum_eq]
  set M := 2 * Real.pi * gaussA lam
  set E := Real.exp (-1) / lam
  linarith

/-! ## F. Step 8: the numerical assembly at lam0 = 1/1000. -/

/-- The absolute width threshold of this file. -/
def lam₁ : ℝ := 1 / 1000

/-- THE UNCONDITIONAL THEOREM (primes-side form) at lam0 = 1/1000: for every centre c and every
width 0 < lam <= 1/1000, the Weil functional of the Gaussian-derivative autocorrelation is
nonnegative.  No zeros are involved. -/
theorem re_weilForm_gauss_nonneg_1e3 (c lam : ℝ) (hlam : 0 < lam) (hle : lam ≤ 1 / 1000) :
    0 ≤ (archSide (autocorr (RvMBridge8.gaussPhi c lam))
          - primeSide (autocorr (RvMBridge8.gaussPhi c lam))).re := by
  have hA := gaussA_pos hlam
  have hle' : lam ≤ 0.001 := by linarith
  -- Re archSide from the pieces (the E6Bridge16 decomposition)
  have hre : (archSide (autocorr (RvMBridge8.gaussPhi c lam))).re
      = (weilKernel (autocorr (RvMBridge8.gaussPhi c lam)) 0).re
        + (weilKernel (autocorr (RvMBridge8.gaussPhi c lam)) 1).re
        - gaussA lam * Real.log Real.pi
        + (1 / (2 * Real.pi)) * ∫ r : ℝ, bumpR c lam r * psiR r := by
    unfold archSide
    rw [integral_archIntegrand_eq hlam, autocorr_gaussPhi hlam 0, autocorrGauss_zero]
    rw [show (gaussA lam : ℂ) * (Real.log Real.pi : ℂ) = ((gaussA lam * Real.log Real.pi : ℝ) : ℂ) by
        push_cast; ring,
      show (1 / (2 * (Real.pi : ℂ))) * ((∫ r : ℝ, bumpR c lam r * psiR r : ℝ) : ℂ)
        = (((1 / (2 * Real.pi)) * ∫ r : ℝ, bumpR c lam r * psiR r : ℝ) : ℂ) by push_cast; ring]
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re]
  rw [Complex.sub_re, hre]
  -- step 1: the poles
  have hpole : -(Real.exp (lam / 2) / 2)
      ≤ (weilKernel (autocorr (RvMBridge8.gaussPhi c lam)) 0).re
        + (weilKernel (autocorr (RvMBridge8.gaussPhi c lam)) 1).re := by
    rw [weilKernel_zero_eq_gaussTest hlam, weilKernel_one_eq_gaussTest hlam]
    exact pole_floor hlam (by linarith)
  -- numerics shared by the caps
  have hsl0 : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsl : Real.sqrt lam ≤ 0.0317 := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith
  have hsp0 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hsp : Real.sqrt (2 * Real.pi) ≤ 2.5067 := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith [Real.pi_lt_d4]
  have hprod : Real.sqrt (2 * Real.pi) * Real.sqrt lam ≤ 2.5067 * 0.0317 :=
    mul_le_mul hsp hsl hsl0.le (by norm_num)
  have he1 : Real.exp (-1) ≤ 0.3679 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    have := Real.exp_one_gt_d9
    norm_num
    linarith
  have hehalf : Real.exp (lam / 2) ≤ 1.001 := by
    have h1 : 1 - lam / 2 ≤ Real.exp (-(lam / 2)) := by linarith [Real.add_one_le_exp (-(lam / 2))]
    have h2 : Real.exp (lam / 2) * Real.exp (-(lam / 2)) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (lam / 2)).le
    nlinarith [Real.exp_pos (lam / 2)]
  -- the pole term in units of A: e^{lam/2}/2 <= 0.001 A
  have hpoleA : Real.exp (lam / 2) / 2 ≤ 0.001 * gaussA lam := by
    unfold gaussA
    rw [show (0.001 : ℝ) * (1 / (8 * Real.sqrt (2 * Real.pi) * (lam * Real.sqrt lam)))
        = 0.001 / (8 * Real.sqrt (2 * Real.pi) * (lam * Real.sqrt lam)) by ring,
      le_div_iff₀ (by positivity)]
    have h1 : lam * (Real.sqrt (2 * Real.pi) * Real.sqrt lam) ≤ 0.001 * (2.5067 * 0.0317) :=
      mul_le_mul hle' hprod (by positivity) (by norm_num)
    have h2 : Real.exp (lam / 2) * (lam * (Real.sqrt (2 * Real.pi) * Real.sqrt lam))
        ≤ 1.001 * (0.001 * (2.5067 * 0.0317)) :=
      mul_le_mul hehalf h1 (by positivity) (by norm_num)
    nlinarith
  -- the cap constant: e^{-1}/(2 pi lam) <= 0.0375 A
  have hcap : Real.exp (-1) / (2 * Real.pi * lam) ≤ 0.0375 * gaussA lam := by
    unfold gaussA
    rw [show (0.0375 : ℝ) * (1 / (8 * Real.sqrt (2 * Real.pi) * (lam * Real.sqrt lam)))
        = 0.0375 / (8 * Real.sqrt (2 * Real.pi) * (lam * Real.sqrt lam)) by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : Real.exp (-1) * (Real.sqrt (2 * Real.pi) * Real.sqrt lam) ≤ 0.3679 * (2.5067 * 0.0317) :=
      mul_le_mul he1 hprod (by positivity) (by norm_num)
    have hpi := Real.pi_gt_d4
    nlinarith [mul_pos hlam Real.pi_pos]
  -- step 7 in units of A
  have hJ := integral_bumpR_mul_psiR_ge_bands (c := c) hlam
  have hJ' : (1 / (2 * Real.pi)) * ((23499 / 10000) * (2 * Real.pi * gaussA lam) - bandSum * (Real.exp (-1) / lam))
      ≤ (1 / (2 * Real.pi)) * ∫ r : ℝ, bumpR c lam r * psiR r :=
    mul_le_mul_of_nonneg_left hJ (by positivity)
  have hid : (1 / (2 * Real.pi)) * ((23499 / 10000) * (2 * Real.pi * gaussA lam) - bandSum * (Real.exp (-1) / lam))
      = (23499 / 10000) * gaussA lam - bandSum * (Real.exp (-1) / (2 * Real.pi * lam)) := by
    field_simp
  rw [hid] at hJ'
  have hbandA : bandSum * (Real.exp (-1) / (2 * Real.pi * lam)) ≤ bandSum * (0.0375 * gaussA lam) :=
    mul_le_mul_of_nonneg_left hcap (by unfold bandSum; norm_num)
  -- log pi <= 1.1448
  have hlogpi : Real.log Real.pi ≤ 1.1448 := by
    rw [Real.log_le_iff_le_exp Real.pi_pos]
    have h1 : Real.exp 1.1448 = Real.exp 1 * Real.exp 0.1448 := by
      rw [← Real.exp_add]; norm_num
    have h2 := Real.sum_le_exp_of_nonneg (x := 0.1448) (by norm_num) 5
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h2
    norm_num at h2
    have h3 := Real.exp_one_gt_d9
    rw [h1]
    nlinarith [Real.pi_lt_d6, Real.exp_pos (0.1448 : ℝ), Real.exp_pos (1 : ℝ)]
  have hlogA : gaussA lam * Real.log Real.pi ≤ gaussA lam * 1.1448 :=
    mul_le_mul_of_nonneg_left hlogpi hA.le
  -- step 2: the prime side
  have hl2 := Real.log_two_gt_d9
  have hσ : 2 ≤ Real.log 2 / (16 * lam) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hprime := norm_primeSide_le (c := c) hlam hσ
  have hpre := (abs_le.mp (Complex.abs_re_le_norm
    (primeSide (autocorr (RvMBridge8.gaussPhi c lam))))).2
  have hE : 64 * Real.exp (-(Real.log 2) ^ 2 / (16 * lam)) ≤ 0.006 := by
    have hy : 30 ≤ (Real.log 2) ^ 2 / (16 * lam) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    set y := (Real.log 2) ^ 2 / (16 * lam) with hy_def
    have hy0 : 0 ≤ y := by linarith
    have h1 : y ^ 4 / (Nat.factorial 4 : ℝ) ≤ Real.exp y := Real.pow_div_factorial_le_exp _ hy0 4
    rw [show (Nat.factorial 4 : ℝ) = 24 by norm_num [Nat.factorial]] at h1
    have h2 : (30 : ℝ) ^ 4 ≤ y ^ 4 := pow_le_pow_left₀ (by norm_num) hy 4
    have h3 : -(Real.log 2) ^ 2 / (16 * lam) = -y := by rw [hy_def]; ring
    rw [h3, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    nlinarith
  have hprime' : (primeSide (autocorr (RvMBridge8.gaussPhi c lam))).re ≤ 0.006 * gaussA lam := by
    calc (primeSide (autocorr (RvMBridge8.gaussPhi c lam))).re
        ≤ ‖primeSide (autocorr (RvMBridge8.gaussPhi c lam))‖ := hpre
      _ ≤ 64 * gaussA lam * Real.exp (-(Real.log 2) ^ 2 / (16 * lam)) := hprime
      _ = gaussA lam * (64 * Real.exp (-(Real.log 2) ^ 2 / (16 * lam))) := by ring
      _ ≤ gaussA lam * 0.006 := mul_le_mul_of_nonneg_left hE hA.le
      _ = 0.006 * gaussA lam := by ring
  -- assemble: A (-0.001 + 2.3499 - 0.0375 bandSum - 1.1448 - 0.006) > 0
  have hbs : bandSum = 2744863 / 100000 := rfl
  rw [hbs] at hbandA hJ'
  linarith

/-- THE SMALL-WIDTH REGION OF THE WALL AT lam0 = 1/1000, UNCONDITIONAL (zero-side form):
F(c, lam) = Re zeroSide (gaussTest c lam) >= 0 for every centre c and every 0 < lam <= 1/1000.
The Gaussian explicit formula is E6Bridge10.zeroSide_gaussTest_eq (through E6Bridge11's
GaussianExplicitFormula plumbing).  Nothing about RH. -/
theorem gaussian_positivity_small_lam_1e3 (c lam : ℝ) (hlam : 0 < lam) (hle : lam ≤ 1 / 1000) :
    0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re := by
  rw [gaussianExplicitFormula c lam hlam]
  exact re_weilForm_gauss_nonneg_1e3 c lam hlam hle

/-- The same with the named threshold lam₁ = 1/1000, in the shape of
E6Bridge11.gaussian_positivity_small_lam_explicit. -/
theorem gaussian_positivity_small_lam_explicit_1e3 (c lam : ℝ) (hlam : 0 < lam) (hle : lam ≤ lam₁) :
    0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re :=
  gaussian_positivity_small_lam_1e3 c lam hlam (by unfold lam₁ at hle; exact hle)

/-- The existential shape of E6Bridge11.gaussian_positivity_small_lam, now witnessed by 1/1000. -/
theorem gaussian_positivity_small_lam' :
    ∃ lam₀ > 0, ∀ c lam : ℝ, 0 < lam → lam ≤ lam₀ →
      0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re :=
  ⟨1 / 1000, by norm_num, fun c lam hlam hle => gaussian_positivity_small_lam_1e3 c lam hlam hle⟩

/-! ## G. Stretch: twelve bands at lam0 = 3/2000 (margin 0.052 in units of A).

Edges 0.5, 0.9, 1.5, 2.4, 3.6, 5.1, 6.9, 8.9, 11.1, 13.5, 16.1, 18.9 (coordinate ascent on a 0.1
grid against the rigorous floors); the edge 5.1 and its floor are shared with section D.
Rigorous floors: -2.1913, -1.0532, -0.3405, 0.1691, 0.5804, 0.9303, 1.2333, 1.4881, 1.7090,
1.9046, 2.0804, 2.2403.  The cap constant is kappa sqrt(3/2000) = 0.045473 <= 0.0455. -/

lemma psiR_floor_s1 : (-21913 / 10000 : ℝ) ≤ psiR (1/2) := by
  refine le_trans ?_ (psiR_ge_rational (1/2) 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiR_floor_s2 : (-2633 / 2500 : ℝ) ≤ psiR (9/10) := by
  refine le_trans ?_ (psiR_ge_rational (9/10) 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiR_floor_s3 : (-681 / 2000 : ℝ) ≤ psiR (3/2) := by
  refine le_trans ?_ (psiR_ge_rational (3/2) 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiR_floor_s4 : (1691 / 10000 : ℝ) ≤ psiR (12/5) := by
  refine le_trans ?_ (psiR_ge_rational (12/5) 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiR_floor_s5 : (1451 / 2500 : ℝ) ≤ psiR (18/5) := by
  refine le_trans ?_ (psiR_ge_rational (18/5) 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiR_floor_s7 : (12333 / 10000 : ℝ) ≤ psiR (69/10) := by
  refine le_trans ?_ (psiR_ge_rational (69/10) 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiR_floor_s8 : (14881 / 10000 : ℝ) ≤ psiR (89/10) := by
  refine le_trans ?_ (psiR_ge_rational (89/10) 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiR_floor_s9 : (1709 / 1000 : ℝ) ≤ psiR (111/10) := by
  refine le_trans ?_ (psiR_ge_rational (111/10) 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiR_floor_s10 : (9523 / 5000 : ℝ) ≤ psiR (27/2) := by
  refine le_trans ?_ (psiR_ge_rational (27/2) 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiR_floor_s11 : (5201 / 2500 : ℝ) ≤ psiR (161/10) := by
  refine le_trans ?_ (psiR_ge_rational (161/10) 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiR_floor_s12 : (22403 / 10000 : ℝ) ≤ psiR (189/10) := by
  refine le_trans ?_ (psiR_ge_rational (189/10) 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- Σ_k (phi_k - phi_{k-1}) rho_k over the twelve bands. -/
def bandSum12 : ℝ := 458103 / 20000

lemma bandSum12_eq : bandSum12
    = (-21913 / 10000 - (-8463 / 2000)) * (1 / 2) + (-2633 / 2500 - (-21913 / 10000)) * (9 / 10)
      + (-681 / 2000 - (-2633 / 2500)) * (3 / 2) + (1691 / 10000 - (-681 / 2000)) * (12 / 5)
      + (1451 / 2500 - 1691 / 10000) * (18 / 5) + (9303 / 10000 - 1451 / 2500) * (51 / 10)
      + (12333 / 10000 - 9303 / 10000) * (69 / 10) + (14881 / 10000 - 12333 / 10000) * (89 / 10)
      + (1709 / 1000 - 14881 / 10000) * (111 / 10) + (9523 / 5000 - 1709 / 1000) * (27 / 2)
      + (5201 / 2500 - 9523 / 5000) * (161 / 10) + (22403 / 10000 - 5201 / 2500) * (189 / 10) := by
  unfold bandSum12
  norm_num

/-- THE TWELVE-BAND ARCHIMEDEAN LOWER BOUND:
∫ bumpR psiR >= phi_12 (2 pi A) - bandSum12 e^{-1} / lam, for every centre c. -/
theorem integral_bumpR_mul_psiR_ge_bands12 {c lam : ℝ} (hlam : 0 < lam) :
    (22403 / 10000) * (2 * Real.pi * gaussA lam) - bandSum12 * (Real.exp (-1) / lam)
      ≤ ∫ r : ℝ, bumpR c lam r * psiR r := by
  have h0 : Cake c lam (-8463 / 2000) 0 ((-8463 / 2000) * (2 * Real.pi * gaussA lam)) :=
    cake_base hlam fun r => (psiR_floor_0.trans (psiR_mono le_rfl (abs_nonneg r)))
  have h1 := cake_step hlam h0 (by norm_num) (by norm_num) (by norm_num) psiR_floor_s1
  have h2 := cake_step hlam h1 (by norm_num) (by norm_num) (by norm_num) psiR_floor_s2
  have h3 := cake_step hlam h2 (by norm_num) (by norm_num) (by norm_num) psiR_floor_s3
  have h4 := cake_step hlam h3 (by norm_num) (by norm_num) (by norm_num) psiR_floor_s4
  have h5 := cake_step hlam h4 (by norm_num) (by norm_num) (by norm_num) psiR_floor_s5
  have h6 := cake_step hlam h5 (by norm_num) (by norm_num) (by norm_num) psiR_floor_4
  have h7 := cake_step hlam h6 (by norm_num) (by norm_num) (by norm_num) psiR_floor_s7
  have h8 := cake_step hlam h7 (by norm_num) (by norm_num) (by norm_num) psiR_floor_s8
  have h9 := cake_step hlam h8 (by norm_num) (by norm_num) (by norm_num) psiR_floor_s9
  have h10 := cake_step hlam h9 (by norm_num) (by norm_num) (by norm_num) psiR_floor_s10
  have h11 := cake_step hlam h10 (by norm_num) (by norm_num) (by norm_num) psiR_floor_s11
  have h12 := cake_step hlam h11 (by norm_num) (by norm_num) (by norm_num) psiR_floor_s12
  have h := cake_integral hlam h12
  rw [bandSum12_eq]
  set M := 2 * Real.pi * gaussA lam
  set E := Real.exp (-1) / lam
  linarith

/-- The stretch threshold. -/
def lam₂ : ℝ := 3 / 2000

/-- THE UNCONDITIONAL THEOREM (primes-side form) at lam0 = 3/2000. -/
theorem re_weilForm_gauss_nonneg_3e3 (c lam : ℝ) (hlam : 0 < lam) (hle : lam ≤ 3 / 2000) :
    0 ≤ (archSide (autocorr (RvMBridge8.gaussPhi c lam))
          - primeSide (autocorr (RvMBridge8.gaussPhi c lam))).re := by
  have hA := gaussA_pos hlam
  have hle' : lam ≤ 0.0015 := by linarith
  have hre : (archSide (autocorr (RvMBridge8.gaussPhi c lam))).re
      = (weilKernel (autocorr (RvMBridge8.gaussPhi c lam)) 0).re
        + (weilKernel (autocorr (RvMBridge8.gaussPhi c lam)) 1).re
        - gaussA lam * Real.log Real.pi
        + (1 / (2 * Real.pi)) * ∫ r : ℝ, bumpR c lam r * psiR r := by
    unfold archSide
    rw [integral_archIntegrand_eq hlam, autocorr_gaussPhi hlam 0, autocorrGauss_zero]
    rw [show (gaussA lam : ℂ) * (Real.log Real.pi : ℂ) = ((gaussA lam * Real.log Real.pi : ℝ) : ℂ) by
        push_cast; ring,
      show (1 / (2 * (Real.pi : ℂ))) * ((∫ r : ℝ, bumpR c lam r * psiR r : ℝ) : ℂ)
        = (((1 / (2 * Real.pi)) * ∫ r : ℝ, bumpR c lam r * psiR r : ℝ) : ℂ) by push_cast; ring]
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re]
  rw [Complex.sub_re, hre]
  -- step 1: the poles
  have hpole : -(Real.exp (lam / 2) / 2)
      ≤ (weilKernel (autocorr (RvMBridge8.gaussPhi c lam)) 0).re
        + (weilKernel (autocorr (RvMBridge8.gaussPhi c lam)) 1).re := by
    rw [weilKernel_zero_eq_gaussTest hlam, weilKernel_one_eq_gaussTest hlam]
    exact pole_floor hlam (by linarith)
  -- numerics shared by the caps
  have hsl0 : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsl : Real.sqrt lam ≤ 0.038731 := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith
  have hsp0 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hsp : Real.sqrt (2 * Real.pi) ≤ 2.50663 := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith [Real.pi_lt_d6]
  have hprod : Real.sqrt (2 * Real.pi) * Real.sqrt lam ≤ 2.50663 * 0.038731 :=
    mul_le_mul hsp hsl hsl0.le (by norm_num)
  have he1 : Real.exp (-1) ≤ 0.36788 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    have := Real.exp_one_gt_d9
    norm_num
    linarith
  have hehalf : Real.exp (lam / 2) ≤ 1.001 := by
    have h1 : 1 - lam / 2 ≤ Real.exp (-(lam / 2)) := by linarith [Real.add_one_le_exp (-(lam / 2))]
    have h2 : Real.exp (lam / 2) * Real.exp (-(lam / 2)) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (lam / 2)).le
    nlinarith [Real.exp_pos (lam / 2)]
  -- the pole term in units of A: e^{lam/2}/2 <= 0.0006 A
  have hpoleA : Real.exp (lam / 2) / 2 ≤ 0.0006 * gaussA lam := by
    unfold gaussA
    rw [show (0.0006 : ℝ) * (1 / (8 * Real.sqrt (2 * Real.pi) * (lam * Real.sqrt lam)))
        = 0.0006 / (8 * Real.sqrt (2 * Real.pi) * (lam * Real.sqrt lam)) by ring,
      le_div_iff₀ (by positivity)]
    have h1 : lam * (Real.sqrt (2 * Real.pi) * Real.sqrt lam) ≤ 0.0015 * (2.50663 * 0.038731) :=
      mul_le_mul hle' hprod (by positivity) (by norm_num)
    have h2 : Real.exp (lam / 2) * (lam * (Real.sqrt (2 * Real.pi) * Real.sqrt lam))
        ≤ 1.001 * (0.0015 * (2.50663 * 0.038731)) :=
      mul_le_mul hehalf h1 (by positivity) (by norm_num)
    nlinarith
  -- the cap constant: e^{-1}/(2 pi lam) <= 0.0455 A
  have hcap : Real.exp (-1) / (2 * Real.pi * lam) ≤ 0.0455 * gaussA lam := by
    unfold gaussA
    rw [show (0.0455 : ℝ) * (1 / (8 * Real.sqrt (2 * Real.pi) * (lam * Real.sqrt lam)))
        = 0.0455 / (8 * Real.sqrt (2 * Real.pi) * (lam * Real.sqrt lam)) by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : Real.exp (-1) * (Real.sqrt (2 * Real.pi) * Real.sqrt lam) ≤ 0.36788 * (2.50663 * 0.038731) :=
      mul_le_mul he1 hprod (by positivity) (by norm_num)
    have hpi := Real.pi_gt_d6
    nlinarith [mul_pos hlam Real.pi_pos]
  -- step 7 in units of A
  have hJ := integral_bumpR_mul_psiR_ge_bands12 (c := c) hlam
  have hJ' : (1 / (2 * Real.pi)) * ((22403 / 10000) * (2 * Real.pi * gaussA lam) - bandSum12 * (Real.exp (-1) / lam))
      ≤ (1 / (2 * Real.pi)) * ∫ r : ℝ, bumpR c lam r * psiR r :=
    mul_le_mul_of_nonneg_left hJ (by positivity)
  have hid : (1 / (2 * Real.pi)) * ((22403 / 10000) * (2 * Real.pi * gaussA lam) - bandSum12 * (Real.exp (-1) / lam))
      = (22403 / 10000) * gaussA lam - bandSum12 * (Real.exp (-1) / (2 * Real.pi * lam)) := by
    field_simp
  rw [hid] at hJ'
  have hbandA : bandSum12 * (Real.exp (-1) / (2 * Real.pi * lam)) ≤ bandSum12 * (0.0455 * gaussA lam) :=
    mul_le_mul_of_nonneg_left hcap (by unfold bandSum12; norm_num)
  -- log pi <= 1.1448
  have hlogpi : Real.log Real.pi ≤ 1.1448 := by
    rw [Real.log_le_iff_le_exp Real.pi_pos]
    have h1 : Real.exp 1.1448 = Real.exp 1 * Real.exp 0.1448 := by
      rw [← Real.exp_add]; norm_num
    have h2 := Real.sum_le_exp_of_nonneg (x := 0.1448) (by norm_num) 5
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h2
    norm_num at h2
    have h3 := Real.exp_one_gt_d9
    rw [h1]
    nlinarith [Real.pi_lt_d6, Real.exp_pos (0.1448 : ℝ), Real.exp_pos (1 : ℝ)]
  have hlogA : gaussA lam * Real.log Real.pi ≤ gaussA lam * 1.1448 :=
    mul_le_mul_of_nonneg_left hlogpi hA.le
  -- step 2: the prime side (y^6/720 <= e^y at y >= 20)
  have hl2 := Real.log_two_gt_d9
  have hσ : 2 ≤ Real.log 2 / (16 * lam) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hprime := norm_primeSide_le (c := c) hlam hσ
  have hpre := (abs_le.mp (Complex.abs_re_le_norm
    (primeSide (autocorr (RvMBridge8.gaussPhi c lam))))).2
  have hE : 64 * Real.exp (-(Real.log 2) ^ 2 / (16 * lam)) ≤ 0.001 := by
    have hy : 20 ≤ (Real.log 2) ^ 2 / (16 * lam) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    set y := (Real.log 2) ^ 2 / (16 * lam) with hy_def
    have hy0 : 0 ≤ y := by linarith
    have h1 : y ^ 6 / (Nat.factorial 6 : ℝ) ≤ Real.exp y := Real.pow_div_factorial_le_exp _ hy0 6
    rw [show (Nat.factorial 6 : ℝ) = 720 by norm_num [Nat.factorial]] at h1
    have h2 : (20 : ℝ) ^ 6 ≤ y ^ 6 := pow_le_pow_left₀ (by norm_num) hy 6
    have h3 : -(Real.log 2) ^ 2 / (16 * lam) = -y := by rw [hy_def]; ring
    rw [h3, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    nlinarith
  have hprime' : (primeSide (autocorr (RvMBridge8.gaussPhi c lam))).re ≤ 0.001 * gaussA lam := by
    calc (primeSide (autocorr (RvMBridge8.gaussPhi c lam))).re
        ≤ ‖primeSide (autocorr (RvMBridge8.gaussPhi c lam))‖ := hpre
      _ ≤ 64 * gaussA lam * Real.exp (-(Real.log 2) ^ 2 / (16 * lam)) := hprime
      _ = gaussA lam * (64 * Real.exp (-(Real.log 2) ^ 2 / (16 * lam))) := by ring
      _ ≤ gaussA lam * 0.001 := mul_le_mul_of_nonneg_left hE hA.le
      _ = 0.001 * gaussA lam := by ring
  -- assemble: A (-0.0006 + 2.2403 - 0.0455 bandSum12 - 1.1448 - 0.001) > 0
  have hbs : bandSum12 = 458103 / 20000 := rfl
  rw [hbs] at hbandA hJ'
  linarith

/-- THE SMALL-WIDTH REGION OF THE WALL AT lam0 = 3/2000, UNCONDITIONAL (zero-side form). -/
theorem gaussian_positivity_small_lam_3e3 (c lam : ℝ) (hlam : 0 < lam) (hle : lam ≤ 3 / 2000) :
    0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re := by
  rw [gaussianExplicitFormula c lam hlam]
  exact re_weilForm_gauss_nonneg_3e3 c lam hlam hle

theorem gaussian_positivity_small_lam_explicit_3e3 (c lam : ℝ) (hlam : 0 < lam) (hle : lam ≤ lam₂) :
    0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re :=
  gaussian_positivity_small_lam_3e3 c lam hlam (by unfold lam₂ at hle; exact hle)

end RvMBridge30
