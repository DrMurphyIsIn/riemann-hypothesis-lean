/-
  E6Bridge16 -- the SHARP envelope of the Wall (2026-09-21): the band's upper edge with the
  exact c-uniform prime-side constant.

  E6Bridge11.gaussian_positivity_envelope gives, for every width lam > 0, an explicit c1(lam)
  with F(c, lam) >= 0 for |c| >= c1(lam), but its constant carries e^{9 + 2 X(lam)} with
  X(lam) ∋ 16 e^{16 lam} (the AM-GM prime bound): c1(1) ~ e^{2.8e8}.  This file replaces every
  crude step by its exact form and proves

      F(c, lam) >= 0   for   |c| >= envelopeCsharp lam
                          := 2 pi e^{primeAbs lam + 1/2} + sqrt((16 + 2 primeAbs lam)/lam)
                             + 3/sqrt lam + 1,

  where  primeAbs lam := 2 Sum_{n} Lambda(n) n^{-1/2} |1 - (log n)^2/(4 lam)| e^{-(log n)^2/(8 lam)}
  is the EXACT size of the c-uniform prime side in units of A = 1/(8 sqrt(2 pi) lam^{3/2})
  (an explicit convergent series, a real number, NOT an obligation): the prime side of the
  Gaussian test is  2A Sum Lambda(n) n^{-1/2} cos(c log n) (1 - x) e^{-u^2/(8 lam)}, and the
  only c-uniform bound is |cos| <= 1.  Numerically (seam_b_small_lam.py --band-edge)
  primeAbs = 1.40, 3.04, 4.60, 8.74, 13.8, 23.7, 89.6 at lam = 0.1, 0.2, 0.3, 0.5, 0.7, 1, 2, so
  envelopeCsharp = 66, 234, 1050, 6.5e4, 1.0e7, 2.1e11, 8.6e39 (the memo's table; E6Bridge11's
  envelopeC at the same widths is 3e86, 2e368, ..., 1e123494302, ...).

  The other sharpenings: the pole terms are EVALUATED, weilKernel f 0 = gaussTest c lam (i/2),
  weilKernel f 1 = gaussTest c lam (-i/2), of modulus (c^2 + 1/4) e^{-2 lam (c^2 - 1/4)}
  (negligible for |c| >= 3/sqrt lam + 1: section B, via the Gaussian Fourier transform of f at
  a COMPLEX frequency); the Stirling error is kept as 20/r^2 (section C); the bump tail beyond
  |r - c| >= L is e^{-lam L^2} 2 sqrt 2 (2 pi A) with L chosen so that the tail is e^{-16 - 2 P}
  (section D); the archimedean floor is CAPPED at the needed threshold Theta so that no term
  grows with |c| (section D).

  WHAT THE NUMBERS SAY (docs/WALL_SHARP_ENVELOPE_2026-09-21.md): the lead's targets
  envelopeC'(1) <= 1e9 and envelopeC'(0.5) <= 1e6 are NOT reachable: the first not by any
  c-uniform argument (the exact absolute prime sum already gives 2 pi e^{23.7} = 1.2e11 at
  lam = 1), the second not with the island's Chebyshev constants (Mathlib's psi(x) <= (log 4) x
  + 2 sqrt x log x through Abel summation gives ~1e14; Rosser-Schoenfeld's 1.04 x would give
  ~2e6).  What IS proved here is the sharpest c-uniform envelope of the method, with its
  constant an explicit series that the numerics evaluate.  Bounding primeAbs by a closed form
  sharply is what does NOT close (only the crude primeAbs <= 16 e^{16 lam} of E6Bridge11 is
  re-proved, section E).

  Proves nothing about RH.  conjecture1_proved = False.
-/
import E6Bridge10
import E6Bridge11
import RvMBridgeGauss

open Zeta23 Complex MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace RvMBridge16
open WeilExplicit RvMBridge11

/-! ## A. The Gaussian Fourier transform of f at a COMPLEX frequency. -/

/-! The second Gaussian moment at a complex frequency (with the integrability majorant
|x|^2 e^{-a x^2 + |Im w| |x|}) is the prelude's RvMBridgeGauss.integral_sq_mul_cexp_gaussian_fourier
(formerly the primed lemma here). -/

/-- 4 lam A sqrt(8 pi lam) = 1 (the Plancherel normalisation, as a complex identity). -/
lemma gaussA_mul_sqrt {lam : ℝ} (hlam : 0 < lam) :
    (gaussA lam : ℂ) * ((Real.sqrt (8 * Real.pi * lam) : ℝ) : ℂ) * (4 * (lam : ℂ)) = 1 := by
  have hS : Real.sqrt (8 * Real.pi * lam) = 2 * (Real.sqrt (2 * Real.pi) * Real.sqrt lam) := by
    rw [show 8 * Real.pi * lam = 2 ^ 2 * ((2 * Real.pi) * lam) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num),
      Real.sqrt_mul (by positivity)]
  have hreal : gaussA lam * Real.sqrt (8 * Real.pi * lam) * (4 * lam) = 1 := by
    unfold gaussA
    rw [hS]
    have hsp0 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    have hsl0 : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
    field_simp
    norm_num
  exact_mod_cast hreal

/-- THE TRANSFORM OF f AT ANY COMPLEX FREQUENCY:
∫ f(u) e^{i w u} du = (w - c)^2 e^{-2 lam (w - c)^2} = gaussTest c lam w. -/
theorem fourier_autocorrGauss {c lam : ℝ} (hlam : 0 < lam) (w : ℂ) :
    ∫ u : ℝ, autocorrGauss c lam u * cexp (I * w * (u : ℂ)) = RvMBridge6.gaussTest c lam w := by
  set a : ℝ := 1 / (8 * lam) with ha_def
  have ha : 0 < a := by positivity
  have haC : 0 < (a : ℂ).re := by simpa using ha
  set W : ℂ := w - c with hW_def
  have hfun : (fun u : ℝ => autocorrGauss c lam u * cexp (I * w * (u : ℂ)))
      = fun u : ℝ => (gaussA lam : ℂ) * (cexp (I * W * (u : ℂ)) * cexp (-(a : ℂ) * (u : ℂ) ^ 2))
        - ((gaussA lam : ℂ) * ((1 / (4 * lam) : ℝ) : ℂ))
          * ((u : ℂ) ^ 2 * cexp (-(a : ℂ) * (u : ℂ) ^ 2) * cexp (I * W * (u : ℂ))) := by
    funext u
    unfold autocorrGauss
    have e1 : cexp (-(I * c * u)) * cexp (I * w * (u : ℂ)) = cexp (I * W * (u : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      rw [hW_def]
      ring
    have e2 : ((Real.exp (-(u ^ 2) / (8 * lam)) : ℝ) : ℂ) = cexp (-(a : ℂ) * (u : ℂ) ^ 2) := by
      rw [Complex.ofReal_exp]
      congr 1
      rw [ha_def]
      push_cast
      ring
    rw [← e1, e2]
    push_cast
    ring
  have hmaj : Integrable (fun x : ℝ => |x| ^ 2 * Real.exp (-a * x ^ 2 + |W.im| * |x|)) :=
    RvMBridgeGauss.integrable_abs_pow_mul_exp_quadratic_abs ha |W.im| 2
  have hi_sq : Integrable (fun x : ℝ => (x : ℂ) ^ 2 * cexp (-(a : ℂ) * (x : ℂ) ^ 2)
      * cexp (I * W * (x : ℂ))) := by
    refine hmaj.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_exp, Complex.norm_exp,
      Real.norm_eq_abs]
    have h1 : (-(a : ℂ) * (x : ℂ) ^ 2).re = -a * x ^ 2 := by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, pow_two]
    have h2 : (I * W * (x : ℂ)).re = -(W.im * x) := by simp
    rw [h1, h2, mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.exp_le_exp]
    have : -(W.im * x) ≤ |W.im| * |x| := by
      rw [← abs_mul]
      exact neg_le_abs _
    linarith
  have hi_uv : Integrable (fun x : ℝ => cexp (I * W * (x : ℂ)) * cexp (-(a : ℂ) * (x : ℂ) ^ 2)) := by
    have h := integrable_cexp_quadratic haC (I * W) 0
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [add_zero, Complex.exp_add]
    ring
  rw [hfun, integral_sub (hi_uv.const_mul _) (hi_sq.const_mul _), integral_const_mul,
    integral_const_mul, fourierIntegral_gaussian haC W,
    RvMBridgeGauss.integral_sq_mul_cexp_gaussian_fourier ha W,
    cpow_pi_div_a hlam]
  have hE : cexp (-W ^ 2 / (4 * (a : ℂ))) = cexp (-(2 * (lam : ℂ)) * W ^ 2) := by
    congr 1
    rw [ha_def]
    push_cast
    field_simp
    ring
  rw [hE]
  unfold RvMBridge6.gaussTest
  rw [← hW_def]
  have hAS := gaussA_mul_sqrt hlam
  set S : ℂ := ((Real.sqrt (8 * Real.pi * lam) : ℝ) : ℂ) with hS
  set E : ℂ := cexp (-(2 * (lam : ℂ)) * W ^ 2) with hE_def
  have hlam0 : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hacast : (a : ℂ) = 1 / (8 * (lam : ℂ)) := by rw [ha_def]; push_cast; ring
  calc (gaussA lam : ℂ) * (S * E) - (gaussA lam : ℂ) * ((1 / (4 * lam) : ℝ) : ℂ)
        * (1 / (2 * (a : ℂ)) * (S * E + I * W * (I * W / (2 * (a : ℂ)) * (S * E))))
      = ((gaussA lam : ℂ) * S * (4 * (lam : ℂ))) * (W ^ 2 * E) := by
        rw [hacast]
        push_cast
        field_simp
        ring_nf
        simp only [I_sq]
        ring
    _ = W ^ 2 * E := by rw [hAS, one_mul]

/-! ## B. The pole terms, evaluated. -/

/-- weilKernel f 0 = ∫ f(u) e^{-u/2} du = ∫ f(u) e^{i (i/2) u} du = gaussTest c lam (i/2). -/
theorem weilKernel_zero_eq_gaussTest {c lam : ℝ} (hlam : 0 < lam) :
    weilKernel (autocorr (RvMBridge8.gaussPhi c lam)) 0 = RvMBridge6.gaussTest c lam (I / 2) := by
  rw [autocorr_gaussPhi_funext hlam, ← fourier_autocorrGauss hlam (I / 2)]
  unfold weilKernel
  congr 1
  funext u
  congr 2
  rw [show I * (I / 2) * (u : ℂ) = (I * I) * (u : ℂ) / 2 by ring, I_mul_I]
  ring

theorem weilKernel_one_eq_gaussTest {c lam : ℝ} (hlam : 0 < lam) :
    weilKernel (autocorr (RvMBridge8.gaussPhi c lam)) 1 = RvMBridge6.gaussTest c lam (-I / 2) := by
  rw [autocorr_gaussPhi_funext hlam, ← fourier_autocorrGauss hlam (-I / 2)]
  unfold weilKernel
  congr 1
  funext u
  congr 2
  rw [show I * (-I / 2) * (u : ℂ) = -(I * I) * (u : ℂ) / 2 by ring, I_mul_I]
  ring

/-- |gaussTest c lam (± i/2)| = (c^2 + 1/4) e^{-2 lam (c^2 - 1/4)}. -/
lemma norm_gaussTest_half (c lam : ℝ) (s : ℝ) (hs : s = 1 / 2 ∨ s = -1 / 2) :
    ‖RvMBridge6.gaussTest c lam ((s : ℝ) * I)‖ = (c ^ 2 + 1 / 4) * Real.exp (-(2 * lam) * (c ^ 2 - 1 / 4)) := by
  unfold RvMBridge6.gaussTest
  rw [norm_mul, norm_pow, Complex.norm_exp]
  have hsq : s ^ 2 = 1 / 4 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hn : ‖(s : ℂ) * I - (c : ℂ)‖ ^ 2 = c ^ 2 + 1 / 4 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    nlinarith [hsq]
  have hre : (-(2 * (lam : ℂ)) * ((s : ℂ) * I - (c : ℂ)) ^ 2).re = -(2 * lam) * (c ^ 2 - 1 / 4) := by
    have : ((s : ℂ) * I - (c : ℂ)) ^ 2 = ((c ^ 2 - s ^ 2 : ℝ) : ℂ) + ((-2 * s * c : ℝ) : ℂ) * I := by
      have hI : I ^ 2 = -1 := I_sq
      push_cast
      linear_combination (s : ℂ) ^ 2 * hI
    rw [this, hsq, show -(2 * (lam : ℂ)) = ((-(2 * lam) : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [hn, hre]

/-- THE POLE-TERM BOUND, sharp: for c^2 >= 6/lam + 1 the two pole terms together are at most
0.13 A (they decay like e^{-2 lam c^2}). -/
theorem norm_poles_le {c lam : ℝ} (hlam : 0 < lam) (hc : 6 / lam + 1 ≤ c ^ 2) :
    ‖weilKernel (autocorr (RvMBridge8.gaussPhi c lam)) 0‖
      + ‖weilKernel (autocorr (RvMBridge8.gaussPhi c lam)) 1‖ ≤ 0.13 * gaussA lam := by
  have hA := gaussA_pos hlam
  rw [weilKernel_zero_eq_gaussTest hlam, weilKernel_one_eq_gaussTest hlam]
  have h0 : RvMBridge6.gaussTest c lam (I / 2) = RvMBridge6.gaussTest c lam (((1 / 2 : ℝ) : ℝ) * I) := by
    congr 1; push_cast; ring
  have h1 : RvMBridge6.gaussTest c lam (-I / 2) = RvMBridge6.gaussTest c lam (((-1 / 2 : ℝ) : ℝ) * I) := by
    congr 1; push_cast; ring
  rw [h0, h1, norm_gaussTest_half c lam _ (Or.inl rfl), norm_gaussTest_half c lam _ (Or.inr rfl)]
  -- (c^2 + 1/4) e^{-2 lam (c^2 - 1/4)} <= (5/4) c^2 e^{lam/2} e^{-2 lam c^2}
  --   <= (5/4) (1/lam) e^{lam/2} e^{-lam c^2}   (y e^{-y} <= 1 with y = lam c^2)
  --   <= (5/4) (1/lam) e^{lam/2} e^{-6 - lam}                (lam c^2 >= 6 + lam)
  have hc1 : 1 ≤ c ^ 2 := by
    have : 0 < 6 / lam := by positivity
    linarith
  have hy : 6 + lam ≤ lam * c ^ 2 := by
    have := mul_le_mul_of_nonneg_left hc hlam.le
    rw [mul_add, mul_div_cancel₀ _ hlam.ne', mul_one] at this
    linarith
  have hye : lam * c ^ 2 * Real.exp (-(lam * c ^ 2)) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    linarith [Real.add_one_le_exp (lam * c ^ 2)]
  have hexp1 : Real.exp (-(2 * lam) * (c ^ 2 - 1 / 4))
      = Real.exp (lam / 2) * (Real.exp (-(lam * c ^ 2)) * Real.exp (-(lam * c ^ 2))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hexp2 : Real.exp (-(lam * c ^ 2)) ≤ Real.exp (-6) * Real.exp (-lam) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    linarith
  have hkey : (c ^ 2 + 1 / 4) * Real.exp (-(2 * lam) * (c ^ 2 - 1 / 4))
      ≤ (5 / 4) * (1 / lam) * Real.exp (lam / 2) * (Real.exp (-6) * Real.exp (-lam)) := by
    rw [hexp1]
    have hc54 : c ^ 2 + 1 / 4 ≤ (5 / 4) * c ^ 2 := by linarith
    calc (c ^ 2 + 1 / 4) * (Real.exp (lam / 2) * (Real.exp (-(lam * c ^ 2)) * Real.exp (-(lam * c ^ 2))))
        ≤ (5 / 4) * c ^ 2 * (Real.exp (lam / 2) * (Real.exp (-(lam * c ^ 2)) * Real.exp (-(lam * c ^ 2)))) :=
          mul_le_mul_of_nonneg_right hc54 (by positivity)
      _ = (5 / 4) * (1 / lam) * Real.exp (lam / 2) * Real.exp (-(lam * c ^ 2))
          * (lam * c ^ 2 * Real.exp (-(lam * c ^ 2))) := by field_simp
      _ ≤ (5 / 4) * (1 / lam) * Real.exp (lam / 2) * Real.exp (-(lam * c ^ 2)) * 1 :=
          mul_le_mul_of_nonneg_left hye (by positivity)
      _ = (5 / 4) * (1 / lam) * Real.exp (lam / 2) * Real.exp (-(lam * c ^ 2)) := by ring
      _ ≤ (5 / 4) * (1 / lam) * Real.exp (lam / 2) * (Real.exp (-6) * Real.exp (-lam)) :=
          mul_le_mul_of_nonneg_left hexp2 (by positivity)
  -- numerics: e^{-6} <= 1/400, sqrt(2 pi) <= 2.51, sqrt lam e^{-lam/2} <= 1
  have he6 : Real.exp (-6) ≤ 1 / 400 := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    have h1 : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h1]
    have := Real.exp_one_gt_d9
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283) this.le 6]
  have hsp : Real.sqrt (2 * Real.pi) ≤ 2.51 := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith [Real.pi_lt_d2]
  have hsl0 : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsle : Real.sqrt lam * Real.exp (-(lam / 2)) ≤ 1 := by
    -- sqrt lam <= e^{lam/2}  <=>  lam <= e^{lam}
    have h1 : lam ≤ Real.exp lam := by linarith [Real.add_one_le_exp lam]
    have h2 : Real.sqrt lam ≤ Real.exp (lam / 2) := by
      rw [Real.sqrt_le_left (Real.exp_pos _).le, ← Real.exp_nat_mul]
      push_cast
      rw [show (2 : ℝ) * (lam / 2) = lam by ring]
      exact h1
    have h3 : Real.exp (lam / 2) * Real.exp (-(lam / 2)) = 1 := by
      rw [← Real.exp_add]; simp
    calc Real.sqrt lam * Real.exp (-(lam / 2)) ≤ Real.exp (lam / 2) * Real.exp (-(lam / 2)) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = 1 := h3
  -- the target in the form (5/2)(1/lam) e^{lam/2} e^{-6} e^{-lam} <= 0.13 A
  have hexp3 : Real.exp (lam / 2) * Real.exp (-lam) = Real.exp (-(lam / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hAinv : gaussA lam = 1 / (8 * Real.sqrt (2 * Real.pi) * (lam * Real.sqrt lam)) := rfl
  have hfinal : 2 * ((5 / 4) * (1 / lam) * Real.exp (lam / 2) * (Real.exp (-6) * Real.exp (-lam)))
      ≤ 0.13 * gaussA lam := by
    have hsp0 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    have e : 2 * ((5 / 4) * (1 / lam) * Real.exp (lam / 2) * (Real.exp (-6) * Real.exp (-lam)))
        = (20 * (Real.exp (-6) * Real.sqrt (2 * Real.pi)) * (Real.sqrt lam * Real.exp (-(lam / 2))))
          * gaussA lam := by
      rw [← hexp3, hAinv]
      field_simp
      ring
    rw [e]
    have h1 : Real.exp (-6) * Real.sqrt (2 * Real.pi) ≤ (1 / 400) * 2.51 :=
      mul_le_mul he6 hsp hsp0.le (by norm_num)
    have h2 : 20 * (Real.exp (-6) * Real.sqrt (2 * Real.pi)) * (Real.sqrt lam * Real.exp (-(lam / 2)))
        ≤ 20 * ((1 / 400) * 2.51) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) hsle (by positivity) (by positivity)
    have h3 : 20 * ((1 / 400) * 2.51) * 1 ≤ (0.13 : ℝ) := by norm_num
    exact mul_le_mul_of_nonneg_right (h2.trans h3) hA.le
  linarith

/-! ## C. The exact c-uniform prime constant. -/

/-- The n-th absolute prime term, in units of A. -/
def primeAbsTerm (lam : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.sqrt n
    * (|1 - (Real.log n) ^ 2 / (4 * lam)| * Real.exp (-(Real.log n) ^ 2 / (8 * lam)))

/-- primeAbs lam = 2 Σ_n Λ(n) n^{-1/2} |1 - (log n)^2/(4 lam)| e^{-(log n)^2/(8 lam)}: the exact
size of the c-uniform prime side in units of A. -/
def primeAbs (lam : ℝ) : ℝ := 2 * ∑' n : ℕ, primeAbsTerm lam n

lemma primeAbsTerm_nonneg (lam : ℝ) (n : ℕ) : 0 ≤ primeAbsTerm lam n := by
  unfold primeAbsTerm
  have := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  positivity

/-- primeAbsTerm lam n <= 4 e^{16 lam} / n^2 (the crude majorant, for summability). -/
lemma primeAbsTerm_le {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    primeAbsTerm lam n ≤ 4 * Real.exp (16 * lam) * (1 / (n : ℝ) ^ 2) := by
  unfold primeAbsTerm
  rcases lt_or_ge n 2 with hn | hn
  · have h0 : ArithmeticFunction.vonMangoldt n = 0 := by
      interval_cases n
      · simp
      · exact ArithmeticFunction.vonMangoldt_apply_one
    rw [h0]
    simp only [zero_div, zero_mul]
    positivity
  · have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hΛ : ArithmeticFunction.vonMangoldt n / Real.sqrt n ≤ 2 := by
      have h1 : ArithmeticFunction.vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
      have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
      have h2 : Real.log n ≤ 2 * Real.sqrt n := by
        have := Real.log_le_sub_one_of_pos hs
        rw [Real.log_sqrt hn0.le] at this
        linarith
      rw [div_le_iff₀ hs]
      linarith
    have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n :=
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    -- |1 - 2s| e^{-s} <= 2 e^{-s/2}, s = (log n)^2/(8 lam)
    set s := (Real.log n) ^ 2 / (8 * lam) with hs_def
    have hs0 : 0 ≤ s := by positivity
    have e1 : 1 - (Real.log n) ^ 2 / (4 * lam) = 1 - 2 * s := by rw [hs_def]; ring
    have e2 : -(Real.log n) ^ 2 / (8 * lam) = -s := by rw [hs_def]; ring
    rw [e1, e2]
    have hg := abs_one_sub_two_mul_exp_le hs0
    have hexp : Real.exp (-(s / 2)) ≤ Real.exp (16 * lam) * (1 / (n : ℝ) ^ 2) := by
      have e3 : (1 : ℝ) / (n : ℝ) ^ 2 = Real.exp (-(2 * Real.log n)) := by
        rw [Real.exp_neg, show 2 * Real.log n = Real.log ((n : ℝ) ^ 2) by
          rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity), one_div]
      rw [e3, ← Real.exp_add, Real.exp_le_exp, hs_def]
      rw [show -((Real.log n) ^ 2 / (8 * lam) / 2) = -(Real.log n) ^ 2 / (16 * lam) by ring,
        div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg (Real.log n - 16 * lam)]
    calc ArithmeticFunction.vonMangoldt n / Real.sqrt n * (|1 - 2 * s| * Real.exp (-s))
        ≤ 2 * (2 * Real.exp (-(s / 2))) := mul_le_mul hΛ hg (by positivity) (by norm_num)
      _ ≤ 2 * (2 * (Real.exp (16 * lam) * (1 / (n : ℝ) ^ 2))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ = 4 * Real.exp (16 * lam) * (1 / (n : ℝ) ^ 2) := by ring

lemma summable_primeAbsTerm {lam : ℝ} (hlam : 0 < lam) : Summable (primeAbsTerm lam) :=
  Summable.of_nonneg_of_le (primeAbsTerm_nonneg lam) (primeAbsTerm_le hlam)
    ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left _)

lemma primeAbs_nonneg {lam : ℝ} (_hlam : 0 < lam) : 0 ≤ primeAbs lam := by
  unfold primeAbs
  have h : 0 ≤ ∑' n : ℕ, primeAbsTerm lam n := tsum_nonneg (primeAbsTerm_nonneg lam)
  linarith

/-- The crude bound of E6Bridge11, re-derived: primeAbs lam <= 16 e^{16 lam}. -/
lemma primeAbs_le_crude {lam : ℝ} (hlam : 0 < lam) : primeAbs lam ≤ 16 * Real.exp (16 * lam) := by
  unfold primeAbs
  have hM : Summable (fun n : ℕ => 4 * Real.exp (16 * lam) * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left _
  have h := (summable_primeAbsTerm hlam).tsum_le_tsum (primeAbsTerm_le hlam) hM
  rw [tsum_mul_left, hasSum_zeta_two.tsum_eq] at h
  have hpi2 : Real.pi ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have he : 0 < Real.exp (16 * lam) := Real.exp_pos _
  nlinarith

/-- |f(u) + f(-u)| <= 2 A |1 - u^2/(4 lam)| e^{-u^2/(8 lam)}  (|cos| <= 1 is the only loss). -/
lemma norm_autocorrGauss_add_neg_le {c lam : ℝ} (hlam : 0 < lam) (u : ℝ) :
    ‖autocorrGauss c lam u + autocorrGauss c lam (-u)‖
      ≤ 2 * gaussA lam * (|1 - u ^ 2 / (4 * lam)| * Real.exp (-(u ^ 2) / (8 * lam))) := by
  have hA := gaussA_pos hlam
  unfold autocorrGauss
  rw [neg_sq]
  have e : (gaussA lam : ℂ) * ((1 - u ^ 2 / (4 * lam) : ℝ) : ℂ) * ((Real.exp (-(u ^ 2) / (8 * lam)) : ℝ) : ℂ)
        * cexp (-(I * c * u))
      + (gaussA lam : ℂ) * ((1 - u ^ 2 / (4 * lam) : ℝ) : ℂ) * ((Real.exp (-(u ^ 2) / (8 * lam)) : ℝ) : ℂ)
        * cexp (-(I * c * ((-u : ℝ) : ℂ)))
      = ((gaussA lam * ((1 - u ^ 2 / (4 * lam)) * Real.exp (-(u ^ 2) / (8 * lam))) : ℝ) : ℂ)
        * (cexp (-(I * c * u)) + cexp (I * c * u)) := by
    push_cast
    ring_nf
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hA, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  have h2 : ‖cexp (-(I * c * u)) + cexp (I * c * u)‖ ≤ 2 := by
    calc ‖cexp (-(I * c * u)) + cexp (I * c * u)‖ ≤ ‖cexp (-(I * c * u))‖ + ‖cexp (I * c * u)‖ :=
          norm_add_le _ _
      _ = 1 + 1 := by
          rw [Complex.norm_exp, Complex.norm_exp]
          have h1 : (-(I * c * u)).re = 0 := by simp
          have h2 : (I * c * u).re = 0 := by simp
          rw [h1, h2, Real.exp_zero]
      _ = 2 := by norm_num
  calc gaussA lam * (|1 - u ^ 2 / (4 * lam)| * Real.exp (-(u ^ 2) / (8 * lam)))
        * ‖cexp (-(I * c * u)) + cexp (I * c * u)‖
      ≤ gaussA lam * (|1 - u ^ 2 / (4 * lam)| * Real.exp (-(u ^ 2) / (8 * lam))) * 2 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2 * gaussA lam * (|1 - u ^ 2 / (4 * lam)| * Real.exp (-(u ^ 2) / (8 * lam))) := by ring

/-- THE SHARP PRIME BOUND: ‖primeSide f‖ <= A primeAbs lam. -/
theorem norm_primeSide_le_primeAbs {c lam : ℝ} (hlam : 0 < lam) :
    ‖primeSide (autocorr (RvMBridge8.gaussPhi c lam))‖ ≤ gaussA lam * primeAbs lam := by
  rw [autocorr_gaussPhi_funext hlam]
  unfold primeSide
  set T : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
    * (autocorrGauss c lam (Real.log n) + autocorrGauss c lam (-Real.log n)) with hT
  have hA := gaussA_pos hlam
  have hterm : ∀ n : ℕ, ‖T n‖ ≤ 2 * gaussA lam * primeAbsTerm lam n := by
    intro n
    have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n :=
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    unfold primeAbsTerm
    calc ‖T n‖ = (ArithmeticFunction.vonMangoldt n / Real.sqrt n)
          * ‖autocorrGauss c lam (Real.log n) + autocorrGauss c lam (-Real.log n)‖ := by
          rw [hT]
          simp only []
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hΛ0]
      _ ≤ (ArithmeticFunction.vonMangoldt n / Real.sqrt n)
          * (2 * gaussA lam * (|1 - (Real.log n) ^ 2 / (4 * lam)|
              * Real.exp (-(Real.log n) ^ 2 / (8 * lam)))) :=
          mul_le_mul_of_nonneg_left (norm_autocorrGauss_add_neg_le hlam _) hΛ0
      _ = 2 * gaussA lam * (ArithmeticFunction.vonMangoldt n / Real.sqrt n
          * (|1 - (Real.log n) ^ 2 / (4 * lam)| * Real.exp (-(Real.log n) ^ 2 / (8 * lam)))) := by
          ring
  have hM : Summable (fun n : ℕ => 2 * gaussA lam * primeAbsTerm lam n) :=
    (summable_primeAbsTerm hlam).mul_left _
  have hs : Summable (fun n : ℕ => ‖T n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hM
  calc ‖∑' n : ℕ, T n‖ ≤ ∑' n : ℕ, ‖T n‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n : ℕ, 2 * gaussA lam * primeAbsTerm lam n := hs.tsum_le_tsum hterm hM
    _ = gaussA lam * primeAbs lam := by
        rw [tsum_mul_left]
        unfold primeAbs
        ring

/-! ## D. The archimedean floor, capped, with the sharper Stirling error and a free tail radius. -/

/-- Re psi(1/4 + i r/2) >= log(|r|/2) - 20/r^2 for |r| >= 2 (Stirling, error kept). -/
theorem re_digamma_quarter_ge_log' {r : ℝ} (hr : 2 ≤ |r|) :
    Real.log (|r| / 2) - 20 / r ^ 2
      ≤ (Complex.digamma (((1 / 4 : ℝ) : ℂ) + I * ((r / 2 : ℝ) : ℂ))).re := by
  have ht : 1 / 2 ≤ |r / 2| := by rw [abs_div, abs_two]; linarith
  have h := Zeta23.StirlingVert.re_digamma_stirling' (a := 1 / 4) (by norm_num) (by norm_num) ht
  have hr2 : 5 / (r / 2) ^ 2 = 20 / r ^ 2 := by
    have : r ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hr
      linarith
    field_simp
    ring
  have := (abs_le.mp h).1
  rw [abs_div, abs_two, hr2] at this
  linarith

lemma psiR_ge_log' {r : ℝ} (hr : 2 ≤ |r|) : Real.log (|r| / 2) - 20 / r ^ 2 ≤ psiR r := by
  rw [psiR_eq]
  exact re_digamma_quarter_ge_log' hr

/-- Tail mass beyond |r - c| >= L: ∫ <= e^{-lam L^2} (2 pi A(lam/2)). -/
lemma integral_indicator_bumpR_tail_le' {c lam : ℝ} (hlam : 0 < lam) {L : ℝ} (hL : 0 ≤ L) :
    ∫ r : ℝ, (Set.Ioo (c - L) (c + L))ᶜ.indicator (bumpR c lam) r
      ≤ Real.exp (-(lam * L ^ 2)) * (2 * Real.pi * gaussA (lam / 2)) := by
  have hbi : Integrable (bumpR c lam) := integrable_bumpR hlam
  have hind : Integrable ((Set.Ioo (c - L) (c + L))ᶜ.indicator (bumpR c lam)) :=
    hbi.indicator measurableSet_Ioo.compl
  have hhalf : Integrable (fun r : ℝ => Real.exp (-(lam * L ^ 2)) * bumpR c (lam / 2) r) :=
    (integrable_bumpR (c := c) (by positivity : 0 < lam / 2)).const_mul _
  have hle : (Set.Ioo (c - L) (c + L))ᶜ.indicator (bumpR c lam)
      ≤ fun r : ℝ => Real.exp (-(lam * L ^ 2)) * bumpR c (lam / 2) r := by
    intro r
    by_cases hr : r ∈ (Set.Ioo (c - L) (c + L))ᶜ
    · rw [Set.indicator_of_mem hr]
      show bumpR c lam r ≤ Real.exp (-(lam * L ^ 2)) * bumpR c (lam / 2) r
      rw [bumpR_half]
      unfold bumpR
      have hx : L ^ 2 ≤ (r - c) ^ 2 := by
        simp only [Set.mem_compl_iff, Set.mem_Ioo, not_and_or, not_lt] at hr
        rcases hr with h | h
        · nlinarith
        · nlinarith
      have hexp : Real.exp (-(2 * lam) * (r - c) ^ 2)
          ≤ Real.exp (-(lam * L ^ 2)) * Real.exp (-lam * (r - c) ^ 2) := by
        rw [← Real.exp_add, Real.exp_le_exp]
        nlinarith
      calc (r - c) ^ 2 * Real.exp (-(2 * lam) * (r - c) ^ 2)
          ≤ (r - c) ^ 2 * (Real.exp (-(lam * L ^ 2)) * Real.exp (-lam * (r - c) ^ 2)) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = Real.exp (-(lam * L ^ 2)) * ((r - c) ^ 2 * Real.exp (-lam * (r - c) ^ 2)) := by ring
    · rw [Set.indicator_of_notMem hr]
      have := bumpR_nonneg c (lam / 2) r
      positivity
  calc ∫ r : ℝ, (Set.Ioo (c - L) (c + L))ᶜ.indicator (bumpR c lam) r
      ≤ ∫ r : ℝ, Real.exp (-(lam * L ^ 2)) * bumpR c (lam / 2) r := integral_mono hind hhalf hle
    _ = Real.exp (-(lam * L ^ 2)) * (2 * Real.pi * gaussA (lam / 2)) := by
        rw [integral_const_mul, integral_bumpR (by positivity)]

/-- THE CAPPED FLOOR: for 0 <= Theta <= log((|c| - L)/2) - 20/(|c| - L)^2 (with |c| - L >= 2),
∫ bumpR psi >= Theta (2 pi A) - (Theta + 5) e^{-lam L^2} (2 pi A(lam/2)). -/
theorem integral_bumpR_mul_psiR_ge_capped {c lam L Θ : ℝ} (hlam : 0 < lam) (hL : 0 ≤ L)
    (hc : 2 ≤ |c| - L) (hΘ0 : 0 ≤ Θ) (hΘ : Θ ≤ Real.log ((|c| - L) / 2) - 20 / (|c| - L) ^ 2) :
    Θ * (2 * Real.pi * gaussA lam)
      - (Θ + 5) * (Real.exp (-(lam * L ^ 2)) * (2 * Real.pi * gaussA (lam / 2)))
      ≤ ∫ r : ℝ, bumpR c lam r * psiR r := by
  set S := (Set.Ioo (c - L) (c + L))ᶜ with hS
  have hbi : Integrable (bumpR c lam) := integrable_bumpR hlam
  have hind : Integrable (S.indicator (bumpR c lam)) := hbi.indicator measurableSet_Ioo.compl
  set Lf : ℝ → ℝ := fun r => Θ * bumpR c lam r - (Θ + 5) * S.indicator (bumpR c lam) r with hLf
  have hLi : Integrable Lf := (hbi.const_mul Θ).sub (hind.const_mul (Θ + 5))
  have hle : Lf ≤ fun r => bumpR c lam r * psiR r := by
    intro r
    simp only [hLf]
    have hb0 := bumpR_nonneg c lam r
    by_cases hr : r ∈ S
    · rw [Set.indicator_of_mem hr]
      have := psiR_ge r
      nlinarith
    · rw [Set.indicator_of_notMem hr]
      have hr' : r ∈ Set.Ioo (c - L) (c + L) := by simpa [hS] using hr
      have habs : |c| - L ≤ |r| := by
        have h1 : |c| - |r| ≤ |c - r| := abs_sub_abs_le_abs_sub c r
        have h2 : |c - r| < L := by
          rw [abs_lt]
          constructor <;> linarith [hr'.1, hr'.2]
        linarith
      have hr2 : 2 ≤ |r| := le_trans hc habs
      have hlog : Θ ≤ psiR r := by
        have h := psiR_ge_log' hr2
        have hmono : Real.log ((|c| - L) / 2) ≤ Real.log (|r| / 2) :=
          Real.log_le_log (by linarith) (by linarith)
        have hR0 : 0 < |c| - L := by linarith
        have herr : 20 / r ^ 2 ≤ 20 / (|c| - L) ^ 2 := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          rw [← sq_abs r]
          exact pow_le_pow_left₀ hR0.le habs 2
        linarith
      nlinarith
  have hmono := integral_mono hLi (integrable_bumpR_mul_psiR hlam) hle
  rw [hLf, integral_sub (hbi.const_mul Θ) (hind.const_mul (Θ + 5)), integral_const_mul,
    integral_const_mul, integral_bumpR hlam] at hmono
  have htail := integral_indicator_bumpR_tail_le' (c := c) hlam hL
  rw [← hS] at htail
  have hΘ5 : 0 ≤ Θ + 5 := by linarith
  have := mul_le_mul_of_nonneg_left htail hΘ5
  linarith

/-! ## E. The sharp envelope. -/

/-- The tail radius: lam L^2 = 16 + 2 primeAbs lam, so the tail is e^{-16 - 2 P}. -/
def tailRadius (lam : ℝ) : ℝ := Real.sqrt ((16 + 2 * primeAbs lam) / lam)

/-- THE SHARP ENVELOPE THRESHOLD: c1(lam) = 2 pi e^{primeAbs lam + 1/2} + tailRadius lam
+ 3/sqrt lam + 1. -/
def envelopeCsharp (lam : ℝ) : ℝ :=
  2 * Real.pi * Real.exp (primeAbs lam + 1 / 2) + tailRadius lam + 3 / Real.sqrt lam + 1

lemma tailRadius_sq {lam : ℝ} (hlam : 0 < lam) :
    lam * tailRadius lam ^ 2 = 16 + 2 * primeAbs lam := by
  unfold tailRadius
  rw [Real.sq_sqrt (by have := primeAbs_nonneg hlam; positivity)]
  field_simp

lemma tailRadius_nonneg (lam : ℝ) : 0 ≤ tailRadius lam := Real.sqrt_nonneg _

set_option maxHeartbeats 1600000 in
/-- THE SHARP ENVELOPE THEOREM (primes-side form), UNCONDITIONAL. -/
theorem re_weilForm_gauss_nonneg_sharp (c lam : ℝ) (hlam : 0 < lam) (hc : envelopeCsharp lam ≤ |c|) :
    0 ≤ (archSide (autocorr (RvMBridge8.gaussPhi c lam))
          - primeSide (autocorr (RvMBridge8.gaussPhi c lam))).re := by
  have hA := gaussA_pos hlam
  set P := primeAbs lam with hP
  have hP0 : 0 ≤ P := primeAbs_nonneg hlam
  set L := tailRadius lam with hL
  have hL0 : 0 ≤ L := tailRadius_nonneg lam
  have hLsq : lam * L ^ 2 = 16 + 2 * P := tailRadius_sq hlam
  have hsl0 : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsl : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlam.le
  -- e^{1/2} >= 1.648, so 2 pi e^{P + 1/2} >= 10.3 e^P >= 10.3
  have hehalf : (1.648 : ℝ) ≤ Real.exp (1 / 2) := by
    have h : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have := Real.exp_one_gt_d9
    nlinarith [Real.exp_pos (1 / 2)]
  have heP : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP0
  have hexpP : Real.exp (P + 1 / 2) = Real.exp P * Real.exp (1 / 2) := Real.exp_add _ _
  have hR : 2 * Real.pi * Real.exp (P + 1 / 2) ≤ |c| - L - (3 / Real.sqrt lam + 1) := by
    unfold envelopeCsharp at hc
    rw [← hP, ← hL] at hc
    linarith
  have hR10 : 10.3 ≤ 2 * Real.pi * Real.exp (P + 1 / 2) := by
    rw [hexpP]
    have hprod : 1 * 1.648 ≤ Real.exp P * Real.exp (1 / 2) :=
      mul_le_mul heP hehalf (by norm_num) (Real.exp_pos P).le
    nlinarith [Real.pi_gt_d2, hprod]
  have hcL2 : 2 ≤ |c| - L := by
    have : 0 < 3 / Real.sqrt lam + 1 := by positivity
    linarith
  -- the pole condition c^2 >= 6/lam + 1 from |c| >= 3/sqrt lam + 1
  have hc3 : 3 / Real.sqrt lam + 1 ≤ |c| := by
    have := Real.exp_pos (P + 1 / 2)
    have := Real.pi_pos
    linarith [mul_pos (mul_pos two_pos Real.pi_pos) (Real.exp_pos (P + 1 / 2))]
  have hc2 : 6 / lam + 1 ≤ c ^ 2 := by
    have h1 : (3 / Real.sqrt lam + 1) ^ 2 ≤ |c| ^ 2 :=
      pow_le_pow_left₀ (by positivity) hc3 2
    rw [sq_abs] at h1
    have h2 : (3 / Real.sqrt lam) ^ 2 = 9 / lam := by
      rw [div_pow, hsl]; norm_num
    have h3 : 0 ≤ 3 / Real.sqrt lam := by positivity
    have h4 : 6 / lam ≤ 9 / lam := by
      apply div_le_div_of_nonneg_right (by norm_num) hlam.le
    nlinarith
  -- the capped threshold
  set Θ := Real.log Real.pi + P + 0.31 with hΘ
  have hΘ0 : 0 ≤ Θ := by
    have : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_d2])
    linarith
  have hΘle : Θ ≤ Real.log ((|c| - L) / 2) - 20 / (|c| - L) ^ 2 := by
    have hR0 : (10.3 : ℝ) ≤ |c| - L := by
      have : 0 < 3 / Real.sqrt lam + 1 := by positivity
      linarith
    have h1 : Real.log Real.pi + P + 1 / 2 ≤ Real.log ((|c| - L) / 2) := by
      have : Real.log Real.pi + P + 1 / 2 = Real.log (Real.pi * Real.exp (P + 1 / 2)) := by
        rw [Real.log_mul Real.pi_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
        ring
      rw [this]
      apply Real.log_le_log (by positivity)
      have : 0 < 3 / Real.sqrt lam + 1 := by positivity
      linarith
    have h2 : 20 / (|c| - L) ^ 2 ≤ 0.19 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hJ := integral_bumpR_mul_psiR_ge_capped (c := c) hlam hL0 hcL2 hΘ0 hΘle
  rw [hLsq] at hJ
  -- the pieces
  have hpoles := norm_poles_le hlam hc2
  have hprime := norm_primeSide_le_primeAbs (c := c) hlam
  rw [← hP] at hprime
  have hpre := (abs_le.mp (Complex.abs_re_le_norm
    (primeSide (autocorr (RvMBridge8.gaussPhi c lam))))).2
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
  have h0 := (abs_le.mp (Complex.abs_re_le_norm (weilKernel (autocorr (RvMBridge8.gaussPhi c lam)) 0))).1
  have h1 := (abs_le.mp (Complex.abs_re_le_norm (weilKernel (autocorr (RvMBridge8.gaussPhi c lam)) 1))).1
  -- J in units of A
  have hJ' : (1 / (2 * Real.pi)) * (Θ * (2 * Real.pi * gaussA lam)
      - (Θ + 5) * (Real.exp (-(16 + 2 * P)) * (2 * Real.pi * gaussA (lam / 2))))
      ≤ (1 / (2 * Real.pi)) * ∫ r : ℝ, bumpR c lam r * psiR r :=
    mul_le_mul_of_nonneg_left hJ (by positivity)
  have hid : (1 / (2 * Real.pi)) * (Θ * (2 * Real.pi * gaussA lam)
      - (Θ + 5) * (Real.exp (-(16 + 2 * P)) * (2 * Real.pi * gaussA (lam / 2))))
      = Θ * gaussA lam - (Θ + 5) * Real.exp (-(16 + 2 * P)) * gaussA (lam / 2) := by
    field_simp
  rw [hid] at hJ'
  -- the tail term: (Θ + 5) e^{-16 - 2P} A(lam/2) <= 3 A e^{-16} (Θ + 5) e^{-2P} <= 3 A e^{-16} * 6.5
  have hs2 : Real.sqrt 2 ≤ 1.5 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hhalf : gaussA (lam / 2) ≤ 3 * gaussA lam := by
    rw [gaussA_half hlam]
    nlinarith
  have he16 : Real.exp (-16) ≤ 1 / 8000000 := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    have h1 : Real.exp 16 = Real.exp 1 ^ 16 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h1]
    have := Real.exp_one_gt_d9
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283) this.le 16]
  have hlogpi : Real.log Real.pi ≤ 1.3863 := by
    have h1 : Real.log Real.pi ≤ Real.log 4 :=
      Real.log_le_log Real.pi_pos (by linarith [Real.pi_lt_d2])
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    linarith [Real.log_two_lt_d9]
  -- (Θ + 5) e^{-2P} <= 6.7 :  (P + 6.7) e^{-2P} <= 6.7  since e^{2P} >= 1 + 2P >= 1 + P/6.7
  have hcap : (Θ + 5) * Real.exp (-(2 * P)) ≤ 6.7 := by
    have h1 : Real.exp (-(2 * P)) = 1 / Real.exp (2 * P) := by rw [Real.exp_neg, one_div]
    have h2 : 1 + 2 * P ≤ Real.exp (2 * P) := by linarith [Real.add_one_le_exp (2 * P)]
    rw [h1, ← mul_div_assoc, div_le_iff₀ (Real.exp_pos _)]
    nlinarith
  have htailA : (Θ + 5) * Real.exp (-(16 + 2 * P)) * gaussA (lam / 2)
      ≤ 6.7 * (1 / 8000000) * (3 * gaussA lam) := by
    have e : Real.exp (-(16 + 2 * P)) = Real.exp (-16) * Real.exp (-(2 * P)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e]
    calc (Θ + 5) * (Real.exp (-16) * Real.exp (-(2 * P))) * gaussA (lam / 2)
        = ((Θ + 5) * Real.exp (-(2 * P))) * Real.exp (-16) * gaussA (lam / 2) := by ring
      _ ≤ 6.7 * (1 / 8000000) * (3 * gaussA lam) := by
          apply mul_le_mul _ hhalf (gaussA_pos (by positivity)).le (by positivity)
          exact mul_le_mul hcap he16 (Real.exp_pos _).le (by norm_num)
  have hprime' : (primeSide (autocorr (RvMBridge8.gaussPhi c lam))).re ≤ gaussA lam * P :=
    hpre.trans hprime
  -- assemble: A (Θ - log π - P - 0.13) - tail >= A (0.31 - 0.13 - 2.6e-6) > 0
  have hΘA : Θ * gaussA lam = gaussA lam * Real.log Real.pi + gaussA lam * P + 0.31 * gaussA lam := by
    rw [hΘ]; ring
  clear_value P L Θ
  linarith only [h0, h1, hpoles, hJ', htailA, hprime', hΘA, hA]

/-- THE SHARP ENVELOPE THEOREM (zero-side form), UNCONDITIONAL: for every width lam > 0 and every
centre with |c| >= envelopeCsharp lam, F(c, lam) >= 0. -/
theorem gaussian_positivity_envelope_sharp (c lam : ℝ) (hlam : 0 < lam)
    (hc : envelopeCsharp lam ≤ |c|) :
    0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re := by
  rw [RvMBridge10.zeroSide_gaussTest_eq c lam hlam]
  exact re_weilForm_gauss_nonneg_sharp c lam hlam hc

/-- The band's upper edge: for every lam > 0, every centre beyond envelopeCsharp lam is
Gaussian-positive. -/
theorem band_upper_edge :
    ∀ lam : ℝ, 0 < lam → ∀ c : ℝ, envelopeCsharp lam ≤ |c| →
      0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re :=
  fun lam hlam c hc => gaussian_positivity_envelope_sharp c lam hlam hc

/-- The crude closed-form corollary (the only closed-form bound on primeAbs that closes):
envelopeCsharp lam <= 2 pi e^{16 e^{16 lam} + 1/2} + sqrt((16 + 32 e^{16 lam})/lam) + 3/sqrt lam + 1. -/
theorem envelopeCsharp_le_crude {lam : ℝ} (hlam : 0 < lam) :
    envelopeCsharp lam
      ≤ 2 * Real.pi * Real.exp (16 * Real.exp (16 * lam) + 1 / 2)
        + Real.sqrt ((16 + 2 * (16 * Real.exp (16 * lam))) / lam) + 3 / Real.sqrt lam + 1 := by
  unfold envelopeCsharp tailRadius
  have h := primeAbs_le_crude hlam
  have h1 : Real.exp (primeAbs lam + 1 / 2) ≤ Real.exp (16 * Real.exp (16 * lam) + 1 / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.sqrt ((16 + 2 * primeAbs lam) / lam)
      ≤ Real.sqrt ((16 + 2 * (16 * Real.exp (16 * lam))) / lam) :=
    Real.sqrt_le_sqrt (by apply div_le_div_of_nonneg_right _ hlam.le; linarith)
  have := Real.pi_pos
  nlinarith

/-- THE HEIGHT FORM: Gaussian positivity at width lam holds for every |c| >= T as soon as
envelopeCsharp lam <= T, i.e. (in words) as soon as the proved l1 prime constant satisfies
2 pi e^{primeAbs lam + 1/2} + tailRadius lam + 3/sqrt lam + 1 <= T, essentially
primeAbs lam + 1/2 <= log(T / 2 pi).  With the ladder height T = 640000 this is every
lam <= 0.597; with T = 3e12 (Platt-Trudgian) every lam <= 1.06 (memo table). -/
theorem gaussian_positivity_above_height {lam T : ℝ} (hlam : 0 < lam) (hT : envelopeCsharp lam ≤ T) :
    ∀ c : ℝ, T ≤ |c| → 0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re :=
  fun c hc => gaussian_positivity_envelope_sharp c lam hlam (hT.trans hc)

/-- The log form: if primeAbs lam + 1/2 + log 2 <= log (T / (2 pi)) and the additive terms are
dominated by the main term, then positivity holds for every |c| >= T. -/
theorem gaussian_positivity_above_height_log {lam T : ℝ} (hlam : 0 < lam) (hT : 0 < T)
    (hlog : primeAbs lam + 1 / 2 + Real.log 2 ≤ Real.log (T / (2 * Real.pi)))
    (hadd : tailRadius lam + 3 / Real.sqrt lam + 1 ≤ 2 * Real.pi * Real.exp (primeAbs lam + 1 / 2)) :
    ∀ c : ℝ, T ≤ |c| → 0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re := by
  apply gaussian_positivity_above_height hlam
  unfold envelopeCsharp
  have hmain : 2 * Real.pi * Real.exp (primeAbs lam + 1 / 2) * 2 ≤ T := by
    have e : Real.log (2 * Real.pi * Real.exp (primeAbs lam + 1 / 2) * 2)
        = Real.log (2 * Real.pi) + (primeAbs lam + 1 / 2 + Real.log 2) := by
      rw [Real.log_mul (by positivity) (by norm_num),
        Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
      ring
    have hd : Real.log (T / (2 * Real.pi)) = Real.log T - Real.log (2 * Real.pi) :=
      Real.log_div hT.ne' (by positivity)
    have hle : Real.log (2 * Real.pi * Real.exp (primeAbs lam + 1 / 2) * 2) ≤ Real.log T := by
      rw [e]
      linarith
    exact (Real.log_le_log_iff (by positivity) hT).mp hle
  linarith

end RvMBridge16
