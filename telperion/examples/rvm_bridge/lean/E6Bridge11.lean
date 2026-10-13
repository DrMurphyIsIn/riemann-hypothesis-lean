/-
  E6Bridge11 -- seam B of the Wall (2026-09-21): the UNCONDITIONAL small-width region.

  The two-parameter Wall functional is the zero side of the explicit formula for the
  Gaussian-derivative test,

      F(c, lam) := Re zeroSide (gaussTest c lam)
                 = Re Sum_rho m(rho) (gamma_rho - c)^2 exp (-2 lam (gamma_rho - c)^2),

  and (a parallel file proves) RH <-> F(c, lam) >= 0 for every centre c and width lam > 0.
  This file proves, UNCONDITIONALLY and with explicit constants, that the primes-side
  expression of F is nonnegative for every c once lam is small enough:

      0 <= Re [archSide (autocorr (gaussPhi c lam)) - primeSide (autocorr (gaussPhi c lam))]
                                                       for all c, all 0 < lam <= lam0 := 10^-7,

  and hence, through the Gaussian explicit formula (stated here as the `def : Prop`
  GaussianExplicitFormula and DISCHARGED in section K from E6Bridge10.zeroSide_gaussTest_eq),
  that F(c, lam) >= 0 on the strip 0 < lam <= lam0 -- for EVERY centre c, so lam0 is ABSOLUTE
  (gaussian_positivity_small_lam, unconditional).  Section L adds the ENVELOPE form: for every
  width lam > 0 an explicit c1(lam) = envelopeC lam with F(c, lam) >= 0 for all |c| >= c1(lam)
  (gaussian_positivity_envelope, unconditional): at large height the bump-average of
  Re psi ~ log(|c|/2) dominates the lam-only prime bound 16 A e^{16 lam}.

  Why this is Yoshida-type (unconditional) positivity: with f := phi * phi~ the autocorrelation
  of phi(u) = K u e^{-u^2/(4 lam)} e^{-icu}, an explicit computation (section B) gives

      f(u) = A (1 - u^2/(4 lam)) e^{-u^2/(8 lam)} e^{-icu},    A = 1 / (8 sqrt(2 pi) lam^{3/2}),

  so the prime side Sum_n Lambda(n) n^{-1/2} (f(log n) + f(-log n)) is EXPONENTIALLY small in
  1/lam (the n = 2 term already carries e^{-(log 2)^2/(8 lam)}), while the archimedean side is
      A [ <Re psi(1/4 + i r/2)>_bump - log pi ] + pole terms,
  where the bump |h(r)|^2 = (r - c)^2 e^{-2 lam (r - c)^2} has total mass 2 pi A and, for small
  lam, puts all but O(sqrt lam) of its mass at |r| >= 41, where Re psi(1/4 + i r/2) >= 2 > log pi
  (Stirling, Zeta23.StirlingVert.re_digamma_stirling'); the pole terms h(i/2) + h(-i/2) are
  O(A sqrt lam) uniformly in c (they DECAY in c: |G(i/2)| = (c^2 + 1/4) e^{lam/2 - 2 lam c^2}).
  The c-uniformity is exactly the point: the bump is centred at c, and Re psi(1/4 + i r/2) is
  bounded below by -5 everywhere and by 2 beyond |r| >= 41, so the c-dependence of the
  archimedean side only ever HELPS (Re psi ~ log(|c|/2) near r ~ c).  Nothing here involves
  the zeros; the theorem is a statement about the E8 functional on one explicit test.

  CONSTANTS ARE CRUDE: lam0 = 10^-7 and c1(lam) = 2 e^{9 + 2 X(lam)} + 2/sqrt lam,
  X(lam) = 4 e^{2 lam} sqrt(32 pi lam) + 16 e^{16 lam}, are what the elementary inequalities
  below give; the numerics (telperion/examples/rvm_bridge/seam_b_small_lam.py, memo
  telperion/docs/WALL_SEAM_B_SMALL_LAM_2026-09-21.md, and the landscape memo
  WALL_LANDSCAPE_2026-09-21.md) put the true c-uniform threshold near lam ~ 0.01 (the
  archimedean side itself turns negative at c <= 14 for lam >= 0.02) and the true envelope
  c1(lam) far below ours.  Neither region touches the Wall proper (lam of order one, c -> infinity
  at bounded lam): there the pair term of a hypothetical off-line zero is not dominated by
  anything unconditional.

  Proves nothing about RH.  conjecture1_proved = False.
-/
import E6Bridge8
import E6Bridge10
import RvMBridgeGauss
import Zeta23.GammaFacts.StirlingVert
import Zeta23.GammaFacts.Mu
import Zeta23.Analytic.Stirling
import Zeta23.WeilEF.VerticalLine

open Zeta23 Complex MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace RvMBridge11
open WeilExplicit

/-! ## A. The named hypothesis and the constants. -/

/-- The explicit formula for the Gaussian-derivative test (NOT compactly supported, so outside
the E8 class; a parallel file proves it by the same Tannery/DCT transfer as E6Bridge8).  Restated
verbatim, consumed only as a hypothesis of gaussian_positivity_small_lam_of. -/
def GaussianExplicitFormula : Prop := ∀ (c lam : ℝ), 0 < lam →
  (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re
    = (WeilExplicit.archSide (WeilExplicit.autocorr (RvMBridge8.gaussPhi c lam))
        - WeilExplicit.primeSide (WeilExplicit.autocorr (RvMBridge8.gaussPhi c lam))).re

/-- A = 1 / (8 sqrt(2 pi) lam^{3/2}) = f(0) = ‖phi‖_2^2, the scale of everything. -/
def gaussA (lam : ℝ) : ℝ := 1 / (8 * Real.sqrt (2 * Real.pi) * (lam * Real.sqrt lam))

lemma gaussA_pos {lam : ℝ} (hlam : 0 < lam) : 0 < gaussA lam := by
  unfold gaussA
  have := Real.sqrt_pos.mpr hlam
  have := Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 2 * Real.pi)
  positivity

/-- The closed form of the autocorrelation phi * phi~ (proved in section B). -/
def autocorrGauss (c lam : ℝ) (u : ℝ) : ℂ :=
  (gaussA lam : ℂ) * ((1 - u ^ 2 / (4 * lam) : ℝ) : ℂ) * ((Real.exp (-(u ^ 2) / (8 * lam)) : ℝ) : ℂ)
    * cexp (-(I * c * u))

/-- The bump |h(r)|^2 = (r - c)^2 e^{-2 lam (r - c)^2} (real). -/
def bumpR (c lam : ℝ) (r : ℝ) : ℝ := (r - c) ^ 2 * Real.exp (-(2 * lam) * (r - c) ^ 2)

/-- The radius beyond which Re psi(1/4 + i r/2) >= 2. -/
def R₀ : ℝ := 41

/-- The absolute width threshold. -/
def lam₀ : ℝ := 1 / 10000000

/-! ## B. Gaussian integrals: the second moment and the closed form of the autocorrelation. -/

/-- ∫ x^2 e^{-a x^2} dx = sqrt(pi/a) / (2a), by integrating d/dx [ -x e^{-a x^2} / (2a) ]. -/
theorem integral_sq_mul_exp_neg_mul_sq {a : ℝ} (ha : 0 < a) :
    ∫ x : ℝ, x ^ 2 * Real.exp (-a * x ^ 2) = Real.sqrt (Real.pi / a) / (2 * a) := by
  -- F(x) = -x e^{-a x^2}/(2a), F'(x) = x^2 e^{-a x^2} - e^{-a x^2}/(2a)
  have hF : ∀ x : ℝ, HasDerivAt (fun x : ℝ => -x * Real.exp (-a * x ^ 2) / (2 * a))
      (x ^ 2 * Real.exp (-a * x ^ 2) - Real.exp (-a * x ^ 2) / (2 * a)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => Real.exp (-a * x ^ 2))
        (Real.exp (-a * x ^ 2) * (-a * (2 * x))) x := by
      have := ((hasDerivAt_pow 2 x).const_mul (-a)).exp
      convert this using 1
      ring
    have hneg : HasDerivAt (fun y : ℝ => -y) (-1) x := (hasDerivAt_id x).neg
    exact ((hneg.mul h1).div_const (2 * a)).congr_deriv (by field_simp; ring)
  have hi1 : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-a * x ^ 2)) := by
    have := RvMBridgeGauss.integrable_abs_pow_mul_exp_quadratic_abs ha 0 2
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [sq_abs]
  have hi0 : Integrable (fun x : ℝ => Real.exp (-a * x ^ 2)) := integrable_exp_neg_mul_sq ha
  have hiF : Integrable (fun x : ℝ => -x * Real.exp (-a * x ^ 2) / (2 * a)) := by
    have := (RvMBridgeGauss.integrable_abs_pow_mul_exp_quadratic_abs ha 0 1).div_const (2 * a)
    refine this.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs, zero_mul, add_zero, pow_one]
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * a), abs_mul, abs_neg,
      abs_of_pos (Real.exp_pos _)]
  have hiF' : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-a * x ^ 2) - Real.exp (-a * x ^ 2) / (2 * a)) :=
    hi1.sub (hi0.div_const _)
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hF hiF' hiF
  rw [integral_sub hi1 (hi0.div_const _), integral_div, integral_gaussian] at hzero
  linarith

/-- The complex form: ∫ x^2 cexp(-a x^2) = sqrt(pi/a)/(2a). -/
theorem integral_sq_mul_cexp_neg_mul_sq {a : ℝ} (ha : 0 < a) :
    ∫ x : ℝ, (x : ℂ) ^ 2 * cexp (-(a : ℂ) * (x : ℂ) ^ 2)
      = ((Real.sqrt (Real.pi / a) / (2 * a) : ℝ) : ℂ) := by
  rw [← integral_sq_mul_exp_neg_mul_sq ha, ← integral_complex_ofReal]
  congr 1
  funext x
  push_cast
  ring_nf

/-! ## C. Digamma on the line Re = 1/4: the two lower bounds. -/

/-- Re psi(1/4 + i t) >= -5 for every real t (from the real series on vertical lines). -/
theorem re_digamma_quarter_ge (t : ℝ) :
    -5 ≤ (Complex.digamma (((1 / 4 : ℝ) : ℂ) + I * (t : ℂ))).re := by
  rw [Zeta23.MuFields.re_digamma_vertical (by norm_num) (by norm_num) t]
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hfrac : (1 / 4 : ℝ) / ((1 / 4) ^ 2 + t ^ 2) ≤ 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg t]
  have hsum : 0 ≤ ∑' n : ℕ, (1 / ((n : ℝ) + 1)
      - ((n : ℝ) + 1 + 1 / 4) / (((n : ℝ) + 1 + 1 / 4) ^ 2 + t ^ 2)) := by
    apply tsum_nonneg
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 + 1 / 4 := by positivity
    have h1 : ((n : ℝ) + 1 + 1 / 4) / (((n : ℝ) + 1 + 1 / 4) ^ 2 + t ^ 2) ≤ 1 / ((n : ℝ) + 1 + 1 / 4) := by
      rw [div_le_div_iff₀ (by positivity) hn]
      nlinarith [sq_nonneg t]
    have h2 : 1 / ((n : ℝ) + 1 + 1 / 4) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  linarith

/-- Re psi(1/4 + i r/2) >= 2 for |r| >= 41 (Stirling on the vertical line). -/
theorem re_digamma_quarter_ge_two {r : ℝ} (hr : R₀ ≤ |r|) :
    2 ≤ (Complex.digamma (((1 / 4 : ℝ) : ℂ) + I * ((r / 2 : ℝ) : ℂ))).re := by
  unfold R₀ at hr
  have ht : 1 / 2 ≤ |r / 2| := by rw [abs_div, abs_two]; linarith
  have h := Zeta23.StirlingVert.re_digamma_stirling' (a := 1 / 4) (by norm_num) (by norm_num) ht
  have hlog : 3 ≤ Real.log |r / 2| := by
    rw [abs_div, abs_two]
    have he : Real.exp 3 ≤ |r| / 2 := by
      have h1 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      have h2 := Real.exp_one_lt_d9
      have h3 : Real.exp 1 ^ 3 ≤ 2.7182818286 ^ 3 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le h2.le 3
      rw [h1]
      nlinarith
    calc (3 : ℝ) = Real.log (Real.exp 3) := (Real.log_exp 3).symm
      _ ≤ Real.log (|r| / 2) := Real.log_le_log (Real.exp_pos 3) he
  have hr2 : 5 / (r / 2) ^ 2 ≤ 1 := by
    have : (41 : ℝ) ^ 2 ≤ r ^ 2 := by
      rw [← sq_abs r]
      exact pow_le_pow_left₀ (by norm_num) hr 2
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  have := (abs_le.mp h).1
  linarith

/-! ## D. The closed form of the autocorrelation phi * phi~. -/

/-- The integrand of the autocorrelation: phi(v) conj phi(v - u). -/
lemma gaussPhi_mul_conj (c lam : ℝ) (u v : ℝ) :
    RvMBridge8.gaussPhi c lam v * conj (RvMBridge8.gaussPhi c lam (v - u))
      = (RvMBridge8.gaussK lam * conj (RvMBridge8.gaussK lam)) * ((v : ℂ) * ((v : ℂ) - u))
        * cexp (-(RvMBridge8.gaussB lam : ℂ) * ((v : ℂ) ^ 2 + ((v : ℂ) - u) ^ 2) - I * c * u) := by
  unfold RvMBridge8.gaussPhi
  simp only [map_mul, map_sub, map_neg, map_pow, Complex.conj_ofReal, Complex.conj_I,
    ← Complex.exp_conj]
  push_cast
  have : cexp (-(RvMBridge8.gaussB lam : ℂ) * (v : ℂ) ^ 2 - I * c * v)
      * cexp (-(RvMBridge8.gaussB lam : ℂ) * ((v : ℂ) - u) ^ 2 - -I * c * ((v : ℂ) - u))
      = cexp (-(RvMBridge8.gaussB lam : ℂ) * ((v : ℂ) ^ 2 + ((v : ℂ) - u) ^ 2) - I * c * u) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [← this]
  ring

/-- After the shift v = w + u/2 the autocorrelation is a constant times a centred Gaussian
moment integral. -/
lemma autocorr_gaussPhi_eq_integral (c lam : ℝ) (u : ℝ) :
    autocorr (RvMBridge8.gaussPhi c lam) u
      = (RvMBridge8.gaussK lam * conj (RvMBridge8.gaussK lam))
        * cexp (-(RvMBridge8.gaussB lam : ℂ) * (u : ℂ) ^ 2 / 2 - I * c * u)
        * ∫ w : ℝ, ((w : ℂ) ^ 2 - (u : ℂ) ^ 2 / 4)
            * cexp (-(2 * (RvMBridge8.gaussB lam : ℂ)) * (w : ℂ) ^ 2) := by
  unfold autocorr
  simp_rw [gaussPhi_mul_conj]
  rw [← integral_add_right_eq_self (fun v : ℝ => (RvMBridge8.gaussK lam * conj (RvMBridge8.gaussK lam))
      * ((v : ℂ) * ((v : ℂ) - u))
      * cexp (-(RvMBridge8.gaussB lam : ℂ) * ((v : ℂ) ^ 2 + ((v : ℂ) - u) ^ 2) - I * c * u)) (u / 2),
    ← integral_const_mul]
  congr 1
  funext w
  push_cast
  have : cexp (-(RvMBridge8.gaussB lam : ℂ) * (((w : ℂ) + u / 2) ^ 2 + ((w : ℂ) + u / 2 - u) ^ 2) - I * c * u)
      = cexp (-(RvMBridge8.gaussB lam : ℂ) * (u : ℂ) ^ 2 / 2 - I * c * u)
        * cexp (-(2 * (RvMBridge8.gaussB lam : ℂ)) * (w : ℂ) ^ 2) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [this]
  ring

/-- ∫ (w^2 - u^2/4) e^{-2b w^2} dw = sqrt(pi/(2b)) (1/(4b) - u^2/4). -/
lemma integral_sq_sub_mul_cexp {b : ℝ} (hb : 0 < b) (u : ℝ) :
    ∫ w : ℝ, ((w : ℂ) ^ 2 - (u : ℂ) ^ 2 / 4) * cexp (-(2 * (b : ℂ)) * (w : ℂ) ^ 2)
      = ((Real.sqrt (Real.pi / (2 * b)) * (1 / (4 * b) - u ^ 2 / 4) : ℝ) : ℂ) := by
  have h2b : 0 < 2 * b := by positivity
  have hcast : ∀ w : ℝ, cexp (-(2 * (b : ℂ)) * (w : ℂ) ^ 2)
      = ((Real.exp (-(2 * b) * w ^ 2) : ℝ) : ℂ) := by
    intro w
    rw [Complex.ofReal_exp]
    push_cast
    ring_nf
  have hi1 : Integrable (fun w : ℝ => (w : ℂ) ^ 2 * cexp (-(2 * (b : ℂ)) * (w : ℂ) ^ 2)) := by
    have := (RvMBridgeGauss.integrable_abs_pow_mul_exp_quadratic_abs h2b 0 2).ofReal (𝕜 := ℂ)
    refine this.congr (Filter.Eventually.of_forall fun w => ?_)
    show (((|w| ^ 2 * Real.exp (-(2 * b) * w ^ 2 + 0 * |w|) : ℝ)) : ℂ)
      = (w : ℂ) ^ 2 * cexp (-(2 * (b : ℂ)) * (w : ℂ) ^ 2)
    rw [hcast]
    simp only [zero_mul, add_zero, sq_abs]
    push_cast
    ring
  have hi2 : Integrable (fun w : ℝ => ((u : ℂ) ^ 2 / 4) * cexp (-(2 * (b : ℂ)) * (w : ℂ) ^ 2)) := by
    have := ((integrable_exp_neg_mul_sq h2b).ofReal (𝕜 := ℂ)).const_mul ((u : ℂ) ^ 2 / 4)
    refine this.congr (Filter.Eventually.of_forall fun w => ?_)
    show (u : ℂ) ^ 2 / 4 * ((Real.exp (-(2 * b) * w ^ 2) : ℝ) : ℂ)
      = (u : ℂ) ^ 2 / 4 * cexp (-(2 * (b : ℂ)) * (w : ℂ) ^ 2)
    rw [hcast]
  have hfun : (fun w : ℝ => ((w : ℂ) ^ 2 - (u : ℂ) ^ 2 / 4) * cexp (-(2 * (b : ℂ)) * (w : ℂ) ^ 2))
      = fun w : ℝ => (w : ℂ) ^ 2 * cexp (-(2 * (b : ℂ)) * (w : ℂ) ^ 2)
        - ((u : ℂ) ^ 2 / 4) * cexp (-(2 * (b : ℂ)) * (w : ℂ) ^ 2) := by
    funext w
    ring
  rw [hfun, integral_sub hi1 hi2, integral_const_mul]
  have hsq : ∫ w : ℝ, (w : ℂ) ^ 2 * cexp (-(2 * (b : ℂ)) * (w : ℂ) ^ 2)
      = ((Real.sqrt (Real.pi / (2 * b)) / (2 * (2 * b)) : ℝ) : ℂ) := by
    rw [← integral_sq_mul_cexp_neg_mul_sq h2b]
    congr 1
    funext w
    push_cast
    ring_nf
  have hg : ∫ w : ℝ, cexp (-(2 * (b : ℂ)) * (w : ℂ) ^ 2) = ((Real.sqrt (Real.pi / (2 * b)) : ℝ) : ℂ) := by
    simp_rw [hcast]
    rw [integral_complex_ofReal, integral_gaussian]
  rw [hsq, hg]
  push_cast
  field_simp
  ring

/-- |K|^2 = K conj K = 1 / (16 pi lam^3). -/
lemma gaussK_mul_conj {lam : ℝ} (hlam : 0 < lam) :
    RvMBridge8.gaussK lam * conj (RvMBridge8.gaussK lam)
      = ((1 / (16 * Real.pi * lam ^ 3) : ℝ) : ℂ) := by
  unfold RvMBridge8.gaussK
  have hS : ((Real.pi : ℂ) / (RvMBridge8.gaussB lam : ℂ)) ^ (1 / 2 : ℂ)
      = ((Real.sqrt (4 * Real.pi * lam) : ℝ) : ℂ) := by
    rw [show (Real.pi : ℂ) / (RvMBridge8.gaussB lam : ℂ) = ((4 * Real.pi * lam : ℝ) : ℂ) by
          unfold RvMBridge8.gaussB
          push_cast
          field_simp,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow (by positivity),
      Real.sqrt_eq_rpow]
  rw [hS]
  set s : ℝ := Real.sqrt (4 * Real.pi * lam) with hs_def
  have hs : s * s = 4 * Real.pi * lam := Real.mul_self_sqrt (by positivity)
  simp only [map_inv₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  rw [← mul_inv]
  have : 2 * (lam : ℂ) * I * (s : ℂ) * (2 * (lam : ℂ) * -I * (s : ℂ))
      = ((16 * Real.pi * lam ^ 3 : ℝ) : ℂ) := by
    have hI : I * -I = 1 := by rw [mul_neg, I_mul_I]; ring
    calc 2 * (lam : ℂ) * I * (s : ℂ) * (2 * (lam : ℂ) * -I * (s : ℂ))
        = 4 * (lam : ℂ) ^ 2 * ((s : ℂ) * (s : ℂ)) * (I * -I) := by ring
      _ = 4 * (lam : ℂ) ^ 2 * ((4 * Real.pi * lam : ℝ) : ℂ) * 1 := by
          rw [hI, ← Complex.ofReal_mul, hs]
      _ = ((16 * Real.pi * lam ^ 3 : ℝ) : ℂ) := by push_cast; ring
  rw [this, ← Complex.ofReal_inv]
  push_cast
  ring

/-- THE CLOSED FORM: phi * phi~ (u) = A (1 - u^2/(4 lam)) e^{-u^2/(8 lam)} e^{-icu}. -/
theorem autocorr_gaussPhi {c lam : ℝ} (hlam : 0 < lam) (u : ℝ) :
    autocorr (RvMBridge8.gaussPhi c lam) u = autocorrGauss c lam u := by
  rw [autocorr_gaussPhi_eq_integral, integral_sq_sub_mul_cexp (RvMBridge8.gaussB_pos hlam),
    gaussK_mul_conj hlam]
  unfold autocorrGauss RvMBridge8.gaussB
  have hexp : cexp (-(((1 / (4 * lam) : ℝ) : ℂ)) * (u : ℂ) ^ 2 / 2 - I * c * u)
      = ((Real.exp (-(u ^ 2) / (8 * lam)) : ℝ) : ℂ) * cexp (-(I * c * u)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  rw [hexp]
  have hconst : (1 / (16 * Real.pi * lam ^ 3))
      * (Real.sqrt (Real.pi / (2 * (1 / (4 * lam)))) * (1 / (4 * (1 / (4 * lam))) - u ^ 2 / 4))
      = gaussA lam * (1 - u ^ 2 / (4 * lam)) := by
    unfold gaussA
    rw [show Real.pi / (2 * (1 / (4 * lam))) = 2 * Real.pi * lam by field_simp; ring,
      Real.sqrt_mul (by positivity)]
    set sp := Real.sqrt (2 * Real.pi) with hsp_def
    set sl := Real.sqrt lam with hsl_def
    have hsp : sp ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
    have hsl : sl ^ 2 = lam := Real.sq_sqrt hlam.le
    have hsp0 : 0 < sp := Real.sqrt_pos.mpr (by positivity)
    have hsl0 : 0 < sl := Real.sqrt_pos.mpr hlam
    have hpi : Real.pi = sp ^ 2 / 2 := by rw [hsp]; ring
    have hlam' : lam = sl ^ 2 := hsl.symm
    rw [hpi, hlam']
    field_simp
    ring
  calc ((1 / (16 * Real.pi * lam ^ 3) : ℝ) : ℂ)
        * (((Real.exp (-(u ^ 2) / (8 * lam)) : ℝ) : ℂ) * cexp (-(I * c * u)))
        * ((Real.sqrt (Real.pi / (2 * (1 / (4 * lam)))) * (1 / (4 * (1 / (4 * lam))) - u ^ 2 / 4) : ℝ) : ℂ)
      = (((1 / (16 * Real.pi * lam ^ 3))
          * (Real.sqrt (Real.pi / (2 * (1 / (4 * lam)))) * (1 / (4 * (1 / (4 * lam))) - u ^ 2 / 4)) : ℝ) : ℂ)
        * ((Real.exp (-(u ^ 2) / (8 * lam)) : ℝ) : ℂ) * cexp (-(I * c * u)) := by
        push_cast
        ring
    _ = _ := by
        rw [hconst]
        push_cast
        ring

/-! ## E. The Gaussian majorant of the autocorrelation, and its value at 0. -/

lemma autocorrGauss_zero (c lam : ℝ) : autocorrGauss c lam 0 = (gaussA lam : ℂ) := by
  unfold autocorrGauss
  simp

/-- |1 - 2s| e^{-s} <= 2 e^{-s/2} for s >= 0 (since 1 + 2s <= 2 + s + s^2/4 <= 2 e^{s/2}). -/
lemma abs_one_sub_two_mul_exp_le {s : ℝ} (hs : 0 ≤ s) :
    |1 - 2 * s| * Real.exp (-s) ≤ 2 * Real.exp (-(s / 2)) := by
  have h1 : |1 - 2 * s| ≤ 1 + 2 * s := by
    rw [abs_le]
    constructor <;> linarith
  have h2 : 1 + 2 * s ≤ 2 * Real.exp (s / 2) := by
    have := Real.quadratic_le_exp_of_nonneg (x := s / 2) (by positivity)
    nlinarith [sq_nonneg (s / 2 - 1)]
  have h3 : Real.exp (-s) = Real.exp (-(s / 2)) * Real.exp (-(s / 2)) := by
    rw [← Real.exp_add]
    ring_nf
  have h4 : Real.exp (s / 2) * Real.exp (-(s / 2)) = 1 := by
    rw [← Real.exp_add]
    simp
  calc |1 - 2 * s| * Real.exp (-s) ≤ (2 * Real.exp (s / 2)) * Real.exp (-s) :=
        mul_le_mul_of_nonneg_right (h1.trans h2) (Real.exp_pos _).le
    _ = 2 * Real.exp (-(s / 2)) := by
        rw [h3]
        linear_combination (2 * Real.exp (-(s / 2))) * h4

/-- The majorant: |f(u)| <= 2 A e^{-u^2/(16 lam)}. -/
theorem norm_autocorrGauss_le {c lam : ℝ} (hlam : 0 < lam) (u : ℝ) :
    ‖autocorrGauss c lam u‖ ≤ 2 * gaussA lam * Real.exp (-(u ^ 2) / (16 * lam)) := by
  unfold autocorrGauss
  have hA := gaussA_pos hlam
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
    Complex.norm_exp]
  simp only [Real.norm_eq_abs, abs_of_pos hA, abs_of_pos (Real.exp_pos _)]
  have hre : (-(I * c * u)).re = 0 := by simp
  rw [hre, Real.exp_zero, mul_one]
  set s := u ^ 2 / (8 * lam) with hs_def
  have hs0 : 0 ≤ s := by positivity
  have e1 : 1 - u ^ 2 / (4 * lam) = 1 - 2 * s := by rw [hs_def]; ring
  have e2 : -(u ^ 2) / (8 * lam) = -s := by rw [hs_def]; ring
  have e3 : -(u ^ 2) / (16 * lam) = -(s / 2) := by rw [hs_def]; ring
  rw [e1, e2, e3]
  have := abs_one_sub_two_mul_exp_le hs0
  calc gaussA lam * |1 - 2 * s| * Real.exp (-s) = gaussA lam * (|1 - 2 * s| * Real.exp (-s)) := by ring
    _ ≤ gaussA lam * (2 * Real.exp (-(s / 2))) := mul_le_mul_of_nonneg_left this hA.le
    _ = 2 * gaussA lam * Real.exp (-(s / 2)) := by ring

/-- The autocorrelation as a function. -/
theorem autocorr_gaussPhi_funext {c lam : ℝ} (hlam : 0 < lam) :
    autocorr (RvMBridge8.gaussPhi c lam) = autocorrGauss c lam :=
  funext fun u => autocorr_gaussPhi hlam u

/-! ## F. The prime side is exponentially small in 1/lam. -/

/-- Each prime-side term is at most 8 A 2^{-(sigma - 2)} / n^2, sigma := log 2 / (16 lam) >= 2. -/
lemma prime_term_bound {c lam : ℝ} (hlam : 0 < lam) (hσ : 2 ≤ Real.log 2 / (16 * lam)) (n : ℕ) :
    ‖((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
        * (autocorrGauss c lam (Real.log n) + autocorrGauss c lam (-Real.log n))‖
      ≤ 8 * gaussA lam * Real.exp (-(Real.log 2 / (16 * lam) - 2) * Real.log 2)
          * (1 / (n : ℝ) ^ 2) := by
  have hA := gaussA_pos hlam
  rcases lt_or_ge n 2 with hn | hn
  · have h0 : ArithmeticFunction.vonMangoldt n = 0 := by
      interval_cases n
      · simp
      · exact ArithmeticFunction.vonMangoldt_apply_one
    rw [h0]
    simp only [zero_div, Complex.ofReal_zero, zero_mul, norm_zero]
    positivity
  · have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn'
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
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
    have hg : ‖autocorrGauss c lam (Real.log n) + autocorrGauss c lam (-Real.log n)‖
        ≤ 4 * gaussA lam * Real.exp (-(Real.log n) ^ 2 / (16 * lam)) := by
      have h1 := norm_autocorrGauss_le (c := c) hlam (Real.log n)
      have h2 := norm_autocorrGauss_le (c := c) hlam (-Real.log n)
      rw [neg_sq] at h2
      calc ‖autocorrGauss c lam (Real.log n) + autocorrGauss c lam (-Real.log n)‖
          ≤ ‖autocorrGauss c lam (Real.log n)‖ + ‖autocorrGauss c lam (-Real.log n)‖ := norm_add_le _ _
        _ ≤ 2 * gaussA lam * Real.exp (-(Real.log n) ^ 2 / (16 * lam))
            + 2 * gaussA lam * Real.exp (-(Real.log n) ^ 2 / (16 * lam)) := add_le_add h1 h2
        _ = 4 * gaussA lam * Real.exp (-(Real.log n) ^ 2 / (16 * lam)) := by ring
    have hexp : Real.exp (-(Real.log n) ^ 2 / (16 * lam))
        ≤ Real.exp (-(Real.log 2 / (16 * lam) - 2) * Real.log 2) * (1 / (n : ℝ) ^ 2) := by
      have e1 : (1 : ℝ) / (n : ℝ) ^ 2 = Real.exp (-(2 * Real.log n)) := by
        rw [Real.exp_neg, show 2 * Real.log n = Real.log ((n : ℝ) ^ 2) by
          rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity), one_div]
      rw [e1, ← Real.exp_add, Real.exp_le_exp]
      have hk : 0 < 1 / (16 * lam) := by positivity
      have hσ' : 2 ≤ Real.log 2 * (1 / (16 * lam)) := by rwa [← div_eq_mul_one_div]
      rw [div_eq_mul_one_div (-(Real.log n) ^ 2) (16 * lam), div_eq_mul_one_div (Real.log 2) (16 * lam)]
      have hfac : 0 ≤ (Real.log n - Real.log 2) * ((Real.log n + Real.log 2) * (1 / (16 * lam)) - 2) := by
        apply mul_nonneg (by linarith)
        nlinarith [mul_le_mul_of_nonneg_right hlogn hk.le]
      nlinarith [hfac]
    calc ‖((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
          * (autocorrGauss c lam (Real.log n) + autocorrGauss c lam (-Real.log n))‖
        = (ArithmeticFunction.vonMangoldt n / Real.sqrt n)
          * ‖autocorrGauss c lam (Real.log n) + autocorrGauss c lam (-Real.log n)‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hΛ0]
      _ ≤ 2 * (4 * gaussA lam * (Real.exp (-(Real.log 2 / (16 * lam) - 2) * Real.log 2)
            * (1 / (n : ℝ) ^ 2))) := by
          apply mul_le_mul hΛ _ (norm_nonneg _) (by norm_num)
          calc ‖autocorrGauss c lam (Real.log n) + autocorrGauss c lam (-Real.log n)‖
              ≤ 4 * gaussA lam * Real.exp (-(Real.log n) ^ 2 / (16 * lam)) := hg
            _ ≤ 4 * gaussA lam * (Real.exp (-(Real.log 2 / (16 * lam) - 2) * Real.log 2)
                * (1 / (n : ℝ) ^ 2)) := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = 8 * gaussA lam * Real.exp (-(Real.log 2 / (16 * lam) - 2) * Real.log 2)
          * (1 / (n : ℝ) ^ 2) := by ring

/-- THE PRIME-SIDE BOUND: ‖primeSide f‖ <= 64 A e^{-(log 2)^2 / (16 lam)} once log 2 / (16 lam) >= 2. -/
theorem norm_primeSide_le {c lam : ℝ} (hlam : 0 < lam) (hσ : 2 ≤ Real.log 2 / (16 * lam)) :
    ‖primeSide (autocorr (RvMBridge8.gaussPhi c lam))‖
      ≤ 64 * gaussA lam * Real.exp (-(Real.log 2) ^ 2 / (16 * lam)) := by
  rw [autocorr_gaussPhi_funext hlam]
  unfold primeSide
  set T : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
    * (autocorrGauss c lam (Real.log n) + autocorrGauss c lam (-Real.log n)) with hT
  set K : ℝ := 8 * gaussA lam * Real.exp (-(Real.log 2 / (16 * lam) - 2) * Real.log 2) with hK
  have hK0 : 0 < K := by have := gaussA_pos hlam; positivity
  have hM : Summable (fun n : ℕ => K * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left K
  have hterm : ∀ n : ℕ, ‖T n‖ ≤ K * (1 / (n : ℝ) ^ 2) := fun n => prime_term_bound hlam hσ n
  have hs : Summable (fun n : ℕ => ‖T n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hM
  have hA := gaussA_pos hlam
  have hpi2 : Real.pi ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hexp4 : Real.exp (-(Real.log 2 / (16 * lam) - 2) * Real.log 2)
      = 4 * Real.exp (-(Real.log 2) ^ 2 / (16 * lam)) := by
    rw [show -(Real.log 2 / (16 * lam) - 2) * Real.log 2
        = -(Real.log 2) ^ 2 / (16 * lam) + 2 * Real.log 2 by ring, Real.exp_add,
      show (2 : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by norm_num)]
    ring
  calc ‖∑' n : ℕ, T n‖ ≤ ∑' n : ℕ, ‖T n‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n : ℕ, K * (1 / (n : ℝ) ^ 2) := hs.tsum_le_tsum hterm hM
    _ = K * (Real.pi ^ 2 / 6) := by rw [tsum_mul_left, hasSum_zeta_two.tsum_eq]
    _ ≤ K * 2 := mul_le_mul_of_nonneg_left hpi2 hK0.le
    _ = 64 * gaussA lam * Real.exp (-(Real.log 2) ^ 2 / (16 * lam)) := by
        rw [hK, hexp4]
        ring

/-! ## G. The two pole terms h(i/2) + h(-i/2) = weilKernel f 0 + weilKernel f 1: an O(A sqrt lam)
bound, uniform in the centre c. -/

/-- ∫ |f(u)| e^{k u} du <= 2 A e^{2 lam} sqrt(32 pi lam) for |k| <= 1/2. -/
lemma norm_integral_autocorrGauss_mul_exp_le {c lam : ℝ} (hlam : 0 < lam) {k : ℝ}
    (hk : |k| ≤ 1 / 2) :
    ‖∫ u : ℝ, autocorrGauss c lam u * cexp ((k : ℂ) * (u : ℂ))‖
      ≤ 2 * gaussA lam * Real.exp (2 * lam) * Real.sqrt (32 * Real.pi * lam) := by
  have hA := gaussA_pos hlam
  have hb : 0 < 1 / (32 * lam) := by positivity
  have hmaj : Integrable (fun u : ℝ => 2 * gaussA lam * Real.exp (2 * lam)
      * Real.exp (-(1 / (32 * lam)) * u ^ 2)) :=
    (integrable_exp_neg_mul_sq hb).const_mul _
  have hle : ∀ u : ℝ, ‖autocorrGauss c lam u * cexp ((k : ℂ) * (u : ℂ))‖
      ≤ 2 * gaussA lam * Real.exp (2 * lam) * Real.exp (-(1 / (32 * lam)) * u ^ 2) := by
    intro u
    rw [norm_mul, Complex.norm_exp]
    have hre : ((k : ℂ) * (u : ℂ)).re = k * u := by simp
    rw [hre]
    have h1 := norm_autocorrGauss_le (c := c) hlam u
    have h2 : Real.exp (k * u) ≤ Real.exp (2 * lam) * Real.exp (-(1 / (32 * lam)) * u ^ 2)
        * Real.exp (u ^ 2 / (16 * lam)) := by
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      have hku : k * u ≤ |u| / 2 := by
        calc k * u ≤ |k * u| := le_abs_self _
          _ = |k| * |u| := abs_mul _ _
          _ ≤ (1 / 2) * |u| := mul_le_mul_of_nonneg_right hk (abs_nonneg _)
          _ = |u| / 2 := by ring
      have hsq : 0 ≤ (|u| - 8 * lam) ^ 2 := sq_nonneg _
      have hu2 : |u| ^ 2 = u ^ 2 := sq_abs u
      have : |u| / 2 ≤ 2 * lam + u ^ 2 / (32 * lam) := by
        have hid : 2 * lam + u ^ 2 / (32 * lam) - |u| / 2 = (|u| - 8 * lam) ^ 2 / (32 * lam) := by
          rw [← hu2]
          field_simp
          ring
        have : 0 ≤ (|u| - 8 * lam) ^ 2 / (32 * lam) := by positivity
        linarith
      have e : -(1 / (32 * lam)) * u ^ 2 + u ^ 2 / (16 * lam) = u ^ 2 / (32 * lam) := by
        field_simp
        ring
      linarith
    calc ‖autocorrGauss c lam u‖ * Real.exp (k * u)
        ≤ (2 * gaussA lam * Real.exp (-(u ^ 2) / (16 * lam)))
          * (Real.exp (2 * lam) * Real.exp (-(1 / (32 * lam)) * u ^ 2) * Real.exp (u ^ 2 / (16 * lam))) :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
      _ = 2 * gaussA lam * Real.exp (2 * lam) * Real.exp (-(1 / (32 * lam)) * u ^ 2)
          * (Real.exp (-(u ^ 2) / (16 * lam)) * Real.exp (u ^ 2 / (16 * lam))) := by ring
      _ = 2 * gaussA lam * Real.exp (2 * lam) * Real.exp (-(1 / (32 * lam)) * u ^ 2) := by
          rw [← Real.exp_add, show -(u ^ 2) / (16 * lam) + u ^ 2 / (16 * lam) = 0 by ring,
            Real.exp_zero, mul_one]
  calc ‖∫ u : ℝ, autocorrGauss c lam u * cexp ((k : ℂ) * (u : ℂ))‖
      ≤ ∫ u : ℝ, 2 * gaussA lam * Real.exp (2 * lam) * Real.exp (-(1 / (32 * lam)) * u ^ 2) :=
        norm_integral_le_of_norm_le hmaj (Filter.Eventually.of_forall hle)
    _ = 2 * gaussA lam * Real.exp (2 * lam) * Real.sqrt (Real.pi / (1 / (32 * lam))) := by
        rw [integral_const_mul, integral_gaussian]
    _ = 2 * gaussA lam * Real.exp (2 * lam) * Real.sqrt (32 * Real.pi * lam) := by
        congr 2
        field_simp

/-- weilKernel f 0 = ∫ f(u) e^{-u/2} du and weilKernel f 1 = ∫ f(u) e^{u/2} du. -/
lemma weilKernel_zero_eq (g : ℝ → ℂ) :
    weilKernel g 0 = ∫ u : ℝ, g u * cexp (((-1 / 2 : ℝ) : ℂ) * (u : ℂ)) := by
  unfold weilKernel
  congr 1
  funext u
  congr 2
  push_cast
  ring

lemma weilKernel_one_eq (g : ℝ → ℂ) :
    weilKernel g 1 = ∫ u : ℝ, g u * cexp (((1 / 2 : ℝ) : ℂ) * (u : ℂ)) := by
  unfold weilKernel
  congr 1
  funext u
  congr 2
  push_cast
  ring

/-- THE POLE-TERM BOUND. -/
theorem norm_weilKernel_zero_le {c lam : ℝ} (hlam : 0 < lam) :
    ‖weilKernel (autocorr (RvMBridge8.gaussPhi c lam)) 0‖
      ≤ 2 * gaussA lam * Real.exp (2 * lam) * Real.sqrt (32 * Real.pi * lam) := by
  rw [autocorr_gaussPhi_funext hlam, weilKernel_zero_eq]
  exact norm_integral_autocorrGauss_mul_exp_le hlam (by rw [abs_le]; constructor <;> norm_num)

theorem norm_weilKernel_one_le {c lam : ℝ} (hlam : 0 < lam) :
    ‖weilKernel (autocorr (RvMBridge8.gaussPhi c lam)) 1‖
      ≤ 2 * gaussA lam * Real.exp (2 * lam) * Real.sqrt (32 * Real.pi * lam) := by
  rw [autocorr_gaussPhi_funext hlam, weilKernel_one_eq]
  exact norm_integral_autocorrGauss_mul_exp_le hlam (by rw [abs_le]; constructor <;> norm_num)

/-! ## H. The transform of f on the line: weilKernel f (1/2 + i r) = |h(r)|^2 = bumpR c lam r. -/

/-! The second Gaussian moment ∫ x^2 e^{-a x^2} e^{i w x} dx at a real frequency w is the case
w = (r : ℂ) of the prelude's RvMBridgeGauss.integral_sq_mul_cexp_gaussian_fourier (the
real-frequency copy formerly here is gone). -/

/-- weilKernel g (1/2 + i r) = ∫ g(u) e^{i r u} du. -/
lemma weilKernel_line_eq (g : ℝ → ℂ) (r : ℝ) :
    weilKernel g (1 / 2 + (r : ℂ) * I) = ∫ u : ℝ, g u * cexp (I * (r : ℂ) * (u : ℂ)) := by
  unfold weilKernel
  congr 1
  funext u
  congr 2
  ring

/-- (pi / a)^{1/2} for a = 1/(8 lam) is the real sqrt(8 pi lam). -/
lemma cpow_pi_div_a {lam : ℝ} (hlam : 0 < lam) :
    ((Real.pi : ℂ) / ((1 / (8 * lam) : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
      = ((Real.sqrt (8 * Real.pi * lam) : ℝ) : ℂ) := by
  rw [show (Real.pi : ℂ) / ((1 / (8 * lam) : ℝ) : ℂ) = ((8 * Real.pi * lam : ℝ) : ℂ) by
        push_cast
        field_simp,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow (by positivity),
    Real.sqrt_eq_rpow]

/-- THE TRANSFORM ON THE LINE: weilKernel (phi * phi~) (1/2 + i r) = (r - c)^2 e^{-2 lam (r-c)^2}. -/
theorem weilKernel_autocorrGauss_line {c lam : ℝ} (hlam : 0 < lam) (r : ℝ) :
    weilKernel (autocorr (RvMBridge8.gaussPhi c lam)) (1 / 2 + (r : ℂ) * I) = (bumpR c lam r : ℂ) := by
  rw [autocorr_gaussPhi_funext hlam, weilKernel_line_eq]
  set a : ℝ := 1 / (8 * lam) with ha_def
  have ha : 0 < a := by positivity
  have haC : 0 < (a : ℂ).re := by simpa using ha
  set w : ℝ := r - c with hw_def
  have hfun : (fun u : ℝ => autocorrGauss c lam u * cexp (I * (r : ℂ) * (u : ℂ)))
      = fun u : ℝ => (gaussA lam : ℂ) * (cexp (I * (w : ℂ) * (u : ℂ)) * cexp (-(a : ℂ) * (u : ℂ) ^ 2))
        - ((gaussA lam : ℂ) * ((1 / (4 * lam) : ℝ) : ℂ))
          * ((u : ℂ) ^ 2 * cexp (-(a : ℂ) * (u : ℂ) ^ 2) * cexp (I * (w : ℂ) * (u : ℂ))) := by
    funext u
    unfold autocorrGauss
    have e1 : cexp (-(I * c * u)) * cexp (I * (r : ℂ) * (u : ℂ)) = cexp (I * (w : ℂ) * (u : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      rw [hw_def]
      push_cast
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
  have hmaj : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-a * x ^ 2)) := by
    have := RvMBridgeGauss.integrable_abs_pow_mul_exp_quadratic_abs ha 0 2
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [sq_abs]
  have hi_sq : Integrable (fun x : ℝ => (x : ℂ) ^ 2 * cexp (-(a : ℂ) * (x : ℂ) ^ 2)
      * cexp (I * (w : ℂ) * (x : ℂ))) := by
    refine hmaj.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_exp, Complex.norm_exp,
      Real.norm_eq_abs, sq_abs]
    have h1 : (-(a : ℂ) * (x : ℂ) ^ 2).re = -a * x ^ 2 := by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, pow_two]
    have h2 : (I * (w : ℂ) * (x : ℂ)).re = 0 := by simp
    rw [h1, h2, Real.exp_zero, mul_one]
  have hi_uv : Integrable (fun x : ℝ => cexp (I * (w : ℂ) * (x : ℂ)) * cexp (-(a : ℂ) * (x : ℂ) ^ 2)) := by
    have h := integrable_cexp_quadratic haC (I * w) 0
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [add_zero, Complex.exp_add]
    ring
  rw [hfun, integral_sub (hi_uv.const_mul _) (hi_sq.const_mul _), integral_const_mul,
    integral_const_mul, fourierIntegral_gaussian haC w,
    RvMBridgeGauss.integral_sq_mul_cexp_gaussian_fourier ha w, cpow_pi_div_a hlam]
  -- the exponential is real
  have hE : cexp (-(w : ℂ) ^ 2 / (4 * (a : ℂ))) = ((Real.exp (-(2 * lam) * w ^ 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    rw [ha_def]
    push_cast
    field_simp
    ring
  rw [hE]
  -- reduce to a real identity
  unfold bumpR
  rw [← hw_def]
  set S := Real.sqrt (8 * Real.pi * lam) with hS_def
  set E := Real.exp (-(2 * lam) * w ^ 2) with hE_def
  have hreal : gaussA lam * (S * E) - gaussA lam * (1 / (4 * lam))
      * ((1 / (2 * a)) * (S * E + (-(w * (w / (2 * a)))) * (S * E))) = w ^ 2 * E := by
    have hS : S = 2 * (Real.sqrt (2 * Real.pi) * Real.sqrt lam) := by
      rw [hS_def, show 8 * Real.pi * lam = 2 ^ 2 * ((2 * Real.pi) * lam) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num),
        Real.sqrt_mul (by positivity)]
    unfold gaussA
    rw [hS, ha_def]
    have hsp0 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    have hsl0 : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
    field_simp
    ring
  calc (gaussA lam : ℂ) * ((S : ℂ) * (E : ℂ))
        - (gaussA lam : ℂ) * ((1 / (4 * lam) : ℝ) : ℂ)
          * (1 / (2 * (a : ℂ)) * ((S : ℂ) * (E : ℂ) + I * (w : ℂ) * (I * (w : ℂ) / (2 * (a : ℂ)) * ((S : ℂ) * (E : ℂ)))))
      = ((gaussA lam * (S * E) - gaussA lam * (1 / (4 * lam))
          * ((1 / (2 * a)) * (S * E + (-(w * (w / (2 * a)))) * (S * E))) : ℝ) : ℂ) := by
        push_cast
        have hI : I * (w : ℂ) * (I * (w : ℂ) / (2 * (a : ℂ)) * ((S : ℂ) * (E : ℂ)))
            = -((w : ℂ) * ((w : ℂ) / (2 * (a : ℂ)))) * ((S : ℂ) * (E : ℂ)) := by
          have : I * (w : ℂ) * (I * (w : ℂ) / (2 * (a : ℂ)) * ((S : ℂ) * (E : ℂ)))
              = (I * I) * ((w : ℂ) * ((w : ℂ) / (2 * (a : ℂ)))) * ((S : ℂ) * (E : ℂ)) := by ring
          rw [this, I_mul_I]
          ring
        rw [hI]
    _ = ((w ^ 2 * E : ℝ) : ℂ) := by rw [hreal]
    _ = _ := by push_cast; ring

/-! ## I. The archimedean integral: integrability and the lower bound. -/

/-- psi(r) := Re digamma(1/4 + i r/2), the archimedean weight of archIntegrand. -/
def psiR (r : ℝ) : ℝ := (Complex.digamma (1 / 4 + ((r : ℂ) / 2) * I)).re

lemma psiR_eq (r : ℝ) :
    psiR r = (Complex.digamma (((1 / 4 : ℝ) : ℂ) + I * ((r / 2 : ℝ) : ℂ))).re := by
  unfold psiR
  rw [show (1 / 4 : ℂ) + ((r : ℂ) / 2) * I = ((1 / 4 : ℝ) : ℂ) + I * ((r / 2 : ℝ) : ℂ) by
    push_cast; ring]

lemma psiR_ge (r : ℝ) : -5 ≤ psiR r := by
  rw [psiR_eq]
  exact re_digamma_quarter_ge (r / 2)

lemma psiR_ge_two {r : ℝ} (hr : R₀ ≤ |r|) : 2 ≤ psiR r := by
  rw [psiR_eq]
  exact re_digamma_quarter_ge_two hr

lemma continuous_psiR : Continuous psiR := by
  unfold psiR
  apply Complex.continuous_re.comp
  refine continuous_iff_continuousAt.mpr fun r => ?_
  have hz : (1 / 4 + ((r : ℂ) / 2) * I) ∈ Complex.integerComplement := by
    rintro ⟨k, hk⟩
    have := congrArg Complex.re hk
    simp at this
    have h4 : (4 * k : ℤ) = 1 := by exact_mod_cast (by linarith : (4 * (k : ℝ)) = 1)
    omega
  have hf : Continuous (fun r : ℝ => (1 / 4 + ((r : ℂ) / 2) * I)) := by fun_prop
  exact ContinuousAt.comp (g := Complex.digamma) (f := fun r : ℝ => (1 / 4 + ((r : ℂ) / 2) * I))
    (Zeta23.Stirling.differentiableAt_digamma hz).continuousAt hf.continuousAt

lemma bumpR_nonneg (c lam r : ℝ) : 0 ≤ bumpR c lam r := by
  unfold bumpR
  positivity

lemma continuous_bumpR (c lam : ℝ) : Continuous (bumpR c lam) := by
  unfold bumpR
  fun_prop

lemma integrable_bumpR {c lam : ℝ} (hlam : 0 < lam) : Integrable (bumpR c lam) := by
  have h := (RvMBridgeGauss.integrable_abs_pow_mul_exp_quadratic_abs (b := 2 * lam) (by positivity) 0 2).comp_sub_right c
  refine h.congr (Filter.Eventually.of_forall fun r => ?_)
  unfold bumpR
  simp [sq_abs]

/-- The archimedean integrand is integrable: |psi(r)| grows like log |r| (Zeta23's
digamma_growth_strip) against the Gaussian bump. -/
theorem integrable_bumpR_mul_psiR {c lam : ℝ} (hlam : 0 < lam) :
    Integrable (fun r : ℝ => bumpR c lam r * psiR r) := by
  obtain ⟨C, hC0, hC⟩ := Zeta23.WeilEF.digamma_growth_strip
  have h2 := (RvMBridgeGauss.integrable_abs_pow_mul_exp_quadratic_abs (b := 2 * lam) (by positivity) 0 2).comp_sub_right c
  have h3 := (RvMBridgeGauss.integrable_abs_pow_mul_exp_quadratic_abs (b := 2 * lam) (by positivity) 0 3).comp_sub_right c
  have hmaj : Integrable (fun r : ℝ => C * ((1 + |c| / 2) * |r - c| ^ 2 + (1 / 2) * |r - c| ^ 3)
      * Real.exp (-(2 * lam) * (r - c) ^ 2)) := by
    refine ((h2.const_mul (C * (1 + |c| / 2))).add (h3.const_mul (C * (1 / 2)))).congr
      (Filter.Eventually.of_forall fun r => ?_)
    simp only [Pi.add_apply, zero_mul, add_zero]
    ring
  refine hmaj.mono' ((continuous_bumpR c lam).mul continuous_psiR).aestronglyMeasurable
    (Filter.Eventually.of_forall fun r => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (bumpR_nonneg c lam r)]
  have hψ : |psiR r| ≤ C * (1 + |r| / 2) := by
    have hre : (1 / 4 + ((r : ℂ) / 2) * I).re = 1 / 4 := by simp
    have him : (1 / 4 + ((r : ℂ) / 2) * I).im = r / 2 := by simp
    have hs := hC (1 / 4 + ((r : ℂ) / 2) * I) (by rw [hre]) (by rw [hre]; norm_num)
    rw [him] at hs
    have hlog : Real.log (2 + |r / 2|) ≤ 1 + |r| / 2 := by
      rw [abs_div, abs_two]
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 + |r| / 2)
      linarith
    calc |psiR r| ≤ ‖Complex.digamma (1 / 4 + ((r : ℂ) / 2) * I)‖ := Complex.abs_re_le_norm _
      _ ≤ C * Real.log (2 + |r / 2|) := hs
      _ ≤ C * (1 + |r| / 2) := mul_le_mul_of_nonneg_left hlog hC0.le
  have hr : |r| ≤ |r - c| + |c| := by
    have := abs_sub_abs_le_abs_sub r c
    linarith
  unfold bumpR
  set x := |r - c| with hx
  have hx0 : 0 ≤ x := abs_nonneg _
  have hsq : (r - c) ^ 2 = x ^ 2 := (sq_abs (r - c)).symm
  rw [hsq]
  have hE0 : 0 < Real.exp (-(2 * lam) * x ^ 2) := Real.exp_pos _
  calc x ^ 2 * Real.exp (-(2 * lam) * x ^ 2) * |psiR r|
        ≤ x ^ 2 * Real.exp (-(2 * lam) * x ^ 2) * (C * (1 + |r| / 2)) :=
        mul_le_mul_of_nonneg_left hψ (by positivity)
    _ ≤ x ^ 2 * Real.exp (-(2 * lam) * x ^ 2) * (C * ((1 + |c| / 2) + x / 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ hC0.le
        linarith
    _ = C * ((1 + |c| / 2) * x ^ 2 + (1 / 2) * x ^ 3) * Real.exp (-(2 * lam) * x ^ 2) := by ring

/-- bumpR <= 1/(2 lam) (y e^{-y} <= 1). -/
lemma bumpR_le {c lam : ℝ} (hlam : 0 < lam) (r : ℝ) : bumpR c lam r ≤ 1 / (2 * lam) := by
  unfold bumpR
  set y := 2 * lam * (r - c) ^ 2 with hy
  have hy0 : 0 ≤ y := by positivity
  have h1 : y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  have h2 : y * Real.exp (-y) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    exact h1
  have e0 : -(2 * lam) * (r - c) ^ 2 = -y := by rw [hy]; ring
  have e : (r - c) ^ 2 * Real.exp (-y) = (1 / (2 * lam)) * (y * Real.exp (-y)) := by
    rw [hy]
    field_simp
  rw [e0, e]
  calc (1 / (2 * lam)) * (y * Real.exp (-y)) ≤ (1 / (2 * lam)) * 1 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 1 / (2 * lam) := mul_one _

/-- ∫ bumpR = sqrt(pi/(2 lam)) / (4 lam) = 2 pi A (Plancherel for this pair, by hand). -/
lemma integral_bumpR {c lam : ℝ} (hlam : 0 < lam) :
    ∫ r : ℝ, bumpR c lam r = 2 * Real.pi * gaussA lam := by
  unfold bumpR
  rw [integral_sub_right_eq_self (fun x : ℝ => x ^ 2 * Real.exp (-(2 * lam) * x ^ 2)) c,
    integral_sq_mul_exp_neg_mul_sq (by positivity : (0 : ℝ) < 2 * lam)]
  unfold gaussA
  rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  set sπ := Real.sqrt Real.pi with hsπ
  set s2 := Real.sqrt 2 with hs2
  set sl := Real.sqrt lam with hsl
  have hsπ0 : 0 < sπ := Real.sqrt_pos.mpr Real.pi_pos
  have hs20 : 0 < s2 := Real.sqrt_pos.mpr (by norm_num)
  have hsl0 : 0 < sl := Real.sqrt_pos.mpr hlam
  have hpi : Real.pi = sπ ^ 2 := (Real.sq_sqrt Real.pi_pos.le).symm
  have hlam' : lam = sl ^ 2 := (Real.sq_sqrt hlam.le).symm
  rw [hpi, hlam']
  field_simp
  ring

lemma R₀_pos : 0 < R₀ := by unfold R₀; norm_num

/-- ∫_{|r| < R₀} bumpR <= R₀ / lam. -/
lemma setIntegral_bumpR_le {c lam : ℝ} (hlam : 0 < lam) :
    ∫ r in Set.Ioo (-R₀) R₀, bumpR c lam r ≤ R₀ / lam := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioo (-R₀) R₀)
    (f := bumpR c lam) (C := 1 / (2 * lam)) (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)
    (fun r _ => by rw [Real.norm_eq_abs, abs_of_nonneg (bumpR_nonneg c lam r)]; exact bumpR_le hlam r)
  rw [Real.volume_real_Ioo_of_le (by linarith [R₀_pos]), Real.norm_eq_abs] at h
  calc ∫ r in Set.Ioo (-R₀) R₀, bumpR c lam r ≤ |∫ r in Set.Ioo (-R₀) R₀, bumpR c lam r| := le_abs_self _
    _ ≤ 1 / (2 * lam) * (R₀ - -R₀) := h
    _ = R₀ / lam := by field_simp; ring

/-- THE ARCHIMEDEAN LOWER BOUND: ∫ bumpR psi >= 2 (2 pi A) - 7 R₀ / lam, from psi >= 2 beyond R₀
and psi >= -5 everywhere. -/
theorem integral_bumpR_mul_psiR_ge {c lam : ℝ} (hlam : 0 < lam) :
    2 * (2 * Real.pi * gaussA lam) - 7 * (R₀ / lam) ≤ ∫ r : ℝ, bumpR c lam r * psiR r := by
  have hbi : Integrable (bumpR c lam) := integrable_bumpR hlam
  have hind : Integrable ((Set.Ioo (-R₀) R₀).indicator (bumpR c lam)) :=
    hbi.indicator measurableSet_Ioo
  set L : ℝ → ℝ := fun r => 2 * bumpR c lam r - 7 * (Set.Ioo (-R₀) R₀).indicator (bumpR c lam) r
    with hL
  have hLi : Integrable L := (hbi.const_mul 2).sub (hind.const_mul 7)
  have hle : L ≤ fun r => bumpR c lam r * psiR r := by
    intro r
    simp only [hL]
    have hb0 := bumpR_nonneg c lam r
    by_cases hr : r ∈ Set.Ioo (-R₀) R₀
    · rw [Set.indicator_of_mem hr]
      have := psiR_ge r
      nlinarith
    · rw [Set.indicator_of_notMem hr]
      have hr' : R₀ ≤ |r| := by
        simp only [Set.mem_Ioo, not_and_or, not_lt] at hr
        rcases hr with h | h
        · rw [abs_of_nonpos (by linarith [R₀_pos])]
          linarith
        · rw [abs_of_nonneg (by linarith [R₀_pos])]
          exact h
      have := psiR_ge_two hr'
      nlinarith
  have hmono := integral_mono hLi (integrable_bumpR_mul_psiR hlam) hle
  rw [hL, integral_sub (hbi.const_mul 2) (hind.const_mul 7), integral_const_mul, integral_const_mul,
    integral_indicator measurableSet_Ioo, integral_bumpR hlam] at hmono
  have hset := setIntegral_bumpR_le (c := c) hlam
  linarith

/-! ## J. Assembly. -/

/-- The archimedean integral is real: ∫ archIntegrand f = ∫ bumpR psi (a real number). -/
lemma integral_archIntegrand_eq {c lam : ℝ} (hlam : 0 < lam) :
    ∫ r : ℝ, archIntegrand (autocorr (RvMBridge8.gaussPhi c lam)) r
      = ((∫ r : ℝ, bumpR c lam r * psiR r : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  congr 1
  funext r
  unfold archIntegrand psiR
  rw [weilKernel_autocorrGauss_line hlam r]
  push_cast
  ring

/-- Re archSide f >= A (2 - log pi) - 2 |poles| - 7 R₀ / (2 pi lam). -/
theorem re_archSide_ge {c lam : ℝ} (hlam : 0 < lam) :
    2 * gaussA lam - gaussA lam * Real.log Real.pi
      - 2 * (2 * gaussA lam * Real.exp (2 * lam) * Real.sqrt (32 * Real.pi * lam))
      - 7 * (R₀ / lam) / (2 * Real.pi)
    ≤ (archSide (autocorr (RvMBridge8.gaussPhi c lam))).re := by
  unfold archSide
  rw [integral_archIntegrand_eq hlam, autocorr_gaussPhi hlam 0, autocorrGauss_zero]
  set W0 := weilKernel (autocorr (RvMBridge8.gaussPhi c lam)) 0 with hW0
  set W1 := weilKernel (autocorr (RvMBridge8.gaussPhi c lam)) 1 with hW1
  set J := ∫ r : ℝ, bumpR c lam r * psiR r with hJ
  have h0 := (abs_le.mp (Complex.abs_re_le_norm W0)).1
  have h1 := (abs_le.mp (Complex.abs_re_le_norm W1)).1
  have hn0 := norm_weilKernel_zero_le (c := c) hlam
  have hn1 := norm_weilKernel_one_le (c := c) hlam
  rw [← hW0] at hn0
  rw [← hW1] at hn1
  have hJge := integral_bumpR_mul_psiR_ge (c := c) hlam
  rw [← hJ] at hJge
  have hre : (W0 + W1 - (gaussA lam : ℂ) * (Real.log Real.pi : ℂ)
      + (1 / (2 * (Real.pi : ℂ))) * (J : ℂ)).re
      = W0.re + W1.re - gaussA lam * Real.log Real.pi + (1 / (2 * Real.pi)) * J := by
    rw [show (gaussA lam : ℂ) * (Real.log Real.pi : ℂ) = ((gaussA lam * Real.log Real.pi : ℝ) : ℂ) by
        push_cast; ring,
      show (1 / (2 * (Real.pi : ℂ))) * (J : ℂ) = (((1 / (2 * Real.pi)) * J : ℝ) : ℂ) by push_cast; ring]
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re]
  rw [hre]
  have hJ' : (1 / (2 * Real.pi)) * (2 * (2 * Real.pi * gaussA lam) - 7 * (R₀ / lam))
      ≤ (1 / (2 * Real.pi)) * J := mul_le_mul_of_nonneg_left hJge (by positivity)
  have hid : (1 / (2 * Real.pi)) * (2 * (2 * Real.pi * gaussA lam) - 7 * (R₀ / lam))
      = 2 * gaussA lam - 7 * (R₀ / lam) / (2 * Real.pi) := by
    field_simp
  linarith

/-- THE UNCONDITIONAL THEOREM (primes-side form): for every centre c and every width
0 < lam <= lam₀ = 10^-7, the Weil functional of the Gaussian-derivative autocorrelation is
nonnegative.  No zeros are involved. -/
theorem re_weilForm_gauss_nonneg (c lam : ℝ) (hlam : 0 < lam) (hlam0 : lam ≤ lam₀) :
    0 ≤ (archSide (autocorr (RvMBridge8.gaussPhi c lam))
          - primeSide (autocorr (RvMBridge8.gaussPhi c lam))).re := by
  have hA := gaussA_pos hlam
  unfold lam₀ at hlam0
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hσ : 2 ≤ Real.log 2 / (16 * lam) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have harch := re_archSide_ge (c := c) hlam
  have hprime := norm_primeSide_le (c := c) hlam hσ
  have hpre := (abs_le.mp (Complex.abs_re_le_norm
    (primeSide (autocorr (RvMBridge8.gaussPhi c lam))))).2
  rw [Complex.sub_re]
  -- numerical bounds
  have hs0 : 0 ≤ Real.sqrt lam := Real.sqrt_nonneg _
  have hs : Real.sqrt lam ≤ 1 / 3000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith
  have hlogpi : Real.log Real.pi ≤ 1.3863 := by
    have h1 : Real.log Real.pi ≤ Real.log 4 :=
      Real.log_le_log Real.pi_pos (by linarith [Real.pi_lt_d2])
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    linarith
  have hexp : Real.exp (2 * lam) ≤ 3 := by
    have : Real.exp (2 * lam) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
    linarith [Real.exp_one_lt_d9]
  have hsqrt32 : Real.sqrt (32 * Real.pi * lam) ≤ 11 / 3000 := by
    rw [Real.sqrt_mul (by positivity)]
    calc Real.sqrt (32 * Real.pi) * Real.sqrt lam ≤ 11 * (1 / 3000) := by
          apply mul_le_mul _ hs hs0 (by norm_num)
          rw [Real.sqrt_le_left (by norm_num)]
          nlinarith [Real.pi_lt_d2]
      _ = 11 / 3000 := by norm_num
  have hE : 64 * Real.exp (-(Real.log 2) ^ 2 / (16 * lam)) ≤ 1 / 1000 := by
    have hx : (64000 : ℝ) ≤ (Real.log 2) ^ 2 / (16 * lam) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have hx0 : 0 < (Real.log 2) ^ 2 / (16 * lam) := by linarith
    have h1 : Real.exp (-(Real.log 2) ^ 2 / (16 * lam)) ≤ 1 / ((Real.log 2) ^ 2 / (16 * lam)) := by
      rw [show -(Real.log 2) ^ 2 / (16 * lam) = -((Real.log 2) ^ 2 / (16 * lam)) by ring,
        Real.exp_neg, one_div]
      exact inv_anti₀ hx0 (by linarith [Real.add_one_le_exp ((Real.log 2) ^ 2 / (16 * lam))])
    have h2 : 1 / ((Real.log 2) ^ 2 / (16 * lam)) ≤ 1 / 64000 :=
      one_div_le_one_div_of_le (by norm_num) hx
    linarith
  have hsp0 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hsp : Real.sqrt (2 * Real.pi) ≤ 2.51 := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith [Real.pi_lt_d2]
  have hsl0 : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have key : 287 * (Real.sqrt (2 * Real.pi) * Real.sqrt lam) ≤ 0.08 * Real.pi := by
    have := mul_le_mul hsp hs hs0 (by norm_num)
    nlinarith [Real.pi_gt_d2]
  have hpole : 7 * (R₀ / lam) / (2 * Real.pi) ≤ 0.32 * gaussA lam := by
    unfold R₀ gaussA
    rw [show 7 * (41 / lam) / (2 * Real.pi) = 287 / (2 * Real.pi * lam) by field_simp; ring,
      show (0.32 : ℝ) * (1 / (8 * Real.sqrt (2 * Real.pi) * (lam * Real.sqrt lam)))
        = 0.04 / (Real.sqrt (2 * Real.pi) * lam * Real.sqrt lam) by field_simp; ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left key hlam.le]
  have hpoles : 2 * (2 * gaussA lam * Real.exp (2 * lam) * Real.sqrt (32 * Real.pi * lam))
      ≤ 0.044 * gaussA lam := by
    have h := mul_le_mul hexp hsqrt32 (Real.sqrt_nonneg _) (by norm_num)
    nlinarith
  have hprime' : ‖primeSide (autocorr (RvMBridge8.gaussPhi c lam))‖ ≤ 0.001 * gaussA lam := by
    calc ‖primeSide (autocorr (RvMBridge8.gaussPhi c lam))‖
        ≤ 64 * gaussA lam * Real.exp (-(Real.log 2) ^ 2 / (16 * lam)) := hprime
      _ = gaussA lam * (64 * Real.exp (-(Real.log 2) ^ 2 / (16 * lam))) := by ring
      _ ≤ gaussA lam * (1 / 1000) := mul_le_mul_of_nonneg_left hE hA.le
      _ = 0.001 * gaussA lam := by ring
  have hlogpi' : gaussA lam * Real.log Real.pi ≤ gaussA lam * 1.3863 :=
    mul_le_mul_of_nonneg_left hlogpi hA.le
  linarith

/-- THE WALL'S SMALL-WIDTH REGION, modulo the Gaussian explicit formula: an ABSOLUTE
lam₀ > 0 (namely 10^-7) such that F(c, lam) = Re zeroSide (gaussTest c lam) >= 0 for EVERY
centre c and every 0 < lam <= lam₀. -/
theorem gaussian_positivity_small_lam_of (hEF : GaussianExplicitFormula) :
    ∃ lam₀ > 0, ∀ c lam : ℝ, 0 < lam → lam ≤ lam₀ →
      0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re :=
  ⟨lam₀, by unfold lam₀; norm_num, fun c lam hlam hle => by
    rw [hEF c lam hlam]
    exact re_weilForm_gauss_nonneg c lam hlam hle⟩

/-- The same with the explicit threshold. -/
theorem gaussian_positivity_small_lam_explicit_of (hEF : GaussianExplicitFormula)
    (c lam : ℝ) (hlam : 0 < lam) (hle : lam ≤ lam₀) :
    0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re := by
  rw [hEF c lam hlam]
  exact re_weilForm_gauss_nonneg c lam hlam hle

/-! ## K. The obligation is DISCHARGED on the island (E6Bridge10.zeroSide_gaussTest_eq), so the
small-width theorems are unconditional. -/

theorem gaussianExplicitFormula : GaussianExplicitFormula := fun c lam hlam => by
  rw [RvMBridge10.zeroSide_gaussTest_eq c lam hlam]

/-- THE SMALL-WIDTH REGION OF THE WALL, UNCONDITIONAL: an absolute lam₀ > 0 with
F(c, lam) >= 0 for every centre c and every 0 < lam <= lam₀. -/
theorem gaussian_positivity_small_lam :
    ∃ lam₀ > 0, ∀ c lam : ℝ, 0 < lam → lam ≤ lam₀ →
      0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re :=
  gaussian_positivity_small_lam_of gaussianExplicitFormula

theorem gaussian_positivity_small_lam_explicit (c lam : ℝ) (hlam : 0 < lam) (hle : lam ≤ lam₀) :
    0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re :=
  gaussian_positivity_small_lam_explicit_of gaussianExplicitFormula c lam hlam hle

/-! ## L. The ENVELOPE form: for every width lam, F(c, lam) >= 0 once |c| is large
(archimedean dominance at large height: Re psi(1/4 + i r/2) ~ log(|r|/2) grows, the prime
side is bounded by a lam-only multiple of A). -/

/-- A lam-uniform prime-side bound: ‖primeSide f‖ <= 16 A e^{16 lam}
(AM-GM: (log n)^2/(16 lam) >= 2 log n - 16 lam). -/
lemma prime_term_bound_uniform {c lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    ‖((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
        * (autocorrGauss c lam (Real.log n) + autocorrGauss c lam (-Real.log n))‖
      ≤ 8 * gaussA lam * Real.exp (16 * lam) * (1 / (n : ℝ) ^ 2) := by
  have hA := gaussA_pos hlam
  rcases lt_or_ge n 2 with hn | hn
  · have h0 : ArithmeticFunction.vonMangoldt n = 0 := by
      interval_cases n
      · simp
      · exact ArithmeticFunction.vonMangoldt_apply_one
    rw [h0]
    simp only [zero_div, Complex.ofReal_zero, zero_mul, norm_zero]
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
    have hg : ‖autocorrGauss c lam (Real.log n) + autocorrGauss c lam (-Real.log n)‖
        ≤ 4 * gaussA lam * Real.exp (-(Real.log n) ^ 2 / (16 * lam)) := by
      have h1 := norm_autocorrGauss_le (c := c) hlam (Real.log n)
      have h2 := norm_autocorrGauss_le (c := c) hlam (-Real.log n)
      rw [neg_sq] at h2
      calc ‖autocorrGauss c lam (Real.log n) + autocorrGauss c lam (-Real.log n)‖
          ≤ ‖autocorrGauss c lam (Real.log n)‖ + ‖autocorrGauss c lam (-Real.log n)‖ := norm_add_le _ _
        _ ≤ 2 * gaussA lam * Real.exp (-(Real.log n) ^ 2 / (16 * lam))
            + 2 * gaussA lam * Real.exp (-(Real.log n) ^ 2 / (16 * lam)) := add_le_add h1 h2
        _ = 4 * gaussA lam * Real.exp (-(Real.log n) ^ 2 / (16 * lam)) := by ring
    have hexp : Real.exp (-(Real.log n) ^ 2 / (16 * lam))
        ≤ Real.exp (16 * lam) * (1 / (n : ℝ) ^ 2) := by
      have e1 : (1 : ℝ) / (n : ℝ) ^ 2 = Real.exp (-(2 * Real.log n)) := by
        rw [Real.exp_neg, show 2 * Real.log n = Real.log ((n : ℝ) ^ 2) by
          rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity), one_div]
      rw [e1, ← Real.exp_add, Real.exp_le_exp, div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg (Real.log n - 16 * lam)]
    calc ‖((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
          * (autocorrGauss c lam (Real.log n) + autocorrGauss c lam (-Real.log n))‖
        = (ArithmeticFunction.vonMangoldt n / Real.sqrt n)
          * ‖autocorrGauss c lam (Real.log n) + autocorrGauss c lam (-Real.log n)‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hΛ0]
      _ ≤ 2 * (4 * gaussA lam * (Real.exp (16 * lam) * (1 / (n : ℝ) ^ 2))) := by
          apply mul_le_mul hΛ _ (norm_nonneg _) (by norm_num)
          calc ‖autocorrGauss c lam (Real.log n) + autocorrGauss c lam (-Real.log n)‖
              ≤ 4 * gaussA lam * Real.exp (-(Real.log n) ^ 2 / (16 * lam)) := hg
            _ ≤ 4 * gaussA lam * (Real.exp (16 * lam) * (1 / (n : ℝ) ^ 2)) :=
                mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = 8 * gaussA lam * Real.exp (16 * lam) * (1 / (n : ℝ) ^ 2) := by ring

theorem norm_primeSide_le_uniform {c lam : ℝ} (hlam : 0 < lam) :
    ‖primeSide (autocorr (RvMBridge8.gaussPhi c lam))‖ ≤ 16 * gaussA lam * Real.exp (16 * lam) := by
  rw [autocorr_gaussPhi_funext hlam]
  unfold primeSide
  set T : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
    * (autocorrGauss c lam (Real.log n) + autocorrGauss c lam (-Real.log n)) with hT
  set K : ℝ := 8 * gaussA lam * Real.exp (16 * lam) with hK
  have hK0 : 0 < K := by have := gaussA_pos hlam; positivity
  have hM : Summable (fun n : ℕ => K * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left K
  have hterm : ∀ n : ℕ, ‖T n‖ ≤ K * (1 / (n : ℝ) ^ 2) := fun n => prime_term_bound_uniform hlam n
  have hs : Summable (fun n : ℕ => ‖T n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hM
  have hpi2 : Real.pi ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  calc ‖∑' n : ℕ, T n‖ ≤ ∑' n : ℕ, ‖T n‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n : ℕ, K * (1 / (n : ℝ) ^ 2) := hs.tsum_le_tsum hterm hM
    _ = K * (Real.pi ^ 2 / 6) := by rw [tsum_mul_left, hasSum_zeta_two.tsum_eq]
    _ ≤ K * 2 := mul_le_mul_of_nonneg_left hpi2 hK0.le
    _ = 16 * gaussA lam * Real.exp (16 * lam) := by rw [hK]; ring

/-- Re psi(1/4 + i r/2) >= log(|r|/2) - 5 for |r| >= 2 (Stirling). -/
theorem re_digamma_quarter_ge_log {r : ℝ} (hr : 2 ≤ |r|) :
    Real.log (|r| / 2) - 5 ≤ (Complex.digamma (((1 / 4 : ℝ) : ℂ) + I * ((r / 2 : ℝ) : ℂ))).re := by
  have ht : 1 / 2 ≤ |r / 2| := by rw [abs_div, abs_two]; linarith
  have h := Zeta23.StirlingVert.re_digamma_stirling' (a := 1 / 4) (by norm_num) (by norm_num) ht
  have hr2 : 5 / (r / 2) ^ 2 ≤ 5 := by
    have : (2 : ℝ) ^ 2 ≤ r ^ 2 := by
      rw [← sq_abs r]
      exact pow_le_pow_left₀ (by norm_num) hr 2
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  have := (abs_le.mp h).1
  rw [abs_div, abs_two] at this
  linarith

lemma psiR_ge_log {r : ℝ} (hr : 2 ≤ |r|) : Real.log (|r| / 2) - 5 ≤ psiR r := by
  rw [psiR_eq]
  exact re_digamma_quarter_ge_log hr

/-- A(lam/2) = 2 sqrt 2 A(lam). -/
lemma gaussA_half {lam : ℝ} (hlam : 0 < lam) :
    gaussA (lam / 2) = 2 * Real.sqrt 2 * gaussA lam := by
  unfold gaussA
  rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2)]
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsl : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsp : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp

/-- The bump at width lam/2 is the half-width Gaussian moment. -/
lemma bumpR_half (c lam r : ℝ) :
    bumpR c (lam / 2) r = (r - c) ^ 2 * Real.exp (-lam * (r - c) ^ 2) := by
  unfold bumpR
  congr 2
  ring

/-- Tail mass: ∫_{|r - c| >= 2/sqrt lam} bumpR <= e^{-4} (2 pi A(lam/2)) = e^{-4} 2 sqrt 2 (2 pi A). -/
lemma integral_indicator_bumpR_tail_le {c lam : ℝ} (hlam : 0 < lam) :
    ∫ r : ℝ, (Set.Ioo (c - 2 / Real.sqrt lam) (c + 2 / Real.sqrt lam))ᶜ.indicator (bumpR c lam) r
      ≤ Real.exp (-4) * (2 * Real.pi * gaussA (lam / 2)) := by
  set L := 2 / Real.sqrt lam with hL
  have hL0 : 0 < L := by positivity
  have hLsq : lam * L ^ 2 = 4 := by
    rw [hL, div_pow, Real.sq_sqrt hlam.le]
    field_simp
    norm_num
  have hbi : Integrable (bumpR c lam) := integrable_bumpR hlam
  have hind : Integrable ((Set.Ioo (c - L) (c + L))ᶜ.indicator (bumpR c lam)) :=
    hbi.indicator measurableSet_Ioo.compl
  have hhalf : Integrable (fun r : ℝ => Real.exp (-4) * bumpR c (lam / 2) r) :=
    (integrable_bumpR (c := c) (by positivity : 0 < lam / 2)).const_mul _
  have hle : (Set.Ioo (c - L) (c + L))ᶜ.indicator (bumpR c lam)
      ≤ fun r : ℝ => Real.exp (-4) * bumpR c (lam / 2) r := by
    intro r
    by_cases hr : r ∈ (Set.Ioo (c - L) (c + L))ᶜ
    · rw [Set.indicator_of_mem hr]
      show bumpR c lam r ≤ Real.exp (-4) * bumpR c (lam / 2) r
      rw [bumpR_half]
      unfold bumpR
      have hx : L ^ 2 ≤ (r - c) ^ 2 := by
        simp only [Set.mem_compl_iff, Set.mem_Ioo, not_and_or, not_lt] at hr
        rcases hr with h | h
        · nlinarith
        · nlinarith
      have hexp : Real.exp (-(2 * lam) * (r - c) ^ 2) ≤ Real.exp (-4) * Real.exp (-lam * (r - c) ^ 2) := by
        rw [← Real.exp_add, Real.exp_le_exp]
        nlinarith
      calc (r - c) ^ 2 * Real.exp (-(2 * lam) * (r - c) ^ 2)
          ≤ (r - c) ^ 2 * (Real.exp (-4) * Real.exp (-lam * (r - c) ^ 2)) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = Real.exp (-4) * ((r - c) ^ 2 * Real.exp (-lam * (r - c) ^ 2)) := by ring
    · rw [Set.indicator_of_notMem hr]
      have := bumpR_nonneg c (lam / 2) r
      positivity
  calc ∫ r : ℝ, (Set.Ioo (c - L) (c + L))ᶜ.indicator (bumpR c lam) r
      ≤ ∫ r : ℝ, Real.exp (-4) * bumpR c (lam / 2) r := integral_mono hind hhalf hle
    _ = Real.exp (-4) * (2 * Real.pi * gaussA (lam / 2)) := by
        rw [integral_const_mul, integral_bumpR (by positivity)]

/-- THE ENVELOPE LOWER BOUND on the archimedean integral: with L = 2/sqrt lam and
theta := log((|c| - L)/2) - 5 >= 0 (so |c| - L >= 2),
∫ bumpR psi >= theta (2 pi A) - (theta + 5) e^{-4} (2 pi A(lam/2)). -/
theorem integral_bumpR_mul_psiR_ge_envelope {c lam : ℝ} (hlam : 0 < lam)
    (hc : 2 ≤ |c| - 2 / Real.sqrt lam)
    (hθ : 0 ≤ Real.log ((|c| - 2 / Real.sqrt lam) / 2) - 5) :
    (Real.log ((|c| - 2 / Real.sqrt lam) / 2) - 5) * (2 * Real.pi * gaussA lam)
      - (Real.log ((|c| - 2 / Real.sqrt lam) / 2) - 5 + 5)
          * (Real.exp (-4) * (2 * Real.pi * gaussA (lam / 2)))
      ≤ ∫ r : ℝ, bumpR c lam r * psiR r := by
  set L := 2 / Real.sqrt lam with hL
  set θ := Real.log ((|c| - L) / 2) - 5 with hθdef
  set S := (Set.Ioo (c - L) (c + L))ᶜ with hS
  have hbi : Integrable (bumpR c lam) := integrable_bumpR hlam
  have hind : Integrable (S.indicator (bumpR c lam)) := hbi.indicator measurableSet_Ioo.compl
  set Lf : ℝ → ℝ := fun r => θ * bumpR c lam r - (θ + 5) * S.indicator (bumpR c lam) r with hLf
  have hLi : Integrable Lf := (hbi.const_mul θ).sub (hind.const_mul (θ + 5))
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
      have hlog : θ ≤ psiR r := by
        have := psiR_ge_log hr2
        have hmono : Real.log ((|c| - L) / 2) ≤ Real.log (|r| / 2) :=
          Real.log_le_log (by linarith) (by linarith)
        linarith
      nlinarith
  have hmono := integral_mono hLi (integrable_bumpR_mul_psiR hlam) hle
  rw [hLf, integral_sub (hbi.const_mul θ) (hind.const_mul (θ + 5)), integral_const_mul,
    integral_const_mul, integral_bumpR hlam] at hmono
  have htail := integral_indicator_bumpR_tail_le (c := c) hlam
  rw [← hL, ← hS] at htail
  have hθ5 : 0 ≤ θ + 5 := by linarith
  have := mul_le_mul_of_nonneg_left htail hθ5
  linarith

/-- The explicit envelope threshold c₁(lam). -/
def envelopeX (lam : ℝ) : ℝ :=
  4 * Real.exp (2 * lam) * Real.sqrt (32 * Real.pi * lam) + 16 * Real.exp (16 * lam)

def envelopeC (lam : ℝ) : ℝ := 2 * Real.exp (9 + 2 * envelopeX lam) + 2 / Real.sqrt lam

lemma envelopeX_nonneg (lam : ℝ) : 0 ≤ envelopeX lam := by
  unfold envelopeX
  positivity

/-- THE ENVELOPE THEOREM (primes-side form), UNCONDITIONAL: for every width lam > 0 and every
centre with |c| >= c₁(lam), the Weil functional of the Gaussian-derivative autocorrelation is
nonnegative. -/
theorem re_weilForm_gauss_nonneg_of_large_c (c lam : ℝ) (hlam : 0 < lam) (hc : envelopeC lam ≤ |c|) :
    0 ≤ (archSide (autocorr (RvMBridge8.gaussPhi c lam))
          - primeSide (autocorr (RvMBridge8.gaussPhi c lam))).re := by
  have hA := gaussA_pos hlam
  set L := 2 / Real.sqrt lam with hL
  set X := envelopeX lam with hX
  have hX0 := envelopeX_nonneg lam
  have hexp0 : 0 < Real.exp (9 + 2 * X) := Real.exp_pos _
  have hcL : 2 * Real.exp (9 + 2 * X) ≤ |c| - L := by
    unfold envelopeC at hc
    rw [← hX, ← hL] at hc
    linarith
  have hc2 : 2 ≤ |c| - L := by
    have : (1 : ℝ) ≤ Real.exp (9 + 2 * X) := by
      rw [Real.one_le_exp_iff]
      positivity
    linarith
  set θ := Real.log ((|c| - L) / 2) - 5 with hθdef
  have hθX : 4 + 2 * X ≤ θ := by
    have : 9 + 2 * X ≤ Real.log ((|c| - L) / 2) := by
      rw [← Real.log_exp (9 + 2 * X)]
      exact Real.log_le_log hexp0 (by linarith)
    linarith
  have hθ0 : 0 ≤ θ := by linarith
  -- the pieces
  have harch : 2 * gaussA lam - gaussA lam * Real.log Real.pi
      - 2 * (2 * gaussA lam * Real.exp (2 * lam) * Real.sqrt (32 * Real.pi * lam))
      - 7 * (R₀ / lam) / (2 * Real.pi)
      ≤ (archSide (autocorr (RvMBridge8.gaussPhi c lam))).re := re_archSide_ge hlam
  -- (harch is the small-lam bound; here we redo the archimedean step with the envelope bound)
  clear harch
  have hJ := integral_bumpR_mul_psiR_ge_envelope (c := c) hlam hc2 hθ0
  rw [← hL, ← hθdef] at hJ
  have hprime := norm_primeSide_le_uniform (c := c) hlam
  have hpre := (abs_le.mp (Complex.abs_re_le_norm
    (primeSide (autocorr (RvMBridge8.gaussPhi c lam))))).2
  -- Re archSide from the pieces
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
  have hn0 := norm_weilKernel_zero_le (c := c) hlam
  have hn1 := norm_weilKernel_one_le (c := c) hlam
  -- numerics
  have hlogpi : Real.log Real.pi ≤ 1.3863 := by
    have h1 : Real.log Real.pi ≤ Real.log 4 :=
      Real.log_le_log Real.pi_pos (by linarith [Real.pi_lt_d2])
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    linarith [Real.log_two_lt_d9]
  have he4 : Real.exp (-4) ≤ 1 / 54 := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    have h1 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h1]
    have := Real.exp_one_gt_d9
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283) this.le 4]
  have hs2 : Real.sqrt 2 ≤ 1.5 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hhalf : gaussA (lam / 2) ≤ 3 * gaussA lam := by
    rw [gaussA_half hlam]
    nlinarith
  -- put J's bound in units of A
  have hJ' : (1 / (2 * Real.pi)) * (θ * (2 * Real.pi * gaussA lam)
      - (θ + 5) * (Real.exp (-4) * (2 * Real.pi * gaussA (lam / 2))))
      ≤ (1 / (2 * Real.pi)) * ∫ r : ℝ, bumpR c lam r * psiR r :=
    mul_le_mul_of_nonneg_left hJ (by positivity)
  have hid : (1 / (2 * Real.pi)) * (θ * (2 * Real.pi * gaussA lam)
      - (θ + 5) * (Real.exp (-4) * (2 * Real.pi * gaussA (lam / 2))))
      = θ * gaussA lam - (θ + 5) * Real.exp (-4) * gaussA (lam / 2) := by
    field_simp
  rw [hid] at hJ'
  have htailA : (θ + 5) * Real.exp (-4) * gaussA (lam / 2) ≤ (θ + 5) * (1 / 54) * (3 * gaussA lam) := by
    apply mul_le_mul _ hhalf (gaussA_pos (by positivity)).le (by positivity)
    exact mul_le_mul_of_nonneg_left he4 (by linarith)
  have hpoles : (weilKernel (autocorr (RvMBridge8.gaussPhi c lam)) 0).re
      + (weilKernel (autocorr (RvMBridge8.gaussPhi c lam)) 1).re
      ≥ -(4 * Real.exp (2 * lam) * Real.sqrt (32 * Real.pi * lam)) * gaussA lam := by
    nlinarith
  have hprime' : (primeSide (autocorr (RvMBridge8.gaussPhi c lam))).re
      ≤ 16 * Real.exp (16 * lam) * gaussA lam := by
    nlinarith
  have hXdef : X = 4 * Real.exp (2 * lam) * Real.sqrt (32 * Real.pi * lam) + 16 * Real.exp (16 * lam) := rfl
  have hlogA : gaussA lam * Real.log Real.pi ≤ gaussA lam * 1.3863 :=
    mul_le_mul_of_nonneg_left hlogpi hA.le
  have hθA : (4 + 2 * X) * gaussA lam ≤ θ * gaussA lam := mul_le_mul_of_nonneg_right hθX hA.le
  nlinarith

/-- THE ENVELOPE THEOREM (zero-side form), UNCONDITIONAL: for every width lam > 0 there is an
explicit c₁(lam) = envelopeC lam with F(c, lam) >= 0 for all |c| >= c₁(lam). -/
theorem gaussian_positivity_envelope (c lam : ℝ) (hlam : 0 < lam) (hc : envelopeC lam ≤ |c|) :
    0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re := by
  rw [gaussianExplicitFormula c lam hlam]
  exact re_weilForm_gauss_nonneg_of_large_c c lam hlam hc

theorem gaussian_positivity_envelope' :
    ∀ lam : ℝ, 0 < lam → ∃ c₁ : ℝ, ∀ c : ℝ, c₁ ≤ c →
      0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re :=
  fun lam hlam => ⟨envelopeC lam, fun c hc =>
    gaussian_positivity_envelope c lam hlam (hc.trans (le_abs_self c))⟩

end RvMBridge11
