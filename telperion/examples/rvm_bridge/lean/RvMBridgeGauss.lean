/-
  RvMBridgeGauss -- the PRELUDE of the Gaussian / Wall cluster (E6Bridge6 .. E6Bridge16, E6Bridge30),
  2026-09-22.  The cluster was written by parallel agents against the E6Bridge6 vocabulary and
  re-proved its shared helpers in several modules (telperion/docs/SHAPES_AUDIT_48H_2026-09-22.md
  section 4, rows 19 and 21, proposal P2; SHAPES_AUDIT_B sections N1, N5, D1, D5).  This module
  holds ONE copy of each such helper; E6Bridge6, 7, 8, 10, 11, 12 (and, for the shared majorant,
  every later consumer) import it and their copies are gone.

    A. The Gaussian integrability calculus (formerly E6Bridge8 section A): exp (-b x^2 + k x),
       exp (-b x^2 + k |x|), |x|^m exp (-b x^2 + k |x|) and x exp (-b x^2 + c x) are integrable
       for b > 0.
    B. The Gaussian moments at a COMPLEX frequency: M_1 (integral_mul_cexp_gaussian_fourier,
       formerly E6Bridge8) and M_2 (integral_sq_mul_cexp_gaussian_fourier: the complex-frequency
       form formerly E6Bridge16's primed lemma; E6Bridge11's real-frequency copy was its
       specialisation and is gone), each one integration by parts against Mathlib's
       fourierIntegral_gaussian.
    C. The tail envelope: a family bounded on a set S by a nonnegative summable majorant has
       ‖Sum'_S f‖ <= Sum' M (norm_tsum_subtype_le_tsum, the skeleton formerly repeated verbatim
       in E6Bridge7.tail_bound, E6Bridge12.tail_bound_window and E6Bridge17.ptail_bound), its
       E-scaled face, and the rate-splitting companion e^{2 lam phi} <= e^{2 (lam - 1) P} e^{2 phi}
       for lam >= 1, phi <= P.
    D. The shared local-count majorant Sum_rho m(rho) C/(1 + |gamma_rho|^2) over ALL rho : C
       (summable_mult_div_one_add_normSq, formerly E6Bridge6; Zeta23's zero_sum_inv_sq
       transported from the carrier subtype), and the Tannery transfer of a zero sum against it
       (tendsto_tsum_zeroMult_of_strip_bound: an n-uniform C/(1 + |z|^2) bound on the strip
       |Im z| <= 1/2 plus pointwise convergence there give convergence of the divisor-weighted
       zero sums; formerly inlined in E6Bridge6.gaussianTransfer_of_approx AND
       E6Bridge10.zeroSide_gaussTests_tendsto).
    E. The certified ordinate window |Im rho - c| <= D: winSet, zeroWindowSet, the finite
       zeroWindow and mem_zeroWindow (formerly E6Bridge12; consumed by E6Bridge12 and E6Bridge14).

  Kept where they are, deliberately: E6Bridge7's half-open window (Im rho_0 - 1, Im rho_0 + 1]
  and E6Bridge14's band [T1 - D, T2 + D] are different window shapes, not copies of zeroWindow;
  E6Bridge11's zero-frequency moments (integral_sq_mul_exp_neg_mul_sq and its cast) are stated in
  sqrt form and are not instances of M_2's cpow form; the sharper variants of E6Bridge16 and
  E6Bridge30 (bumpR_le', setIntegral_bumpR_le', re_digamma_quarter_ge_log',
  integral_indicator_bumpR_tail_le') refine E6Bridge11's originals with different hypotheses and
  both members of each pair are load-bearing in their own module.

  Every declaration here is a helper: no registry node statement lives in this module, no node
  theorem was moved, renamed or re-stated (each stays verbatim in its own artifact file), and
  there is no `sorry`.  Nothing here says anything about whether RH holds.
  conjecture1_proved = False.
-/
import E6Bridge4
import Zeta23.Statement.SeamClosed
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open Zeta23 Complex MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace RvMBridgeGauss
open WeilExplicit

/-! ## A. Gaussian majorants with an exponential weight. -/

/-- exp (-b x^2 + k x) is integrable for b > 0 (the norm of a complex Gaussian quadratic). -/
lemma integrable_exp_quadratic {b : ℝ} (hb : 0 < b) (k : ℝ) :
    Integrable (fun x : ℝ => Real.exp (-b * x ^ 2 + k * x)) := by
  have h := (integrable_cexp_quadratic (b := (b : ℂ)) (by simpa using hb) (k : ℂ) 0).norm
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  show ‖cexp _‖ = Real.exp _
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, pow_two]

/-- exp (-b x^2 + k |x|) is integrable for b > 0. -/
lemma integrable_exp_quadratic_abs {b : ℝ} (hb : 0 < b) (k : ℝ) :
    Integrable (fun x : ℝ => Real.exp (-b * x ^ 2 + k * |x|)) := by
  refine ((integrable_exp_quadratic hb k).add (integrable_exp_quadratic hb (-k))).mono'
    (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_neg hx]
    have : -b * x ^ 2 + k * -x = -b * x ^ 2 + -k * x := by ring
    rw [this]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

/-- |x|^m <= exp (m |x|). -/
lemma abs_pow_le_exp (x : ℝ) (m : ℕ) : |x| ^ m ≤ Real.exp (m * |x|) := by
  have h1 : |x| ≤ Real.exp |x| := by
    have := Real.add_one_le_exp |x|
    linarith
  calc |x| ^ m ≤ (Real.exp |x|) ^ m := pow_le_pow_left₀ (abs_nonneg x) h1 m
    _ = Real.exp (m * |x|) := by rw [← Real.exp_nat_mul]

/-- |x|^m exp (-b x^2 + k |x|) is integrable for b > 0. -/
lemma integrable_abs_pow_mul_exp_quadratic_abs {b : ℝ} (hb : 0 < b) (k : ℝ) (m : ℕ) :
    Integrable (fun x : ℝ => |x| ^ m * Real.exp (-b * x ^ 2 + k * |x|)) := by
  refine (integrable_exp_quadratic_abs hb (k + m)).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc |x| ^ m * Real.exp (-b * x ^ 2 + k * |x|)
      ≤ Real.exp (m * |x|) * Real.exp (-b * x ^ 2 + k * |x|) :=
        mul_le_mul_of_nonneg_right (abs_pow_le_exp x m) (Real.exp_pos _).le
    _ = Real.exp (-b * x ^ 2 + (k + m) * |x|) := by rw [← Real.exp_add]; congr 1; ring

/-- x * exp (-b x^2 + c x) is integrable for real b > 0 and complex c. -/
lemma integrable_mul_cexp_quadratic {b : ℝ} (hb : 0 < b) (c : ℂ) :
    Integrable (fun x : ℝ => (x : ℂ) * cexp (-(b : ℂ) * x ^ 2 + c * x)) := by
  refine (integrable_abs_pow_mul_exp_quadratic_abs hb |c.re| 1).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, pow_one]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg x)
  have hre : (-(b : ℂ) * (x : ℂ) ^ 2 + c * x).re = -b * x ^ 2 + c.re * x := by
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, pow_two]
  rw [hre]
  have : c.re * x ≤ |c.re| * |x| := by rw [← abs_mul]; exact le_abs_self _
  linarith

/-! ## B. The Gaussian moments M_1 and M_2 at a complex frequency: one integration by parts each
against fourierIntegral_gaussian.  Valid for EVERY complex w (no strip needed). -/

/-- ∫ u exp (-b u^2) exp (i w u) du = (i w / (2 b)) (pi/b)^{1/2} exp (-w^2/(4 b)), b > 0 real. -/
theorem integral_mul_cexp_gaussian_fourier {b : ℝ} (hb : 0 < b) (w : ℂ) :
    ∫ x : ℝ, (x : ℂ) * cexp (-(b : ℂ) * x ^ 2) * cexp (I * w * x)
      = (I * w / (2 * b)) * (((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ) * cexp (-w ^ 2 / (4 * b))) := by
  have hbC : 0 < (b : ℂ).re := by simpa using hb
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  -- derivatives of the two factors
  have hv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => cexp (-(b : ℂ) * (x : ℂ) ^ 2))
      (cexp (-(b : ℂ) * (x : ℂ) ^ 2) * (-(b : ℂ) * (2 * x))) x := by
    intro x
    have := (((hasDerivAt_pow 2 (x : ℂ)).const_mul (-(b : ℂ))).cexp).comp_ofReal
    convert this using 1
    push_cast
    ring
  have hu : ∀ x : ℝ, HasDerivAt (fun x : ℝ => cexp (I * w * (x : ℂ)))
      (cexp (I * w * (x : ℂ)) * (I * w)) x := by
    intro x
    have := (((hasDerivAt_id (x : ℂ)).const_mul (I * w)).cexp).comp_ofReal
    simpa using this
  -- integrability of the three products
  have hi1 : Integrable (fun x : ℝ => cexp (I * w * (x : ℂ))
      * (cexp (-(b : ℂ) * (x : ℂ) ^ 2) * (-(b : ℂ) * (2 * x)))) := by
    have h := (integrable_mul_cexp_quadratic hb (I * w)).const_mul (-(b : ℂ) * 2)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Complex.exp_add]
    ring
  have hi2 : Integrable (fun x : ℝ => cexp (I * w * (x : ℂ)) * (I * w)
      * cexp (-(b : ℂ) * (x : ℂ) ^ 2)) := by
    have h := (integrable_cexp_quadratic hbC (I * w) 0).const_mul (I * w)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [add_zero, Complex.exp_add]
    ring
  have hi3 : Integrable (fun x : ℝ => cexp (I * w * (x : ℂ)) * cexp (-(b : ℂ) * (x : ℂ) ^ 2)) := by
    have h := integrable_cexp_quadratic hbC (I * w) 0
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [add_zero, Complex.exp_add]
    ring
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hu x) (fun x _ => hv x)
    hi1 hi2 hi3
  have hG := fourierIntegral_gaussian hbC w
  -- rewrite both sides of key
  have hL : ∫ x : ℝ, cexp (I * w * (x : ℂ)) * (cexp (-(b : ℂ) * (x : ℂ) ^ 2) * (-(b : ℂ) * (2 * x)))
      = (-(b : ℂ) * 2) * ∫ x : ℝ, (x : ℂ) * cexp (-(b : ℂ) * x ^ 2) * cexp (I * w * x) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  have hR : ∫ x : ℝ, cexp (I * w * (x : ℂ)) * (I * w) * cexp (-(b : ℂ) * (x : ℂ) ^ 2)
      = (I * w) * ∫ x : ℝ, cexp (I * w * x) * cexp (-(b : ℂ) * x ^ 2) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hL, hR, hG] at key
  have h2 : (-(b : ℂ) * 2) ≠ 0 := by
    apply mul_ne_zero (neg_ne_zero.mpr hb0) two_ne_zero
  apply mul_left_cancel₀ h2
  rw [key]
  generalize ((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ) * cexp (-w ^ 2 / (4 * b)) = G
  field_simp

/-- The second Gaussian moment with a complex frequency: ∫ x^2 e^{-a x^2} e^{i w x} dx
= (1/(2a)) (M0 + i w M1) where M0, M1 are the zeroth and first moments; one integration by
parts (u = e^{iwx}, v = x e^{-a x^2}) with the integrability majorant |x|^2 e^{-a x^2 + |Im w| |x|}.
A real frequency is the case w = (r : ℂ). -/
theorem integral_sq_mul_cexp_gaussian_fourier {a : ℝ} (ha : 0 < a) (w : ℂ) :
    ∫ x : ℝ, (x : ℂ) ^ 2 * cexp (-(a : ℂ) * (x : ℂ) ^ 2) * cexp (I * w * (x : ℂ))
      = (1 / (2 * (a : ℂ)))
        * ((((Real.pi : ℂ) / a) ^ (1 / 2 : ℂ) * cexp (-w ^ 2 / (4 * a)))
          + I * w * ((I * w / (2 * a))
              * (((Real.pi : ℂ) / a) ^ (1 / 2 : ℂ) * cexp (-w ^ 2 / (4 * a))))) := by
  have haC : 0 < (a : ℂ).re := by simpa using ha
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have h2a : (2 * (a : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero ha0
  have hu : ∀ x : ℝ, HasDerivAt (fun x : ℝ => cexp (I * w * (x : ℂ)))
      (cexp (I * w * (x : ℂ)) * (I * w)) x := by
    intro x
    have := (((hasDerivAt_id (x : ℂ)).const_mul (I * w)).cexp).comp_ofReal
    simpa using this
  have hv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (x : ℂ) * cexp (-(a : ℂ) * (x : ℂ) ^ 2))
      (cexp (-(a : ℂ) * (x : ℂ) ^ 2) * (1 - 2 * a * (x : ℂ) ^ 2)) x := by
    intro x
    have hE : HasDerivAt (fun z : ℂ => -(a : ℂ) * z ^ 2) (-(a : ℂ) * (2 * x)) (x : ℂ) := by
      have := (hasDerivAt_pow 2 (x : ℂ)).const_mul (-(a : ℂ))
      refine this.congr_deriv ?_
      push_cast
      ring
    have h := ((hasDerivAt_id (x : ℂ)).mul hE.cexp).comp_ofReal
    refine h.congr_deriv ?_
    simp only [id]
    ring
  have hmaj : Integrable (fun x : ℝ => |x| ^ 2 * Real.exp (-a * x ^ 2 + |w.im| * |x|)) :=
    integrable_abs_pow_mul_exp_quadratic_abs ha |w.im| 2
  have hi_sq : Integrable (fun x : ℝ => (x : ℂ) ^ 2 * cexp (-(a : ℂ) * (x : ℂ) ^ 2)
      * cexp (I * w * (x : ℂ))) := by
    refine hmaj.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_exp, Complex.norm_exp,
      Real.norm_eq_abs]
    have h1 : (-(a : ℂ) * (x : ℂ) ^ 2).re = -a * x ^ 2 := by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, pow_two]
    have h2 : (I * w * (x : ℂ)).re = -(w.im * x) := by simp
    rw [h1, h2, mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.exp_le_exp]
    have : -(w.im * x) ≤ |w.im| * |x| := by
      rw [← abs_mul]
      exact neg_le_abs _
    linarith
  have hi_uv : Integrable (fun x : ℝ => cexp (I * w * (x : ℂ)) * cexp (-(a : ℂ) * (x : ℂ) ^ 2)) := by
    have h := integrable_cexp_quadratic haC (I * w) 0
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [add_zero, Complex.exp_add]
    ring
  have hi_xv : Integrable (fun x : ℝ => (x : ℂ) * cexp (-(a : ℂ) * (x : ℂ) ^ 2)
      * cexp (I * w * (x : ℂ))) := by
    have h := integrable_mul_cexp_quadratic ha (I * w)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Complex.exp_add]
    ring
  have hi1 : Integrable ((fun x : ℝ => cexp (I * w * (x : ℂ)))
      * fun x : ℝ => cexp (-(a : ℂ) * (x : ℂ) ^ 2) * (1 - 2 * a * (x : ℂ) ^ 2)) := by
    refine (hi_uv.sub (hi_sq.const_mul (2 * (a : ℂ)))).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply, Pi.sub_apply]
    ring
  have hi2 : Integrable ((fun x : ℝ => cexp (I * w * (x : ℂ)) * (I * w))
      * fun x : ℝ => (x : ℂ) * cexp (-(a : ℂ) * (x : ℂ) ^ 2)) := by
    refine (hi_xv.const_mul (I * w)).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply]
    ring
  have hi3 : Integrable ((fun x : ℝ => cexp (I * w * (x : ℂ)))
      * fun x : ℝ => (x : ℂ) * cexp (-(a : ℂ) * (x : ℂ) ^ 2)) := by
    refine hi_xv.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply]
    ring
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hu x) (fun x _ => hv x)
    hi1 hi2 hi3
  have hG := fourierIntegral_gaussian haC w
  have hM1 := integral_mul_cexp_gaussian_fourier ha w
  have hL : ∫ x : ℝ, cexp (I * w * (x : ℂ)) * (cexp (-(a : ℂ) * (x : ℂ) ^ 2) * (1 - 2 * a * (x : ℂ) ^ 2))
      = (∫ x : ℝ, cexp (I * w * (x : ℂ)) * cexp (-(a : ℂ) * (x : ℂ) ^ 2))
        - (2 * (a : ℂ)) * ∫ x : ℝ, (x : ℂ) ^ 2 * cexp (-(a : ℂ) * (x : ℂ) ^ 2) * cexp (I * w * (x : ℂ)) := by
    rw [← integral_const_mul, ← integral_sub hi_uv (hi_sq.const_mul _)]
    congr 1
    funext x
    ring
  have hR : ∫ x : ℝ, cexp (I * w * (x : ℂ)) * (I * w) * ((x : ℂ) * cexp (-(a : ℂ) * (x : ℂ) ^ 2))
      = (I * w) * ∫ x : ℝ, (x : ℂ) * cexp (-(a : ℂ) * (x : ℂ) ^ 2) * cexp (I * w * (x : ℂ)) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hL, hR, hG, hM1] at key
  set M2 := ∫ x : ℝ, (x : ℂ) ^ 2 * cexp (-(a : ℂ) * (x : ℂ) ^ 2) * cexp (I * w * (x : ℂ)) with hM2
  have hsolve : 2 * (a : ℂ) * M2
      = (((Real.pi : ℂ) / a) ^ (1 / 2 : ℂ) * cexp (-w ^ 2 / (4 * a)))
        + I * w * ((I * w / (2 * a)) * (((Real.pi : ℂ) / a) ^ (1 / 2 : ℂ) * cexp (-w ^ 2 / (4 * a)))) := by
    linear_combination -key
  rw [← hsolve]
  field_simp

/-! ## C. The tail envelope and the rate-splitting companion. -/

/-- The tail envelope: a family bounded on a set S by a nonnegative summable majorant M has
‖Sum'_{x : S} f x‖ <= Sum'_{x} M x, the whole-space sum of the majorant. -/
lemma norm_tsum_subtype_le_tsum {ι : Type*} {f : ι → ℂ} {M : ι → ℝ} (S : Set ι)
    (hM : Summable M) (hM0 : ∀ x, 0 ≤ M x) (hle : ∀ x : S, ‖f x‖ ≤ M x) :
    ‖∑' x : S, f x‖ ≤ ∑' x : ι, M x := by
  have hsumM : Summable (fun x : S => M x) := hM.subtype S
  have hsumN : Summable (fun x : S => ‖f x‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsumM
  calc ‖∑' x : S, f x‖
      ≤ ∑' x : S, ‖f x‖ := norm_tsum_le_tsum_norm hsumN
    _ ≤ ∑' x : S, M x := hsumN.tsum_le_tsum hle hsumM
    _ ≤ ∑' x : ι, M x := hM.tsum_subtype_le _ _ hM0

/-- The E-scaled face: ‖f x‖ <= E w x on S with w a nonnegative summable weight gives
‖Sum'_{x : S} f x‖ <= E Sum' w. -/
lemma norm_tsum_subtype_le_mul_tsum {ι : Type*} {f : ι → ℂ} {w : ι → ℝ} (S : Set ι) {E : ℝ}
    (hE : 0 ≤ E) (hw : Summable w) (hw0 : ∀ x, 0 ≤ w x) (hle : ∀ x : S, ‖f x‖ ≤ E * w x) :
    ‖∑' x : S, f x‖ ≤ E * ∑' x : ι, w x := by
  rw [← tsum_mul_left]
  exact norm_tsum_subtype_le_tsum S (hw.mul_left E) (fun x => mul_nonneg hE (hw0 x)) hle

/-- The rate-splitting companion: for lam >= 1 and phi <= P,
e^{2 lam phi} <= e^{2 (lam - 1) P} e^{2 phi} (the lam-dependence decouples from the summand). -/
lemma exp_two_mul_le_of_le {lam φ P : ℝ} (hlam : 1 ≤ lam) (hφ : φ ≤ P) :
    Real.exp (2 * lam * φ) ≤ Real.exp (2 * (lam - 1) * P) * Real.exp (2 * φ) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hφ (sub_nonneg.mpr hlam)]

/-! ## D. The shared local-count majorant over ALL rho : C, and the Tannery transfer. -/

/-- The weighted local-count majorant Sum_rho m(rho) C/(1 + |gamma_rho|^2) over ALL rho : C
(zero off the nontrivial zeros) is summable: Zeta23.WeilEF.zero_sum_inv_sq transported from the
carrier subtype. -/
lemma summable_mult_div_one_add_normSq (C : ℝ) :
    Summable (fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℝ) * (C / (1 + Complex.normSq (gammaOf ρ)))) := by
  set F : ℂ → ℝ := fun ρ => (WeilExplicit.zeroMult ρ : ℝ) * (C / (1 + Complex.normSq (gammaOf ρ)))
    with hF
  have hsub : Summable (F ∘ (Subtype.val : {ρ : ℂ | IsNontrivialZero ρ} → ℂ)) := by
    have h := (Zeta23.WeilEF.zero_sum_inv_sq zetaSeam).mul_left C
    refine h.congr fun ρ => ?_
    simp only [Function.comp, hF]
    have hm : (WeilExplicit.zeroMult ρ : ℝ) = (Zeta23.zeroMult ρ : ℝ) := by
      rw [RvMBridge4.zeroMult_eq_mult ρ.2]
      rfl
    rw [hm]
    ring
  rw [summable_subtype_iff_indicator] at hsub
  have hind : ({ρ : ℂ | IsNontrivialZero ρ} : Set ℂ).indicator F = F := by
    rw [Set.indicator_eq_self]
    intro ρ hρ
    by_contra hn
    apply hρ
    simp only [hF, RvMBridge4.zeroMult_eq_zero_of_not_nontrivial hn]
    simp
  rwa [hind] at hsub

/-- Tannery's theorem for a divisor-weighted zero sum: transforms H_n converging pointwise to G
on the strip |Im z| <= 1/2 with an n-uniform bound C/(1 + |z|^2) there give
Sum_rho m(rho) H_n(gamma_rho) -> Sum_rho m(rho) G(gamma_rho) (dominating function
m(rho) C/(1 + |gamma_rho|^2), summable by the local zero count).  The sums run over ALL rho : C;
off the nontrivial zeros the weight is 0 and nothing is assumed of H_n or G. -/
lemma tendsto_tsum_zeroMult_of_strip_bound {H : ℕ → ℂ → ℂ} {G : ℂ → ℂ} {C : ℝ}
    (hC : ∀ n (z : ℂ), |z.im| ≤ 1 / 2 → ‖H n z‖ ≤ C / (1 + Complex.normSq z))
    (hlim : ∀ z : ℂ, |z.im| ≤ 1 / 2 → Tendsto (fun n => H n z) atTop (𝓝 (G z))) :
    Tendsto (fun n => ∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) * H n (gammaOf ρ)) atTop
      (𝓝 (∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) * G (gammaOf ρ))) := by
  refine tendsto_tsum_of_dominated_convergence (summable_mult_div_one_add_normSq C) ?_
    (Filter.Eventually.of_forall fun n ρ => ?_)
  · intro ρ
    by_cases h : IsNontrivialZero ρ
    · exact ((hlim (gammaOf ρ) (Zeta23.WeilEF.abs_gammaOf_im_lt h.2).le).const_mul _)
    · simp only [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial h, Nat.cast_zero, zero_mul]
      exact tendsto_const_nhds
  · rw [norm_mul, Complex.norm_natCast]
    by_cases h : IsNontrivialZero ρ
    · exact mul_le_mul_of_nonneg_left
        (hC n (gammaOf ρ) (Zeta23.WeilEF.abs_gammaOf_im_lt h.2).le) (Nat.cast_nonneg _)
    · rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial h]
      simp

/-! ## E. The certified ordinate window |Im rho - c| <= D. -/

/-- The ordinate window as an index set. -/
def winSet (c D : ℝ) : Set ℂ := {ρ : ℂ | |ρ.im - c| ≤ D}

/-- The nontrivial zeros with |Im rho - c| <= D: finite by the local zero count
(Zeta23.zetaSeam.finite_window). -/
def zeroWindowSet (c D : ℝ) : Set ℂ := {ρ | IsNontrivialZero ρ} ∩ winSet c D

lemma zeroWindowSet_finite (c D : ℝ) : (zeroWindowSet c D).Finite := by
  refine (zetaSeam.finite_window (c - D - 1) (c + D)).subset ?_
  rintro ρ ⟨hnt, hw⟩
  have hw' : |ρ.im - c| ≤ D := hw
  have h := abs_le.mp hw'
  exact ⟨hnt, by linarith [h.1], by linarith [h.2]⟩

/-- The certified window as a Finset. -/
def zeroWindow (c D : ℝ) : Finset ℂ := (zeroWindowSet_finite c D).toFinset

lemma mem_zeroWindow {c D : ℝ} {ρ : ℂ} :
    ρ ∈ zeroWindow c D ↔ IsNontrivialZero ρ ∧ |ρ.im - c| ≤ D := by
  unfold zeroWindow
  rw [Set.Finite.mem_toFinset]
  rfl

end RvMBridgeGauss
