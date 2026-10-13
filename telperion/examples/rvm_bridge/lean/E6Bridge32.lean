/-
  E6Bridge32 -- the archimedean integral in u-space, part 1 (2026-09-23): the exponential-kernel
  series lower bound behind the prime-free window (companion of E6Bridge31).

  For the goal node's test f = autocorr g, h(r) = |ĝ(r)|^2 and psiR(r) = Re psi(1/4 + i r/2),
  the vertical-line digamma series (Zeta23 re_digamma_vertical, as E6Bridge30 psiR_ge_series)

      psiR(r) >= -gamma - lor(1/2, r) + sum_{n<N} [ 1/(n+1) - lor(b_n, r) ],
      lor(b, r) = 2b / (b^2 + r^2),  b_n = 2n + 5/2,

  is paired with h through the Lorentzian pair  e^{-b|u|} <-> 2b/(b^2 + r^2)  (Mathlib's Fourier
  inversion, in Zeta23's paper_inversion spelling, applied to f, and Fubini):

      (1/2pi) ∫ h(r) lor(b, r) dr = Re ∫ f(u) e^{-b|u|} du                     (theorem pairing)

  so that

      (1/2pi) ∫ h psiR >= (-gamma + sum_{n<N} 1/(n+1)) f(0)
                          - Re ∫ f e^{-|u|/2} - sum_{n<N} Re ∫ f e^{-b_n |u|}      (re_arch_integral_ge).

  This is the exact u-space shape of the archimedean Weil distribution truncated at N (the tail
  is nonnegative termwise); E6Bridge33 turns each  f(0) ∫ e^{-b|u|} - Re ∫ f e^{-b|u|}  into the
  Dirichlet form (1/2) ∫∫ |g(v) - g(w)|^2 e^{-b|v-w|} and bounds it from the support of g.

  No zeros, no RH progress.  conjecture1_proved = False.
-/
import E6Bridge31

open Zeta23 Complex MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace RvMBridge32
open WeilExplicit RvMBridge11 RvMBridge30 RvMBridge31

/-! ## A. The exponential kernel and the Lorentzian. -/

/-- e^{-b|u|}. -/
def expK (b u : ℝ) : ℝ := Real.exp (-b * |u|)

/-- 2b / (b^2 + r^2). -/
def lor (b r : ℝ) : ℝ := 2 * b / (b ^ 2 + r ^ 2)

lemma expK_nonneg (b u : ℝ) : 0 ≤ expK b u := (Real.exp_pos _).le

lemma continuous_expK (b : ℝ) : Continuous (expK b) := by
  unfold expK
  fun_prop

lemma lor_nonneg {b : ℝ} (hb : 0 < b) (r : ℝ) : 0 ≤ lor b r := by
  unfold lor
  positivity

lemma lor_le {b : ℝ} (hb : 0 < b) (r : ℝ) : lor b r ≤ 2 / b := by
  unfold lor
  rw [div_le_div_iff₀ (by positivity) hb]
  nlinarith [sq_nonneg r, sq_nonneg b]

lemma lor_neg (b r : ℝ) : lor b (-r) = lor b r := by
  unfold lor
  rw [neg_sq]

lemma continuous_lor {b : ℝ} (hb : 0 < b) : Continuous (lor b) := by
  unfold lor
  refine continuous_const.div (by fun_prop) fun r => ?_
  positivity

/-- e^{-x} <= 2/(1 + x^2) (from 1 + x + x^2/2 <= e^x), in the kernel's spelling. -/
lemma expK_le_two_div {b : ℝ} (hb : 0 < b) (u : ℝ) : expK b u ≤ 2 * (1 + (b * u) ^ 2)⁻¹ := by
  unfold expK
  have hx : 0 ≤ b * |u| := by positivity
  have hpos := Real.exp_pos (b * |u|)
  have h := Real.quadratic_le_exp_of_nonneg hx
  have h2 : 1 + (b * u) ^ 2 ≤ 2 * Real.exp (b * |u|) := by
    rw [mul_pow, ← sq_abs u, ← mul_pow]
    nlinarith
  rw [show -b * |u| = -(b * |u|) by ring, Real.exp_neg, ← one_div, ← one_div, mul_one_div,
    div_le_div_iff₀ hpos (by positivity)]
  linarith

lemma integrable_expK {b : ℝ} (hb : 0 < b) : Integrable (expK b) := by
  have h1 : Integrable (fun u : ℝ => 2 * (1 + (b * u) ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq.comp_mul_left' hb.ne').const_mul 2
  refine h1.mono' (continuous_expK b).aestronglyMeasurable ?_
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_of_nonneg (expK_nonneg b u)]
  exact expK_le_two_div hb u

/-! ## B. The Lorentzian pair: ∫ e^{-b|x|} e^{i ω x} dx = 2b/(b^2 + ω^2). -/

lemma integrable_expK_mul_cexp {b : ℝ} (hb : 0 < b) (ω : ℝ) :
    Integrable (fun x : ℝ => (expK b x : ℂ) * cexp (I * ω * x)) := by
  refine ((integrable_expK hb).ofReal).mul_bdd (c := 1) (by fun_prop) ?_
  filter_upwards with x
  rw [Complex.norm_exp]
  simp

lemma sub_I_mul_ne_zero {b : ℝ} (hb : 0 < b) (ω : ℝ) : ((b : ℂ) - I * ω) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

lemma add_I_mul_ne_zero {b : ℝ} (hb : 0 < b) (ω : ℝ) : ((b : ℂ) + I * ω) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

/-- The right half-line. -/
lemma integral_Ioi_expK_cexp {b : ℝ} (hb : 0 < b) (ω : ℝ) :
    ∫ x in Set.Ioi (0 : ℝ), (expK b x : ℂ) * cexp (I * ω * x) = 1 / ((b : ℂ) - I * ω) := by
  have h : ∫ x in Set.Ioi (0 : ℝ), (expK b x : ℂ) * cexp (I * ω * x)
      = ∫ x in Set.Ioi (0 : ℝ), cexp ((-(b : ℂ) + I * ω) * x) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    unfold expK
    rw [abs_of_pos hx, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hre : (-(b : ℂ) + I * ω).re < 0 := by
    simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.I_re, Complex.I_im]
    linarith
  rw [h, integral_exp_mul_complex_Ioi hre 0]
  have hne : (-(b : ℂ) + I * ω) ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.zero_re] at this
    linarith
  rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    div_eq_div_iff hne (sub_I_mul_ne_zero hb ω)]
  ring

/-- The left half-line. -/
lemma integral_Iic_expK_cexp {b : ℝ} (hb : 0 < b) (ω : ℝ) :
    ∫ x in Set.Iic (0 : ℝ), (expK b x : ℂ) * cexp (I * ω * x) = 1 / ((b : ℂ) + I * ω) := by
  have h := integral_comp_neg_Iic (0 : ℝ)
    (fun y : ℝ => (expK b (-y) : ℂ) * cexp (I * ω * ((-y : ℝ) : ℂ)))
  simp only [neg_neg, neg_zero] at h
  rw [h]
  have h2 : ∫ y in Set.Ioi (0 : ℝ), (expK b (-y) : ℂ) * cexp (I * ω * ((-y : ℝ) : ℂ))
      = ∫ y in Set.Ioi (0 : ℝ), cexp ((-(b : ℂ) - I * ω) * y) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    unfold expK
    rw [abs_neg, abs_of_pos hy, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hre : (-(b : ℂ) - I * ω).re < 0 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.I_re, Complex.I_im]
    linarith
  rw [h2, integral_exp_mul_complex_Ioi hre 0]
  have hne : (-(b : ℂ) - I * ω) ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0
    simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.zero_re] at this
    linarith
  rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    div_eq_div_iff hne (add_I_mul_ne_zero hb ω)]
  ring

/-- THE LORENTZIAN PAIR. -/
theorem integral_expK_mul_cexp {b : ℝ} (hb : 0 < b) (ω : ℝ) :
    ∫ x : ℝ, (expK b x : ℂ) * cexp (I * ω * x) = (lor b ω : ℂ) := by
  rw [← integral_add_compl (μ := volume) measurableSet_Ioi (integrable_expK_mul_cexp hb ω),
    Set.compl_Ioi, integral_Ioi_expK_cexp hb ω, integral_Iic_expK_cexp hb ω]
  unfold lor
  have h1 := sub_I_mul_ne_zero hb ω
  have h2 := add_I_mul_ne_zero hb ω
  have h3 : ((b : ℂ) ^ 2 + (ω : ℂ) ^ 2) ≠ 0 := by
    intro h0
    have h0' : ((b ^ 2 + ω ^ 2 : ℝ) : ℂ) = 0 := by push_cast; exact h0
    have := Complex.ofReal_eq_zero.mp h0'
    nlinarith [sq_nonneg ω, sq_nonneg b]
  push_cast
  rw [div_add_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) h3]
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ## C. The pairing (1/2pi) ∫ h lor_b = Re ∫ f e^{-b|u|}. -/

lemma continuous_hsq {g : ℝ → ℂ} (hg : IsWeilTest g) : Continuous (hsq g) := by
  unfold hsq
  exact (RvMBridge4.continuous_paperFT_real hg).norm.pow 2

/-- Paper inversion for f = autocorr g, with h in place of paperFT f. -/
lemma autocorr_inversion {g : ℝ → ℂ} (hg : IsWeilTest g) (u : ℝ) :
    autocorr g u = (1 / (2 * (Real.pi : ℂ))) * ∫ r : ℝ, (hsq g r : ℂ) * cexp (-I * r * u) := by
  have hf := RvMBridge5.isWeilTest_autocorr hg
  have hk2 := RvMBridge4.contDiff_two_of_test hf
  have h := Zeta23.EF.paper_inversion hk2.continuous
    (hk2.continuous.integrable_of_hasCompactSupport hf.2)
    (Zeta23.EF.integrable_fourier_of_contDiff_two hk2 hf.2) u
  rw [h]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp only
  rw [paperFT_autocorr_eq hg]

/-- The Fubini integrand of the pairing is integrable on the plane. -/
lemma integrable_pairing_integrand {g : ℝ → ℂ} (hg : IsWeilTest g) {b : ℝ} (hb : 0 < b) :
    Integrable (Function.uncurry fun (u r : ℝ) =>
      (hsq g r : ℂ) * cexp (-I * r * u) * (expK b u : ℂ)) (volume.prod volume) := by
  have hprod : Integrable (fun z : ℝ × ℝ => expK b z.1 * hsq g z.2) (volume.prod volume) :=
    (integrable_expK hb).mul_prod (integrable_hsq hg)
  refine hprod.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    have h1 : Continuous fun z : ℝ × ℝ => (hsq g z.2 : ℂ) :=
      Complex.continuous_ofReal.comp ((continuous_hsq hg).comp continuous_snd)
    have h2 : Continuous fun z : ℝ × ℝ => (expK b z.1 : ℂ) :=
      Complex.continuous_ofReal.comp ((continuous_expK b).comp continuous_fst)
    have h3 : Continuous fun z : ℝ × ℝ => cexp (-I * (z.2 : ℂ) * (z.1 : ℂ)) := by fun_prop
    exact (h1.mul h3).mul h2
  · filter_upwards with z
    show ‖(hsq g z.2 : ℂ) * cexp (-I * (z.2 : ℂ) * (z.1 : ℂ)) * (expK b z.1 : ℂ)‖
      ≤ expK b z.1 * hsq g z.2
    rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_exp, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    apply le_of_eq
    rw [show (-I * (z.2 : ℂ) * (z.1 : ℂ)).re = 0 by
        simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
        ring,
      Real.exp_zero, mul_one, abs_of_nonneg (hsq_nonneg g _), abs_of_nonneg (expK_nonneg b _),
      mul_comm]

/-- THE PAIRING: ∫ f e^{-b|u|} = (1/2pi) ∫ h lor_b. -/
theorem pairing {g : ℝ → ℂ} (hg : IsWeilTest g) {b : ℝ} (hb : 0 < b) :
    ∫ u : ℝ, autocorr g u * (expK b u : ℂ)
      = (1 / (2 * (Real.pi : ℂ))) * ((∫ r : ℝ, hsq g r * lor b r : ℝ) : ℂ) := by
  have hF := integrable_pairing_integrand hg hb
  calc ∫ u : ℝ, autocorr g u * (expK b u : ℂ)
      = ∫ u : ℝ, (1 / (2 * (Real.pi : ℂ)))
          * ∫ r : ℝ, (hsq g r : ℂ) * cexp (-I * r * u) * (expK b u : ℂ) := by
        congr 1
        funext u
        rw [autocorr_inversion hg u, mul_assoc, ← integral_mul_const]
    _ = (1 / (2 * (Real.pi : ℂ)))
          * ∫ u : ℝ, ∫ r : ℝ, (hsq g r : ℂ) * cexp (-I * r * u) * (expK b u : ℂ) := by
        rw [integral_const_mul]
    _ = (1 / (2 * (Real.pi : ℂ)))
          * ∫ r : ℝ, ∫ u : ℝ, (hsq g r : ℂ) * cexp (-I * r * u) * (expK b u : ℂ) := by
        rw [integral_integral_swap hF]
    _ = (1 / (2 * (Real.pi : ℂ))) * ∫ r : ℝ, (hsq g r : ℂ) * (lor b r : ℂ) := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
        simp only
        have h := integral_expK_mul_cexp hb (-r)
        rw [lor_neg] at h
        rw [← h, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        simp only
        push_cast
        ring_nf
    _ = (1 / (2 * (Real.pi : ℂ))) * ((∫ r : ℝ, hsq g r * lor b r : ℝ) : ℂ) := by
        rw [← integral_complex_ofReal]
        push_cast
        rfl

/-- The real form of the pairing. -/
theorem integral_hsq_mul_lor {g : ℝ → ℂ} (hg : IsWeilTest g) {b : ℝ} (hb : 0 < b) :
    ∫ r : ℝ, hsq g r * lor b r
      = 2 * Real.pi * (∫ u : ℝ, autocorr g u * (expK b u : ℂ)).re := by
  rw [pairing hg hb]
  rw [show (1 / (2 * (Real.pi : ℂ))) * ((∫ r : ℝ, hsq g r * lor b r : ℝ) : ℂ)
      = (((1 / (2 * Real.pi)) * ∫ r : ℝ, hsq g r * lor b r : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_re]
  field_simp

lemma integrable_hsq_mul_lor {g : ℝ → ℂ} (hg : IsWeilTest g) {b : ℝ} (hb : 0 < b) :
    Integrable (fun r : ℝ => hsq g r * lor b r) := by
  refine (integrable_hsq hg).mul_bdd (c := 2 / b) (continuous_lor hb).aestronglyMeasurable ?_
  filter_upwards with r
  rw [Real.norm_eq_abs, abs_of_nonneg (lor_nonneg hb r)]
  exact lor_le hb r

/-! ## D. The finite series lower bound. -/

/-- b_n = 2n + 5/2, the n-th Lorentzian abscissa of the digamma series (a = 1/4, t = r/2). -/
def bN (n : ℕ) : ℝ := 2 * n + 5 / 2

lemma bN_pos (n : ℕ) : 0 < bN n := by unfold bN; positivity

/-- The series term serF (r/2) n = 1/(n+1) - lor (b_n) r. -/
lemma serF_eq_lor (r : ℝ) (n : ℕ) : serF (r / 2) n = 1 / ((n : ℝ) + 1) - lor (bN n) r := by
  unfold serF lor bN
  have h1 : ((n : ℝ) + 1 + 1 / 4) ^ 2 + (r / 2) ^ 2 ≠ 0 := by positivity
  have h2 : (2 * (n : ℝ) + 5 / 2) ^ 2 + r ^ 2 ≠ 0 := by positivity
  rw [sub_eq_sub_iff_sub_eq_sub, sub_self, eq_comm, sub_eq_zero, div_eq_div_iff h1 h2]
  ring

/-- The a-term of the series is the b = 1/2 Lorentzian. -/
lemma lor_half_eq (r : ℝ) : (1 / 4 : ℝ) / ((1 / 4) ^ 2 + (r / 2) ^ 2) = lor (1 / 2) r := by
  unfold lor
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- The pointwise finite lower bound (E6Bridge30 psiR_ge_series with M = 0). -/
theorem psiR_ge_finite (r : ℝ) (N : ℕ) :
    -Real.eulerMascheroniConstant - lor (1 / 2) r
      + ∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1) - lor (bN n) r) ≤ psiR r := by
  have h := psiR_ge_series r N 0
  simp only [Nat.cast_zero, add_zero, sub_self] at h
  rw [lor_half_eq] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  exact Finset.sum_congr rfl fun n _ => (serF_eq_lor r n).symm

/-- The truncated weight φ_N(r). -/
def phiN (N : ℕ) (r : ℝ) : ℝ :=
  -Real.eulerMascheroniConstant - lor (1 / 2) r
    + ∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1) - lor (bN n) r)

lemma integrable_hsq_mul_phiN {g : ℝ → ℂ} (hg : IsWeilTest g) (N : ℕ) :
    Integrable (fun r : ℝ => hsq g r * phiN N r) := by
  have hh := integrable_hsq hg
  have hfun : (fun r : ℝ => hsq g r * phiN N r)
      = fun r => (-Real.eulerMascheroniConstant) * hsq g r - hsq g r * lor (1 / 2) r
        + ∑ n ∈ Finset.range N, ((1 / ((n : ℝ) + 1)) * hsq g r - hsq g r * lor (bN n) r) := by
    funext r
    unfold phiN
    rw [mul_add, Finset.mul_sum]
    have hin : ∀ n ∈ Finset.range N, hsq g r * (1 / ((n : ℝ) + 1) - lor (bN n) r)
        = (1 / ((n : ℝ) + 1)) * hsq g r - hsq g r * lor (bN n) r := fun n _ => by ring
    rw [Finset.sum_congr rfl hin]
    ring
  rw [hfun]
  have hA : Integrable (fun r : ℝ => (-Real.eulerMascheroniConstant) * hsq g r
      - hsq g r * lor (1 / 2) r) :=
    (hh.const_mul _).sub (integrable_hsq_mul_lor hg (by norm_num))
  have hB : Integrable (fun r : ℝ => ∑ n ∈ Finset.range N,
      ((1 / ((n : ℝ) + 1)) * hsq g r - hsq g r * lor (bN n) r)) :=
    integrable_finsetSum _ fun n _ => (hh.const_mul _).sub (integrable_hsq_mul_lor hg (bN_pos n))
  exact hA.add hB

/-- ∫ h φ_N in closed form through the pairings. -/
theorem integral_hsq_mul_phiN {g : ℝ → ℂ} (hg : IsWeilTest g) (N : ℕ) :
    ∫ r : ℝ, hsq g r * phiN N r
      = 2 * Real.pi * ((-Real.eulerMascheroniConstant
          + ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1)) * mass g
        - (∫ u : ℝ, autocorr g u * (expK (1 / 2) u : ℂ)).re
        - ∑ n ∈ Finset.range N, (∫ u : ℝ, autocorr g u * (expK (bN n) u : ℂ)).re) := by
  have hh := integrable_hsq hg
  have hfun : (fun r : ℝ => hsq g r * phiN N r)
      = fun r => (-Real.eulerMascheroniConstant) * hsq g r - hsq g r * lor (1 / 2) r
        + ∑ n ∈ Finset.range N, ((1 / ((n : ℝ) + 1)) * hsq g r - hsq g r * lor (bN n) r) := by
    funext r
    unfold phiN
    rw [mul_add, Finset.mul_sum]
    have hin : ∀ n ∈ Finset.range N, hsq g r * (1 / ((n : ℝ) + 1) - lor (bN n) r)
        = (1 / ((n : ℝ) + 1)) * hsq g r - hsq g r * lor (bN n) r := fun n _ => by ring
    rw [Finset.sum_congr rfl hin]
    ring
  have hA : Integrable (fun r : ℝ => (-Real.eulerMascheroniConstant) * hsq g r
      - hsq g r * lor (1 / 2) r) :=
    (hh.const_mul _).sub (integrable_hsq_mul_lor hg (by norm_num))
  have hA1 : Integrable (fun r : ℝ => (-Real.eulerMascheroniConstant) * hsq g r) := hh.const_mul _
  have hA2 : Integrable (fun r : ℝ => hsq g r * lor (1 / 2) r) := integrable_hsq_mul_lor hg (by norm_num)
  have hBn : ∀ n ∈ Finset.range N, Integrable (fun r : ℝ =>
      (1 / ((n : ℝ) + 1)) * hsq g r - hsq g r * lor (bN n) r) :=
    fun n _ => (hh.const_mul _).sub (integrable_hsq_mul_lor hg (bN_pos n))
  have hB : Integrable (fun r : ℝ => ∑ n ∈ Finset.range N,
      ((1 / ((n : ℝ) + 1)) * hsq g r - hsq g r * lor (bN n) r)) :=
    integrable_finsetSum _ hBn
  rw [hfun, integral_add hA hB, integral_sub hA1 hA2, integral_finsetSum _ hBn, integral_const_mul,
    integral_hsq hg, integral_hsq_mul_lor hg (by norm_num)]
  have hsum : ∀ n ∈ Finset.range N,
      ∫ r : ℝ, ((1 / ((n : ℝ) + 1)) * hsq g r - hsq g r * lor (bN n) r)
        = (1 / ((n : ℝ) + 1)) * (2 * Real.pi * mass g)
          - 2 * Real.pi * (∫ u : ℝ, autocorr g u * (expK (bN n) u : ℂ)).re := by
    intro n _
    have h1 : Integrable (fun r : ℝ => (1 / ((n : ℝ) + 1)) * hsq g r) := hh.const_mul _
    have h2 : Integrable (fun r : ℝ => hsq g r * lor (bN n) r) := integrable_hsq_mul_lor hg (bN_pos n)
    rw [integral_sub h1 h2, integral_const_mul, integral_hsq hg, integral_hsq_mul_lor hg (bN_pos n)]
  rw [Finset.sum_congr rfl hsum, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- THE SERIES LOWER BOUND for the archimedean integral, at every truncation N. -/
theorem re_arch_integral_ge {g : ℝ → ℂ} (hg : IsWeilTest g) (N : ℕ) :
    (-Real.eulerMascheroniConstant + ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1)) * mass g
      - (∫ u : ℝ, autocorr g u * (expK (1 / 2) u : ℂ)).re
      - ∑ n ∈ Finset.range N, (∫ u : ℝ, autocorr g u * (expK (bN n) u : ℂ)).re
    ≤ (1 / (2 * Real.pi)) * ∫ r : ℝ, hsq g r * psiR r := by
  have hmono : ∫ r : ℝ, hsq g r * phiN N r ≤ ∫ r : ℝ, hsq g r * psiR r :=
    integral_mono (integrable_hsq_mul_phiN hg N) (integrable_hsq_mul_psiR hg) fun r =>
      mul_le_mul_of_nonneg_left (psiR_ge_finite r N) (hsq_nonneg g r)
  rw [integral_hsq_mul_phiN hg N] at hmono
  have hpi := Real.pi_pos
  have h := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))
  refine le_trans (le_of_eq ?_) h
  field_simp

end RvMBridge32
