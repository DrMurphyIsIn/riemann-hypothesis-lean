/-
  E6Bridge28 -- THE LI LADDER on the rvm island (2026-09-21; Li face brief, section 5).

  E6Bridge15 proved that the symmetric window sums of Li's kernel converge to
      liLimit N = Sum'_rho m(rho) Re (1 - (1 - 1/rho)^N)        (absolutely convergent),
  and E6Bridge27 proved the Bombieri-Lagarias value identity liLimit N = archSide N + finiteSide N
  (N >= 1).  This module asks what the SIGN of liLimit N costs, rung by rung.

  PROVED (kernel-checked, no `sorry`):
    * the divisor is symmetric under rho -> 1 - conj rho (E6Bridge6's zeroMult_reflect, restated);
    * the pair identity: with w = rho/(rho - 1) = r e^{i theta},
        Re K_N(rho) + Re K_N(1 - conj rho) = 2 - (r^N + r^{-N}) cos (N theta)
                                         = 2 - 2 cosh (N log r) cos (N theta);
    * Lemma A: cosh a cos b <= 1 whenever |a| <= |b| <= pi/2 (two antitone arguments);
    * Lemma B: for a strip point with |Im rho| >= 1,
        |theta| = arctan (beta/|gamma|) + arctan ((1-beta)/|gamma|),
        1/(2|gamma|) <= |theta| <= 1/|gamma|,   |log r| <= 1/(2 gamma^2);
    * Theorem C (termwise): |Im rho| >= 1 and N <= 3 pi |Im rho| / 2 give a nonnegative pair
      term, whether or not rho is on the line (b = N theta: |b| <= pi/2 is Lemma A, and
      pi/2 <= |b| <= 3 pi/2 has cos b <= 0, so the term is >= 2: the factor 3 of the survey);
    * Theorem D (the ladder): if every nontrivial zero with |Im rho| <= T (T >= 1) has real part
      1/2, then 0 <= Re (liLimit N) for every N <= 3 pi T / 2
      (liLimit_re_nonneg_of_line_below), and hence 0 <= Re (archSide N + finiteSide N)
      (E6Bridge27's liValue is hypothesis-free);
    * rung N = 1 with NO hypothesis: liLimit_one_re_nonneg, since K_1(rho) = 1/rho has real part
      Re rho / |rho|^2 > 0 on the strip;
    * the low-height box (section 4 of the brief): a nontrivial zero sigma + i t satisfies
      4 sigma^2 <= (1 - sigma)^2 + t^2 and its reflection, hence |t| >= sqrt 3 / 2 (Box 1) and
      (sigma - 1/2)^2 <= t^2/3 - 1/4 (Box 2), from Zeta23's summation-by-parts representation
      Zeta0EqZeta at N = 1 and the SHARP bound |int_1^infty {x} x^{-s-1} dx| <= 1/(2 Re s)
      (integration by parts on each unit interval);
    * hypothesis-free rungs N = 2, 3, 4, 5: termwise (UNPAIRED) positivity of Re K_N(rho) on the
      box, i.e. Re (A + i gamma)^N <= P^N with A = beta^2 - beta + gamma^2, P = |rho|^2; N = 2, 3
      need only A >= 0, N = 4 needs Box 1 (6 A^2 >= gamma^2), N = 5 needs Box 2 through the
      parametrisation u = beta - 1/2, e = gamma^2 - 3u^2 - 3/4 >= 0 (the polynomial is
      Sum_k c_k(u) e^k with c_k > 0 on |u| <= 1/2; min c_0 = 0.27).  Rung N = 6 FAILS termwise
      inside the box (at beta = 0.29, gamma = 0.939 (inside Box 2)), so N <= 5 is the reach of this method.

  The regrouping of the tsum uses the involution rho <-> 1 - conj rho as an equivalence of C,
  summability from E6Bridge15 (summable_liPaired), and the real part of the HasSum.

  NOTHING here proves anything about RH: Theorem D consumes zero localisation (a hypothesis, or
  the finite box) and produces sign information about finitely many Li coefficients.
  conjecture1_proved = False.
-/
import E6Bridge27
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

open Zeta23 Complex MeasureTheory Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace RvMBridge28
open RvMBridge15 RvMBridge15.BombieriLagarias

/-! ## A. The divisor is symmetric under rho -> 1 - conj rho. -/

/-- m(1 - conj rho) = m(rho): Zeta23's reflection symmetry of the divisor (E6Bridge6). -/
theorem zeroMult_one_sub_conj (ρ : ℂ) :
    WeilExplicit.zeroMult (1 - conj ρ) = WeilExplicit.zeroMult ρ :=
  RvMBridge6.zeroMult_reflect ρ

lemma isNontrivialZero_one_sub_conj {ρ : ℂ} (h : IsNontrivialZero ρ) :
    IsNontrivialZero (1 - conj ρ) :=
  Zeta23.zeta_reflect_zero ρ h

/-! ## B. The pair identity in polar form. -/

/-- w(rho) = rho/(rho - 1) = (1 - 1/rho)^{-1}. -/
def wOf (ρ : ℂ) : ℂ := ρ / (ρ - 1)

lemma wOf_ne_zero {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) : wOf ρ ≠ 0 := by
  unfold wOf
  exact div_ne_zero h0 (sub_ne_zero.mpr h1)

lemma one_sub_inv_eq_inv_wOf {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) : 1 - 1 / ρ = (wOf ρ)⁻¹ := by
  unfold wOf
  have h1' : ρ - 1 ≠ 0 := sub_ne_zero.mpr h1
  rw [inv_div]
  field_simp

lemma one_sub_inv_one_sub_conj {ρ : ℂ} (h1 : ρ ≠ 1) :
    1 - 1 / (1 - conj ρ) = conj (wOf ρ) := by
  unfold wOf
  have h2 : (1 : ℂ) - conj ρ ≠ 0 := by
    intro h
    apply h1
    have := congrArg conj h
    rw [map_sub, map_one, Complex.conj_conj, map_zero] at this
    exact (sub_eq_zero.mp this).symm
  have h3 : conj ρ - 1 ≠ 0 := by
    intro h; apply h2; linear_combination -h
  rw [map_div₀, map_sub, map_one]
  field_simp
  ring

lemma liKernel_eq_inv_wOf {N : ℕ} {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    liKernel N ρ = 1 - ((wOf ρ)⁻¹) ^ N := by
  unfold liKernel
  rw [one_sub_inv_eq_inv_wOf h0 h1]

lemma liKernel_one_sub_conj {N : ℕ} {ρ : ℂ} (h1 : ρ ≠ 1) :
    liKernel N (1 - conj ρ) = conj (1 - (wOf ρ) ^ N) := by
  unfold liKernel
  rw [one_sub_inv_one_sub_conj h1, map_sub, map_one, map_pow]

/-- Re (z^N) = |z|^N cos (N arg z). -/
lemma re_pow_eq (z : ℂ) (N : ℕ) : (z ^ N).re = ‖z‖ ^ N * Real.cos (N * arg z) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
  rw [mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_pow,
    show (N : ℂ) * ((arg z : ℂ) * I) = ((N * arg z : ℝ) : ℂ) * I by push_cast; ring,
    Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- Re (z^{-N}) = |z|^{-N} cos (N arg z). -/
lemma re_inv_pow_eq (z : ℂ) (N : ℕ) :
    ((z⁻¹) ^ N).re = (‖z‖⁻¹) ^ N * Real.cos (N * arg z) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
  rw [mul_inv, ← Complex.exp_neg, mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_inv,
    ← Complex.ofReal_pow,
    show (N : ℂ) * (-((arg z : ℂ) * I)) = ((-(N * arg z) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-- **The pair identity.**  Re K_N(rho) + Re K_N(1 - conj rho) = 2 - (r^N + r^{-N}) cos (N theta),
with r = |w|, theta = arg w, w = rho/(rho - 1). -/
theorem pair_re_eq {N : ℕ} {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    (liKernel N ρ).re + (liKernel N (1 - conj ρ)).re
      = 2 - (‖wOf ρ‖ ^ N + (‖wOf ρ‖⁻¹) ^ N) * Real.cos (N * arg (wOf ρ)) := by
  rw [liKernel_eq_inv_wOf h0 h1, liKernel_one_sub_conj h1, Complex.conj_re, Complex.sub_re,
    Complex.sub_re, Complex.one_re, re_inv_pow_eq, re_pow_eq]
  ring

/-- r^N + r^{-N} = 2 cosh (N log r) for r > 0. -/
lemma pow_add_inv_pow_eq_cosh {r : ℝ} (hr : 0 < r) (N : ℕ) :
    r ^ N + (r⁻¹) ^ N = 2 * Real.cosh (N * Real.log r) := by
  rw [Real.cosh_eq, Real.exp_nat_mul, Real.exp_log hr,
    show -((N : ℝ) * Real.log r) = N * (-Real.log r) by ring,
    Real.exp_nat_mul, Real.exp_neg, Real.exp_log hr]
  ring

/-! ## C. Lemma A: cosh a cos b <= 1 for |a| <= |b| <= pi/2. -/

/-- g(x) = sinh x cos x - cosh x sin x is nonpositive on [0, pi] (g(0) = 0, g' = -2 sinh sin). -/
lemma sinh_mul_cos_sub_cosh_mul_sin_nonpos {x : ℝ} (hx0 : 0 ≤ x) (hxπ : x ≤ Real.pi) :
    Real.sinh x * Real.cos x - Real.cosh x * Real.sin x ≤ 0 := by
  set g : ℝ → ℝ := fun x => Real.sinh x * Real.cos x - Real.cosh x * Real.sin x with hg
  have hderiv : ∀ x, HasDerivAt g (-2 * (Real.sinh x * Real.sin x)) x := by
    intro x
    have := ((Real.hasDerivAt_sinh x).mul (Real.hasDerivAt_cos x)).sub
      ((Real.hasDerivAt_cosh x).mul (Real.hasDerivAt_sin x))
    exact this.congr_deriv (by ring)
  have hanti : AntitoneOn g (Icc 0 Real.pi) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (continuousOn_of_forall_continuousAt fun x _ => (hderiv x).continuousAt)
      (fun x _ => (hderiv x).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [(hderiv x).deriv]
    have h1 : 0 ≤ Real.sinh x := Real.sinh_nonneg_iff.mpr hx.1.le
    have h2 : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx.1.le hx.2.le
    nlinarith [mul_nonneg h1 h2]
  have := hanti (left_mem_Icc.mpr Real.pi_pos.le) ⟨hx0, hxπ⟩ hx0
  have h0 : g 0 = 0 := by simp [hg]
  rw [h0] at this
  exact this

/-- cosh x cos x <= 1 on [0, pi/2]. -/
lemma cosh_mul_cos_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 2) :
    Real.cosh x * Real.cos x ≤ 1 := by
  set f : ℝ → ℝ := fun x => Real.cosh x * Real.cos x with hf
  have hderiv : ∀ x, HasDerivAt f (Real.sinh x * Real.cos x - Real.cosh x * Real.sin x) x := by
    intro x
    have := (Real.hasDerivAt_cosh x).mul (Real.hasDerivAt_cos x)
    exact this.congr_deriv (by ring)
  have hanti : AntitoneOn f (Icc 0 (Real.pi / 2)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (continuousOn_of_forall_continuousAt fun x _ => (hderiv x).continuousAt)
      (fun x _ => (hderiv x).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [(hderiv x).deriv]
    exact sinh_mul_cos_sub_cosh_mul_sin_nonpos hx.1.le (by linarith [hx.2, Real.pi_pos])
  have := hanti (left_mem_Icc.mpr (by positivity)) ⟨hx0, hx⟩ hx0
  have h0 : f 0 = 1 := by simp [hf]
  rw [h0] at this
  exact this

/-- **Lemma A.**  cosh a cos b <= 1 whenever |a| <= |b| <= pi/2. -/
theorem cosh_mul_cos_le_one_of_abs_le {a b : ℝ} (hab : |a| ≤ |b|) (hb : |b| ≤ Real.pi / 2) :
    Real.cosh a * Real.cos b ≤ 1 := by
  rw [← Real.cosh_abs, ← Real.cos_abs]
  have h1 : Real.cos |b| ≤ Real.cos |a| :=
    Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg a) (by linarith [Real.pi_pos]) hab
  calc Real.cosh |a| * Real.cos |b| ≤ Real.cosh |a| * Real.cos |a| :=
        mul_le_mul_of_nonneg_left h1 (Real.cosh_pos _).le
    _ ≤ 1 := cosh_mul_cos_le_one (abs_nonneg a) (hab.trans hb)

/-! ## D. Lemma B: the geometry of a strip point. -/

lemma arctan_le_self {u : ℝ} (hu : 0 ≤ u) : Real.arctan u ≤ u := by
  rcases hu.lt_or_eq with hu | hu
  · have h1 : 0 < Real.arctan u := Real.arctan_pos.mpr hu
    have h2 := Real.arctan_lt_pi_div_two u
    have := Real.lt_tan h1 h2
    rw [Real.tan_arctan] at this
    exact this.le
  · rw [← hu, Real.arctan_zero]

lemma half_le_arctan {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : u / 2 ≤ Real.arctan u := by
  set h : ℝ → ℝ := fun x => Real.arctan x - x / 2 with hh
  have hderiv : ∀ x, HasDerivAt h (1 / (1 + x ^ 2) - 1 / 2) x := by
    intro x
    have := (Real.hasDerivAt_arctan x).sub ((hasDerivAt_id x).div_const 2)
    exact this
  have hmono : MonotoneOn h (Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (continuousOn_of_forall_continuousAt fun x _ => (hderiv x).continuousAt)
      (fun x _ => (hderiv x).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [(hderiv x).deriv]
    have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
    have : 1 / 2 ≤ 1 / (1 + x ^ 2) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      linarith
    linarith
  have := hmono (left_mem_Icc.mpr zero_le_one) ⟨hu0, hu1⟩ hu0
  have h0 : h 0 = 0 := by simp [hh]
  rw [h0] at this
  have hu : h u = Real.arctan u - u / 2 := rfl
  linarith

lemma abs_arctan (t : ℝ) : |Real.arctan t| = Real.arctan |t| := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht, abs_of_nonneg (Real.arctan_nonneg.mpr ht)]
  · have hlt : Real.arctan t < 0 := by
      have := Real.arctan_strictMono ht
      rwa [Real.arctan_zero] at this
    rw [abs_of_neg ht, Real.arctan_neg, abs_of_neg hlt]

lemma wOf_re (ρ : ℂ) :
    (wOf ρ).re = (ρ.re * (ρ.re - 1) + ρ.im * ρ.im) / Complex.normSq (ρ - 1) := by
  unfold wOf
  rw [Complex.div_re, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero]
  ring

lemma wOf_im (ρ : ℂ) : (wOf ρ).im = -ρ.im / Complex.normSq (ρ - 1) := by
  unfold wOf
  rw [Complex.div_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero]
  ring

lemma normSq_sub_one (ρ : ℂ) : Complex.normSq (ρ - 1) = (ρ.re - 1) ^ 2 + ρ.im ^ 2 := by
  rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  ring

lemma normSq_eq_sq_add_sq (ρ : ℂ) : Complex.normSq ρ = ρ.re ^ 2 + ρ.im ^ 2 := by
  rw [Complex.normSq_apply]; ring

/-- On the strip with |Im rho| >= 1, Re w > 0. -/
lemma wOf_re_pos {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hγ : 1 ≤ |ρ.im|) : 0 < (wOf ρ).re := by
  rw [wOf_re]
  have hD : 0 < Complex.normSq (ρ - 1) := by
    rw [normSq_sub_one]
    have : 1 ≤ ρ.im ^ 2 := by rw [← sq_abs]; nlinarith
    positivity
  apply div_pos _ hD
  have : 1 ≤ ρ.im ^ 2 := by rw [← sq_abs]; nlinarith
  nlinarith

/-- |theta| = arctan (beta/|gamma|) + arctan ((1 - beta)/|gamma|). -/
theorem abs_arg_wOf_eq {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hγ : 1 ≤ |ρ.im|) :
    |arg (wOf ρ)| = Real.arctan (ρ.re / |ρ.im|) + Real.arctan ((1 - ρ.re) / |ρ.im|) := by
  have hre := wOf_re_pos h0 h1 hγ
  have hg : 0 < |ρ.im| := by linarith
  have hγ0 : ρ.im ≠ 0 := fun h => by rw [h, abs_zero] at hγ; linarith
  have hg2 : ρ.im ^ 2 = |ρ.im| ^ 2 := (sq_abs _).symm
  have hlt : |arg (wOf ρ)| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have hlt' := abs_lt.mp hlt
  -- arg w = arctan (tan (arg w)) = arctan (Im w / Re w)
  have htan : arg (wOf ρ) = Real.arctan ((wOf ρ).im / (wOf ρ).re) := by
    rw [← Complex.tan_arg, Real.arctan_tan hlt'.1 hlt'.2]
  -- the quotient in closed form
  have hD : Complex.normSq (ρ - 1) ≠ 0 := by
    rw [normSq_sub_one]
    have : 1 ≤ ρ.im ^ 2 := by rw [hg2]; nlinarith
    positivity
  have hden : ρ.re * (ρ.re - 1) + ρ.im * ρ.im ≠ 0 := by
    have : 1 ≤ ρ.im ^ 2 := by rw [hg2]; nlinarith
    nlinarith
  have hq : (wOf ρ).im / (wOf ρ).re = -ρ.im / (ρ.re * (ρ.re - 1) + ρ.im * ρ.im) := by
    rw [wOf_im, wOf_re]
    field_simp
  rw [htan, hq, abs_arctan, abs_div, abs_neg]
  have hpos : 0 < ρ.re * (ρ.re - 1) + ρ.im * ρ.im := by
    have : 1 ≤ ρ.im ^ 2 := by rw [hg2]; nlinarith
    nlinarith
  rw [abs_of_pos hpos]
  -- the arctan addition formula
  have hprod : ρ.re / |ρ.im| * ((1 - ρ.re) / |ρ.im|) < 1 := by
    rw [div_mul_div_comm, div_lt_one (by positivity), ← sq, ← hg2]
    have : 1 ≤ ρ.im ^ 2 := by rw [hg2]; nlinarith
    nlinarith
  rw [Real.arctan_add hprod]
  congr 1
  rw [div_mul_div_comm, abs_mul_abs_self, ← add_div,
    show ρ.re + (1 - ρ.re) = (1 : ℝ) by ring, one_sub_div (mul_ne_zero hγ0 hγ0), div_div_div_eq,
    one_mul, show ρ.re * (ρ.re - 1) + ρ.im * ρ.im = ρ.im * ρ.im - ρ.re * (1 - ρ.re) by ring,
    ← abs_mul_abs_self ρ.im, mul_div_mul_left _ _ hg.ne']

/-- Upper bound: |theta| <= 1/|gamma|. -/
theorem abs_arg_wOf_le {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hγ : 1 ≤ |ρ.im|) :
    |arg (wOf ρ)| ≤ 1 / |ρ.im| := by
  rw [abs_arg_wOf_eq h0 h1 hγ]
  have hg : 0 < |ρ.im| := by linarith
  have ha := arctan_le_self (div_nonneg h0.le hg.le)
  have hb := arctan_le_self (div_nonneg (sub_nonneg.mpr h1.le) hg.le)
  calc Real.arctan (ρ.re / |ρ.im|) + Real.arctan ((1 - ρ.re) / |ρ.im|)
      ≤ ρ.re / |ρ.im| + (1 - ρ.re) / |ρ.im| := add_le_add ha hb
    _ = 1 / |ρ.im| := by ring

/-- Lower bound: 1/(2|gamma|) <= |theta|. -/
theorem le_abs_arg_wOf {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hγ : 1 ≤ |ρ.im|) :
    1 / (2 * |ρ.im|) ≤ |arg (wOf ρ)| := by
  rw [abs_arg_wOf_eq h0 h1 hγ]
  have hg : 0 < |ρ.im| := by linarith
  have ha := half_le_arctan (div_nonneg h0.le hg.le)
    (by rw [div_le_one hg]; linarith)
  have hb := half_le_arctan (div_nonneg (sub_nonneg.mpr h1.le) hg.le)
    (by rw [div_le_one hg]; linarith)
  calc 1 / (2 * |ρ.im|) = ρ.re / |ρ.im| / 2 + (1 - ρ.re) / |ρ.im| / 2 := by
        ring
    _ ≤ Real.arctan (ρ.re / |ρ.im|) + Real.arctan ((1 - ρ.re) / |ρ.im|) := add_le_add ha hb

/-- |log r| <= 1/(2 gamma^2) on the strip (gamma ≠ 0). -/
theorem abs_log_norm_wOf_le {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hγ : ρ.im ≠ 0) :
    |Real.log ‖wOf ρ‖| ≤ 1 / (2 * ρ.im ^ 2) := by
  have hγ2 : 0 < ρ.im ^ 2 := by positivity
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at h0; simp at h0
  have hρ1 : ρ ≠ 1 := fun h => by rw [h] at h1; simp at h1
  set P := Complex.normSq ρ with hP
  set Q := Complex.normSq (ρ - 1) with hQ
  have hPe : P = ρ.re ^ 2 + ρ.im ^ 2 := normSq_eq_sq_add_sq ρ
  have hQe : Q = (ρ.re - 1) ^ 2 + ρ.im ^ 2 := normSq_sub_one ρ
  have hPpos : 0 < P := by rw [hPe]; positivity
  have hQpos : 0 < Q := by rw [hQe]; positivity
  -- 2 log |w| = log P - log Q
  have hlog : 2 * Real.log ‖wOf ρ‖ = Real.log P - Real.log Q := by
    unfold wOf
    rw [norm_div, Real.log_div (norm_ne_zero_iff.mpr hρ0)
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hρ1)), hP, hQ,
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hup : Real.log P - Real.log Q ≤ 1 / ρ.im ^ 2 := by
    rw [← Real.log_div hPpos.ne' hQpos.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos hPpos hQpos)).trans ?_
    rw [div_sub_one hQpos.ne', div_le_div_iff₀ hQpos hγ2, hPe, hQe]
    nlinarith
  have hlow : -(1 / ρ.im ^ 2) ≤ Real.log P - Real.log Q := by
    have : Real.log Q - Real.log P ≤ 1 / ρ.im ^ 2 := by
      rw [← Real.log_div hQpos.ne' hPpos.ne']
      refine (Real.log_le_sub_one_of_pos (div_pos hQpos hPpos)).trans ?_
      rw [div_sub_one hPpos.ne', div_le_div_iff₀ hPpos hγ2, hPe, hQe]
      nlinarith
    linarith
  rw [abs_le]
  constructor
  · have : -(1 / (2 * ρ.im ^ 2)) = (-(1 / ρ.im ^ 2)) / 2 := by ring
    rw [this]
    linarith
  · have : 1 / (2 * ρ.im ^ 2) = (1 / ρ.im ^ 2) / 2 := by ring
    rw [this]
    linarith

/-! ## E. Theorem C (termwise) and the on-line case. -/

/-- **Theorem C.**  For a strip point with |Im rho| >= 1 and N <= 3 pi |Im rho| / 2, the pair
term is nonnegative, whether or not rho is on the line: with b = N theta, either |b| <= pi/2
(Lemma A with |a| <= |b|) or pi/2 <= |b| <= 3 pi/2 (cos b <= 0, so the term is >= 2). -/
theorem pair_re_nonneg_of_far {N : ℕ} {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hγ : 1 ≤ |ρ.im|)
    (hN : (N : ℝ) ≤ 3 * Real.pi * |ρ.im| / 2) :
    0 ≤ (liKernel N ρ).re + (liKernel N (1 - conj ρ)).re := by
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at h0; simp at h0
  have hρ1 : ρ ≠ 1 := fun h => by rw [h] at h1; simp at h1
  have hγ0 : ρ.im ≠ 0 := fun h => by rw [h, abs_zero] at hγ; linarith
  have hg : 0 < |ρ.im| := by linarith
  have hw : 0 < ‖wOf ρ‖ := norm_pos_iff.mpr (wOf_ne_zero hρ0 hρ1)
  rw [pair_re_eq hρ0 hρ1, pow_add_inv_pow_eq_cosh hw]
  have hab : |(N : ℝ) * Real.log ‖wOf ρ‖| ≤ |(N : ℝ) * arg (wOf ρ)| := by
    rw [abs_mul, abs_mul, Nat.abs_cast]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    calc |Real.log ‖wOf ρ‖| ≤ 1 / (2 * ρ.im ^ 2) := abs_log_norm_wOf_le h0 h1 hγ0
      _ ≤ 1 / (2 * |ρ.im|) := by
          apply one_div_le_one_div_of_le (by positivity)
          rw [← sq_abs]
          nlinarith
      _ ≤ |arg (wOf ρ)| := le_abs_arg_wOf h0 h1 hγ
  have hb : |(N : ℝ) * arg (wOf ρ)| ≤ 3 * Real.pi / 2 := by
    rw [abs_mul, Nat.abs_cast]
    calc (N : ℝ) * |arg (wOf ρ)| ≤ (N : ℝ) * (1 / |ρ.im|) :=
          mul_le_mul_of_nonneg_left (abs_arg_wOf_le h0 h1 hγ) (Nat.cast_nonneg _)
      _ ≤ (3 * Real.pi * |ρ.im| / 2) * (1 / |ρ.im|) :=
          mul_le_mul_of_nonneg_right hN (by positivity)
      _ = 3 * Real.pi / 2 := by field_simp
  by_cases hsmall : |(N : ℝ) * arg (wOf ρ)| ≤ Real.pi / 2
  · have := cosh_mul_cos_le_one_of_abs_le hab hsmall
    linarith
  · have hsmall := not_le.mp hsmall
    have hcos : Real.cos ((N : ℝ) * arg (wOf ρ)) ≤ 0 := by
      rw [← Real.cos_abs]
      exact Real.cos_nonpos_of_pi_div_two_le_of_le hsmall.le (by linarith)
    have := mul_nonpos_of_nonneg_of_nonpos
      (Real.cosh_pos ((N : ℝ) * Real.log ‖wOf ρ‖)).le hcos
    linarith

/-- On the line the pair term is 2 (1 - cos (N theta)) >= 0. -/
theorem pair_re_nonneg_of_on_line {N : ℕ} {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    0 ≤ (liKernel N ρ).re + (liKernel N (1 - conj ρ)).re := by
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at hre; simp at hre
  have hρ1 : ρ ≠ 1 := fun h => by rw [h] at hre; norm_num at hre
  have hw : ‖wOf ρ‖ = 1 := by
    have := norm_one_sub_inv_of_on_line hre hρ0
    rwa [one_sub_inv_eq_inv_wOf hρ0 hρ1, norm_inv, inv_eq_one] at this
  rw [pair_re_eq hρ0 hρ1, hw, one_pow, inv_one, one_pow]
  linarith [Real.cos_le_one ((N : ℝ) * arg (wOf ρ))]

/-- **Theorem D, termwise.**  Zeros on the line up to height T >= 1 make every pair term
nonnegative for N <= 3 pi T / 2. -/
theorem pair_re_nonneg_of_line_below {T : ℝ} (hT : 1 ≤ T)
    (hline : ∀ ρ, IsNontrivialZero ρ → |ρ.im| ≤ T → ρ.re = 1 / 2) {N : ℕ}
    (hN : (N : ℝ) ≤ 3 * Real.pi * T / 2) {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    0 ≤ (liKernel N ρ).re + (liKernel N (1 - conj ρ)).re := by
  by_cases hT' : |ρ.im| ≤ T
  · exact pair_re_nonneg_of_on_line (hline ρ hρ hT')
  · have hT' := not_le.mp hT'
    refine pair_re_nonneg_of_far hρ.2.1 hρ.2.2 (hT.trans hT'.le) (hN.trans ?_)
    have := Real.pi_pos
    nlinarith

/-! ## F. The regrouping of the tsum over the involution, and Theorem D. -/

/-- The real-part family of E6Bridge15's paired terms. -/
def liRe (N : ℕ) (ρ : ℂ) : ℝ := (liPaired N ρ).re

lemma liRe_eq (N : ℕ) (ρ : ℂ) :
    liRe N ρ = (WeilExplicit.zeroMult ρ : ℝ) * (liKernel N ρ).re :=
  liPaired_re N ρ

lemma liRe_add_one_sub_conj (N : ℕ) (ρ : ℂ) :
    liRe N ρ + liRe N (1 - conj ρ)
      = (WeilExplicit.zeroMult ρ : ℝ) * ((liKernel N ρ).re + (liKernel N (1 - conj ρ)).re) := by
  rw [liRe_eq, liRe_eq, zeroMult_one_sub_conj]
  ring

lemma hasSum_liRe (N : ℕ) : HasSum (liRe N) (liLimit N).re :=
  Complex.hasSum_re (summable_liPaired N).hasSum

/-- **The regrouping.**  If every pair (rho, 1 - conj rho) contributes a nonnegative term, then
Re (liLimit N) >= 0. -/
theorem liLimit_re_nonneg_of_pairs {N : ℕ}
    (hpair : ∀ ρ, IsNontrivialZero ρ → 0 ≤ (liKernel N ρ).re + (liKernel N (1 - conj ρ)).re) :
    0 ≤ (liLimit N).re := by
  have h1 : HasSum (liRe N) (liLimit N).re := hasSum_liRe N
  have h2 : HasSum (fun ρ => liRe N (RvMBridge6.reflectEquiv ρ)) (liLimit N).re :=
    (RvMBridge6.reflectEquiv.hasSum_iff).mpr h1
  have h3 : HasSum (fun ρ => liRe N ρ + liRe N (1 - conj ρ)) (2 * (liLimit N).re) := by
    rw [two_mul]
    exact h1.add h2
  have h4 : 0 ≤ 2 * (liLimit N).re := by
    rw [← h3.tsum_eq]
    refine tsum_nonneg fun ρ => ?_
    rw [liRe_add_one_sub_conj]
    by_cases hρ : IsNontrivialZero ρ
    · exact mul_nonneg (Nat.cast_nonneg _) (hpair ρ hρ)
    · rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial hρ]
      simp
  linarith

/-- **Theorem D (the Li ladder).**  If every nontrivial zero with |Im rho| <= T (T >= 1) has real
part 1/2, then Re (liLimit N) >= 0 for every N <= 3 pi T / 2. -/
theorem liLimit_re_nonneg_of_line_below (T : ℝ) (hT : 1 ≤ T)
    (hline : ∀ ρ, IsNontrivialZero ρ → |ρ.im| ≤ T → ρ.re = 1 / 2) (N : ℕ)
    (hN : (N : ℝ) ≤ 3 * Real.pi * T / 2) : 0 ≤ (liLimit N).re :=
  liLimit_re_nonneg_of_pairs fun _ hρ => pair_re_nonneg_of_line_below hT hline hN hρ

/-- The closed form: 0 <= Re (archSide N + finiteSide N) under the same hypothesis (N >= 1). -/
theorem archSide_add_finiteSide_re_nonneg_of_line_below (T : ℝ) (hT : 1 ≤ T)
    (hline : ∀ ρ, IsNontrivialZero ρ → |ρ.im| ≤ T → ρ.re = 1 / 2) (N : ℕ) (hN0 : 0 < N)
    (hN : (N : ℝ) ≤ 3 * Real.pi * T / 2) : 0 ≤ (archSide N + finiteSide N).re := by
  have h : liLimit N = archSide N + finiteSide N := RvMBridge27.liValue N hN0
  rw [← h]
  exact liLimit_re_nonneg_of_line_below T hT hline N hN

/-! ## G. Rung N = 1 with no hypothesis. -/

lemma liKernel_one (ρ : ℂ) : liKernel 1 ρ = 1 / ρ := by
  unfold liKernel
  ring

/-- Every term of rung 1 is nonnegative: Re (1/rho) = Re rho / |rho|^2 > 0 on the strip. -/
lemma liRe_one_nonneg (ρ : ℂ) : 0 ≤ liRe 1 ρ := by
  rw [liRe_eq, liKernel_one]
  by_cases h : IsNontrivialZero ρ
  · refine mul_nonneg (Nat.cast_nonneg _) ?_
    rw [one_div, Complex.inv_re]
    exact div_nonneg h.2.1.le (Complex.normSq_nonneg _)
  · rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial h]
    simp

/-- **Rung 1, hypothesis-free.**  0 <= Re (liLimit 1). -/
theorem liLimit_one_re_nonneg : 0 ≤ (liLimit 1).re := by
  rw [← (hasSum_liRe 1).tsum_eq]
  exact tsum_nonneg liRe_one_nonneg

/-- The closed form at N = 1: 0 <= Re (archSide 1 + finiteSide 1), unconditionally. -/
theorem archSide_add_finiteSide_one_re_nonneg : 0 ≤ (archSide 1 + finiteSide 1).re := by
  have h : liLimit 1 = archSide 1 + finiteSide 1 := RvMBridge27.liValue 1 one_pos
  rw [← h]
  exact liLimit_one_re_nonneg

/-! ## H. The low-height box: the SHARP sawtooth bound |int_1^infty {x} x^{-s-1} dx| <= 1/(2 Re s). -/

/-- On a unit interval [m, m+1] (m >= 1) the centred sawtooth integrates to a nonpositive
number against x^{-sigma-1}: integration by parts with G(x) = (x - m - 1/2)^2/2 - 1/8 <= 0,
G(m) = G(m+1) = 0, against the decreasing weight. -/
lemma integral_shifted_mul_rpow_nonpos {σ : ℝ} (hσ : 0 < σ) {m : ℕ} (hm : 1 ≤ m) :
    ∫ x in (m : ℝ)..(m : ℝ) + 1, (x - ((m : ℝ) + 1 / 2)) * x ^ (-σ - 1) ≤ 0 := by
  set c : ℝ := (m : ℝ) + 1 / 2 with hc
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : ∀ x ∈ uIcc (m : ℝ) ((m : ℝ) + 1), 0 < x := by
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    linarith [hx.1]
  have hu : ∀ x ∈ uIcc (m : ℝ) ((m : ℝ) + 1),
      HasDerivAt (fun x => (x - c) ^ 2 / 2 - 1 / 8) (x - c) x := by
    intro x _
    have := ((((hasDerivAt_id x).sub_const c).pow 2).div_const 2).sub_const (1 / 8)
    refine this.congr_deriv ?_
    simp only [id, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
    ring
  have hv : ∀ x ∈ uIcc (m : ℝ) ((m : ℝ) + 1),
      HasDerivAt (fun x => x ^ (-σ - 1)) ((-σ - 1) * x ^ (-σ - 1 - 1)) x := by
    intro x hx
    exact Real.hasDerivAt_rpow_const (Or.inl (hpos x hx).ne')
  have hu' : IntervalIntegrable (fun x => x - c) volume (m : ℝ) ((m : ℝ) + 1) :=
    (continuous_id.sub continuous_const).intervalIntegrable _ _
  have hv' : IntervalIntegrable (fun x => (-σ - 1) * x ^ (-σ - 1 - 1)) volume (m : ℝ)
      ((m : ℝ) + 1) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul (continuousOn_of_forall_continuousAt fun x hx => ?_)
    exact Real.continuousAt_rpow_const x _ (Or.inl (hpos x hx).ne')
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hu0 : ((m : ℝ) - c) ^ 2 / 2 - 1 / 8 = 0 := by rw [hc]; ring
  have hu1 : ((m : ℝ) + 1 - c) ^ 2 / 2 - 1 / 8 = 0 := by rw [hc]; ring
  simp only [hu1, hu0, zero_mul, sub_zero, zero_sub] at hibp
  have hnn : 0 ≤ ∫ x in (m : ℝ)..(m : ℝ) + 1,
      ((x - c) ^ 2 / 2 - 1 / 8) * ((-σ - 1) * x ^ (-σ - 1 - 1)) := by
    refine intervalIntegral.integral_nonneg (by linarith) fun x hx => ?_
    have hx0 : 0 < x := by linarith [hx.1]
    have h1 : (x - c) ^ 2 / 2 - 1 / 8 ≤ 0 := by
      have hl : -(1 / 2) ≤ x - c := by rw [hc]; linarith [hx.1]
      have hr : x - c ≤ 1 / 2 := by rw [hc]; linarith [hx.2]
      nlinarith [hl, hr]
    have h2 : (-σ - 1) * x ^ (-σ - 1 - 1) ≤ 0 := by
      have := Real.rpow_nonneg hx0.le (-σ - 1 - 1)
      nlinarith
    nlinarith [h1, h2]
  linarith

/-- On (m, m+1) the sawtooth {x} - 1/2 is x - m - 1/2. -/
lemma integral_fract_eq_shifted {σ : ℝ} {m : ℕ} (hm : 1 ≤ m) :
    ∫ x in (m : ℝ)..(m : ℝ) + 1, (Int.fract x - 1 / 2) * x ^ (-σ - 1)
      = ∫ x in (m : ℝ)..(m : ℝ) + 1, (x - ((m : ℝ) + 1 / 2)) * x ^ (-σ - 1) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have hf : Int.fract x = x - m := by
    rw [Int.fract_eq_iff]
    refine ⟨by linarith [hx.1], by linarith [hx.2], ⟨m, ?_⟩⟩
    push_cast
    ring
  simp only [hf]
  ring

lemma integrableOn_sawtooth {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun x : ℝ => (Int.fract x - 1 / 2) * x ^ (-σ - 1)) (Ioi 1) := by
  refine Integrable.bdd_mul (c := 1 / 2) (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos)
    ((measurable_fract.sub measurable_const).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [Int.fract_nonneg x, Int.fract_lt_one x]

/-- int_1^infty ({x} - 1/2) x^{-sigma-1} dx <= 0: the unit intervals summed, then the limit. -/
lemma integral_sawtooth_nonpos {σ : ℝ} (hσ : 0 < σ) :
    ∫ x in Ioi (1 : ℝ), (Int.fract x - 1 / 2) * x ^ (-σ - 1) ≤ 0 := by
  have hint := integrableOn_sawtooth hσ
  have htend : Tendsto (fun n : ℕ => ∫ x in (1 : ℝ)..((n : ℝ) + 1),
      (Int.fract x - 1 / 2) * x ^ (-σ - 1)) atTop
      (𝓝 (∫ x in Ioi (1 : ℝ), (Int.fract x - 1 / 2) * x ^ (-σ - 1))) :=
    intervalIntegral_tendsto_integral_Ioi 1 hint
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  refine le_of_tendsto' htend fun n => ?_
  have hadj : ∀ k < n, IntervalIntegrable (fun x : ℝ => (Int.fract x - 1 / 2) * x ^ (-σ - 1))
      volume ((k : ℝ) + 1) (((k + 1 : ℕ) : ℝ) + 1) := by
    intro k _
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by push_cast; linarith)]
    refine hint.mono_set fun x hx => ?_
    have : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    exact lt_of_le_of_lt this hx.1
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k : ℝ) + 1) (n := n) hadj
  simp only [Nat.cast_zero, zero_add] at hsum
  rw [← hsum]
  refine Finset.sum_nonpos fun k _ => ?_
  have h1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
  have := integral_shifted_mul_rpow_nonpos hσ h1
  rw [← integral_fract_eq_shifted h1] at this
  push_cast at this ⊢
  exact this

/-- **The sharp real bound.**  int_1^infty {x} x^{-sigma-1} dx <= 1/(2 sigma). -/
theorem integral_fract_mul_rpow_le {σ : ℝ} (hσ : 0 < σ) :
    ∫ x in Ioi (1 : ℝ), Int.fract x * x ^ (-σ - 1) ≤ 1 / (2 * σ) := by
  have hφ : IntegrableOn (fun x : ℝ => x ^ (-σ - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hF := integrableOn_sawtooth hσ
  have heq : (fun x : ℝ => Int.fract x * x ^ (-σ - 1))
      = fun x => (Int.fract x - 1 / 2) * x ^ (-σ - 1) + (1 / 2) * x ^ (-σ - 1) := by
    funext x; ring
  rw [heq, integral_add hF (hφ.const_mul _), integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow, show (-σ - 1 + 1) = -σ by ring,
    neg_div_neg_eq]
  have := integral_sawtooth_nonpos hσ
  have h2 : (1 / 2 : ℝ) * (1 / σ) = 1 / (2 * σ) := by field_simp
  linarith

/-- **The sharp complex bound.**  |int_1^infty {x} x^{-s-1} dx| <= 1/(2 Re s) for Re s > 0. -/
theorem norm_integral_fract_cpow_le {s : ℂ} (hs : 0 < s.re) :
    ‖∫ x in Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))‖ ≤ 1 / (2 * s.re) := by
  have hbd : IntegrableOn (fun x : ℝ => Int.fract x * x ^ (-s.re - 1)) (Ioi 1) := by
    refine Integrable.bdd_mul (c := 1) (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos)
      measurable_fract.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x)]
    exact (Int.fract_lt_one x).le
  refine (norm_integral_le_of_norm_le hbd ?_).trans (integral_fract_mul_rpow_le hs)
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_)
  have hx0 : 0 < x := lt_trans one_pos hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x),
    Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
  rw [show -(s.re + 1) = -s.re - 1 by ring]

/-! ## I. The zero constraint from Zeta0EqZeta at N = 1. -/

/-- At a nontrivial zero, int_1^infty {x} x^{-s-1} dx = 1/(s - 1) (Zeta0EqZeta at N = 1). -/
theorem integral_fract_cpow_eq_of_zero {s : ℂ} (hs : IsNontrivialZero s) :
    (∫ x in Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))) = 1 / (s - 1) := by
  have hσ := hs.2.1
  have hs1 : s ≠ 1 := fun h => by
    have := hs.2.2
    rw [h, Complex.one_re] at this
    exact lt_irrefl _ this
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hσ; exact lt_irrefl _ hσ
  have hz := hs.1
  rw [← Zeta0EqZeta (N := 1) one_pos hσ hs1] at hz
  simp only [riemannZeta0, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Complex.zero_cpow hs0, Nat.cast_one, Complex.one_cpow, div_one, div_zero, zero_add] at hz
  have hre : (-(s + 1)).re < -1 := by
    simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
    linarith
  have hint1 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-(s + 1))) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt hre one_pos
  have hint2 : IntegrableOn (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))) (Ioi 1) := by
    refine Integrable.bdd_mul (c := 1) hint1
      (Complex.continuous_ofReal.measurable.comp measurable_fract).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x)]
    exact (Int.fract_lt_one x).le
  set J' := ∫ x in Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1)) with hJ'
  have hJ : (∫ x in Ioi (1 : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - x) / (x : ℂ) ^ (s + 1))
      = (1 / 2) * (1 / s) - J' := by
    have heq : (fun x : ℝ => ((⌊x⌋ : ℂ) + 1 / 2 - x) / (x : ℂ) ^ (s + 1))
        = fun x : ℝ => (1 / 2) * (x : ℂ) ^ (-(s + 1)) - ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
      funext x
      rw [Complex.cpow_neg, div_eq_mul_inv]
      unfold Int.fract
      push_cast
      ring
    rw [heq, integral_sub (hint1.const_mul _) hint2, integral_const_mul,
      integral_Ioi_cpow_of_lt hre one_pos, Complex.ofReal_one, Complex.one_cpow]
    congr 2
    rw [show -(s + 1) + 1 = -s by ring, neg_div_neg_eq]
  rw [hJ, mul_sub, show s * (1 / 2 * (1 / s)) = 1 / 2 by field_simp,
    show (-1 : ℂ) / (1 - s) = 1 / (s - 1) by rw [neg_div, ← div_neg, neg_sub]] at hz
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have h2 : s * J' = 1 + 1 / (s - 1) := by linear_combination -hz
  have h3 : (1 : ℂ) + 1 / (s - 1) = s * (1 / (s - 1)) := by
    rw [one_add_div hs1', sub_add_cancel, mul_one_div]
  exact mul_left_cancel₀ hs0 (h2.trans h3)

/-- **The zero constraint.**  A nontrivial zero sigma + i t has 4 sigma^2 <= (sigma - 1)^2 + t^2
(i.e. 2 sigma <= |s - 1|). -/
theorem zero_constraint {s : ℂ} (hs : IsNontrivialZero s) :
    4 * s.re ^ 2 ≤ (s.re - 1) ^ 2 + s.im ^ 2 := by
  have hσ := hs.2.1
  have hs1 : s ≠ 1 := fun h => by
    have := hs.2.2
    rw [h, Complex.one_re] at this
    exact lt_irrefl _ this
  have h := norm_integral_fract_cpow_le hσ
  rw [integral_fract_cpow_eq_of_zero hs, norm_div, norm_one] at h
  have hn : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs1)
  have h2 : 2 * s.re ≤ ‖s - 1‖ := by
    rw [div_le_div_iff₀ hn (by positivity)] at h
    linarith
  have h3 : (2 * s.re) ^ 2 ≤ ‖s - 1‖ ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  rw [← Complex.normSq_eq_norm_sq, normSq_sub_one] at h3
  have : (2 * s.re) ^ 2 = 4 * s.re ^ 2 := by ring
  linarith

/-- The reflected constraint: 4 (1 - sigma)^2 <= sigma^2 + t^2. -/
theorem zero_constraint_reflect {s : ℂ} (hs : IsNontrivialZero s) :
    4 * (1 - s.re) ^ 2 ≤ s.re ^ 2 + s.im ^ 2 := by
  have h := zero_constraint (isNontrivialZero_one_sub_conj hs)
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.conj_re,
    Complex.conj_im] at h
  nlinarith [h]

/-- Box 1, squared form: t^2 >= 3/4 for every nontrivial zero. -/
theorem box_one_sq {s : ℂ} (hs : IsNontrivialZero s) : 3 / 4 ≤ s.im ^ 2 := by
  have h1 := zero_constraint hs
  have h2 := zero_constraint_reflect hs
  nlinarith [sq_nonneg (s.re - 1 / 2)]

/-- **Box 1.**  No nontrivial zero has |Im s| < sqrt 3 / 2. -/
theorem box_one {s : ℂ} (hs : IsNontrivialZero s) : Real.sqrt 3 / 2 ≤ |s.im| := by
  have ht := box_one_sq hs
  rw [← Real.sqrt_sq_eq_abs]
  have : Real.sqrt 3 / 2 = Real.sqrt (3 / 4) := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 3), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [this]
  exact Real.sqrt_le_sqrt ht

/-- **Box 2.**  Every nontrivial zero satisfies (Re s - 1/2)^2 <= (Im s)^2/3 - 1/4. -/
theorem box_two {s : ℂ} (hs : IsNontrivialZero s) :
    (s.re - 1 / 2) ^ 2 ≤ s.im ^ 2 / 3 - 1 / 4 := by
  have h1 := zero_constraint hs
  have h2 := zero_constraint_reflect hs
  nlinarith

/-! ## J. Hypothesis-free rungs from the box: termwise (unpaired) positivity. -/

/-- 1 - 1/rho = (A + i gamma)/P with A = beta^2 - beta + gamma^2 and P = |rho|^2. -/
lemma one_sub_inv_eq_div_normSq {ρ : ℂ} (h0 : ρ ≠ 0) :
    1 - 1 / ρ = (((ρ.re ^ 2 - ρ.re + ρ.im ^ 2 : ℝ) : ℂ) + (ρ.im : ℂ) * I)
      / ((Complex.normSq ρ : ℝ) : ℂ) := by
  have hP : ((Complex.normSq ρ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Complex.normSq_pos.mpr h0).ne'
  rw [eq_div_iff hP, one_div, Complex.inv_def, sub_mul, one_mul, mul_assoc,
    ← Complex.ofReal_mul, inv_mul_cancel₀ (Complex.normSq_pos.mpr h0).ne', Complex.ofReal_one,
    mul_one]
  apply Complex.ext
  · simp [Complex.normSq_apply, sq]
    ring
  · simp [sq]

lemma liKernel_re_eq (N : ℕ) {ρ : ℂ} (h0 : ρ ≠ 0) :
    (liKernel N ρ).re = 1 - ((((ρ.re ^ 2 - ρ.re + ρ.im ^ 2 : ℝ) : ℂ) + (ρ.im : ℂ) * I) ^ N).re
      / (Complex.normSq ρ) ^ N := by
  unfold liKernel
  rw [one_sub_inv_eq_div_normSq h0, div_pow, Complex.sub_re, Complex.one_re, ← Complex.ofReal_pow,
    Complex.div_ofReal_re]

/-- Termwise (unpaired) positivity gives the sign of the rung. -/
theorem liLimit_re_nonneg_of_termwise (N : ℕ)
    (h : ∀ ρ, IsNontrivialZero ρ → 0 ≤ (liKernel N ρ).re) : 0 ≤ (liLimit N).re := by
  rw [← (hasSum_liRe N).tsum_eq]
  refine tsum_nonneg fun ρ => ?_
  rw [liRe_eq]
  by_cases hρ : IsNontrivialZero ρ
  · exact mul_nonneg (Nat.cast_nonneg _) (h ρ hρ)
  · rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial hρ]
    simp

lemma re_pow_two (a b : ℝ) : (((a : ℂ) + (b : ℂ) * I) ^ 2).re = a ^ 2 - b ^ 2 := by
  simp only [sq, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

lemma re_pow_three (a b : ℝ) :
    (((a : ℂ) + (b : ℂ) * I) ^ 3).re = a ^ 3 - 3 * a * b ^ 2 := by
  simp only [pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.add_re, Complex.add_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

lemma re_pow_four (a b : ℝ) :
    (((a : ℂ) + (b : ℂ) * I) ^ 4).re = a ^ 4 - 6 * a ^ 2 * b ^ 2 + b ^ 4 := by
  simp only [pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.add_re, Complex.add_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

lemma re_pow_five (a b : ℝ) :
    (((a : ℂ) + (b : ℂ) * I) ^ 5).re = a ^ 5 - 10 * a ^ 3 * b ^ 2 + 5 * a * b ^ 4 := by
  simp only [pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.add_re, Complex.add_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

lemma ne_zero_of_nontrivial {ρ : ℂ} (h : IsNontrivialZero ρ) : ρ ≠ 0 := fun h0 => by
  have := h.2.1
  rw [h0, Complex.zero_re] at this
  exact lt_irrefl _ this

/-- Rung 2, termwise: Re K_2(rho) >= 0 for every nontrivial zero (needs only |Im rho|^2 >= 3/4). -/
theorem liKernel_two_re_nonneg {ρ : ℂ} (hρ : IsNontrivialZero ρ) : 0 ≤ (liKernel 2 ρ).re := by
  have h0 := ne_zero_of_nontrivial hρ
  have hβ := hρ.2.1
  have hβ1 := hρ.2.2
  have ht := box_one_sq hρ
  rw [liKernel_re_eq 2 h0, sub_nonneg, div_le_one (pow_pos (Complex.normSq_pos.mpr h0) 2),
    re_pow_two, normSq_eq_sq_add_sq]
  have hA : 0 ≤ 2 * ρ.re ^ 2 - ρ.re + 2 * ρ.im ^ 2 := by nlinarith
  nlinarith [mul_nonneg hβ.le hA]

/-- Rung 3, termwise. -/
theorem liKernel_three_re_nonneg {ρ : ℂ} (hρ : IsNontrivialZero ρ) : 0 ≤ (liKernel 3 ρ).re := by
  have h0 := ne_zero_of_nontrivial hρ
  have hβ := hρ.2.1
  have hβ1 := hρ.2.2
  have ht := box_one_sq hρ
  rw [liKernel_re_eq 3 h0, sub_nonneg, div_le_one (pow_pos (Complex.normSq_pos.mpr h0) 3),
    re_pow_three, normSq_eq_sq_add_sq]
  set a := ρ.re ^ 2 - ρ.re + ρ.im ^ 2 with ha
  set p := ρ.re ^ 2 + ρ.im ^ 2 with hp
  have hA : 0 ≤ a := by rw [ha]; nlinarith
  have h1 : 0 ≤ ρ.re * (p ^ 2 + p * a + a ^ 2) := by
    refine mul_nonneg hβ.le ?_
    have : 0 ≤ p := by rw [hp]; positivity
    positivity
  have h2 : 0 ≤ a * ρ.im ^ 2 := mul_nonneg hA (sq_nonneg _)
  have hpa : p - a = ρ.re := by rw [hp, ha]; ring
  nlinarith [h1, h2, hpa]

/-- Rung 4, termwise. -/
theorem liKernel_four_re_nonneg {ρ : ℂ} (hρ : IsNontrivialZero ρ) : 0 ≤ (liKernel 4 ρ).re := by
  have h0 := ne_zero_of_nontrivial hρ
  have hβ := hρ.2.1
  have hβ1 := hρ.2.2
  have ht := box_one_sq hρ
  rw [liKernel_re_eq 4 h0, sub_nonneg, div_le_one (pow_pos (Complex.normSq_pos.mpr h0) 4),
    re_pow_four, normSq_eq_sq_add_sq]
  set a := ρ.re ^ 2 - ρ.re + ρ.im ^ 2 with ha
  set p := ρ.re ^ 2 + ρ.im ^ 2 with hp
  have hA' : ρ.im ^ 2 - 1 / 4 ≤ a := by rw [ha]; nlinarith [sq_nonneg (ρ.re - 1 / 2)]
  have hA : 0 ≤ a := by linarith
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hpa : p - a = ρ.re := by rw [hp, ha]; ring
  have h1 : 0 ≤ ρ.re * ((p + a) * (p ^ 2 + a ^ 2)) := by
    refine mul_nonneg hβ.le ?_
    positivity
  have hA2 : (ρ.im ^ 2 - 1 / 4) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by linarith) hA' 2
  have h6 : ρ.im ^ 2 ≤ 6 * (ρ.im ^ 2 - 1 / 4) ^ 2 := by nlinarith [ht]
  have h2 : 0 ≤ ρ.im ^ 2 * (6 * a ^ 2 - ρ.im ^ 2) := by
    refine mul_nonneg (sq_nonneg _) ?_
    linarith
  nlinarith [h1, h2, hpa]

/-- **Rungs 2, 3, 4, hypothesis-free.** -/
theorem liLimit_two_re_nonneg : 0 ≤ (liLimit 2).re :=
  liLimit_re_nonneg_of_termwise 2 fun _ hρ => liKernel_two_re_nonneg hρ

theorem liLimit_three_re_nonneg : 0 ≤ (liLimit 3).re :=
  liLimit_re_nonneg_of_termwise 3 fun _ hρ => liKernel_three_re_nonneg hρ

theorem liLimit_four_re_nonneg : 0 ≤ (liLimit 4).re :=
  liLimit_re_nonneg_of_termwise 4 fun _ hρ => liKernel_four_re_nonneg hρ

theorem archSide_add_finiteSide_two_re_nonneg : 0 ≤ (archSide 2 + finiteSide 2).re := by
  have h : liLimit 2 = archSide 2 + finiteSide 2 := RvMBridge27.liValue 2 (by norm_num)
  rw [← h]; exact liLimit_two_re_nonneg

theorem archSide_add_finiteSide_three_re_nonneg : 0 ≤ (archSide 3 + finiteSide 3).re := by
  have h : liLimit 3 = archSide 3 + finiteSide 3 := RvMBridge27.liValue 3 (by norm_num)
  rw [← h]; exact liLimit_three_re_nonneg

theorem archSide_add_finiteSide_four_re_nonneg : 0 ≤ (archSide 4 + finiteSide 4).re := by
  have h : liLimit 4 = archSide 4 + finiteSide 4 := RvMBridge27.liValue 4 (by norm_num)
  rw [← h]; exact liLimit_four_re_nonneg

/-! ### Rung 5: the box-2 parametrisation.  With u = beta - 1/2 and e = gamma^2 - 3 u^2 - 3/4 >= 0
(Box 2), the rung-5 polynomial P^5 - Re (A + i gamma)^5 is Sum_k c_k(u) e^k with every c_k > 0 on
|u| <= 1/2 (numerically min c_0 = 0.27 at u = -0.094; rung 6 FAILS termwise at beta = 0.29, gamma = 0.939, inside Box 2). -/

def li5c0 (u : ℝ) : ℝ :=
  1280 * u ^ 9 + 3200 * u ^ 8 + 1440 * u ^ 7 + 2000 * u ^ 6 + 561 * u ^ 5 + 845 / 2 * u ^ 4
    + 90 * u ^ 3 + 65 / 2 * u ^ 2 + 5 * u + 1 / 2
def li5c1 (u : ℝ) : ℝ :=
  1280 * u ^ 7 + 3200 * u ^ 6 + 1040 * u ^ 5 + 1400 * u ^ 4 + 260 * u ^ 3 + 175 * u ^ 2 + 20 * u + 5
def li5c2 (u : ℝ) : ℝ := 480 * u ^ 5 + 1200 * u ^ 4 + 250 * u ^ 3 + 325 * u ^ 2 + 30 * u + 35 / 2
def li5c3 (u : ℝ) : ℝ := 80 * u ^ 3 + 200 * u ^ 2 + 20 * u + 25
def li5c4 (u : ℝ) : ℝ := 5 * u + 25 / 2

lemma li5c4_nonneg {u : ℝ} (h1 : -1 / 2 ≤ u) : 0 ≤ li5c4 u := by unfold li5c4; linarith

lemma li5c3_nonneg {u : ℝ} (h1 : -1 / 2 ≤ u) (h2 : u ≤ 1 / 2) : 0 ≤ li5c3 u := by
  unfold li5c3
  have hm : 0 ≤ 1 / 2 - u := by linarith
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ u + 1 / 2) hm,
    sq_nonneg u, mul_nonneg (sq_nonneg u) (by linarith : (0 : ℝ) ≤ u + 1 / 2)]

lemma li5c2_nonneg {u : ℝ} (h1 : -1 / 2 ≤ u) (h2 : u ≤ 1 / 2) : 0 ≤ li5c2 u := by
  unfold li5c2
  have hp : 0 ≤ u + 1 / 2 := by linarith
  have hm : 0 ≤ 1 / 2 - u := by linarith
  nlinarith [mul_nonneg hp hm, sq_nonneg u, mul_nonneg (pow_nonneg (sq_nonneg u) 2) hp,
    mul_nonneg (sq_nonneg u) hp, mul_nonneg (pow_nonneg (sq_nonneg u) 2) hm,
    mul_nonneg (sq_nonneg u) hm]

lemma li5c1_nonneg {u : ℝ} (h1 : -1 / 2 ≤ u) (h2 : u ≤ 1 / 2) : 0 ≤ li5c1 u := by
  unfold li5c1
  have hp : 0 ≤ u + 1 / 2 := by linarith
  have hm : 0 ≤ 1 / 2 - u := by linarith
  nlinarith [mul_nonneg hp hm, sq_nonneg u, mul_nonneg (pow_nonneg (sq_nonneg u) 3) hp,
    mul_nonneg (pow_nonneg (sq_nonneg u) 2) hp, mul_nonneg (sq_nonneg u) hp,
    mul_nonneg (pow_nonneg (sq_nonneg u) 3) hm, mul_nonneg (pow_nonneg (sq_nonneg u) 2) hm,
    mul_nonneg (sq_nonneg u) hm, sq_nonneg (u + 2 / 35)]

lemma li5c0_nonneg {u : ℝ} (h1 : -1 / 2 ≤ u) (h2 : u ≤ 1 / 2) : 0 ≤ li5c0 u := by
  unfold li5c0
  have hp : 0 ≤ u + 1 / 2 := by linarith
  have hm : 0 ≤ 1 / 2 - u := by linarith
  nlinarith [mul_nonneg hp hm, sq_nonneg u, mul_nonneg (pow_nonneg (sq_nonneg u) 4) hp,
    mul_nonneg (pow_nonneg (sq_nonneg u) 3) hp, mul_nonneg (pow_nonneg (sq_nonneg u) 2) hp,
    mul_nonneg (sq_nonneg u) hp, mul_nonneg (pow_nonneg (sq_nonneg u) 4) hm,
    mul_nonneg (pow_nonneg (sq_nonneg u) 3) hm, mul_nonneg (pow_nonneg (sq_nonneg u) 2) hm,
    mul_nonneg (sq_nonneg u) hm, sq_nonneg (u + 1 / 13), sq_nonneg (u ^ 2 + u / 13),
    mul_nonneg (mul_nonneg hp hm) (sq_nonneg (u + 1 / 13))]

/-- The rung-5 identity: P^5 - Re (A + i gamma)^5 = Sum_k c_k(u) e^k. -/
lemma rung5_identity (β γ : ℝ) :
    (β ^ 2 + γ ^ 2) ^ 5 - ((β ^ 2 - β + γ ^ 2) ^ 5 - 10 * (β ^ 2 - β + γ ^ 2) ^ 3 * γ ^ 2
        + 5 * (β ^ 2 - β + γ ^ 2) * γ ^ 4)
      = li5c0 (β - 1 / 2) + li5c1 (β - 1 / 2) * (γ ^ 2 - 3 * (β - 1 / 2) ^ 2 - 3 / 4)
        + li5c2 (β - 1 / 2) * (γ ^ 2 - 3 * (β - 1 / 2) ^ 2 - 3 / 4) ^ 2
        + li5c3 (β - 1 / 2) * (γ ^ 2 - 3 * (β - 1 / 2) ^ 2 - 3 / 4) ^ 3
        + li5c4 (β - 1 / 2) * (γ ^ 2 - 3 * (β - 1 / 2) ^ 2 - 3 / 4) ^ 4 := by
  unfold li5c0 li5c1 li5c2 li5c3 li5c4
  ring

/-- Rung 5, termwise (uses Box 2). -/
theorem liKernel_five_re_nonneg {ρ : ℂ} (hρ : IsNontrivialZero ρ) : 0 ≤ (liKernel 5 ρ).re := by
  have h0 := ne_zero_of_nontrivial hρ
  have hβ := hρ.2.1
  have hβ1 := hρ.2.2
  have hb2 := box_two hρ
  rw [liKernel_re_eq 5 h0, sub_nonneg, div_le_one (pow_pos (Complex.normSq_pos.mpr h0) 5),
    re_pow_five, normSq_eq_sq_add_sq, ← sub_nonneg, rung5_identity]
  have hu1 : -1 / 2 ≤ ρ.re - 1 / 2 := by linarith
  have hu2 : ρ.re - 1 / 2 ≤ 1 / 2 := by linarith
  have he : 0 ≤ ρ.im ^ 2 - 3 * (ρ.re - 1 / 2) ^ 2 - 3 / 4 := by linarith
  have c0 := li5c0_nonneg hu1 hu2
  have c1 := li5c1_nonneg hu1 hu2
  have c2 := li5c2_nonneg hu1 hu2
  have c3 := li5c3_nonneg hu1 hu2
  have c4 := li5c4_nonneg hu1
  have := add_nonneg (add_nonneg (add_nonneg (add_nonneg c0 (mul_nonneg c1 he))
    (mul_nonneg c2 (pow_nonneg he 2))) (mul_nonneg c3 (pow_nonneg he 3)))
    (mul_nonneg c4 (pow_nonneg he 4))
  exact this

theorem liLimit_five_re_nonneg : 0 ≤ (liLimit 5).re :=
  liLimit_re_nonneg_of_termwise 5 fun _ hρ => liKernel_five_re_nonneg hρ

theorem archSide_add_finiteSide_five_re_nonneg : 0 ≤ (archSide 5 + finiteSide 5).re := by
  have h : liLimit 5 = archSide 5 + finiteSide 5 := RvMBridge27.liValue 5 (by norm_num)
  rw [← h]; exact liLimit_five_re_nonneg

end RvMBridge28
