/-
  E6Bridge7 -- discharge of the obligation O2 `RvMBridge6.GaussianDominance` (2026-09-20):
  if rho_0 is a nontrivial zero of zeta off the critical line, then for some real centre c and
  some lam > 0 the Gaussian-weighted zero sum

      S(c, lam) := Sum_rho m(rho) (gamma_rho - c)^2 exp (-2 lam (gamma_rho - c)^2),
      gamma_rho = (rho - 1/2)/i,

  has strictly negative real part.  Together with E6Bridge6 this leaves the Weil converse
  (positivity implies RH) modulo the single zero-free Fourier obligation GaussianApprox.

  WHAT IS CONSUMED (all unconditional, #print axioms = [propext, Classical.choice, Quot.sound]):
    RvMBridge6.zeroSide_pair_split, gaussTest_conj, summable_gauss_zeroSide,
    norm_gaussTest_mul_le                                     (E6Bridge6)
    RvMBridgeGauss.summable_mult_div_one_add_normSq, norm_tsum_subtype_le_tsum   (the prelude)
    RvMBridge4.zeroMult_eq_mult, zeroMult_eq_zero_of_not_nontrivial
    Zeta23.zetaSeam.finite_window   (finitely many nontrivial zeros in an ordinate window)
    Zeta23.zetaSeam.one_le_mult     (a nontrivial zero has multiplicity >= 1)
    Zeta23.WeilEF.gammaOf_re / gammaOf_im / abs_gammaOf_im_lt
    Mathlib: Complex.cos_arg / sin_arg, Real.cos_add_int_mul_two_pi, exists_int_gt / lt,
             Finset.exists_max_image, Set.Ioo_infinite, Tannery-free tsum comparison lemmas.

  THE ARGUMENT (the memo's plan, telperion/docs/WEIL_CONVERSE_ATTACK_2026-09-20.md, section 2).
  For a zero rho write y = 1/2 - Re rho, x = Im rho - c, so gamma_rho - c = x + i y and
      |m G(gamma_rho)| = m (x^2 + y^2) e^{2 lam phi_c(rho)},   phi_c(rho) := y^2 - x^2,
      Re G(gamma_rho) = e^{2 lam phi_c(rho)} [ (x^2 - y^2) cos (4 lam x y) + 2 x y sin (4 lam x y) ].
  (1) Window.  W := nontrivial zeros with Im rho_0 - 1 < Im rho <= Im rho_0 + 1 is finite.
  (2) Generic centre.  Two zeros of W with different ordinates have equal phi_c for exactly one
      c (badOf); the interval |c - Im rho_0| < |y_0| minus these finitely many points is
      nonempty.  Pick c there.  Then phi_c(rho_0) > 0.
  (3) Maximiser.  rho_1 maximises phi_c on W; M := phi_c(rho_1) > 0, so rho_1 is off the line.
      Every other rho in W outside the pair {rho_1, 1 - conj rho_1} has phi_c(rho) < M
      (equality would force equal ordinates, hence equal y^2, hence rho in the pair), so there
      is a gap eta > 0 with phi_c <= M - eta on W minus the pair.
  (4) Outside W.  |Im rho - c| > 1/2 >= |y|, so phi_c(rho) < 0 and, for lam >= 1,
      e^{2 lam phi_c} <= e^{2 phi_c}: the term is bounded by its lam = 1 value, which is bounded
      by m C_1/(1 + |gamma_rho|^2), the summable local-count majorant (E6Bridge6).
  (5) Phase.  With (x_1, y_1) for rho_1, y_1 != 0: if x_1 = 0 the bracket is -(x_1^2 + y_1^2)
      for every lam; otherwise lam := (arg(-(x_1 + i y_1)^2) + 2 pi k)/(4 x_1 y_1) with k an
      integer chosen so that lam >= lam_0 makes the bracket exactly -(x_1^2 + y_1^2).
  (6) Assembly.  Re S(c, lam) = 2 m_1 Re G(gamma_1) + Re(rest) <= -2 K e^{2 lam M}
      + A e^{2 lam (M - eta)} + B with K = m_1 (x_1^2 + y_1^2) > 0, A the finite window sum,
      B the majorant sum; lam >= max(1, A/(2 eta K), B/(2 M K)) makes this negative.

  No RH progress is claimed: this is an unconditional statement about a Gaussian-weighted sum
  over the zeros, wherever they are.  conjecture1_proved = False.
-/
import E6Bridge6
import RvMBridgeGauss

open Zeta23 Complex MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace RvMBridge7
open WeilExplicit RvMBridge6 RvMBridgeGauss

/-! ## A. Vocabulary. -/

/-- phi_c(rho) = (1/2 - Re rho)^2 - (Im rho - c)^2 = (Im gamma_rho)^2 - (Re gamma_rho - c)^2. -/
def phi (c : ℝ) (ρ : ℂ) : ℝ := (1 / 2 - ρ.re) ^ 2 - (ρ.im - c) ^ 2

/-- |gamma_rho - c|^2 = (Im rho - c)^2 + (1/2 - Re rho)^2. -/
def wsq (c : ℝ) (ρ : ℂ) : ℝ := (ρ.im - c) ^ 2 + (1 / 2 - ρ.re) ^ 2

/-- The summand of the Gaussian zero side. -/
def term (c lam : ℝ) (ρ : ℂ) : ℂ := (WeilExplicit.zeroMult ρ : ℂ) * gaussTest c lam (gammaOf ρ)

lemma zeroSide_gauss_eq (c lam : ℝ) : zeroSide (gaussTest c lam) = ∑' ρ : ℂ, term c lam ρ := rfl

/-! ## B. The Gaussian summand: modulus and real part. -/

/-- ‖G_{c,lam}(z)‖ = ((Re z - c)^2 + (Im z)^2) exp (2 lam ((Im z)^2 - (Re z - c)^2)). -/
lemma norm_gaussTest (c lam : ℝ) (z : ℂ) :
    ‖gaussTest c lam z‖ = ((z.re - c) ^ 2 + z.im ^ 2)
      * Real.exp (2 * lam * (z.im ^ 2 - (z.re - c) ^ 2)) := by
  have hre : (-(2 * (lam : ℂ)) * (z - c) ^ 2).re = 2 * lam * (z.im ^ 2 - (z.re - c) ^ 2) := by
    simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.re_ofNat,
      Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im, pow_two, Complex.sub_re,
      Complex.sub_im]
    ring
  have hsq : ‖z - c‖ ^ 2 = (z.re - c) ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  unfold gaussTest
  rw [norm_mul, Complex.norm_pow, Complex.norm_exp, hsq, hre]

lemma norm_term (c lam : ℝ) (ρ : ℂ) :
    ‖term c lam ρ‖ = (WeilExplicit.zeroMult ρ : ℝ) * wsq c ρ * Real.exp (2 * lam * phi c ρ) := by
  unfold term
  rw [norm_mul, Complex.norm_natCast, norm_gaussTest, Zeta23.WeilEF.gammaOf_re,
    Zeta23.WeilEF.gammaOf_im]
  unfold wsq phi
  ring

/-- Re G_{c,lam}(z) = e^{2 lam phi} [ (x^2 - y^2) cos (4 lam x y) + 2 x y sin (4 lam x y) ],
x = Re z - c, y = Im z. -/
lemma re_gaussTest (c lam : ℝ) (z : ℂ) :
    (gaussTest c lam z).re = Real.exp (2 * lam * (z.im ^ 2 - (z.re - c) ^ 2))
      * (((z.re - c) ^ 2 - z.im ^ 2) * Real.cos (4 * lam * (z.re - c) * z.im)
        + 2 * (z.re - c) * z.im * Real.sin (4 * lam * (z.re - c) * z.im)) := by
  unfold gaussTest
  have hw2re : ((z - c) ^ 2).re = (z.re - c) ^ 2 - z.im ^ 2 := by
    simp only [pow_two, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have hw2im : ((z - c) ^ 2).im = 2 * (z.re - c) * z.im := by
    simp only [pow_two, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have hEre : (-(2 * (lam : ℂ)) * (z - c) ^ 2).re = 2 * lam * (z.im ^ 2 - (z.re - c) ^ 2) := by
    simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.re_ofNat,
      Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im, hw2re, hw2im]
    ring
  have hEim : (-(2 * (lam : ℂ)) * (z - c) ^ 2).im = -(4 * lam * (z.re - c) * z.im) := by
    simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.re_ofNat,
      Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im, hw2re, hw2im]
    ring
  rw [Complex.mul_re, Complex.exp_re, Complex.exp_im, hEre, hEim, hw2re, hw2im, Real.cos_neg,
    Real.sin_neg]
  ring

/-! ## C. The phase: a lam >= lam_0 at which the bracket equals -(x^2 + y^2). -/

/-- For y != 0 and any lam_0 there is lam >= lam_0 with
(x^2 - y^2) cos (4 lam x y) + 2 x y sin (4 lam x y) = -(x^2 + y^2). -/
lemma exists_lam_trig (lam₀ x y : ℝ) (hy : y ≠ 0) :
    ∃ lam : ℝ, lam₀ ≤ lam ∧
      (x ^ 2 - y ^ 2) * Real.cos (4 * lam * x * y) + 2 * x * y * Real.sin (4 * lam * x * y)
        = -(x ^ 2 + y ^ 2) := by
  by_cases hx : x = 0
  · refine ⟨lam₀, le_rfl, ?_⟩
    subst hx
    simp
  -- the target point on the unit circle: theta = arg (-(x + i y)^2)
  set z₀ : ℂ := ⟨-(x ^ 2 - y ^ 2), -(2 * x * y)⟩ with hz₀
  have hz₀ne : z₀ ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [hz₀, Complex.zero_im] at this
    have hxy : x * y ≠ 0 := mul_ne_zero hx hy
    apply hxy
    linarith
  have hnorm : ‖z₀‖ = x ^ 2 + y ^ 2 := by
    have h1 : ‖z₀‖ ^ 2 = (x ^ 2 + y ^ 2) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [hz₀]
      ring
    have h2 : 0 ≤ ‖z₀‖ := norm_nonneg _
    have h3 : 0 ≤ x ^ 2 + y ^ 2 := by positivity
    exact (pow_left_inj₀ h2 h3 two_ne_zero).mp h1
  set θ : ℝ := Complex.arg z₀ with hθ
  have hcos : Real.cos θ = -(x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2) := by
    rw [hθ, Complex.cos_arg hz₀ne, hnorm]
  have hsin : Real.sin θ = -(2 * x * y) / (x ^ 2 + y ^ 2) := by
    rw [hθ, Complex.sin_arg, hnorm]
  have hpos : 0 < x ^ 2 + y ^ 2 := by positivity
  have hval : (x ^ 2 - y ^ 2) * Real.cos θ + 2 * x * y * Real.sin θ = -(x ^ 2 + y ^ 2) := by
    rw [hcos, hsin]
    field_simp
    ring
  -- choose the integer k so that lam := (theta + k 2pi)/(4 x y) >= lam_0
  have h4 : 4 * x * y ≠ 0 := by
    have := mul_ne_zero hx hy
    intro h
    apply this
    linarith
  obtain ⟨k, hk⟩ : ∃ k : ℤ, lam₀ ≤ (θ + k * (2 * Real.pi)) / (4 * x * y) := by
    rcases lt_or_gt_of_ne h4 with hneg | hpos4
    · obtain ⟨k, hk⟩ := exists_int_lt ((4 * x * y * lam₀ - θ) / (2 * Real.pi))
      refine ⟨k, ?_⟩
      rw [le_div_iff_of_neg hneg]
      have h2π : 0 < 2 * Real.pi := by positivity
      have := (lt_div_iff₀ h2π).mp hk
      linarith
    · obtain ⟨k, hk⟩ := exists_int_gt ((4 * x * y * lam₀ - θ) / (2 * Real.pi))
      refine ⟨k, ?_⟩
      rw [le_div_iff₀ hpos4]
      have h2π : 0 < 2 * Real.pi := by positivity
      have := (div_lt_iff₀ h2π).mp hk
      linarith
  refine ⟨(θ + k * (2 * Real.pi)) / (4 * x * y), hk, ?_⟩
  have hang : 4 * ((θ + k * (2 * Real.pi)) / (4 * x * y)) * x * y = θ + k * (2 * Real.pi) := by
    field_simp
  rw [hang, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]
  exact hval

/-- The phase lemma on the Gaussian summand: for Im z != 0 and any lam_0 there is lam >= lam_0
with Re G_{c,lam}(z) = -((Re z - c)^2 + (Im z)^2) e^{2 lam ((Im z)^2 - (Re z - c)^2)}. -/
lemma exists_lam_re_gaussTest (c lam₀ : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    ∃ lam : ℝ, lam₀ ≤ lam ∧ (gaussTest c lam z).re
      = -(((z.re - c) ^ 2 + z.im ^ 2) * Real.exp (2 * lam * (z.im ^ 2 - (z.re - c) ^ 2))) := by
  obtain ⟨lam, hlam, hval⟩ := exists_lam_trig lam₀ (z.re - c) z.im hz
  refine ⟨lam, hlam, ?_⟩
  rw [re_gaussTest, hval]
  ring

/-! ## D. The window, the generic centre, the maximiser and the gap. -/

/-- The finite window of nontrivial zeros with Im rho_0 - 1 < Im rho <= Im rho_0 + 1. -/
def windowSet (ρ₀ : ℂ) : Set ℂ :=
  {ρ | IsNontrivialZero ρ} ∩ {ρ | ρ₀.im - 1 < ρ.im ∧ ρ.im ≤ ρ₀.im + 1}

lemma windowSet_finite (ρ₀ : ℂ) : (windowSet ρ₀).Finite :=
  zetaSeam.finite_window (ρ₀.im - 1) (ρ₀.im + 1)

/-- The window as a Finset. -/
def window (ρ₀ : ℂ) : Finset ℂ := (windowSet_finite ρ₀).toFinset

lemma mem_window {ρ₀ ρ : ℂ} :
    ρ ∈ window ρ₀ ↔ IsNontrivialZero ρ ∧ (ρ₀.im - 1 < ρ.im ∧ ρ.im ≤ ρ₀.im + 1) := by
  unfold window
  rw [Set.Finite.mem_toFinset]
  rfl

lemma self_mem_window {ρ₀ : ℂ} (h : IsNontrivialZero ρ₀) : ρ₀ ∈ window ρ₀ :=
  mem_window.mpr ⟨h, by linarith, by linarith⟩

/-- The unique centre at which two zeros of different ordinates tie in phi. -/
def badOf (ρ ρ' : ℂ) : ℝ :=
  (ρ.im ^ 2 - ρ'.im ^ 2 - (1 / 2 - ρ.re) ^ 2 + (1 / 2 - ρ'.re) ^ 2) / (2 * (ρ.im - ρ'.im))

lemma eq_badOf_of_phi_eq {c : ℝ} {ρ ρ' : ℂ} (him : ρ.im ≠ ρ'.im) (h : phi c ρ = phi c ρ') :
    c = badOf ρ ρ' := by
  unfold phi at h
  unfold badOf
  have hne : ρ.im - ρ'.im ≠ 0 := sub_ne_zero.mpr him
  rw [eq_div_iff (mul_ne_zero two_ne_zero hne)]
  linear_combination h

/-- The finite set of bad centres for the window. -/
def badSet (ρ₀ : ℂ) : Finset ℝ :=
  (window ρ₀ ×ˢ window ρ₀).image (fun p : ℂ × ℂ => badOf p.1 p.2)

lemma badOf_mem_badSet {ρ₀ ρ ρ' : ℂ} (h : ρ ∈ window ρ₀) (h' : ρ' ∈ window ρ₀) :
    badOf ρ ρ' ∈ badSet ρ₀ :=
  Finset.mem_image.mpr ⟨(ρ, ρ'), Finset.mem_product.mpr ⟨h, h'⟩, rfl⟩

/-- A generic centre exists in the interval |c - Im rho_0| < |1/2 - Re rho_0|. -/
lemma exists_generic_centre {ρ₀ : ℂ} (h₀ : ρ₀.re ≠ 1 / 2) :
    ∃ c : ℝ, |c - ρ₀.im| < |1 / 2 - ρ₀.re| ∧ c ∉ badSet ρ₀ := by
  have hy : 0 < |1 / 2 - ρ₀.re| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h₀))
  have hinf : (Set.Ioo (ρ₀.im - |1 / 2 - ρ₀.re|) (ρ₀.im + |1 / 2 - ρ₀.re|)).Infinite :=
    Set.Ioo_infinite (by linarith)
  obtain ⟨c, hc⟩ := (hinf.sdiff (badSet ρ₀).finite_toSet).nonempty
  refine ⟨c, ?_, ?_⟩
  · have := hc.1
    rw [Set.mem_Ioo] at this
    rw [abs_lt]
    constructor <;> linarith [this.1, this.2]
  · have := hc.2
    simpa using this

/-- Two zeros of the window with the same phi_c at a generic centre are the same point up to
the reflection rho -> 1 - conj rho. -/
lemma eq_or_eq_reflect_of_phi_eq {ρ₀ : ℂ} {c : ℝ} (hc : c ∉ badSet ρ₀) {ρ ρ' : ℂ}
    (h : ρ ∈ window ρ₀) (h' : ρ' ∈ window ρ₀) (hphi : phi c ρ = phi c ρ') :
    ρ = ρ' ∨ ρ = reflect ρ' := by
  have him : ρ.im = ρ'.im := by
    by_contra hne
    exact hc (eq_badOf_of_phi_eq hne hphi ▸ badOf_mem_badSet h h')
  unfold phi at hphi
  rw [him] at hphi
  have hsq : (1 / 2 - ρ.re) ^ 2 = (1 / 2 - ρ'.re) ^ 2 := by linarith
  have hfac : (ρ.re - ρ'.re) * (ρ.re + ρ'.re - 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfac with h1 | h1
  · left
    apply Complex.ext
    · linarith
    · exact him
  · right
    apply Complex.ext
    · simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    · simp only [reflect, Complex.sub_im, Complex.one_im, Complex.conj_im]
      linarith

/-- The maximiser of phi_c on the window and the gap to the rest of the window. -/
lemma exists_maximiser_gap {ρ₀ : ℂ} (h₀ : IsNontrivialZero ρ₀) {c : ℝ} (hc : c ∉ badSet ρ₀) :
    ∃ ρ₁ ∈ window ρ₀, (∀ ρ ∈ window ρ₀, phi c ρ ≤ phi c ρ₁) ∧
      ∃ η : ℝ, 0 < η ∧ ∀ ρ ∈ window ρ₀, ρ ≠ ρ₁ → ρ ≠ reflect ρ₁ → phi c ρ ≤ phi c ρ₁ - η := by
  classical
  obtain ⟨ρ₁, hρ₁, hmax⟩ := Finset.exists_max_image (window ρ₀) (phi c)
    ⟨ρ₀, self_mem_window h₀⟩
  refine ⟨ρ₁, hρ₁, hmax, ?_⟩
  have hlt : ∀ ρ ∈ window ρ₀, ρ ≠ ρ₁ → ρ ≠ reflect ρ₁ → phi c ρ < phi c ρ₁ := by
    intro ρ hρ hne hne'
    rcases lt_or_eq_of_le (hmax ρ hρ) with hlt | heq
    · exact hlt
    · rcases eq_or_eq_reflect_of_phi_eq hc hρ hρ₁ heq with h | h
      · exact absurd h hne
      · exact absurd h hne'
  set F₁ : Finset ℂ := ((window ρ₀).erase ρ₁).erase (reflect ρ₁) with hF₁
  have hmemF₁ : ∀ ρ, ρ ∈ F₁ ↔ ρ ∈ window ρ₀ ∧ ρ ≠ ρ₁ ∧ ρ ≠ reflect ρ₁ := by
    intro ρ
    simp only [hF₁, Finset.mem_erase]
    tauto
  rcases F₁.eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, one_pos, fun ρ hρ hne hne' => ?_⟩
    have : ρ ∈ F₁ := (hmemF₁ ρ).mpr ⟨hρ, hne, hne'⟩
    rw [hemp] at this
    exact absurd this (Finset.notMem_empty ρ)
  · obtain ⟨ρ₂, hρ₂, hmax₂⟩ := Finset.exists_max_image F₁ (phi c) hne
    obtain ⟨hρ₂w, hρ₂ne, hρ₂ne'⟩ := (hmemF₁ ρ₂).mp hρ₂
    refine ⟨phi c ρ₁ - phi c ρ₂, by linarith [hlt ρ₂ hρ₂w hρ₂ne hρ₂ne'], ?_⟩
    intro ρ hρ hne hne'
    have := hmax₂ ρ ((hmemF₁ ρ).mpr ⟨hρ, hne, hne'⟩)
    linarith

/-- Outside the window (for a centre within 1/2 of Im rho_0) phi_c is negative. -/
lemma phi_neg_of_not_mem_window {ρ₀ : ℂ} {c : ℝ} (hc : |c - ρ₀.im| < 1 / 2) {ρ : ℂ}
    (hρ : IsNontrivialZero ρ) (hnot : ρ ∉ window ρ₀) : phi c ρ < 0 := by
  have hw : ¬ (ρ₀.im - 1 < ρ.im ∧ ρ.im ≤ ρ₀.im + 1) := fun h => hnot (mem_window.mpr ⟨hρ, h⟩)
  have hfar : 1 ≤ |ρ.im - ρ₀.im| := by
    rcases le_or_gt ρ.im (ρ₀.im - 1) with h | h
    · rw [le_abs]
      right
      linarith
    · have h' : ρ₀.im + 1 < ρ.im := by
        by_contra h''
        exact hw ⟨h, not_lt.mp h''⟩
      rw [le_abs]
      left
      linarith
  have hc' := abs_lt.mp hc
  have hx : 1 / 2 < |ρ.im - c| := by
    have : ρ.im - c = (ρ.im - ρ₀.im) - (c - ρ₀.im) := by ring
    rw [this]
    have := abs_sub_abs_le_abs_sub (ρ.im - ρ₀.im) (c - ρ₀.im)
    linarith
  have hy : |1 / 2 - ρ.re| < 1 / 2 := by
    rw [abs_lt]
    constructor <;> linarith [hρ.2.1, hρ.2.2]
  unfold phi
  have h1 : (1 / 2 - ρ.re) ^ 2 < (1 / 2) ^ 2 := by
    rw [← sq_abs]
    exact pow_lt_pow_left₀ hy (abs_nonneg _) two_ne_zero
  have h2 : (1 / 2) ^ 2 < (ρ.im - c) ^ 2 := by
    rw [← sq_abs (ρ.im - c)]
    exact pow_lt_pow_left₀ hx (by norm_num) two_ne_zero
  linarith

/-! ## E. The tail: a lam-uniform-in-shape majorant for every summand off the pair. -/

/-- The majorant D_lam(rho) = e^{2 lam (M - eta)} [rho in W] m |w|^2 + m C_1/(1 + |gamma_rho|^2). -/
def majorant (ρ₀ : ℂ) (c M η : ℝ) (lam : ℝ) (ρ : ℂ) : ℝ :=
  Real.exp (2 * lam * (M - η))
      * (if ρ ∈ window ρ₀ then (WeilExplicit.zeroMult ρ : ℝ) * wsq c ρ else 0)
    + (WeilExplicit.zeroMult ρ : ℝ)
      * ((Real.exp (1 / 2) * (2 * c ^ 2 + 13 / 4) / (min 1 1) ^ 2)
          / (1 + Complex.normSq (gammaOf ρ)))

lemma majorant_nonneg (ρ₀ : ℂ) (c M η lam : ℝ) (ρ : ℂ) : 0 ≤ majorant ρ₀ c M η lam ρ := by
  unfold majorant
  have h1 : 0 ≤ (if ρ ∈ window ρ₀ then (WeilExplicit.zeroMult ρ : ℝ) * wsq c ρ else 0) := by
    split_ifs
    · unfold wsq
      positivity
    · exact le_rfl
  have h2 : 0 ≤ (WeilExplicit.zeroMult ρ : ℝ)
      * ((Real.exp (1 / 2) * (2 * c ^ 2 + 13 / 4) / (min 1 1) ^ 2)
          / (1 + Complex.normSq (gammaOf ρ))) := by
    have := Complex.normSq_nonneg (gammaOf ρ)
    have hmin : (0 : ℝ) < min 1 1 := by norm_num
    positivity
  have h3 : 0 ≤ Real.exp (2 * lam * (M - η)) := (Real.exp_pos _).le
  nlinarith [mul_nonneg h3 h1]

lemma summable_majorant (ρ₀ : ℂ) (c M η lam : ℝ) : Summable (majorant ρ₀ c M η lam) := by
  unfold majorant
  refine Summable.add ((summable_of_ne_finset_zero (s := window ρ₀) ?_).mul_left _)
    (summable_mult_div_one_add_normSq _)
  intro ρ hρ
  exact if_neg hρ

/-- The pointwise tail bound for lam >= 1 and rho off the pair of the maximiser. -/
lemma norm_term_le_majorant {ρ₀ : ℂ} {c : ℝ} (hc : |c - ρ₀.im| < 1 / 2) {ρ₁ : ℂ} {η : ℝ}
    (hgap : ∀ ρ ∈ window ρ₀, ρ ≠ ρ₁ → ρ ≠ reflect ρ₁ → phi c ρ ≤ phi c ρ₁ - η)
    {lam : ℝ} (hlam : 1 ≤ lam) {ρ : ℂ} (hne : ρ ≠ ρ₁) (hne' : ρ ≠ reflect ρ₁) :
    ‖term c lam ρ‖ ≤ majorant ρ₀ c (phi c ρ₁) η lam ρ := by
  by_cases hnt : IsNontrivialZero ρ
  · rw [norm_term]
    unfold majorant
    have hw : 0 ≤ wsq c ρ := by unfold wsq; positivity
    have hm : (0 : ℝ) ≤ WeilExplicit.zeroMult ρ := Nat.cast_nonneg _
    have hsecond : 0 ≤ (WeilExplicit.zeroMult ρ : ℝ)
        * ((Real.exp (1 / 2) * (2 * c ^ 2 + 13 / 4) / (min 1 1) ^ 2)
            / (1 + Complex.normSq (gammaOf ρ))) := by
      have := Complex.normSq_nonneg (gammaOf ρ)
      have hmin : (0 : ℝ) < min 1 1 := by norm_num
      positivity
    by_cases hW : ρ ∈ window ρ₀
    · rw [if_pos hW]
      have hφ := hgap ρ hW hne hne'
      have hexp : Real.exp (2 * lam * phi c ρ) ≤ Real.exp (2 * lam * (phi c ρ₁ - η)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have : (WeilExplicit.zeroMult ρ : ℝ) * wsq c ρ * Real.exp (2 * lam * phi c ρ)
          ≤ Real.exp (2 * lam * (phi c ρ₁ - η)) * ((WeilExplicit.zeroMult ρ : ℝ) * wsq c ρ) := by
        have := mul_le_mul_of_nonneg_left hexp (mul_nonneg hm hw)
        linarith
      linarith
    · rw [if_neg hW, mul_zero, zero_add]
      have hφ : phi c ρ < 0 := phi_neg_of_not_mem_window hc hnt hW
      -- lam >= 1 and phi < 0: e^{2 lam phi} <= e^{2 phi}
      have hexp : Real.exp (2 * lam * phi c ρ) ≤ Real.exp (2 * 1 * phi c ρ) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have h1 : (WeilExplicit.zeroMult ρ : ℝ) * wsq c ρ * Real.exp (2 * lam * phi c ρ)
          ≤ (WeilExplicit.zeroMult ρ : ℝ) * wsq c ρ * Real.exp (2 * 1 * phi c ρ) :=
        mul_le_mul_of_nonneg_left hexp (mul_nonneg hm hw)
      have h2 : (WeilExplicit.zeroMult ρ : ℝ) * wsq c ρ * Real.exp (2 * 1 * phi c ρ)
          = ‖term c 1 ρ‖ := (norm_term c 1 ρ).symm
      have hz : |(gammaOf ρ).im| ≤ 1 / 2 := (Zeta23.WeilEF.abs_gammaOf_im_lt hnt.2).le
      have hb := norm_gaussTest_mul_le c 1 one_pos hz
      have hpos : 0 < 1 + Complex.normSq (gammaOf ρ) := by
        have := Complex.normSq_nonneg (gammaOf ρ)
        linarith
      have h3 : ‖gaussTest c 1 (gammaOf ρ)‖
          ≤ (Real.exp (1 / 2) * (2 * c ^ 2 + 13 / 4) / (min 1 1) ^ 2)
            / (1 + Complex.normSq (gammaOf ρ)) := by
        rw [le_div_iff₀ hpos]
        have : (1 : ℝ) / 2 = 1 / 2 := rfl
        simpa using hb
      have h4 : ‖term c 1 ρ‖ = (WeilExplicit.zeroMult ρ : ℝ) * ‖gaussTest c 1 (gammaOf ρ)‖ := by
        unfold term
        rw [norm_mul, Complex.norm_natCast]
      calc (WeilExplicit.zeroMult ρ : ℝ) * wsq c ρ * Real.exp (2 * lam * phi c ρ)
          ≤ ‖term c 1 ρ‖ := h1.trans_eq h2
        _ = (WeilExplicit.zeroMult ρ : ℝ) * ‖gaussTest c 1 (gammaOf ρ)‖ := h4
        _ ≤ _ := mul_le_mul_of_nonneg_left h3 hm
  · have : term c lam ρ = 0 := by
      unfold term
      rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial hnt]
      simp
    rw [this, norm_zero]
    exact majorant_nonneg _ _ _ _ _ _

/-- The finite window constant A and the majorant constant B. -/
def constA (ρ₀ : ℂ) (c : ℝ) : ℝ :=
  ∑ ρ ∈ window ρ₀, (WeilExplicit.zeroMult ρ : ℝ) * wsq c ρ

def constB (c : ℝ) : ℝ :=
  ∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℝ)
    * ((Real.exp (1 / 2) * (2 * c ^ 2 + 13 / 4) / (min 1 1) ^ 2)
        / (1 + Complex.normSq (gammaOf ρ)))

lemma constA_nonneg (ρ₀ : ℂ) (c : ℝ) : 0 ≤ constA ρ₀ c :=
  Finset.sum_nonneg fun ρ _ => by unfold wsq; positivity

lemma constB_nonneg (c : ℝ) : 0 ≤ constB c :=
  tsum_nonneg fun ρ => by
    have := Complex.normSq_nonneg (gammaOf ρ)
    have hmin : (0 : ℝ) < min 1 1 := by norm_num
    positivity

lemma tsum_majorant (ρ₀ : ℂ) (c M η lam : ℝ) :
    ∑' ρ : ℂ, majorant ρ₀ c M η lam ρ = Real.exp (2 * lam * (M - η)) * constA ρ₀ c + constB c := by
  unfold majorant constA constB
  rw [((summable_of_ne_finset_zero (s := window ρ₀) fun ρ hρ => if_neg hρ).mul_left _).tsum_add
    (summable_mult_div_one_add_normSq _), tsum_mul_left]
  congr 2
  rw [tsum_eq_sum (s := window ρ₀) fun ρ hρ => if_neg hρ]
  exact Finset.sum_congr rfl fun ρ hρ => if_pos hρ

/-- The tail sum over all rho off the pair is at most A e^{2 lam (M - eta)} + B for lam >= 1. -/
lemma tail_bound {ρ₀ : ℂ} {c : ℝ} (hc : |c - ρ₀.im| < 1 / 2) {ρ₁ : ℂ} {η : ℝ}
    (hgap : ∀ ρ ∈ window ρ₀, ρ ≠ ρ₁ → ρ ≠ reflect ρ₁ → phi c ρ ≤ phi c ρ₁ - η)
    {lam : ℝ} (hlam : 1 ≤ lam) :
    ‖∑' ρ : {ρ : ℂ // ρ ≠ ρ₁ ∧ ρ ≠ reflect ρ₁}, term c lam ρ‖
      ≤ Real.exp (2 * lam * (phi c ρ₁ - η)) * constA ρ₀ c + constB c := by
  rw [← tsum_majorant ρ₀ c (phi c ρ₁) η lam]
  exact norm_tsum_subtype_le_tsum {ρ : ℂ | ρ ≠ ρ₁ ∧ ρ ≠ reflect ρ₁}
    (summable_majorant ρ₀ c (phi c ρ₁) η lam) (majorant_nonneg ρ₀ c (phi c ρ₁) η lam)
    fun ρ => norm_term_le_majorant hc hgap hlam ρ.2.1 ρ.2.2

/-! ## F. Assembly: the theorem. -/

/-- The real part of the Gaussian zero side, pair term plus tail. -/
lemma re_zeroSide_le {ρ₀ : ℂ} {c : ℝ} (hc : |c - ρ₀.im| < 1 / 2) {ρ₁ : ℂ} (h₁ : ρ₁.re ≠ 1 / 2)
    {η : ℝ} (hgap : ∀ ρ ∈ window ρ₀, ρ ≠ ρ₁ → ρ ≠ reflect ρ₁ → phi c ρ ≤ phi c ρ₁ - η)
    {lam : ℝ} (hlam : 1 ≤ lam) :
    (zeroSide (gaussTest c lam)).re
      ≤ 2 * (WeilExplicit.zeroMult ρ₁ : ℝ) * (gaussTest c lam (gammaOf ρ₁)).re
        + (Real.exp (2 * lam * (phi c ρ₁ - η)) * constA ρ₀ c + constB c) := by
  have hlam0 : 0 < lam := by linarith
  rw [zeroSide_pair_split (gaussTest_conj c lam) (summable_gauss_zeroSide c lam hlam0) h₁,
    Complex.add_re]
  have hre : (2 * (WeilExplicit.zeroMult ρ₁ : ℂ) * ((gaussTest c lam (gammaOf ρ₁)).re : ℂ)).re
      = 2 * (WeilExplicit.zeroMult ρ₁ : ℝ) * (gaussTest c lam (gammaOf ρ₁)).re := by
    have : (2 * (WeilExplicit.zeroMult ρ₁ : ℂ) * ((gaussTest c lam (gammaOf ρ₁)).re : ℂ))
        = ((2 * (WeilExplicit.zeroMult ρ₁ : ℝ) * (gaussTest c lam (gammaOf ρ₁)).re : ℝ) : ℂ) := by
      push_cast
      ring
    rw [this, Complex.ofReal_re]
  rw [hre]
  have htail := tail_bound hc hgap hlam
  have hgoal : (∑' ρ : {ρ : ℂ // ρ ≠ ρ₁ ∧ ρ ≠ reflect ρ₁},
      (WeilExplicit.zeroMult ρ : ℂ) * gaussTest c lam (gammaOf ρ)).re
      ≤ Real.exp (2 * lam * (phi c ρ₁ - η)) * constA ρ₀ c + constB c :=
    le_trans (Complex.re_le_norm _) htail
  linarith

/-- **O2 discharged**: an off-line nontrivial zero forces a negative Gaussian zero sum. -/
theorem gaussian_dominance : RvMBridge6.GaussianDominance := by
  intro ρ₀ h₀ hre₀
  -- (2) generic centre
  obtain ⟨c, hcI, hcbad⟩ := exists_generic_centre hre₀
  have hy₀ : |1 / 2 - ρ₀.re| < 1 / 2 := by
    rw [abs_lt]
    constructor <;> linarith [h₀.2.1, h₀.2.2]
  have hc : |c - ρ₀.im| < 1 / 2 := hcI.trans hy₀
  -- (3) maximiser and gap
  obtain ⟨ρ₁, hρ₁, hmax, η, hη, hgap⟩ := exists_maximiser_gap h₀ hcbad
  have hρ₁nt : IsNontrivialZero ρ₁ := (mem_window.mp hρ₁).1
  set M : ℝ := phi c ρ₁ with hM
  have hM0 : 0 < M := by
    have h1 : phi c ρ₀ ≤ M := hmax ρ₀ (self_mem_window h₀)
    have h2 : 0 < phi c ρ₀ := by
      unfold phi
      have ha : (ρ₀.im - c) ^ 2 < (1 / 2 - ρ₀.re) ^ 2 := by
        rw [← sq_abs (ρ₀.im - c), ← sq_abs (1 / 2 - ρ₀.re), abs_sub_comm]
        exact pow_lt_pow_left₀ hcI (abs_nonneg _) two_ne_zero
      linarith
    linarith
  have hy₁ : (1 / 2 - ρ₁.re) ^ 2 > 0 := by
    have : phi c ρ₁ = (1 / 2 - ρ₁.re) ^ 2 - (ρ₁.im - c) ^ 2 := rfl
    nlinarith [sq_nonneg (ρ₁.im - c)]
  have h₁ : ρ₁.re ≠ 1 / 2 := by
    intro h
    rw [h] at hy₁
    simp at hy₁
  have hm₁ : (1 : ℝ) ≤ WeilExplicit.zeroMult ρ₁ := by
    rw [RvMBridge4.zeroMult_eq_mult hρ₁nt]
    exact_mod_cast zetaSeam.one_le_mult ρ₁ hρ₁nt
  -- the constants
  set K : ℝ := (WeilExplicit.zeroMult ρ₁ : ℝ) * wsq c ρ₁ with hK
  have hwsq : 0 < wsq c ρ₁ := by
    unfold wsq
    nlinarith [sq_nonneg (ρ₁.im - c)]
  have hK0 : 0 < K := mul_pos (by linarith) hwsq
  set A := constA ρ₀ c with hA
  set B := constB c with hB
  have hA0 : 0 ≤ A := constA_nonneg ρ₀ c
  have hB0 : 0 ≤ B := constB_nonneg c
  set lam₀ : ℝ := max 1 (max (A / (2 * η * K)) (B / (2 * M * K))) with hlam₀
  -- (5) the phase
  have hzim : (gammaOf ρ₁).im ≠ 0 := by
    rw [Zeta23.WeilEF.gammaOf_im]
    exact sub_ne_zero.mpr (Ne.symm h₁)
  obtain ⟨lam, hlam, hphase⟩ := exists_lam_re_gaussTest c lam₀ hzim
  have hlam1 : 1 ≤ lam := (le_max_left _ _).trans hlam
  have hlamA : A / (2 * η * K) ≤ lam := ((le_max_left _ _).trans (le_max_right _ _)).trans hlam
  have hlamB : B / (2 * M * K) ≤ lam := ((le_max_right _ _).trans (le_max_right _ _)).trans hlam
  refine ⟨c, lam, by linarith, ?_⟩
  -- (6) assembly
  have hmain := re_zeroSide_le hc h₁ hgap hlam1
  rw [hphase, Zeta23.WeilEF.gammaOf_re, Zeta23.WeilEF.gammaOf_im] at hmain
  have hpair : 2 * (WeilExplicit.zeroMult ρ₁ : ℝ)
      * -(((ρ₁.im - c) ^ 2 + (1 / 2 - ρ₁.re) ^ 2)
          * Real.exp (2 * lam * ((1 / 2 - ρ₁.re) ^ 2 - (ρ₁.im - c) ^ 2)))
      = -(2 * K * Real.exp (2 * lam * M)) := by
    simp only [hK, hM, wsq, phi]
    ring
  rw [hpair] at hmain
  -- e^{2 lam eta} >= A / K and e^{2 lam M} > B / K
  have hexpη : A ≤ K * Real.exp (2 * lam * η) := by
    have h1 : A / K ≤ 2 * lam * η := by
      rw [div_le_iff₀ hK0]
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * η * K)).mp hlamA
      linarith
    have h2 : 2 * lam * η + 1 ≤ Real.exp (2 * lam * η) := Real.add_one_le_exp _
    have h3 : A / K ≤ Real.exp (2 * lam * η) := by linarith
    rwa [div_le_iff₀ hK0, mul_comm] at h3
  have hexpM : B < K * Real.exp (2 * lam * M) := by
    have h1 : B / K ≤ 2 * lam * M := by
      rw [div_le_iff₀ hK0]
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * M * K)).mp hlamB
      linarith
    have h2 : 2 * lam * M + 1 ≤ Real.exp (2 * lam * M) := Real.add_one_le_exp _
    have h3 : B / K < Real.exp (2 * lam * M) := by linarith
    rwa [div_lt_iff₀ hK0, mul_comm] at h3
  have hsplit : Real.exp (2 * lam * (M - η)) * Real.exp (2 * lam * η) = Real.exp (2 * lam * M) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hE1 : 0 < Real.exp (2 * lam * (M - η)) := Real.exp_pos _
  have hAterm : Real.exp (2 * lam * (M - η)) * A ≤ K * Real.exp (2 * lam * M) := by
    calc Real.exp (2 * lam * (M - η)) * A
        ≤ Real.exp (2 * lam * (M - η)) * (K * Real.exp (2 * lam * η)) :=
          mul_le_mul_of_nonneg_left hexpη hE1.le
      _ = K * (Real.exp (2 * lam * (M - η)) * Real.exp (2 * lam * η)) := by ring
      _ = K * Real.exp (2 * lam * M) := by rw [hsplit]
  linarith

/-- The Weil converse with O2 discharged: positivity implies RH modulo the single zero-free
Fourier obligation GaussianApprox (E6Bridge6, section H). -/
theorem weil_positivity_implies_rh_of_approx (hA : RvMBridge6.GaussianApprox)
    (hpos : ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g →
      0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re) :
    RiemannHypothesis :=
  RvMBridge6.weil_positivity_implies_rh_of' hA gaussian_dominance hpos

end RvMBridge7
