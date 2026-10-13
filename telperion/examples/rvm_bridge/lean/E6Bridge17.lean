/-
  E6Bridge17 -- THE PLAIN GAUSSIAN FACE (Theta) and its heat monotonicity (2026-09-21).
  Survey: telperion/docs/research/FIXED_WIDTH_LENS_HEAT_2026-09-21.md (lens 1'); memo:
  telperion/docs/WALL_THETA_FACE_2026-09-21.md.

      plainGauss c lam z := exp (-2 lam (z - c)^2)
      Theta c lam        := Re Sum_rho m(rho) plainGauss c lam (gamma_rho),  gamma_rho = (rho - 1/2)/i.

  Delivered (all #print axioms = [propext, Classical.choice, Quot.sound], no `sorry`):
    (1) rh_iff_theta_positivity : RiemannHypothesis <-> forall c lam, 0 < lam -> 0 <= Theta c lam.
        Forward: on the line every summand is m e^{-2 lam (Im rho - c)^2} >= 0.  Converse: E6Bridge7's
        six steps with the bracket cos (4 lam x y) in place of (x^2 - y^2) cos + 2 x y sin: at a generic
        centre (avoiding the finitely many tying centres AND the finitely many window ordinates, so the
        maximiser has x != 0) the pair term of the maximiser is 2 m e^{2 lam M} cos (4 lam x y), and
        lam = (pi + 2 pi k)/(4 x y) makes the cosine -1; the tail is the plain majorant.
    (2) theta_heat (identity (M)): for 0 < lam' < lam,
          Theta c lam' = sqrt (lam/lam') * int heatKernel sigma2 (c - c') * Theta c' lam dc',
        sigma2 = 1/(4 lam') - 1/(4 lam) = (lam - lam')/(4 lam lam'); termwise (plainGauss_heat, a
        complex-centre Gaussian convolution via Mathlib's integral_cexp_quadratic) then summed
        (integral_tsum_of_summable_integral_norm against the local-count majorant).  Corollary
        theta_pos_mono: positivity at width lam gives positivity at every smaller width.
    (3) ThetaFree lam := forall c, 0 <= Theta c lam;  thetaFree_mono (downward closed);
        rh_iff_thetaFree_all;  not_thetaFree_of_offline: an off-line zero gives Lambda with
        not ThetaFree lam for EVERY lam > Lambda (one negative width from (1) plus (2)).

  2026-09-22: the countability of the zero set (formerly nontrivialZeros_countable here, re-proved
  as zeros_countable in E6Bridge19) and the finite-avoidance radius are the prelude's
  (RvMBridgeXi.nontrivialZeros_countable / exists_mem_Ioo_notMem_finset); the node theorems here
  are unchanged, statements verbatim.

  conjecture1_proved = False.  RH <-> Lambda_Theta = infinity where Lambda_Theta := sup of the free
  widths; certified widths bound Lambda_Theta from below and that is a wall, not a crossing.
-/
import E6Bridge14
import RvMBridgeXi
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Constructions.Polish.Basic

open Zeta23 Complex MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace RvMBridge17
open WeilExplicit RvMBridge6 RvMBridge7 RvMBridge12 RvMBridge14 RvMBridgeGauss

/-! ## A. The plain Gaussian face. -/

/-- The plain Gaussian transform G_{c,lam}(z) = exp (-2 lam (z - c)^2). -/
def plainGauss (c lam : ℝ) (z : ℂ) : ℂ := Complex.exp (-(2 * lam) * (z - c) ^ 2)

/-- The plain Gaussian face Theta(c, lam) = Re Sum_rho m(rho) G_{c,lam}(gamma_rho). -/
def Theta (c lam : ℝ) : ℝ := (zeroSide (plainGauss c lam)).re

/-- The summand. -/
def pterm (c lam : ℝ) (ρ : ℂ) : ℂ := (WeilExplicit.zeroMult ρ : ℂ) * plainGauss c lam (gammaOf ρ)

lemma zeroSide_plain_eq (c lam : ℝ) : zeroSide (plainGauss c lam) = ∑' ρ : ℂ, pterm c lam ρ := rfl

lemma theta_eq (c lam : ℝ) : Theta c lam = (∑' ρ : ℂ, pterm c lam ρ).re := rfl

lemma plainGauss_re_exponent (c lam : ℝ) (z : ℂ) :
    (-(2 * (lam : ℂ)) * (z - c) ^ 2).re = 2 * lam * (z.im ^ 2 - (z.re - c) ^ 2) := by
  simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.re_ofNat,
    Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im, pow_two, Complex.sub_re,
    Complex.sub_im]
  ring

lemma plainGauss_im_exponent (c lam : ℝ) (z : ℂ) :
    (-(2 * (lam : ℂ)) * (z - c) ^ 2).im = -(4 * lam * (z.re - c) * z.im) := by
  simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.re_ofNat,
    Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im, pow_two, Complex.sub_re,
    Complex.sub_im]
  ring

/-- ‖G_{c,lam}(z)‖ = exp (2 lam ((Im z)^2 - (Re z - c)^2)). -/
lemma norm_plainGauss (c lam : ℝ) (z : ℂ) :
    ‖plainGauss c lam z‖ = Real.exp (2 * lam * (z.im ^ 2 - (z.re - c) ^ 2)) := by
  unfold plainGauss
  rw [Complex.norm_exp, plainGauss_re_exponent]

lemma norm_pterm (c lam : ℝ) (ρ : ℂ) :
    ‖pterm c lam ρ‖ = (WeilExplicit.zeroMult ρ : ℝ) * Real.exp (2 * lam * phi c ρ) := by
  unfold pterm
  rw [norm_mul, Complex.norm_natCast, norm_plainGauss, Zeta23.WeilEF.gammaOf_re,
    Zeta23.WeilEF.gammaOf_im]
  rfl

/-- Re G_{c,lam}(z) = e^{2 lam phi} cos (4 lam x y), x = Re z - c, y = Im z. -/
lemma re_plainGauss (c lam : ℝ) (z : ℂ) :
    (plainGauss c lam z).re = Real.exp (2 * lam * (z.im ^ 2 - (z.re - c) ^ 2))
      * Real.cos (4 * lam * (z.re - c) * z.im) := by
  unfold plainGauss
  rw [Complex.exp_re, plainGauss_re_exponent, plainGauss_im_exponent, Real.cos_neg]

lemma plainGauss_conj (c lam : ℝ) (z : ℂ) : plainGauss c lam (conj z) = conj (plainGauss c lam z) := by
  unfold plainGauss
  rw [← Complex.exp_conj, map_mul, map_pow, map_sub, Complex.conj_ofReal, map_neg, map_mul,
    Complex.conj_ofReal, map_ofNat]

lemma plainGauss_ofReal (c lam x : ℝ) :
    plainGauss c lam (x : ℂ) = ((Real.exp (-(2 * lam) * (x - c) ^ 2) : ℝ) : ℂ) := by
  unfold plainGauss
  push_cast
  rfl

lemma pterm_eq_zero_of_not_nontrivial (c lam : ℝ) {ρ : ℂ} (h : ¬ IsNontrivialZero ρ) :
    pterm c lam ρ = 0 := by
  unfold pterm
  rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial h]
  simp

/-- The strip bound: ‖G_{c,lam}(z)‖ (1 + |z|^2) <= e^{lam/2} (2 c^2 + 13/4) / min 1 (2 lam)
for |Im z| <= 1/2, lam > 0. -/
lemma norm_plainGauss_mul_le (c lam : ℝ) (hlam : 0 < lam) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖plainGauss c lam z‖ * (1 + Complex.normSq z)
      ≤ Real.exp (lam / 2) * (2 * c ^ 2 + 13 / 4) / min 1 (2 * lam) := by
  set x : ℝ := z.re - c with hx
  set y : ℝ := z.im with hy
  have hnormSq : Complex.normSq z = (x + c) ^ 2 + y ^ 2 := by
    rw [Complex.normSq_apply, hx, hy]
    ring
  have hy2 : y ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp hz
    nlinarith [this.1, this.2]
  have hmin : 0 < min 1 (2 * lam) := lt_min one_pos (by positivity)
  rw [norm_plainGauss, ← hx, ← hy, hnormSq]
  have hexp1 : Real.exp (2 * lam * (y ^ 2 - x ^ 2))
      = Real.exp (2 * lam * y ^ 2) * Real.exp (-(2 * lam * x ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp2 : Real.exp (2 * lam * y ^ 2) ≤ Real.exp (lam / 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hexp3 : min 1 (2 * lam) * (1 + x ^ 2) * Real.exp (-(2 * lam * x ^ 2)) ≤ 1 := by
    have h1 : min 1 (2 * lam) * (1 + x ^ 2) ≤ 1 + 2 * lam * x ^ 2 := by
      rcases le_total 1 (2 * lam) with h | h
      · rw [min_eq_left h]
        nlinarith [sq_nonneg x]
      · rw [min_eq_right h]
        nlinarith [sq_nonneg x]
    have h2 : 1 + 2 * lam * x ^ 2 ≤ Real.exp (2 * lam * x ^ 2) := by
      have := Real.add_one_le_exp (2 * lam * x ^ 2)
      linarith
    have hpos : 0 < Real.exp (2 * lam * x ^ 2) := Real.exp_pos _
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one hpos]
    exact h1.trans h2
  have hA : 1 + ((x + c) ^ 2 + y ^ 2) ≤ (2 * c ^ 2 + 13 / 4) * (1 + x ^ 2) := by
    nlinarith [sq_nonneg x, sq_nonneg c, sq_nonneg (x + c), sq_nonneg (x - c),
      mul_nonneg (sq_nonneg x) (sq_nonneg c)]
  rw [hexp1, le_div_iff₀ hmin]
  have hE : 0 < Real.exp (-(2 * lam * x ^ 2)) := Real.exp_pos _
  have hE2 : 0 ≤ Real.exp (2 * lam * y ^ 2) := (Real.exp_pos _).le
  have hK : 0 ≤ 2 * c ^ 2 + 13 / 4 := by positivity
  calc Real.exp (2 * lam * y ^ 2) * Real.exp (-(2 * lam * x ^ 2)) * (1 + ((x + c) ^ 2 + y ^ 2))
        * min 1 (2 * lam)
      = Real.exp (2 * lam * y ^ 2) * (1 + ((x + c) ^ 2 + y ^ 2))
        * (min 1 (2 * lam) * Real.exp (-(2 * lam * x ^ 2))) := by ring
    _ ≤ Real.exp (lam / 2) * ((2 * c ^ 2 + 13 / 4) * (1 + x ^ 2))
        * (min 1 (2 * lam) * Real.exp (-(2 * lam * x ^ 2))) := by gcongr
    _ = Real.exp (lam / 2) * (2 * c ^ 2 + 13 / 4)
        * (min 1 (2 * lam) * (1 + x ^ 2) * Real.exp (-(2 * lam * x ^ 2))) := by ring
    _ ≤ Real.exp (lam / 2) * (2 * c ^ 2 + 13 / 4) * 1 := by gcongr
    _ = Real.exp (lam / 2) * (2 * c ^ 2 + 13 / 4) := by ring

/-- The strip constant at width lam. -/
def plainC (c lam : ℝ) : ℝ := Real.exp (lam / 2) * (2 * c ^ 2 + 13 / 4) / min 1 (2 * lam)

lemma plainC_nonneg (c lam : ℝ) (hlam : 0 < lam) : 0 ≤ plainC c lam := by
  unfold plainC
  have : 0 < min 1 (2 * lam) := lt_min one_pos (by positivity)
  positivity

lemma norm_pterm_le (c lam : ℝ) (hlam : 0 < lam) (ρ : ℂ) :
    ‖pterm c lam ρ‖ ≤ (WeilExplicit.zeroMult ρ : ℝ) * (plainC c lam / (1 + Complex.normSq (gammaOf ρ))) := by
  unfold pterm
  rw [norm_mul, Complex.norm_natCast]
  by_cases h : IsNontrivialZero ρ
  · have hz : |(gammaOf ρ).im| ≤ 1 / 2 := (Zeta23.WeilEF.abs_gammaOf_im_lt h.2).le
    have hb := norm_plainGauss_mul_le c lam hlam hz
    have hpos : 0 < 1 + Complex.normSq (gammaOf ρ) := by
      have := Complex.normSq_nonneg (gammaOf ρ)
      linarith
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    rw [le_div_iff₀ hpos]
    exact hb
  · rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial h]
    simp

/-- The plain Gaussian zero sum converges absolutely for every centre and every lam > 0. -/
theorem summable_plain_zeroSide (c lam : ℝ) (hlam : 0 < lam) : Summable (pterm c lam) :=
  Summable.of_norm_bounded (summable_mult_div_one_add_normSq (plainC c lam)) (norm_pterm_le c lam hlam)

/-- Theta is real (the zero side of a Hermitian-symmetric transform); recorded for the ledger. -/
lemma zeroSide_plain_im (c lam : ℝ) : (zeroSide (plainGauss c lam)).im = 0 := by
  have h := zeroSide_conj (plainGauss_conj c lam)
  have := congrArg Complex.im h
  simp only [Complex.conj_im] at this
  linarith

/-! ## B. Forward: RH gives Theta >= 0. -/

lemma pterm_re_nonneg_of_rh (hRH : RiemannHypothesis) (c lam : ℝ) (ρ : ℂ) :
    0 ≤ (pterm c lam ρ).re := by
  by_cases h : IsNontrivialZero ρ
  · have hγ : gammaOf ρ = ((ρ.im : ℝ) : ℂ) := by
      apply Complex.ext
      · rw [Zeta23.WeilEF.gammaOf_re]; simp
      · rw [Zeta23.WeilEF.gammaOf_im, Zeta23.RH_implies_on_line hRH h]; simp
    unfold pterm
    rw [hγ, plainGauss_ofReal]
    have : ((WeilExplicit.zeroMult ρ : ℂ) * ((Real.exp (-(2 * lam) * (ρ.im - c) ^ 2) : ℝ) : ℂ))
        = (((WeilExplicit.zeroMult ρ : ℝ) * Real.exp (-(2 * lam) * (ρ.im - c) ^ 2) : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.ofReal_re]
    positivity
  · rw [pterm_eq_zero_of_not_nontrivial c lam h]
    simp

theorem theta_nonneg_of_rh (hRH : RiemannHypothesis) (c lam : ℝ) (hlam : 0 < lam) :
    0 ≤ Theta c lam :=
  HasSum.nonneg (pterm_re_nonneg_of_rh hRH c lam)
    (Complex.hasSum_re (summable_plain_zeroSide c lam hlam).hasSum)

/-! ## C. Converse: an off-line zero makes Theta negative at some width, at a generic centre. -/

/-- The phase: for x y != 0 and any lam_0 there is lam >= lam_0 with cos (4 lam x y) = -1. -/
lemma exists_lam_cos_neg_one (lam₀ x y : ℝ) (hxy : x * y ≠ 0) :
    ∃ lam : ℝ, lam₀ ≤ lam ∧ Real.cos (4 * lam * x * y) = -1 := by
  have h4 : 4 * x * y ≠ 0 := by
    intro h; apply hxy; linarith
  obtain ⟨k, hk⟩ : ∃ k : ℤ, lam₀ ≤ (Real.pi + k * (2 * Real.pi)) / (4 * x * y) := by
    rcases lt_or_gt_of_ne h4 with hneg | hpos4
    · obtain ⟨k, hk⟩ := exists_int_lt ((4 * x * y * lam₀ - Real.pi) / (2 * Real.pi))
      refine ⟨k, ?_⟩
      rw [le_div_iff_of_neg hneg]
      have h2π : 0 < 2 * Real.pi := by positivity
      have := (lt_div_iff₀ h2π).mp hk
      linarith
    · obtain ⟨k, hk⟩ := exists_int_gt ((4 * x * y * lam₀ - Real.pi) / (2 * Real.pi))
      refine ⟨k, ?_⟩
      rw [le_div_iff₀ hpos4]
      have h2π : 0 < 2 * Real.pi := by positivity
      have := (div_lt_iff₀ h2π).mp hk
      linarith
  refine ⟨(Real.pi + k * (2 * Real.pi)) / (4 * x * y), hk, ?_⟩
  have hang : 4 * ((Real.pi + k * (2 * Real.pi)) / (4 * x * y)) * x * y
      = Real.pi + k * (2 * Real.pi) := by
    rw [show 4 * ((Real.pi + k * (2 * Real.pi)) / (4 * x * y)) * x * y
        = (Real.pi + k * (2 * Real.pi)) * ((4 * x * y) / (4 * x * y)) by ring, div_self h4, mul_one]
  rw [hang, Real.cos_add_int_mul_two_pi, Real.cos_pi]

/-- The extended bad set: tying centres AND the ordinates of the window zeros. -/
def badSet' (ρ₀ : ℂ) : Finset ℝ := badSet ρ₀ ∪ (window ρ₀).image (fun ρ => ρ.im)

/-- A generic centre: within |1/2 - Re rho_0| of Im rho_0, no ties, no window ordinate. -/
lemma exists_generic_centre' {ρ₀ : ℂ} (h₀ : ρ₀.re ≠ 1 / 2) :
    ∃ c : ℝ, |c - ρ₀.im| < |1 / 2 - ρ₀.re| ∧ c ∉ badSet ρ₀ ∧ ∀ ρ ∈ window ρ₀, ρ.im ≠ c := by
  have hy : 0 < |1 / 2 - ρ₀.re| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h₀))
  obtain ⟨c, hc, hnot⟩ := RvMBridgeXi.exists_mem_Ioo_notMem_finset
    (show ρ₀.im - |1 / 2 - ρ₀.re| < ρ₀.im + |1 / 2 - ρ₀.re| by linarith) (badSet' ρ₀)
  refine ⟨c, ?_, fun h => hnot (Finset.mem_union_left _ h), fun ρ hρ h => hnot ?_⟩
  · rw [Set.mem_Ioo] at hc
    rw [abs_lt]
    constructor <;> linarith [hc.1, hc.2]
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨ρ, hρ, h⟩)

/-- The plain majorant (E6Bridge7's majorant without the |w|^2 factor), lam = 1 tail constant. -/
def pmajorant (ρ₀ : ℂ) (c M η lam : ℝ) (ρ : ℂ) : ℝ :=
  Real.exp (2 * lam * (M - η)) * (if ρ ∈ window ρ₀ then (WeilExplicit.zeroMult ρ : ℝ) else 0)
    + (WeilExplicit.zeroMult ρ : ℝ) * (plainC c 1 / (1 + Complex.normSq (gammaOf ρ)))

lemma pmajorant_nonneg (ρ₀ : ℂ) (c M η lam : ℝ) (ρ : ℂ) : 0 ≤ pmajorant ρ₀ c M η lam ρ := by
  unfold pmajorant
  have h1 : 0 ≤ (if ρ ∈ window ρ₀ then (WeilExplicit.zeroMult ρ : ℝ) else 0) := by
    split_ifs
    · exact Nat.cast_nonneg _
    · exact le_rfl
  have h2 : 0 ≤ (WeilExplicit.zeroMult ρ : ℝ) * (plainC c 1 / (1 + Complex.normSq (gammaOf ρ))) := by
    have := Complex.normSq_nonneg (gammaOf ρ)
    have := plainC_nonneg c 1 one_pos
    positivity
  have h3 : 0 ≤ Real.exp (2 * lam * (M - η)) := (Real.exp_pos _).le
  nlinarith [mul_nonneg h3 h1]

lemma summable_pmajorant (ρ₀ : ℂ) (c M η lam : ℝ) : Summable (pmajorant ρ₀ c M η lam) := by
  unfold pmajorant
  refine Summable.add ((summable_of_ne_finset_zero (s := window ρ₀) ?_).mul_left _)
    (summable_mult_div_one_add_normSq _)
  intro ρ hρ
  exact if_neg hρ

/-- The pointwise tail bound for lam >= 1 and rho off the pair of the maximiser. -/
lemma norm_pterm_le_pmajorant {ρ₀ : ℂ} {c : ℝ} (hc : |c - ρ₀.im| < 1 / 2) {ρ₁ : ℂ} {η : ℝ}
    (hgap : ∀ ρ ∈ window ρ₀, ρ ≠ ρ₁ → ρ ≠ reflect ρ₁ → phi c ρ ≤ phi c ρ₁ - η)
    {lam : ℝ} (hlam : 1 ≤ lam) {ρ : ℂ} (hne : ρ ≠ ρ₁) (hne' : ρ ≠ reflect ρ₁) :
    ‖pterm c lam ρ‖ ≤ pmajorant ρ₀ c (phi c ρ₁) η lam ρ := by
  by_cases hnt : IsNontrivialZero ρ
  · rw [norm_pterm]
    unfold pmajorant
    have hm : (0 : ℝ) ≤ WeilExplicit.zeroMult ρ := Nat.cast_nonneg _
    have hsecond : 0 ≤ (WeilExplicit.zeroMult ρ : ℝ)
        * (plainC c 1 / (1 + Complex.normSq (gammaOf ρ))) := by
      have := Complex.normSq_nonneg (gammaOf ρ)
      have := plainC_nonneg c 1 one_pos
      positivity
    by_cases hW : ρ ∈ window ρ₀
    · rw [if_pos hW]
      have hφ := hgap ρ hW hne hne'
      have hexp : Real.exp (2 * lam * phi c ρ) ≤ Real.exp (2 * lam * (phi c ρ₁ - η)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have := mul_le_mul_of_nonneg_left hexp hm
      linarith
    · rw [if_neg hW, mul_zero, zero_add]
      have hφ : phi c ρ < 0 := phi_neg_of_not_mem_window hc hnt hW
      have hexp : Real.exp (2 * lam * phi c ρ) ≤ Real.exp (2 * 1 * phi c ρ) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have h1 : (WeilExplicit.zeroMult ρ : ℝ) * Real.exp (2 * lam * phi c ρ)
          ≤ (WeilExplicit.zeroMult ρ : ℝ) * Real.exp (2 * 1 * phi c ρ) :=
        mul_le_mul_of_nonneg_left hexp hm
      have h2 : (WeilExplicit.zeroMult ρ : ℝ) * Real.exp (2 * 1 * phi c ρ) = ‖pterm c 1 ρ‖ :=
        (norm_pterm c 1 ρ).symm
      calc (WeilExplicit.zeroMult ρ : ℝ) * Real.exp (2 * lam * phi c ρ)
          ≤ ‖pterm c 1 ρ‖ := h1.trans_eq h2
        _ ≤ _ := norm_pterm_le c 1 one_pos ρ
  · rw [pterm_eq_zero_of_not_nontrivial c lam hnt, norm_zero]
    exact pmajorant_nonneg _ _ _ _ _ _

/-- The window count A' and the plain tail constant B'. -/
def pconstA (ρ₀ : ℂ) : ℝ := ∑ ρ ∈ window ρ₀, (WeilExplicit.zeroMult ρ : ℝ)

def pconstB (c : ℝ) : ℝ :=
  ∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℝ) * (plainC c 1 / (1 + Complex.normSq (gammaOf ρ)))

lemma pconstA_nonneg (ρ₀ : ℂ) : 0 ≤ pconstA ρ₀ := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

lemma pconstB_nonneg (c : ℝ) : 0 ≤ pconstB c :=
  tsum_nonneg fun ρ => by
    have := Complex.normSq_nonneg (gammaOf ρ)
    have := plainC_nonneg c 1 one_pos
    positivity

lemma tsum_pmajorant (ρ₀ : ℂ) (c M η lam : ℝ) :
    ∑' ρ : ℂ, pmajorant ρ₀ c M η lam ρ = Real.exp (2 * lam * (M - η)) * pconstA ρ₀ + pconstB c := by
  unfold pmajorant pconstA pconstB
  rw [((summable_of_ne_finset_zero (s := window ρ₀) fun ρ hρ => if_neg hρ).mul_left _).tsum_add
    (summable_mult_div_one_add_normSq _), tsum_mul_left]
  congr 2
  rw [tsum_eq_sum (s := window ρ₀) fun ρ hρ => if_neg hρ]
  exact Finset.sum_congr rfl fun ρ hρ => if_pos hρ

/-- The tail over all rho off the pair, lam >= 1. -/
lemma ptail_bound {ρ₀ : ℂ} {c : ℝ} (hc : |c - ρ₀.im| < 1 / 2) {ρ₁ : ℂ} {η : ℝ}
    (hgap : ∀ ρ ∈ window ρ₀, ρ ≠ ρ₁ → ρ ≠ reflect ρ₁ → phi c ρ ≤ phi c ρ₁ - η)
    {lam : ℝ} (hlam : 1 ≤ lam) :
    ‖∑' ρ : {ρ : ℂ // ρ ≠ ρ₁ ∧ ρ ≠ reflect ρ₁}, pterm c lam ρ‖
      ≤ Real.exp (2 * lam * (phi c ρ₁ - η)) * pconstA ρ₀ + pconstB c := by
  rw [← tsum_pmajorant ρ₀ c (phi c ρ₁) η lam]
  exact norm_tsum_subtype_le_tsum {ρ : ℂ | ρ ≠ ρ₁ ∧ ρ ≠ reflect ρ₁}
    (summable_pmajorant ρ₀ c (phi c ρ₁) η lam) (pmajorant_nonneg ρ₀ c (phi c ρ₁) η lam)
    fun ρ => norm_pterm_le_pmajorant hc hgap hlam ρ.2.1 ρ.2.2

/-- Theta = pair term + tail, bounded above. -/
lemma theta_le_pair_add_tail {ρ₀ : ℂ} {c : ℝ} (hc : |c - ρ₀.im| < 1 / 2) {ρ₁ : ℂ}
    (h₁ : ρ₁.re ≠ 1 / 2) {η : ℝ}
    (hgap : ∀ ρ ∈ window ρ₀, ρ ≠ ρ₁ → ρ ≠ reflect ρ₁ → phi c ρ ≤ phi c ρ₁ - η)
    {lam : ℝ} (hlam : 1 ≤ lam) :
    Theta c lam ≤ 2 * (WeilExplicit.zeroMult ρ₁ : ℝ) * (plainGauss c lam (gammaOf ρ₁)).re
        + (Real.exp (2 * lam * (phi c ρ₁ - η)) * pconstA ρ₀ + pconstB c) := by
  have hlam0 : 0 < lam := by linarith
  unfold Theta
  rw [zeroSide_pair_split (plainGauss_conj c lam) (summable_plain_zeroSide c lam hlam0) h₁,
    Complex.add_re]
  have hre : (2 * (WeilExplicit.zeroMult ρ₁ : ℂ) * ((plainGauss c lam (gammaOf ρ₁)).re : ℂ)).re
      = 2 * (WeilExplicit.zeroMult ρ₁ : ℝ) * (plainGauss c lam (gammaOf ρ₁)).re := by
    have : (2 * (WeilExplicit.zeroMult ρ₁ : ℂ) * ((plainGauss c lam (gammaOf ρ₁)).re : ℂ))
        = ((2 * (WeilExplicit.zeroMult ρ₁ : ℝ) * (plainGauss c lam (gammaOf ρ₁)).re : ℝ) : ℂ) := by
      push_cast
      ring
    rw [this, Complex.ofReal_re]
  rw [hre]
  have htail := ptail_bound hc hgap hlam
  have hgoal : (∑' ρ : {ρ : ℂ // ρ ≠ ρ₁ ∧ ρ ≠ reflect ρ₁},
      (WeilExplicit.zeroMult ρ : ℂ) * plainGauss c lam (gammaOf ρ)).re
      ≤ Real.exp (2 * lam * (phi c ρ₁ - η)) * pconstA ρ₀ + pconstB c :=
    le_trans (Complex.re_le_norm _) htail
  linarith

/-- **The converse mechanism**: an off-line zero gives a centre c and, for every lam_0, a width
lam >= lam_0 at which Theta c lam < 0. -/
theorem exists_theta_neg_of_offline {ρ₀ : ℂ} (h₀ : IsNontrivialZero ρ₀) (hre₀ : ρ₀.re ≠ 1 / 2) :
    ∃ c : ℝ, ∀ lam₀ : ℝ, ∃ lam : ℝ, lam₀ ≤ lam ∧ 0 < lam ∧ Theta c lam < 0 := by
  obtain ⟨c, hcI, hcbad, hcord⟩ := exists_generic_centre' hre₀
  have hy₀ : |1 / 2 - ρ₀.re| < 1 / 2 := by
    rw [abs_lt]
    constructor <;> linarith [h₀.2.1, h₀.2.2]
  have hc : |c - ρ₀.im| < 1 / 2 := hcI.trans hy₀
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
  have hx₁ : ρ₁.im - c ≠ 0 := sub_ne_zero.mpr (hcord ρ₁ hρ₁)
  have hy₁' : (1 / 2 - ρ₁.re) ≠ 0 := sub_ne_zero.mpr (Ne.symm h₁)
  have hm₁ : (1 : ℝ) ≤ WeilExplicit.zeroMult ρ₁ := by
    rw [RvMBridge4.zeroMult_eq_mult hρ₁nt]
    exact_mod_cast zetaSeam.one_le_mult ρ₁ hρ₁nt
  set K : ℝ := (WeilExplicit.zeroMult ρ₁ : ℝ) with hK
  have hK0 : 0 < K := by linarith
  set A := pconstA ρ₀ with hA
  set B := pconstB c with hB
  have hA0 : 0 ≤ A := pconstA_nonneg ρ₀
  have hB0 : 0 ≤ B := pconstB_nonneg c
  refine ⟨c, fun lam₀ => ?_⟩
  set lam₁ : ℝ := max lam₀ (max 1 (max (A / (2 * η * K)) (B / (2 * M * K)))) with hlam₁
  obtain ⟨lam, hlam, hcos⟩ := exists_lam_cos_neg_one lam₁ (ρ₁.im - c) (1 / 2 - ρ₁.re)
    (mul_ne_zero hx₁ hy₁')
  have hlam0' : lam₀ ≤ lam := (le_max_left _ _).trans hlam
  have hlam1 : 1 ≤ lam := ((le_max_left _ _).trans (le_max_right _ _)).trans hlam
  have hlamA : A / (2 * η * K) ≤ lam :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hlam
  have hlamB : B / (2 * M * K) ≤ lam :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hlam
  refine ⟨lam, hlam0', by linarith, ?_⟩
  have hmain := theta_le_pair_add_tail hc h₁ hgap hlam1
  rw [re_plainGauss, Zeta23.WeilEF.gammaOf_re, Zeta23.WeilEF.gammaOf_im, hcos] at hmain
  have hpair : 2 * (WeilExplicit.zeroMult ρ₁ : ℝ)
      * (Real.exp (2 * lam * ((1 / 2 - ρ₁.re) ^ 2 - (ρ₁.im - c) ^ 2)) * -1)
      = -(2 * K * Real.exp (2 * lam * M)) := by
    simp only [hK, hM, phi]
    ring
  rw [hpair] at hmain
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

/-- **(1) RH <-> Theta >= 0 at every centre and every width.** -/
theorem rh_iff_theta_positivity :
    RiemannHypothesis ↔ ∀ c lam : ℝ, 0 < lam → 0 ≤ Theta c lam := by
  constructor
  · exact fun hRH c lam hlam => theta_nonneg_of_rh hRH c lam hlam
  · intro hpos
    apply rh_of_all_on_line
    intro ρ₀ h₀
    by_contra hre
    obtain ⟨c, hc⟩ := exists_theta_neg_of_offline h₀ hre
    obtain ⟨lam, _, hlam0, hneg⟩ := hc 0
    linarith [hpos c lam hlam0]

/-! ## D. Heat monotonicity: the identity (M). -/

/-- The variance of the heat step from width lam to width lam' < lam:
sigma^2 = 1/(4 lam') - 1/(4 lam) = (lam - lam')/(4 lam lam'). -/
def heatVar (lam' lam : ℝ) : ℝ := (lam - lam') / (4 * lam * lam')

/-- The Gaussian (heat) kernel of variance sigma^2. -/
def heatKernel (σ2 u : ℝ) : ℝ := Real.exp (-(u ^ 2) / (2 * σ2)) / Real.sqrt (2 * Real.pi * σ2)

lemma heatVar_pos {lam' lam : ℝ} (h0 : 0 < lam') (hlt : lam' < lam) : 0 < heatVar lam' lam := by
  unfold heatVar
  have : 0 < lam := by linarith
  apply div_pos (by linarith) (by positivity)

lemma heatKernel_nonneg {σ2 : ℝ} (hσ : 0 < σ2) (u : ℝ) : 0 ≤ heatKernel σ2 u := by
  unfold heatKernel
  positivity

lemma continuous_heatKernel (σ2 : ℝ) : Continuous (heatKernel σ2) := by
  unfold heatKernel
  fun_prop

/-- The quadratic coefficient A = 1/(2 sigma^2) + 2 lam = 2 lam^2/(lam - lam'). -/
lemma heat_A_eq {lam' lam : ℝ} (h0 : 0 < lam') (hlt : lam' < lam) :
    1 / (2 * heatVar lam' lam) + 2 * lam = 2 * lam ^ 2 / (lam - lam') := by
  unfold heatVar
  have h1 : lam - lam' ≠ 0 := by linarith
  have h2 : lam ≠ 0 := by linarith
  have h3 : lam' ≠ 0 := by linarith
  field_simp
  ring

/-- The integrand of the heat step as a single Gaussian exponential in c'. -/
lemma heat_integrand_eq {lam' lam : ℝ} (h0 : 0 < lam') (hlt : lam' < lam) (c : ℝ) (γ : ℂ) (c' : ℝ) :
    (heatKernel (heatVar lam' lam) (c - c') : ℂ) * plainGauss c' lam γ
      = ((1 / Real.sqrt (2 * Real.pi * heatVar lam' lam) : ℝ) : ℂ)
        * Complex.exp (-((2 * lam ^ 2 / (lam - lam') : ℝ) : ℂ) * (c' : ℂ) ^ 2
            + ((c / heatVar lam' lam : ℝ) + 4 * lam * γ) * (c' : ℂ)
            + (-((c ^ 2 / (2 * heatVar lam' lam) : ℝ) : ℂ) - 2 * lam * γ ^ 2)) := by
  have hσ : 0 < heatVar lam' lam := heatVar_pos h0 hlt
  have hσne : (heatVar lam' lam : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have hA := heat_A_eq h0 hlt
  unfold heatKernel plainGauss
  rw [Complex.ofReal_div, Complex.ofReal_exp, div_eq_mul_inv, mul_comm (cexp _) _, mul_assoc,
    ← Complex.exp_add]
  have hinv : ((Real.sqrt (2 * Real.pi * heatVar lam' lam) : ℝ) : ℂ)⁻¹
      = ((1 / Real.sqrt (2 * Real.pi * heatVar lam' lam) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hinv]
  congr 1
  have hA' : ((2 * lam ^ 2 / (lam - lam') : ℝ) : ℂ) = 1 / (2 * (heatVar lam' lam : ℂ)) + 2 * lam := by
    rw [← hA]
    push_cast
    ring
  rw [hA']
  push_cast
  field_simp
  ring

/-- **Termwise heat identity (M) for a complex centre.**  For 0 < lam' < lam and any gamma : C,
G_{c,lam'}(gamma) = sqrt (lam/lam') int heatKernel sigma2 (c - c') G_{c',lam}(gamma) dc'. -/
theorem plainGauss_heat {lam' lam : ℝ} (h0 : 0 < lam') (hlt : lam' < lam) (c : ℝ) (γ : ℂ) :
    plainGauss c lam' γ = ((Real.sqrt (lam / lam') : ℝ) : ℂ)
      * ∫ c' : ℝ, (heatKernel (heatVar lam' lam) (c - c') : ℂ) * plainGauss c' lam γ := by
  have hσ : 0 < heatVar lam' lam := heatVar_pos h0 hlt
  have hlam : 0 < lam := by linarith
  have hApos' : 0 < 2 * lam ^ 2 / (lam - lam') := by
    apply div_pos (by positivity) (by linarith)
  simp_rw [heat_integrand_eq h0 hlt c γ]
  rw [integral_const_mul]
  have hbre : (-((2 * lam ^ 2 / (lam - lam') : ℝ) : ℂ)).re < 0 := by
    rw [Complex.neg_re, Complex.ofReal_re]
    linarith
  rw [integral_cexp_quadratic hbre]
  set σ2 : ℝ := heatVar lam' lam with hσ2
  set A : ℝ := 2 * lam ^ 2 / (lam - lam') with hAdef
  have hApos : 0 < A := hApos'
  -- the prefactor
  have hpre : ((Real.sqrt (lam / lam') : ℝ) : ℂ) * (((1 / Real.sqrt (2 * Real.pi * σ2) : ℝ) : ℂ)
      * ((Real.pi : ℂ) / -(-((A : ℝ) : ℂ))) ^ (1 / 2 : ℂ)) = 1 := by
    rw [neg_neg]
    have hcpow : ((Real.pi : ℂ) / ((A : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
        = ((Real.sqrt (Real.pi / A) : ℝ) : ℂ) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity) (1 / 2)]
      push_cast
      ring_nf
    rw [hcpow, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    have hreal : Real.sqrt (lam / lam') * (1 / Real.sqrt (2 * Real.pi * σ2) * Real.sqrt (Real.pi / A))
        = 1 := by
      have h2σ : 0 < 2 * Real.pi * σ2 := by positivity
      have hπA : 0 ≤ Real.pi / A := by positivity
      have hll : 0 ≤ lam / lam' := by positivity
      rw [one_div, ← Real.sqrt_inv, ← Real.sqrt_mul (inv_nonneg.mpr h2σ.le), ← Real.sqrt_mul hll]
      rw [Real.sqrt_eq_one]
      rw [hσ2, hAdef]
      unfold heatVar
      have h1 : lam - lam' ≠ 0 := by linarith
      have h2 : lam ≠ 0 := by linarith
      have h3 : lam' ≠ 0 := by linarith
      have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp
      ring
    rw [hreal]
    push_cast
    rfl
  -- the exponent
  have hexp : (-((c ^ 2 / (2 * σ2) : ℝ) : ℂ) - 2 * lam * γ ^ 2)
      - ((c / σ2 : ℝ) + 4 * lam * γ) ^ 2 / (4 * -((A : ℝ) : ℂ)) = -(2 * lam') * (γ - c) ^ 2 := by
    rw [hσ2, hAdef]
    unfold heatVar
    have h1 : ((lam : ℂ) - lam') ≠ 0 := by
      have : (lam - lam' : ℝ) ≠ 0 := by linarith
      exact_mod_cast this
    have h2 : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
    have h3 : (lam' : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
    push_cast
    field_simp
    ring
  rw [hexp]
  set X : ℂ := ((Real.pi : ℂ) / -(-((A : ℝ) : ℂ))) ^ (1 / 2 : ℂ) with hX
  have hpre' : ((Real.sqrt (lam / lam') : ℝ) : ℂ)
      * (((1 / Real.sqrt (2 * Real.pi * σ2) : ℝ) : ℂ) * X) = 1 := hpre
  calc plainGauss c lam' γ = 1 * Complex.exp (-(2 * (lam' : ℂ)) * (γ - c) ^ 2) := by
        unfold plainGauss
        rw [one_mul]
    _ = (((Real.sqrt (lam / lam') : ℝ) : ℂ)
          * (((1 / Real.sqrt (2 * Real.pi * σ2) : ℝ) : ℂ) * X))
          * Complex.exp (-(2 * (lam' : ℂ)) * (γ - c) ^ 2) := by rw [hpre']
    _ = _ := by ring

/-- The real Gaussian heat step (the termwise identity at a real point), in the form needed for
the majorant: int heatKernel sigma2 (c - c') e^{-2 lam (x - c')^2} dc' = sqrt (lam'/lam) e^{-2 lam' (x - c)^2}. -/
lemma real_gauss_heat {lam' lam : ℝ} (h0 : 0 < lam') (hlt : lam' < lam) (c x : ℝ) :
    ∫ c' : ℝ, heatKernel (heatVar lam' lam) (c - c') * Real.exp (-(2 * lam) * (x - c') ^ 2)
      = Real.sqrt (lam' / lam) * Real.exp (-(2 * lam') * (x - c) ^ 2) := by
  have hlam : 0 < lam := by linarith
  have h := plainGauss_heat h0 hlt c (x : ℂ)
  rw [plainGauss_ofReal] at h
  have hint : (∫ c' : ℝ, (heatKernel (heatVar lam' lam) (c - c') : ℂ) * plainGauss c' lam (x : ℂ))
      = ((∫ c' : ℝ, heatKernel (heatVar lam' lam) (c - c') * Real.exp (-(2 * lam) * (x - c') ^ 2) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun c' => ?_)
    simp only [plainGauss_ofReal]
    push_cast
    ring
  rw [hint, ← Complex.ofReal_mul] at h
  have h' := Complex.ofReal_injective h
  have hs : 0 < Real.sqrt (lam / lam') := Real.sqrt_pos.mpr (by positivity)
  have hprod : Real.sqrt (lam' / lam) * Real.sqrt (lam / lam') = 1 := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show lam' / lam * (lam / lam') = 1 by field_simp]
    exact Real.sqrt_one
  calc (∫ c' : ℝ, heatKernel (heatVar lam' lam) (c - c') * Real.exp (-(2 * lam) * (x - c') ^ 2))
      = Real.sqrt (lam' / lam) * (Real.sqrt (lam / lam')
          * ∫ c' : ℝ, heatKernel (heatVar lam' lam) (c - c') * Real.exp (-(2 * lam) * (x - c') ^ 2)) := by
        rw [← mul_assoc, hprod, one_mul]
    _ = Real.sqrt (lam' / lam) * Real.exp (-(2 * lam') * (x - c) ^ 2) := by rw [← h']

/-- The heat-step integrand of the summand rho. -/
def heatF (lam' lam c : ℝ) (ρ : ℂ) (c' : ℝ) : ℂ :=
  (heatKernel (heatVar lam' lam) (c - c') : ℂ) * pterm c' lam ρ

lemma integrable_heatF {lam' lam : ℝ} (h0 : 0 < lam') (hlt : lam' < lam) (c : ℝ) (ρ : ℂ) :
    Integrable (heatF lam' lam c ρ) := by
  have hint : heatF lam' lam c ρ = fun c' => (WeilExplicit.zeroMult ρ : ℂ)
      * ((heatKernel (heatVar lam' lam) (c - c') : ℂ) * plainGauss c' lam (gammaOf ρ)) := by
    funext c'
    unfold heatF pterm
    ring
  rw [hint]
  simp_rw [heat_integrand_eq h0 hlt c (gammaOf ρ)]
  have hApos : 0 < 2 * lam ^ 2 / (lam - lam') := by
    have : 0 < lam := by linarith
    apply div_pos (by positivity) (by linarith)
  have hbre : 0 < (((2 * lam ^ 2 / (lam - lam') : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]
    exact hApos
  exact ((integrable_cexp_quadratic hbre _ _).const_mul _).const_mul _

/-- The heat-step majorant: int ‖heatF rho‖ <= m e^{lam/2} sqrt (lam'/lam) e^{-2 lam' (Im rho - c)^2}. -/
lemma integral_norm_heatF_le {lam' lam : ℝ} (h0 : 0 < lam') (hlt : lam' < lam) (c : ℝ) (ρ : ℂ) :
    ∫ c' : ℝ, ‖heatF lam' lam c ρ c'‖
      ≤ (WeilExplicit.zeroMult ρ : ℝ) * (Real.exp (lam / 2) * Real.sqrt (lam' / lam)
          * Real.exp (-(2 * lam') * (ρ.im - c) ^ 2)) := by
  have hlam : 0 < lam := by linarith
  have hσ : 0 < heatVar lam' lam := heatVar_pos h0 hlt
  by_cases hnt : IsNontrivialZero ρ
  · have hy : (gammaOf ρ).im ^ 2 ≤ 1 / 4 := by
      have := abs_le.mp (Zeta23.WeilEF.abs_gammaOf_im_lt hnt.2).le
      nlinarith [this.1, this.2]
    have hm : (0 : ℝ) ≤ WeilExplicit.zeroMult ρ := Nat.cast_nonneg _
    -- pointwise bound
    have hpt : ∀ c' : ℝ, ‖heatF lam' lam c ρ c'‖
        ≤ (WeilExplicit.zeroMult ρ : ℝ) * Real.exp (lam / 2)
          * (heatKernel (heatVar lam' lam) (c - c') * Real.exp (-(2 * lam) * (ρ.im - c') ^ 2)) := by
      intro c'
      unfold heatF
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg hσ _),
        norm_pterm]
      have hK := heatKernel_nonneg hσ (c - c')
      have hφ : Real.exp (2 * lam * phi c' ρ)
          ≤ Real.exp (lam / 2) * Real.exp (-(2 * lam) * (ρ.im - c') ^ 2) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        unfold phi
        have : (1 / 2 - ρ.re) ^ 2 = (gammaOf ρ).im ^ 2 := by rw [Zeta23.WeilEF.gammaOf_im]
        nlinarith
      calc heatKernel (heatVar lam' lam) (c - c')
            * ((WeilExplicit.zeroMult ρ : ℝ) * Real.exp (2 * lam * phi c' ρ))
          ≤ heatKernel (heatVar lam' lam) (c - c')
            * ((WeilExplicit.zeroMult ρ : ℝ)
              * (Real.exp (lam / 2) * Real.exp (-(2 * lam) * (ρ.im - c') ^ 2))) := by
            gcongr
        _ = _ := by ring
    -- integrability of the dominating function
    have hK1 : ∀ c' : ℝ, heatKernel (heatVar lam' lam) (c - c')
        ≤ 1 / Real.sqrt (2 * Real.pi * heatVar lam' lam) := by
      intro c'
      unfold heatKernel
      have hs : 0 < Real.sqrt (2 * Real.pi * heatVar lam' lam) := Real.sqrt_pos.mpr (by positivity)
      rw [div_le_div_iff_of_pos_right hs]
      have : -((c - c') ^ 2) / (2 * heatVar lam' lam) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (c - c')]) (by positivity)
      exact Real.exp_le_one_iff.mpr this
    have hintg : Integrable (fun c' : ℝ =>
        heatKernel (heatVar lam' lam) (c - c') * Real.exp (-(2 * lam) * (ρ.im - c') ^ 2)) := by
      have hg : Integrable (fun c' : ℝ => (1 / Real.sqrt (2 * Real.pi * heatVar lam' lam))
          * Real.exp (-(2 * lam) * (c' - ρ.im) ^ 2)) :=
        ((integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 2 * lam)).comp_sub_right ρ.im).const_mul _
      refine hg.mono' ?_ (Filter.Eventually.of_forall fun c' => ?_)
      · exact (((continuous_heatKernel _).comp (continuous_const.sub continuous_id)).mul
          (by fun_prop)).aestronglyMeasurable
      · rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (heatKernel_nonneg hσ _) (Real.exp_pos _).le)]
        have h1 : (ρ.im - c') ^ 2 = (c' - ρ.im) ^ 2 := by ring
        rw [h1]
        exact mul_le_mul_of_nonneg_right (hK1 c') (Real.exp_pos _).le
    calc ∫ c' : ℝ, ‖heatF lam' lam c ρ c'‖
        ≤ ∫ c' : ℝ, (WeilExplicit.zeroMult ρ : ℝ) * Real.exp (lam / 2)
            * (heatKernel (heatVar lam' lam) (c - c') * Real.exp (-(2 * lam) * (ρ.im - c') ^ 2)) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            (hintg.const_mul _) (Filter.Eventually.of_forall hpt)
      _ = (WeilExplicit.zeroMult ρ : ℝ) * Real.exp (lam / 2)
            * ∫ c' : ℝ, heatKernel (heatVar lam' lam) (c - c')
                * Real.exp (-(2 * lam) * (ρ.im - c') ^ 2) := integral_const_mul _ _
      _ = _ := by
          rw [real_gauss_heat h0 hlt c ρ.im]
          ring
  · have h0' : heatF lam' lam c ρ = fun _ => 0 := by
      funext c'
      unfold heatF
      rw [pterm_eq_zero_of_not_nontrivial c' lam hnt, mul_zero]
    rw [h0', RvMBridge4.zeroMult_eq_zero_of_not_nontrivial hnt]
    simp

/-- The heat-step majorant is summable over the zeros. -/
lemma summable_integral_norm_heatF {lam' lam : ℝ} (h0 : 0 < lam') (hlt : lam' < lam) (c : ℝ) :
    Summable (fun ρ : ℂ => ∫ c' : ℝ, ‖heatF lam' lam c ρ c'‖) := by
  have hlam : 0 < lam := by linarith
  set E : ℝ := Real.exp (lam / 2) * Real.sqrt (lam' / lam) with hE
  have hE0 : 0 ≤ E := by positivity
  refine Summable.of_nonneg_of_le (fun ρ => integral_nonneg fun _ => norm_nonneg _)
    (fun ρ => integral_norm_heatF_le h0 hlt c ρ) ?_
  refine Summable.of_nonneg_of_le (fun ρ => by positivity) (fun ρ => ?_)
    ((summable_mult_div_one_add_normSq (plainC c lam')).mul_left E)
  by_cases hnt : IsNontrivialZero ρ
  · have hz : |(gammaOf ρ).im| ≤ 1 / 2 := (Zeta23.WeilEF.abs_gammaOf_im_lt hnt.2).le
    have hb := norm_plainGauss_mul_le c lam' h0 hz
    have hpos : 0 < 1 + Complex.normSq (gammaOf ρ) := by
      have := Complex.normSq_nonneg (gammaOf ρ)
      linarith
    have hle : Real.exp (-(2 * lam') * (ρ.im - c) ^ 2) ≤ ‖plainGauss c lam' (gammaOf ρ)‖ := by
      rw [norm_plainGauss, Zeta23.WeilEF.gammaOf_re, Zeta23.WeilEF.gammaOf_im]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (1 / 2 - ρ.re)]
    have hle2 : ‖plainGauss c lam' (gammaOf ρ)‖ ≤ plainC c lam' / (1 + Complex.normSq (gammaOf ρ)) := by
      rw [le_div_iff₀ hpos]
      exact hb
    have hm : (0 : ℝ) ≤ WeilExplicit.zeroMult ρ := Nat.cast_nonneg _
    calc (WeilExplicit.zeroMult ρ : ℝ) * (E * Real.exp (-(2 * lam') * (ρ.im - c) ^ 2))
        ≤ (WeilExplicit.zeroMult ρ : ℝ) * (E * (plainC c lam' / (1 + Complex.normSq (gammaOf ρ)))) := by
          gcongr
          exact hle.trans hle2
      _ = E * ((WeilExplicit.zeroMult ρ : ℝ) * (plainC c lam' / (1 + Complex.normSq (gammaOf ρ)))) := by
          ring
  · rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial hnt]
    simp

/-- The nontrivial zeros as a (countable) index type for the zero sums (countability:
the prelude's RvMBridgeXi.nontrivialZeros_countable). -/
def NZ : Set ℂ := {ρ : ℂ | IsNontrivialZero ρ}

instance : Countable NZ := RvMBridgeXi.nontrivialZeros_countable.to_subtype

lemma tsum_pterm_NZ (c lam : ℝ) : ∑' ρ : NZ, pterm c lam ρ = ∑' ρ : ℂ, pterm c lam ρ :=
  tsum_subtype_eq_of_support_subset fun ρ hρ => by
    by_contra h
    exact hρ (pterm_eq_zero_of_not_nontrivial c lam h)

lemma tsum_pterm_re_NZ (c lam : ℝ) :
    ∑' ρ : NZ, (pterm c lam ρ).re = ∑' ρ : ℂ, (pterm c lam ρ).re :=
  tsum_subtype_eq_of_support_subset fun ρ hρ => by
    by_contra h
    apply hρ
    show (pterm c lam ρ).re = 0
    rw [pterm_eq_zero_of_not_nontrivial c lam h, Complex.zero_re]

/-- **The heat identity (M) for Theta.**  For 0 < lam' < lam,
Theta c lam' = sqrt (lam/lam') int heatKernel sigma2 (c - c') Theta c' lam dc'. -/
theorem theta_heat {lam' lam : ℝ} (h0 : 0 < lam') (hlt : lam' < lam) (c : ℝ) :
    Theta c lam' = Real.sqrt (lam / lam')
      * ∫ c' : ℝ, heatKernel (heatVar lam' lam) (c - c') * Theta c' lam := by
  have hlam : 0 < lam := by linarith
  have hsumI : Summable (fun ρ : ℂ => ∫ c' : ℝ, heatF lam' lam c ρ c') :=
    Summable.of_norm_bounded (summable_integral_norm_heatF h0 hlt c)
      (fun ρ => norm_integral_le_integral_norm _)
  have h1 : ∀ ρ : ℂ, pterm c lam' ρ
      = ((Real.sqrt (lam / lam') : ℝ) : ℂ) * ∫ c' : ℝ, heatF lam' lam c ρ c' := by
    intro ρ
    unfold pterm
    rw [plainGauss_heat h0 hlt c (gammaOf ρ), ← mul_assoc, mul_comm ((WeilExplicit.zeroMult ρ : ℂ)),
      mul_assoc, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun c' => ?_)
    unfold heatF pterm
    ring
  have h2 : ∀ ρ : ℂ, (∫ c' : ℝ, heatF lam' lam c ρ c').re
      = ∫ c' : ℝ, (heatF lam' lam c ρ c').re := by
    intro ρ
    have := integral_re (integrable_heatF h0 hlt c ρ)
    simp only [RCLike.re_to_complex] at this
    exact this.symm
  have hintre : ∀ ρ : ℂ, Integrable (fun c' : ℝ => (heatF lam' lam c ρ c').re) := by
    intro ρ
    have := (integrable_heatF h0 hlt c ρ).re
    simpa only [RCLike.re_to_complex] using this
  have hsumre : Summable (fun ρ : ℂ => ∫ c' : ℝ, ‖(heatF lam' lam c ρ c').re‖) := by
    refine Summable.of_nonneg_of_le (fun ρ => integral_nonneg fun _ => norm_nonneg _)
      (fun ρ => ?_) (summable_integral_norm_heatF h0 hlt c)
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (integrable_heatF h0 hlt c ρ).norm (Filter.Eventually.of_forall fun c' => ?_)
    show ‖(heatF lam' lam c ρ c').re‖ ≤ ‖heatF lam' lam c ρ c'‖
    rw [Real.norm_eq_abs]
    exact Complex.abs_re_le_norm _
  have hsumI' : Summable (fun ρ : NZ => ∫ c' : ℝ, heatF lam' lam c ρ c') := hsumI.subtype NZ
  have hintre' : ∀ ρ : NZ, Integrable (fun c' : ℝ => (heatF lam' lam c ρ c').re) :=
    fun ρ => hintre ρ
  have hsumre' : Summable (fun ρ : NZ => ∫ c' : ℝ, ‖(heatF lam' lam c ρ c').re‖) :=
    hsumre.subtype NZ
  rw [theta_eq, ← tsum_pterm_NZ]
  simp_rw [h1]
  rw [tsum_mul_left, Complex.re_ofReal_mul, Complex.re_tsum hsumI']
  simp_rw [h2]
  rw [integral_tsum_of_summable_integral_norm hintre' hsumre']
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun c' => ?_)
  have h3 : ∀ ρ : ℂ, (heatF lam' lam c ρ c').re
      = heatKernel (heatVar lam' lam) (c - c') * (pterm c' lam ρ).re := by
    intro ρ
    unfold heatF
    rw [Complex.re_ofReal_mul]
  simp_rw [h3]
  rw [tsum_mul_left, theta_eq, Complex.re_tsum (summable_plain_zeroSide c' lam hlam),
    ← tsum_pterm_re_NZ]

/-- **Positivity is inherited downward in the width.** -/
theorem theta_pos_mono {lam' lam : ℝ} (h0 : 0 < lam') (hlt : lam' < lam)
    (hpos : ∀ c : ℝ, 0 ≤ Theta c lam) (c : ℝ) : 0 ≤ Theta c lam' := by
  rw [theta_heat h0 hlt c]
  refine mul_nonneg (Real.sqrt_nonneg _) (integral_nonneg fun c' => ?_)
  exact mul_nonneg (heatKernel_nonneg (heatVar_pos h0 hlt) _) (hpos c')

/-! ## E. The free widths and the constant Lambda_Theta. -/

/-- Width lam is Theta-free: Theta(c, lam) >= 0 at every centre. -/
def ThetaFree (lam : ℝ) : Prop := ∀ c : ℝ, 0 ≤ Theta c lam

/-- The set of positive free widths; Lambda_Theta is its supremum (possibly 0 or infinity). -/
def ThetaWidths : Set ℝ := {lam : ℝ | 0 < lam ∧ ThetaFree lam}

/-- Free widths are downward closed. -/
theorem thetaFree_mono {lam' lam : ℝ} (h0 : 0 < lam') (hle : lam' ≤ lam) (h : ThetaFree lam) :
    ThetaFree lam' := by
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact theta_pos_mono h0 hlt h
  · rw [heq]; exact h

/-- The free widths form an initial segment of (0, infinity). -/
theorem thetaWidths_Ioc_subset {lam : ℝ} (h : lam ∈ ThetaWidths) : Set.Ioc 0 lam ⊆ ThetaWidths :=
  fun μ hμ => ⟨hμ.1, thetaFree_mono hμ.1 hμ.2 h.2⟩

/-- **RH <-> every width is free (Lambda_Theta = infinity).** -/
theorem rh_iff_thetaFree_all : RiemannHypothesis ↔ ∀ lam : ℝ, 0 < lam → ThetaFree lam := by
  rw [rh_iff_theta_positivity]
  constructor
  · exact fun h lam hlam c => h c lam hlam
  · exact fun h c lam hlam => h lam hlam c

theorem rh_iff_thetaWidths_eq : RiemannHypothesis ↔ ThetaWidths = Set.Ioi 0 := by
  rw [rh_iff_thetaFree_all]
  constructor
  · intro h
    ext lam
    exact ⟨fun hl => hl.1, fun hl => ⟨hl, h lam hl⟩⟩
  · intro h lam hlam
    have : lam ∈ ThetaWidths := by rw [h]; exact hlam
    exact this.2

/-- **An off-line zero bounds Lambda_Theta**: there is Lambda > 0 with no free width >= Lambda. -/
theorem not_thetaFree_of_offline {ρ₀ : ℂ} (h₀ : IsNontrivialZero ρ₀) (hre₀ : ρ₀.re ≠ 1 / 2) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ lam : ℝ, Λ ≤ lam → ¬ ThetaFree lam := by
  obtain ⟨c, hc⟩ := exists_theta_neg_of_offline h₀ hre₀
  obtain ⟨lam₁, _, hlam₁, hneg⟩ := hc 1
  refine ⟨lam₁, hlam₁, fun lam hle hfree => ?_⟩
  have := thetaFree_mono hlam₁ hle hfree c
  linarith

/-- Equivalently: the free widths are bounded above by Lambda. -/
theorem thetaWidths_bddAbove_of_offline {ρ₀ : ℂ} (h₀ : IsNontrivialZero ρ₀)
    (hre₀ : ρ₀.re ≠ 1 / 2) : BddAbove ThetaWidths := by
  obtain ⟨Λ, _, hΛ⟩ := not_thetaFree_of_offline h₀ hre₀
  refine ⟨Λ, fun lam hlam => ?_⟩
  by_contra hlt
  exact hΛ lam (le_of_lt (not_le.mp hlt)) hlam.2

/-- The dichotomy: either RH, or Lambda_Theta is finite (the free widths are bounded). -/
theorem rh_or_thetaWidths_bddAbove : RiemannHypothesis ∨ BddAbove ThetaWidths := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · right
    have : ∃ ρ₀ : ℂ, IsNontrivialZero ρ₀ ∧ ρ₀.re ≠ 1 / 2 := by
      by_contra hno
      apply hRH
      apply rh_of_all_on_line
      intro ρ h
      by_contra hne
      exact hno ⟨ρ, h, hne⟩
    obtain ⟨ρ₀, h₀, hre₀⟩ := this
    exact thetaWidths_bddAbove_of_offline h₀ hre₀

end RvMBridge17
