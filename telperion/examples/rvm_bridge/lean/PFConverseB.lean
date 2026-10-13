/-
  PFConverseB -- pole-free Weil converse, part B (2026-10-12): weighted Gaussian dominance.

  With the weight q(z) = (z^2 + 1/4)^2 (PFConverseA.qw) and qG c lam = q * gaussTest c lam:
  if some nontrivial zero rho_0 is off the critical line, then for some centre c and some
  lam >= 1 the weighted zero sum  Sum_rho m(rho) q(gamma_rho) G_{c,lam}(gamma_rho)  has strictly
  negative real part.  This is E6Bridge7's argument with three changes:
    * the centre also avoids the ordinates of the window zeros, so x_1 = Im rho_1 - c != 0;
    * the phase lemma absorbs the constant phase of P := q(gamma_1) (gamma_1 - c)^2, which is
      nonzero because q(gamma_rho) = (rho (1 - rho))^2 != 0 on the open strip;
    * the tail majorant carries |q|, controlled by ‖q G_{c,1}(z)‖ (1 + |z|^2) <= Cq(c) on the
      strip (a polynomial against exp (-2 x^2)).
  Unconditional statement about a weighted sum over the zeros, wherever they are.  Nothing here
  is progress on RH; conjecture1_proved = False.
-/
import PFConverseA
import E6Bridge7

open Zeta23 Complex MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace RvMBridgePF
open WeilExplicit RvMBridge6 RvMBridge7 RvMBridgeGauss

/-! ## A. The weight. -/

lemma qw_conj (z : ℂ) : qw (conj z) = conj (qw z) := by
  unfold qw
  simp only [map_pow, map_add, map_div₀, map_one, map_ofNat]

lemma qG_conj (c lam : ℝ) (z : ℂ) : qG c lam (conj z) = conj (qG c lam z) := by
  unfold qG
  rw [qw_conj, gaussTest_conj, map_mul]

/-- q(gamma_rho) = (rho - rho^2)^2. -/
lemma qw_gammaOf (ρ : ℂ) : qw (gammaOf ρ) = (ρ - ρ ^ 2) ^ 2 := by
  unfold qw gammaOf
  rw [Complex.div_I]
  have h : (-((ρ - 1 / 2) * I)) ^ 2 + 1 / 4 = ρ - ρ ^ 2 := by
    linear_combination (ρ - 1 / 2) ^ 2 * I_sq
  rw [h]

lemma qw_gammaOf_ne_zero {ρ : ℂ} (h : IsNontrivialZero ρ) : qw (gammaOf ρ) ≠ 0 := by
  rw [qw_gammaOf]
  apply pow_ne_zero
  have h0 : ρ ≠ 0 := by
    intro e; have := h.2.1; rw [e] at this; simp at this
  have h1 : 1 - ρ ≠ 0 := by
    intro e
    have : ρ = 1 := by linear_combination -e
    have := h.2.2; rw [‹ρ = 1›] at this; simp at this
  have : ρ - ρ ^ 2 = ρ * (1 - ρ) := by ring
  rw [this]
  exact mul_ne_zero h0 h1


/-! ## B. The strip bound ‖q G_{c,1}(z)‖ (1 + |z|^2) <= Cq(c). -/

/-- Cq(c) = 16 e^{1/2} (2 c^2 + 5/2)^3. -/
def Cq (c : ℝ) : ℝ := 16 * Real.exp (1 / 2) * (2 * c ^ 2 + 5 / 2) ^ 3

lemma Cq_nonneg (c : ℝ) : 0 ≤ Cq c := by unfold Cq; positivity

lemma one_add_pow_four_mul_exp_le (s : ℝ) (hs : 0 ≤ s) : (1 + s) ^ 4 * Real.exp (-(2 * s)) ≤ 16 := by
  have h1 : 1 + s / 2 ≤ Real.exp (s / 2) := by linarith [Real.add_one_le_exp (s / 2)]
  have h2 : 1 + s ≤ 2 * Real.exp (s / 2) := by linarith
  have h3 : (1 + s) ^ 4 ≤ (2 * Real.exp (s / 2)) ^ 4 := pow_le_pow_left₀ (by linarith) h2 4
  have h4 : (2 * Real.exp (s / 2)) ^ 4 = 16 * Real.exp (2 * s) := by
    rw [mul_pow, ← Real.exp_nat_mul]; norm_num; ring_nf
  have h5 : Real.exp (2 * s) * Real.exp (-(2 * s)) = 1 := by rw [← Real.exp_add]; simp
  have hE := (Real.exp_pos (-(2 * s))).le
  calc (1 + s) ^ 4 * Real.exp (-(2 * s)) ≤ 16 * Real.exp (2 * s) * Real.exp (-(2 * s)) := by
        rw [← h4]; exact mul_le_mul_of_nonneg_right h3 hE
    _ = 16 := by rw [mul_assoc, h5, mul_one]

lemma norm_qw_le (z : ℂ) (hz : |z.im| ≤ 1 / 2) : ‖qw z‖ ≤ (z.re ^ 2 + 1 / 2) ^ 2 := by
  have hy2 : z.im ^ 2 ≤ 1 / 4 := by
    have := sq_abs z.im ▸ pow_le_pow_left₀ (abs_nonneg _) hz 2
    nlinarith
  have hn2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h1 : ‖z ^ 2 + 1 / 4‖ ≤ z.re ^ 2 + 1 / 2 := by
    calc ‖z ^ 2 + 1 / 4‖ ≤ ‖z ^ 2‖ + ‖(1 / 4 : ℂ)‖ := norm_add_le _ _
      _ = ‖z‖ ^ 2 + 1 / 4 := by rw [norm_pow]; norm_num
      _ ≤ z.re ^ 2 + 1 / 2 := by rw [hn2]; linarith
  unfold qw
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

lemma norm_qG_one_mul_le (c : ℝ) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖qG c 1 z‖ * (1 + Complex.normSq z) ≤ Cq c := by
  set a := z.re with ha
  set y := z.im with hy
  set x := a - c with hx
  set s := x ^ 2 with hs
  have hs0 : 0 ≤ s := sq_nonneg x
  have hy2 : y ^ 2 ≤ 1 / 4 := by
    have := sq_abs y ▸ pow_le_pow_left₀ (abs_nonneg _) hz 2
    nlinarith
  have hq := norm_qw_le z hz
  have hg : ‖gaussTest c 1 z‖ = (x ^ 2 + y ^ 2) * Real.exp (2 * 1 * (y ^ 2 - x ^ 2)) :=
    RvMBridge7.norm_gaussTest c 1 z
  have hg' : ‖gaussTest c 1 z‖ ≤ (s + 1 / 4) * (Real.exp (1 / 2) * Real.exp (-(2 * s))) := by
    rw [hg, ← Real.exp_add]
    have : 2 * 1 * (y ^ 2 - x ^ 2) ≤ 1 / 2 + -(2 * s) := by rw [hs]; nlinarith
    exact mul_le_mul (by rw [hs]; linarith) (Real.exp_le_exp.mpr this) (Real.exp_pos _).le
      (by positivity)
  have hn : 1 + Complex.normSq z ≤ a ^ 2 + 5 / 4 := by
    rw [Complex.normSq_apply]; nlinarith
  have ha2 : a ^ 2 ≤ 2 * s + 2 * c ^ 2 := by
    have : a = x + c := by rw [hx]; ring
    rw [this, hs]; nlinarith [sq_nonneg (x - c)]
  set A := 2 * c ^ 2 + 5 / 2 with hA
  have hA2 : 2 ≤ A := by rw [hA]; nlinarith [sq_nonneg c]
  have hq' : (a ^ 2 + 1 / 2) ^ 2 ≤ (A * (1 + s)) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  have hn' : a ^ 2 + 5 / 4 ≤ A * (1 + s) := by nlinarith
  have hs' : s + 1 / 4 ≤ 1 + s := by linarith
  have hE := one_add_pow_four_mul_exp_le s hs0
  have hexp := (Real.exp_pos (-(2 * s))).le
  have he := (Real.exp_pos (1 / 2 : ℝ)).le
  unfold qG
  rw [norm_mul]
  calc ‖qw z‖ * ‖gaussTest c 1 z‖ * (1 + Complex.normSq z)
      ≤ (A * (1 + s)) ^ 2 * ((1 + s) * (Real.exp (1 / 2) * Real.exp (-(2 * s)))) * (A * (1 + s)) := by
        have h1 : ‖qw z‖ ≤ (A * (1 + s)) ^ 2 := hq.trans hq'
        have h2 : ‖gaussTest c 1 z‖ ≤ (1 + s) * (Real.exp (1 / 2) * Real.exp (-(2 * s))) :=
          hg'.trans (mul_le_mul_of_nonneg_right hs' (by positivity))
        have h3 : 1 + Complex.normSq z ≤ A * (1 + s) := hn.trans hn'
        have hN : 0 ≤ 1 + Complex.normSq z := by have := Complex.normSq_nonneg z; linarith
        exact mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3 hN (by positivity)
    _ = Real.exp (1 / 2) * A ^ 3 * ((1 + s) ^ 4 * Real.exp (-(2 * s))) := by ring
    _ ≤ Real.exp (1 / 2) * A ^ 3 * 16 := by gcongr
    _ = Cq c := by unfold Cq; rw [← hA]; ring

/-- For lam >= 1 on the strip: ‖q G_{c,lam}(z)‖ <= e^{(lam - 1)/2} ‖q G_{c,1}(z)‖. -/
lemma norm_qG_le_one (c : ℝ) {lam : ℝ} (hlam : 1 ≤ lam) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖qG c lam z‖ ≤ Real.exp ((lam - 1) / 2) * ‖qG c 1 z‖ := by
  have hy2 : z.im ^ 2 ≤ 1 / 4 := by
    have := sq_abs z.im ▸ pow_le_pow_left₀ (abs_nonneg _) hz 2
    nlinarith
  unfold qG
  rw [norm_mul, norm_mul, RvMBridge7.norm_gaussTest, RvMBridge7.norm_gaussTest]
  have hw : 0 ≤ (z.re - c) ^ 2 + z.im ^ 2 := by positivity
  have hq := norm_nonneg (qw z)
  have key : Real.exp (2 * lam * (z.im ^ 2 - (z.re - c) ^ 2))
      ≤ Real.exp ((lam - 1) / 2) * Real.exp (2 * 1 * (z.im ^ 2 - (z.re - c) ^ 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (z.re - c)]
  calc ‖qw z‖ * (((z.re - c) ^ 2 + z.im ^ 2) * Real.exp (2 * lam * (z.im ^ 2 - (z.re - c) ^ 2)))
      ≤ ‖qw z‖ * (((z.re - c) ^ 2 + z.im ^ 2)
          * (Real.exp ((lam - 1) / 2) * Real.exp (2 * 1 * (z.im ^ 2 - (z.re - c) ^ 2)))) := by gcongr
    _ = _ := by ring

lemma summable_qG_zeroSide (c : ℝ) {lam : ℝ} (hlam : 1 ≤ lam) :
    Summable (fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℂ) * qG c lam (gammaOf ρ)) := by
  refine Summable.of_norm_bounded
    (RvMBridgeGauss.summable_mult_div_one_add_normSq (Real.exp ((lam - 1) / 2) * Cq c)) fun ρ => ?_
  rw [norm_mul, Complex.norm_natCast]
  by_cases h : IsNontrivialZero ρ
  · have hz : |(gammaOf ρ).im| ≤ 1 / 2 := (Zeta23.WeilEF.abs_gammaOf_im_lt h.2).le
    have hpos : 0 < 1 + Complex.normSq (gammaOf ρ) := by
      have := Complex.normSq_nonneg (gammaOf ρ); linarith
    have h1 := norm_qG_le_one c hlam hz
    have h2 := norm_qG_one_mul_le c hz
    have : ‖qG c lam (gammaOf ρ)‖ ≤ Real.exp ((lam - 1) / 2) * Cq c / (1 + Complex.normSq (gammaOf ρ)) := by
      rw [le_div_iff₀ hpos]
      calc ‖qG c lam (gammaOf ρ)‖ * (1 + Complex.normSq (gammaOf ρ))
          ≤ Real.exp ((lam - 1) / 2) * ‖qG c 1 (gammaOf ρ)‖ * (1 + Complex.normSq (gammaOf ρ)) := by
            gcongr
        _ = Real.exp ((lam - 1) / 2) * (‖qG c 1 (gammaOf ρ)‖ * (1 + Complex.normSq (gammaOf ρ))) := by ring
        _ ≤ Real.exp ((lam - 1) / 2) * Cq c := by gcongr
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
  · rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial h]
    simp


/-! ## C. The phase, the value at a zero, and the generic centre. -/

/-- For P != 0 and x y != 0 there is lam >= lam_0 with P exp (-i 4 lam x y) = -‖P‖. -/
lemma exists_lam_phase (lam₀ : ℝ) {P : ℂ} (_hP : P ≠ 0) {x y : ℝ} (hxy : x * y ≠ 0) :
    ∃ lam : ℝ, lam₀ ≤ lam ∧ P * cexp (-(I * ((4 * lam * x * y : ℝ) : ℂ))) = -((‖P‖ : ℝ) : ℂ) := by
  set θ := Complex.arg P with hθ
  have h4 : 4 * x * y ≠ 0 := by
    intro h; apply hxy; linarith
  obtain ⟨k, hk⟩ : ∃ k : ℤ, lam₀ ≤ (θ + Real.pi + k * (2 * Real.pi)) / (4 * x * y) := by
    rcases lt_or_gt_of_ne h4 with hneg | hpos4
    · obtain ⟨k, hk⟩ := exists_int_lt ((4 * x * y * lam₀ - θ - Real.pi) / (2 * Real.pi))
      refine ⟨k, ?_⟩
      rw [le_div_iff_of_neg hneg]
      have h2π : 0 < 2 * Real.pi := by positivity
      have := (lt_div_iff₀ h2π).mp hk
      linarith
    · obtain ⟨k, hk⟩ := exists_int_gt ((4 * x * y * lam₀ - θ - Real.pi) / (2 * Real.pi))
      refine ⟨k, ?_⟩
      rw [le_div_iff₀ hpos4]
      have h2π : 0 < 2 * Real.pi := by positivity
      have := (div_lt_iff₀ h2π).mp hk
      linarith
  refine ⟨(θ + Real.pi + k * (2 * Real.pi)) / (4 * x * y), hk, ?_⟩
  have hx : x ≠ 0 := left_ne_zero_of_mul hxy
  have hy : y ≠ 0 := right_ne_zero_of_mul hxy
  have hang : 4 * ((θ + Real.pi + k * (2 * Real.pi)) / (4 * x * y)) * x * y
      = θ + Real.pi + k * (2 * Real.pi) := by
    field_simp
  rw [hang]
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I P]
  rw [← hθ, mul_assoc, ← Complex.exp_add]
  have harg : (θ : ℂ) * I + -(I * ((θ + Real.pi + k * (2 * Real.pi) : ℝ) : ℂ))
      = -(Real.pi * I) + ((-k : ℤ) : ℂ) * (2 * Real.pi * I) := by
    push_cast; ring
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_neg,
    Complex.exp_pi_mul_I]
  simp

/-- q G_{c,lam} at a zero: P e^{2 lam phi} e^{-i 4 lam x y}, P = q(gamma) (gamma - c)^2. -/
lemma qG_gammaOf_eq (c lam : ℝ) (ρ : ℂ) :
    qG c lam (gammaOf ρ)
      = (qw (gammaOf ρ) * (gammaOf ρ - c) ^ 2) * ((Real.exp (2 * lam * phi c ρ) : ℝ) : ℂ)
        * cexp (-(I * ((4 * lam * (ρ.im - c) * (1 / 2 - ρ.re) : ℝ) : ℂ))) := by
  have hw : gammaOf ρ - c = (((ρ.im - c : ℝ)) : ℂ) + ((1 / 2 - ρ.re : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp [Zeta23.WeilEF.gammaOf_re]
    · simp [Zeta23.WeilEF.gammaOf_im]
  have he : cexp (-(2 * (lam : ℂ)) * (gammaOf ρ - c) ^ 2)
      = ((Real.exp (2 * lam * phi c ρ) : ℝ) : ℂ)
        * cexp (-(I * ((4 * lam * (ρ.im - c) * (1 / 2 - ρ.re) : ℝ) : ℂ))) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    rw [hw]
    unfold phi
    push_cast
    linear_combination (-(2 * (lam : ℂ)) * ((1 / 2 - (ρ.re : ℂ)) ^ 2)) * I_sq
  unfold qG gaussTest
  rw [he]
  ring

lemma norm_qG_gammaOf (c lam : ℝ) (ρ : ℂ) :
    ‖qG c lam (gammaOf ρ)‖ = ‖qw (gammaOf ρ)‖ * wsq c ρ * Real.exp (2 * lam * phi c ρ) := by
  unfold qG
  rw [norm_mul, RvMBridge7.norm_gaussTest, Zeta23.WeilEF.gammaOf_re, Zeta23.WeilEF.gammaOf_im]
  unfold wsq phi
  ring

/-- A centre avoiding the bad set AND the ordinates of the window zeros. -/
lemma exists_generic_centre' {ρ₀ : ℂ} (h₀ : ρ₀.re ≠ 1 / 2) :
    ∃ c : ℝ, |c - ρ₀.im| < |1 / 2 - ρ₀.re| ∧ c ∉ badSet ρ₀ ∧ ∀ ρ ∈ window ρ₀, ρ.im ≠ c := by
  classical
  have hy : 0 < |1 / 2 - ρ₀.re| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h₀))
  have hinf : (Set.Ioo (ρ₀.im - |1 / 2 - ρ₀.re|) (ρ₀.im + |1 / 2 - ρ₀.re|)).Infinite :=
    Set.Ioo_infinite (by linarith)
  set S : Finset ℝ := badSet ρ₀ ∪ (window ρ₀).image Complex.im with hS
  obtain ⟨c, hc⟩ := (hinf.sdiff S.finite_toSet).nonempty
  have hcS : c ∉ S := by simpa using hc.2
  refine ⟨c, ?_, fun h => hcS (Finset.mem_union_left _ h), fun ρ hρ heq => hcS ?_⟩
  · have := hc.1
    rw [Set.mem_Ioo] at this
    rw [abs_lt]
    constructor <;> linarith [this.1, this.2]
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨ρ, hρ, heq⟩)

/-! ## D. The weighted tail. -/

def wterm (c lam : ℝ) (ρ : ℂ) : ℂ := (WeilExplicit.zeroMult ρ : ℂ) * qG c lam (gammaOf ρ)

def majW (ρ₀ : ℂ) (c M η : ℝ) (lam : ℝ) (ρ : ℂ) : ℝ :=
  Real.exp (2 * lam * (M - η))
      * (if ρ ∈ window ρ₀ then (WeilExplicit.zeroMult ρ : ℝ) * (‖qw (gammaOf ρ)‖ * wsq c ρ) else 0)
    + (WeilExplicit.zeroMult ρ : ℝ) * (Cq c / (1 + Complex.normSq (gammaOf ρ)))

lemma majW_nonneg (ρ₀ : ℂ) (c M η lam : ℝ) (ρ : ℂ) : 0 ≤ majW ρ₀ c M η lam ρ := by
  unfold majW
  have h1 : 0 ≤ (if ρ ∈ window ρ₀ then (WeilExplicit.zeroMult ρ : ℝ) * (‖qw (gammaOf ρ)‖ * wsq c ρ)
      else 0) := by
    split_ifs
    · unfold wsq; positivity
    · exact le_rfl
  have h2 : 0 ≤ (WeilExplicit.zeroMult ρ : ℝ) * (Cq c / (1 + Complex.normSq (gammaOf ρ))) := by
    have := Complex.normSq_nonneg (gammaOf ρ)
    have := Cq_nonneg c
    positivity
  have h3 : 0 ≤ Real.exp (2 * lam * (M - η)) := (Real.exp_pos _).le
  nlinarith [mul_nonneg h3 h1]

lemma summable_majW (ρ₀ : ℂ) (c M η lam : ℝ) : Summable (majW ρ₀ c M η lam) := by
  unfold majW
  refine Summable.add ((summable_of_ne_finset_zero (s := window ρ₀) ?_).mul_left _)
    (summable_mult_div_one_add_normSq _)
  intro ρ hρ
  exact if_neg hρ

lemma norm_wterm_le_majW {ρ₀ : ℂ} {c : ℝ} (hc : |c - ρ₀.im| < 1 / 2) {ρ₁ : ℂ} {η : ℝ}
    (hgap : ∀ ρ ∈ window ρ₀, ρ ≠ ρ₁ → ρ ≠ reflect ρ₁ → phi c ρ ≤ phi c ρ₁ - η)
    {lam : ℝ} (hlam : 1 ≤ lam) {ρ : ℂ} (hne : ρ ≠ ρ₁) (hne' : ρ ≠ reflect ρ₁) :
    ‖wterm c lam ρ‖ ≤ majW ρ₀ c (phi c ρ₁) η lam ρ := by
  by_cases hnt : IsNontrivialZero ρ
  · unfold wterm
    rw [norm_mul, Complex.norm_natCast, norm_qG_gammaOf]
    unfold majW
    have hw : 0 ≤ wsq c ρ := by unfold wsq; positivity
    have hm : (0 : ℝ) ≤ WeilExplicit.zeroMult ρ := Nat.cast_nonneg _
    have hq := norm_nonneg (qw (gammaOf ρ))
    have hsecond : 0 ≤ (WeilExplicit.zeroMult ρ : ℝ) * (Cq c / (1 + Complex.normSq (gammaOf ρ))) := by
      have := Complex.normSq_nonneg (gammaOf ρ); have := Cq_nonneg c; positivity
    by_cases hW : ρ ∈ window ρ₀
    · rw [if_pos hW]
      have hφ := hgap ρ hW hne hne'
      have hexp : Real.exp (2 * lam * phi c ρ) ≤ Real.exp (2 * lam * (phi c ρ₁ - η)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have : (WeilExplicit.zeroMult ρ : ℝ) * (‖qw (gammaOf ρ)‖ * wsq c ρ * Real.exp (2 * lam * phi c ρ))
          ≤ Real.exp (2 * lam * (phi c ρ₁ - η))
            * ((WeilExplicit.zeroMult ρ : ℝ) * (‖qw (gammaOf ρ)‖ * wsq c ρ)) := by
        have := mul_le_mul_of_nonneg_left hexp (mul_nonneg hm (mul_nonneg hq hw))
        linarith
      linarith
    · rw [if_neg hW, mul_zero, zero_add]
      have hφ : phi c ρ < 0 := phi_neg_of_not_mem_window hc hnt hW
      have hexp : Real.exp (2 * lam * phi c ρ) ≤ Real.exp (2 * 1 * phi c ρ) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have hz : |(gammaOf ρ).im| ≤ 1 / 2 := (Zeta23.WeilEF.abs_gammaOf_im_lt hnt.2).le
      have hb := norm_qG_one_mul_le c hz
      have hpos : 0 < 1 + Complex.normSq (gammaOf ρ) := by
        have := Complex.normSq_nonneg (gammaOf ρ); linarith
      have h3 : ‖qG c 1 (gammaOf ρ)‖ ≤ Cq c / (1 + Complex.normSq (gammaOf ρ)) := by
        rw [le_div_iff₀ hpos]; exact hb
      rw [norm_qG_gammaOf] at h3
      calc (WeilExplicit.zeroMult ρ : ℝ) * (‖qw (gammaOf ρ)‖ * wsq c ρ * Real.exp (2 * lam * phi c ρ))
          ≤ (WeilExplicit.zeroMult ρ : ℝ) * (‖qw (gammaOf ρ)‖ * wsq c ρ * Real.exp (2 * 1 * phi c ρ)) := by
            gcongr
        _ ≤ _ := mul_le_mul_of_nonneg_left h3 hm
  · have : wterm c lam ρ = 0 := by
      unfold wterm
      rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial hnt]
      simp
    rw [this, norm_zero]
    exact majW_nonneg _ _ _ _ _ _

def constAW (ρ₀ : ℂ) (c : ℝ) : ℝ :=
  ∑ ρ ∈ window ρ₀, (WeilExplicit.zeroMult ρ : ℝ) * (‖qw (gammaOf ρ)‖ * wsq c ρ)

def constBW (c : ℝ) : ℝ :=
  ∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℝ) * (Cq c / (1 + Complex.normSq (gammaOf ρ)))

lemma constAW_nonneg (ρ₀ : ℂ) (c : ℝ) : 0 ≤ constAW ρ₀ c :=
  Finset.sum_nonneg fun ρ _ => by unfold wsq; positivity

lemma constBW_nonneg (c : ℝ) : 0 ≤ constBW c :=
  tsum_nonneg fun ρ => by
    have := Complex.normSq_nonneg (gammaOf ρ); have := Cq_nonneg c; positivity

lemma tsum_majW (ρ₀ : ℂ) (c M η lam : ℝ) :
    ∑' ρ : ℂ, majW ρ₀ c M η lam ρ = Real.exp (2 * lam * (M - η)) * constAW ρ₀ c + constBW c := by
  unfold majW constAW constBW
  rw [((summable_of_ne_finset_zero (s := window ρ₀) fun ρ hρ => if_neg hρ).mul_left _).tsum_add
    (summable_mult_div_one_add_normSq _), tsum_mul_left]
  congr 2
  rw [tsum_eq_sum (s := window ρ₀) fun ρ hρ => if_neg hρ]
  exact Finset.sum_congr rfl fun ρ hρ => if_pos hρ

lemma tail_boundW {ρ₀ : ℂ} {c : ℝ} (hc : |c - ρ₀.im| < 1 / 2) {ρ₁ : ℂ} {η : ℝ}
    (hgap : ∀ ρ ∈ window ρ₀, ρ ≠ ρ₁ → ρ ≠ reflect ρ₁ → phi c ρ ≤ phi c ρ₁ - η)
    {lam : ℝ} (hlam : 1 ≤ lam) :
    ‖∑' ρ : {ρ : ℂ // ρ ≠ ρ₁ ∧ ρ ≠ reflect ρ₁}, wterm c lam ρ‖
      ≤ Real.exp (2 * lam * (phi c ρ₁ - η)) * constAW ρ₀ c + constBW c := by
  rw [← tsum_majW ρ₀ c (phi c ρ₁) η lam]
  exact norm_tsum_subtype_le_tsum {ρ : ℂ | ρ ≠ ρ₁ ∧ ρ ≠ reflect ρ₁}
    (summable_majW ρ₀ c (phi c ρ₁) η lam) (majW_nonneg ρ₀ c (phi c ρ₁) η lam)
    fun ρ => norm_wterm_le_majW hc hgap hlam ρ.2.1 ρ.2.2

/-! ## E. Weighted dominance. -/

/-- **Weighted dominance.**  An off-line nontrivial zero forces a negative weighted Gaussian zero
sum for some centre and some lam >= 1. -/
theorem weighted_dominance (ρ₀ : ℂ) (h₀ : IsNontrivialZero ρ₀) (hre₀ : ρ₀.re ≠ 1 / 2) :
    ∃ c lam : ℝ, 1 ≤ lam ∧ (zeroSide (qG c lam)).re < 0 := by
  obtain ⟨c, hcI, hcbad, hcim⟩ := exists_generic_centre' hre₀
  have hy₀ : |1 / 2 - ρ₀.re| < 1 / 2 := by
    rw [abs_lt]; constructor <;> linarith [h₀.2.1, h₀.2.2]
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
    intro h; rw [h] at hy₁; simp at hy₁
  have hm₁ : (1 : ℝ) ≤ WeilExplicit.zeroMult ρ₁ := by
    rw [RvMBridge4.zeroMult_eq_mult hρ₁nt]
    exact_mod_cast zetaSeam.one_le_mult ρ₁ hρ₁nt
  have hx₁ : ρ₁.im - c ≠ 0 := sub_ne_zero.mpr (hcim ρ₁ hρ₁)
  have hy₁' : 1 / 2 - ρ₁.re ≠ 0 := sub_ne_zero.mpr (Ne.symm h₁)
  have hxy : (ρ₁.im - c) * (1 / 2 - ρ₁.re) ≠ 0 := mul_ne_zero hx₁ hy₁'
  have hq₁ : qw (gammaOf ρ₁) ≠ 0 := qw_gammaOf_ne_zero hρ₁nt
  have hγc : gammaOf ρ₁ - c ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [Zeta23.WeilEF.gammaOf_re] at this
    exact hx₁ (by linarith)
  set P : ℂ := qw (gammaOf ρ₁) * (gammaOf ρ₁ - c) ^ 2 with hP
  have hP0 : P ≠ 0 := mul_ne_zero hq₁ (pow_ne_zero 2 hγc)
  have hnP : ‖P‖ = ‖qw (gammaOf ρ₁)‖ * wsq c ρ₁ := by
    rw [hP, norm_mul, norm_pow]
    congr 1
    rw [Complex.sq_norm, Complex.normSq_apply]
    unfold wsq
    simp [Zeta23.WeilEF.gammaOf_re, Zeta23.WeilEF.gammaOf_im]
    ring
  set K : ℝ := (WeilExplicit.zeroMult ρ₁ : ℝ) * ‖P‖ with hK
  have hK0 : 0 < K := mul_pos (by linarith) (norm_pos_iff.mpr hP0)
  set A := constAW ρ₀ c with hA
  set B := constBW c with hB
  have hA0 : 0 ≤ A := constAW_nonneg ρ₀ c
  have hB0 : 0 ≤ B := constBW_nonneg c
  set lam₀ : ℝ := max 1 (max (A / (2 * η * K)) (B / (2 * M * K))) with hlam₀
  obtain ⟨lam, hlam, hphase⟩ := exists_lam_phase lam₀ hP0 hxy
  have hlam1 : 1 ≤ lam := (le_max_left _ _).trans hlam
  have hlamA : A / (2 * η * K) ≤ lam := ((le_max_left _ _).trans (le_max_right _ _)).trans hlam
  have hlamB : B / (2 * M * K) ≤ lam := ((le_max_right _ _).trans (le_max_right _ _)).trans hlam
  refine ⟨c, lam, hlam1, ?_⟩
  -- pair split
  have hsplit := zeroSide_pair_split (qG_conj c lam) (summable_qG_zeroSide c hlam1) h₁
  have hval : (qG c lam (gammaOf ρ₁)).re = -(‖P‖ * Real.exp (2 * lam * M)) := by
    rw [qG_gammaOf_eq]
    have h4 : 4 * lam * (ρ₁.im - c) * (1 / 2 - ρ₁.re) = 4 * lam * (ρ₁.im - c) * (1 / 2 - ρ₁.re) := rfl
    rw [mul_right_comm, hphase]
    simp only [← hM]
    rw [show -((‖P‖ : ℝ) : ℂ) * ((Real.exp (2 * lam * M) : ℝ) : ℂ)
        = ((-(‖P‖ * Real.exp (2 * lam * M)) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  have hmain : (zeroSide (qG c lam)).re
      ≤ 2 * (WeilExplicit.zeroMult ρ₁ : ℝ) * (qG c lam (gammaOf ρ₁)).re
        + (Real.exp (2 * lam * (M - η)) * A + B) := by
    rw [hsplit, Complex.add_re]
    have hre : (2 * (WeilExplicit.zeroMult ρ₁ : ℂ) * ((qG c lam (gammaOf ρ₁)).re : ℂ)).re
        = 2 * (WeilExplicit.zeroMult ρ₁ : ℝ) * (qG c lam (gammaOf ρ₁)).re := by
      have : (2 * (WeilExplicit.zeroMult ρ₁ : ℂ) * ((qG c lam (gammaOf ρ₁)).re : ℂ))
          = ((2 * (WeilExplicit.zeroMult ρ₁ : ℝ) * (qG c lam (gammaOf ρ₁)).re : ℝ) : ℂ) := by
        push_cast; ring
      rw [this, Complex.ofReal_re]
    rw [hre]
    have htail := tail_boundW hc hgap hlam1
    have hgoal : (∑' ρ : {ρ : ℂ // ρ ≠ ρ₁ ∧ ρ ≠ reflect ρ₁},
        (WeilExplicit.zeroMult ρ : ℂ) * qG c lam (gammaOf ρ)).re
        ≤ Real.exp (2 * lam * (phi c ρ₁ - η)) * constAW ρ₀ c + constBW c :=
      le_trans (Complex.re_le_norm _) htail
    linarith
  rw [hval] at hmain
  have hpair : 2 * (WeilExplicit.zeroMult ρ₁ : ℝ) * -(‖P‖ * Real.exp (2 * lam * M))
      = -(2 * K * Real.exp (2 * lam * M)) := by rw [hK]; ring
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
  have hsplit2 : Real.exp (2 * lam * (M - η)) * Real.exp (2 * lam * η) = Real.exp (2 * lam * M) := by
    rw [← Real.exp_add]; congr 1; ring
  have hE1 : 0 < Real.exp (2 * lam * (M - η)) := Real.exp_pos _
  have hAterm : Real.exp (2 * lam * (M - η)) * A ≤ K * Real.exp (2 * lam * M) := by
    calc Real.exp (2 * lam * (M - η)) * A
        ≤ Real.exp (2 * lam * (M - η)) * (K * Real.exp (2 * lam * η)) :=
          mul_le_mul_of_nonneg_left hexpη hE1.le
      _ = K * (Real.exp (2 * lam * (M - η)) * Real.exp (2 * lam * η)) := by ring
      _ = K * Real.exp (2 * lam * M) := by rw [hsplit2]
  linarith

end RvMBridgePF
