/-
  E6Bridge12 -- the LADDER-CERTIFIED REGION of the two-parameter Wall, as a kernel instrument
  (2026-09-21, WALL ASSAULT seam C).

  The Wall (E6Bridge6/7/8/9): RH  <->  for every real centre c and every lam > 0,

      F(c, lam) := Re zeroSide (gaussTest c lam)
                 = Re Sum_rho m(rho) (gamma_rho - c)^2 exp (-2 lam (gamma_rho - c)^2)  >=  0,

  gamma_rho = (rho - 1/2)/i, so for rho = beta + i t, gamma_rho = t + i (1/2 - beta).

  THIS FILE proves positivity of F(c, lam) on the part of the (c, lam) quadrant that a finite
  Turing verification certifies, with the certification carried as a HYPOTHESIS:

      WindowOnLine c D  :=  every nontrivial zero with |Im rho - c| <= D has Re rho = 1/2.

  The Turing ladder (rh campaign, zeta_zero_localization island, a DIFFERENT toolchain; it cannot
  be imported here) certifies this for every c <= T - D, currently T = 640000
  (AllZeros_h640000.lean).  The instantiation is a registry-level composition, not a Lean import;
  see docs/WALL_SEAM_C_LADDER_REGION_2026-09-21.md.

  THE ARGUMENT.  Split the zero sum at the ordinate window |Im rho - c| <= D.
    (W) Inside the window every zero is on the line (hwin), so gamma_rho = Im rho is REAL and the
        summand m (x - c)^2 e^{-2 lam (x - c)^2} is real and >= 0.  The window sum is therefore
        >= the single certified near term at rho_1 with delta <= |Im rho_1 - c| <= d, which is
        >= delta^2 e^{-2 lam d^2}  (m(rho_1) >= 1, Zeta23.zetaSeam.one_le_mult).
    (T) Outside the window phi_c(rho) = (1/2 - Re rho)^2 - (Im rho - c)^2 <= 1/4 - D^2 < 0, so for
        lam >= 1 the modulus m |w|^2 e^{2 lam phi} <= e^{2 (lam - 1)(1/4 - D^2)} m |w|^2 e^{2 phi}
        = e^{2 (lam - 1)(1/4 - D^2)} |term at lam = 1|, and the lam = 1 term is bounded by the
        summable local-count majorant of E6Bridge6/7 (norm_gaussTest_mul_le at lam = 1,
        summable_mult_div_one_add_normSq); the tail sum is <= e^{2 (lam - 1)(1/4 - D^2)} constB c
        with E6Bridge7's lam-independent constant constB c.
    (A) Positivity follows once  e^{2 (lam - 1)(1/4 - D^2)} B <= delta^2 e^{-2 lam d^2}, i.e.
        e^{2 (D^2 - 1/4)} B e^{-2 lam kappa} <= delta^2 with kappa := D^2 - 1/4 - d^2 > 0; using
        e^{-2 lam kappa} <= 1/(2 lam kappa) this holds for every
        lam >= lamThreshold c D d delta := max 1 (B e^{2 (D^2 - 1/4)} / (2 kappa delta^2)).
        Explicit, log-free.  (For d <= 1, D >= 2: kappa >= 11/4.)
    (G) DOMINANCE FORM (the instrument the numerics actually validate, section G): the window
        part of the zero side is EXACTLY the finite certified sum
            windowSum c D lam = Sum_{|Im rho - c| <= D} m(rho) (Im rho - c)^2 e^{-2 lam (Im rho - c)^2}
        (finite by the local zero count), so  F(c, lam) >= windowSum - tailEnvelope  with
        tailEnvelope c D lam = e^{2 (lam - 1)(1/4 - D^2)} constB c, and F >= 0 whenever the
        computable inequality  tailEnvelope <= windowSum  holds (gaussian_positivity_of_window_dominance).
        The single-near-zero form (A) is the special case windowSum >= one term.

  WHAT IS CONSUMED (all unconditional, #print axioms = [propext, Classical.choice, Quot.sound]):
    RvMBridge6.zeroSide, gaussTest, summable_gauss_zeroSide, norm_gaussTest_mul_le   (E6Bridge6)
    RvMBridgeGauss.summable_mult_div_one_add_normSq, norm_tsum_subtype_le_mul_tsum,
      exp_two_mul_le_of_le, winSet, zeroWindow, mem_zeroWindow            (the prelude)
    RvMBridge7.term, phi, wsq, norm_term, re_gaussTest, constB, constB_nonneg   (E6Bridge7)
    RvMBridge4.zeroMult_eq_mult, zeroMult_eq_zero_of_not_nontrivial
    Zeta23.zetaSeam.one_le_mult, Zeta23.WeilEF.gammaOf_re / gammaOf_im / abs_gammaOf_im_lt
    Mathlib: Summable.tsum_add_tsum_compl, Summable.le_tsum, Summable.tsum_le_tsum,
             Summable.tsum_subtype_le, Complex.re_tsum, Complex.hasSum_re, norm_tsum_le_tsum_norm.

  NOT proved: RH.  Nothing here says anything about zeros outside a certified window, and the
  hypothesis WindowOnLine is exactly what the ladder supplies for c <= T - D and NOTHING supplies
  beyond.  The uncertified residual {c > T - D} x {lam > 0} (together with the small-lam region
  below lamThreshold, seam B) IS the Wall.  conjecture1_proved = False.
-/
import E6Bridge6
import E6Bridge7
import RvMBridgeGauss

open Zeta23 Complex MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace RvMBridge12
open WeilExplicit RvMBridge6 RvMBridge7 RvMBridgeGauss

/-! ## A. Vocabulary: the certified window and the tail weight. -/

/-- All nontrivial zeros with ordinate within D of c lie on the line (what the Turing ladder
certifies for c <= T - D; carried here as a hypothesis, cross-island). -/
def WindowOnLine (c D : ℝ) : Prop :=
  ∀ ρ : ℂ, IsNontrivialZero ρ → |ρ.im - c| ≤ D → ρ.re = 1 / 2

/-- Full RH (every nontrivial zero on the line) gives every window. -/
lemma windowOnLine_of_all_on_line (h : ∀ ρ : ℂ, IsNontrivialZero ρ → ρ.re = 1 / 2) (c D : ℝ) :
    WindowOnLine c D :=
  fun ρ hρ _ => h ρ hρ

/-! The ordinate window winSet c D = {rho | |Im rho - c| <= D} and the certified finite window
zeroWindow c D (with mem_zeroWindow) live in the prelude RvMBridgeGauss, section E
(formerly here). -/

/-- E6Bridge7's lam = 1 local-count majorant m(rho) C_1(c)/(1 + |gamma_rho|^2), with
C_1(c) = e^{1/2} (2 c^2 + 13/4) / (min 1 1)^2; its tsum is constB c definitionally. -/
def tailWeight (c : ℝ) (ρ : ℂ) : ℝ :=
  (WeilExplicit.zeroMult ρ : ℝ)
    * ((Real.exp (1 / 2) * (2 * c ^ 2 + 13 / 4) / (min 1 1) ^ 2)
        / (1 + Complex.normSq (gammaOf ρ)))

lemma tailWeight_nonneg (c : ℝ) (ρ : ℂ) : 0 ≤ tailWeight c ρ := by
  unfold tailWeight
  have := Complex.normSq_nonneg (gammaOf ρ)
  have hmin : (0 : ℝ) < min 1 1 := by norm_num
  positivity

lemma summable_tailWeight (c : ℝ) : Summable (tailWeight c) :=
  summable_mult_div_one_add_normSq _

lemma tsum_tailWeight (c : ℝ) : ∑' ρ : ℂ, tailWeight c ρ = constB c := rfl

/-- The lam threshold: max 1 (B e^{2 (D^2 - 1/4)} / (2 kappa delta^2)), kappa = D^2 - 1/4 - d^2,
B = constB c. -/
def lamThreshold (c D d δ : ℝ) : ℝ :=
  max 1 (constB c * Real.exp (2 * (D ^ 2 - 1 / 4)) / (2 * (D ^ 2 - 1 / 4 - d ^ 2) * δ ^ 2))

lemma one_le_lamThreshold (c D d δ : ℝ) : 1 ≤ lamThreshold c D d δ := le_max_left _ _

/-! ## B. A zero on the line contributes a real, nonnegative summand. -/

/-- On the line the Gaussian summand is real: Re term = m(rho) (Im rho - c)^2 e^{-2 lam (Im rho - c)^2}. -/
lemma re_term_of_on_line (c lam : ℝ) {ρ : ℂ} (h : ρ.re = 1 / 2) :
    (term c lam ρ).re
      = (WeilExplicit.zeroMult ρ : ℝ)
          * ((ρ.im - c) ^ 2 * Real.exp (-(2 * lam) * (ρ.im - c) ^ 2)) := by
  have h0 : (gammaOf ρ).im = 0 := by
    rw [Zeta23.WeilEF.gammaOf_im, h]
    norm_num
  unfold term
  rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, re_gaussTest,
    Zeta23.WeilEF.gammaOf_re, h0]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_sub, sub_zero,
    mul_zero, Real.cos_zero, mul_one, Real.sin_zero, add_zero]
  ring_nf

lemma re_term_nonneg_of_on_line (c lam : ℝ) {ρ : ℂ} (h : ρ.re = 1 / 2) :
    0 ≤ (term c lam ρ).re := by
  rw [re_term_of_on_line c lam h]
  positivity

/-- The summand at a non-zero is 0. -/
lemma term_eq_zero_of_not_nontrivial (c lam : ℝ) {ρ : ℂ} (h : ¬ IsNontrivialZero ρ) :
    term c lam ρ = 0 := by
  unfold term
  rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial h]
  simp

/-- If rho is either not a nontrivial zero or a zero ON the line, its summand has Re >= 0. -/
lemma re_term_nonneg (c lam : ℝ) {ρ : ℂ} (h : IsNontrivialZero ρ → ρ.re = 1 / 2) :
    0 ≤ (term c lam ρ).re := by
  by_cases hnt : IsNontrivialZero ρ
  · exact re_term_nonneg_of_on_line c lam (h hnt)
  · rw [term_eq_zero_of_not_nontrivial c lam hnt]
    simp

/-- The near term is bounded below: a zero on the line with delta <= |Im rho - c| <= d contributes
at least delta^2 e^{-2 lam d^2}. -/
lemma near_term_ge {c lam d δ : ℝ} (hδ : 0 ≤ δ) (hlam : 0 ≤ lam) {ρ : ℂ} (hnt : IsNontrivialZero ρ)
    (hline : ρ.re = 1 / 2) (hδρ : δ ≤ |ρ.im - c|) (hρd : |ρ.im - c| ≤ d) :
    δ ^ 2 * Real.exp (-(2 * lam * d ^ 2)) ≤ (term c lam ρ).re := by
  rw [re_term_of_on_line c lam hline]
  have hm : (1 : ℝ) ≤ WeilExplicit.zeroMult ρ := by
    rw [RvMBridge4.zeroMult_eq_mult hnt]
    exact_mod_cast zetaSeam.one_le_mult ρ hnt
  have hx2 : δ ^ 2 ≤ (ρ.im - c) ^ 2 := by
    rw [← sq_abs (ρ.im - c)]
    exact pow_le_pow_left₀ hδ hδρ 2
  have hx2' : (ρ.im - c) ^ 2 ≤ d ^ 2 := by
    rw [← sq_abs (ρ.im - c)]
    exact pow_le_pow_left₀ (abs_nonneg _) hρd 2
  have hexp : Real.exp (-(2 * lam * d ^ 2)) ≤ Real.exp (-(2 * lam) * (ρ.im - c) ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  calc δ ^ 2 * Real.exp (-(2 * lam * d ^ 2))
      ≤ (ρ.im - c) ^ 2 * Real.exp (-(2 * lam) * (ρ.im - c) ^ 2) :=
        mul_le_mul hx2 hexp (Real.exp_pos _).le (sq_nonneg _)
    _ = 1 * ((ρ.im - c) ^ 2 * Real.exp (-(2 * lam) * (ρ.im - c) ^ 2)) := (one_mul _).symm
    _ ≤ (WeilExplicit.zeroMult ρ : ℝ) * ((ρ.im - c) ^ 2 * Real.exp (-(2 * lam) * (ρ.im - c) ^ 2)) :=
        mul_le_mul_of_nonneg_right hm (by positivity)

/-! ## C. The forward half of the Wall: all zeros on the line gives F(c, lam) >= 0 everywhere. -/

/-- **Forward half (trivial corollary).**  If every nontrivial zero is on the line, then every
Gaussian zero sum is nonnegative: each summand is real and >= 0. -/
theorem gaussian_positivity_of_all_on_line (h : ∀ ρ : ℂ, IsNontrivialZero ρ → ρ.re = 1 / 2)
    (c lam : ℝ) (hlam : 0 < lam) : 0 ≤ (zeroSide (gaussTest c lam)).re := by
  have hs : Summable (term c lam) := summable_gauss_zeroSide c lam hlam
  rw [zeroSide_gauss_eq, Complex.re_tsum hs]
  exact tsum_nonneg fun ρ => re_term_nonneg c lam (h ρ)

/-! ## D. The window/tail split. -/

lemma summable_term_subtype (c lam : ℝ) (hlam : 0 < lam) (s : Set ℂ) :
    Summable (term c lam ∘ (Subtype.val : s → ℂ)) :=
  (summable_gauss_zeroSide c lam hlam).subtype s

/-- zeroSide = window sum + tail sum. -/
lemma zeroSide_split (c D lam : ℝ) (hlam : 0 < lam) :
    zeroSide (gaussTest c lam)
      = (∑' ρ : winSet c D, term c lam ρ) + ∑' ρ : ↥(winSet c D)ᶜ, term c lam ρ := by
  rw [zeroSide_gauss_eq]
  exact (Summable.tsum_add_tsum_compl (f := term c lam) (s := winSet c D)
    (summable_term_subtype c lam hlam _) (summable_term_subtype c lam hlam _)).symm

/-- Under WindowOnLine the window sum is real-nonnegative termwise, hence >= any single term. -/
lemma re_window_ge_term {c D lam : ℝ} (hlam : 0 < lam) (hwin : WindowOnLine c D) {ρ₁ : ℂ}
    (h₁ : |ρ₁.im - c| ≤ D) :
    (term c lam ρ₁).re ≤ (∑' ρ : winSet c D, term c lam ρ).re := by
  have hsum : Summable (fun ρ : winSet c D => term c lam ρ) := summable_term_subtype c lam hlam _
  rw [Complex.re_tsum hsum]
  have hs : Summable (fun ρ : winSet c D => (term c lam ρ).re) :=
    (Complex.hasSum_re hsum.hasSum).summable
  exact hs.le_tsum ⟨ρ₁, h₁⟩ fun ρ _ => re_term_nonneg c lam fun hnt => hwin ρ hnt ρ.2

/-! ## E. The tail: outside the window phi <= 1/4 - D^2 < 0, and lam >= 1 decouples. -/

/-- Outside the ordinate window the exponent phi_c is at most 1/4 - D^2. -/
lemma phi_le_of_far {c D : ℝ} (hD : 0 ≤ D) {ρ : ℂ} (hnt : IsNontrivialZero ρ)
    (hfar : D < |ρ.im - c|) : phi c ρ ≤ 1 / 4 - D ^ 2 := by
  have hy : |1 / 2 - ρ.re| < 1 / 2 := by
    rw [abs_lt]
    constructor <;> linarith [hnt.2.1, hnt.2.2]
  have h1 : (1 / 2 - ρ.re) ^ 2 ≤ (1 / 2) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hy.le 2
  have h2 : D ^ 2 ≤ (ρ.im - c) ^ 2 := by
    rw [← sq_abs (ρ.im - c)]
    exact pow_le_pow_left₀ hD hfar.le 2
  unfold phi
  linarith

/-- The pointwise tail bound for lam >= 1: |term| <= e^{2 (lam - 1)(1/4 - D^2)} tailWeight. -/
lemma norm_term_le_tail {c D : ℝ} (hD : 0 ≤ D) {lam : ℝ} (hlam : 1 ≤ lam) {ρ : ℂ}
    (hfar : D < |ρ.im - c|) :
    ‖term c lam ρ‖ ≤ Real.exp (2 * (lam - 1) * (1 / 4 - D ^ 2)) * tailWeight c ρ := by
  by_cases hnt : IsNontrivialZero ρ
  · rw [norm_term]
    have hφ := phi_le_of_far hD hnt hfar
    have hw : 0 ≤ wsq c ρ := by unfold wsq; positivity
    have hm : (0 : ℝ) ≤ WeilExplicit.zeroMult ρ := Nat.cast_nonneg _
    have hexp : Real.exp (2 * lam * phi c ρ)
        ≤ Real.exp (2 * (lam - 1) * (1 / 4 - D ^ 2)) * Real.exp (2 * 1 * phi c ρ) := by
      rw [show (2 : ℝ) * 1 * phi c ρ = 2 * phi c ρ by ring]
      exact exp_two_mul_le_of_le hlam hφ
    have h1 : (WeilExplicit.zeroMult ρ : ℝ) * wsq c ρ * Real.exp (2 * lam * phi c ρ)
        ≤ Real.exp (2 * (lam - 1) * (1 / 4 - D ^ 2))
          * ((WeilExplicit.zeroMult ρ : ℝ) * wsq c ρ * Real.exp (2 * 1 * phi c ρ)) := by
      have := mul_le_mul_of_nonneg_left hexp (mul_nonneg hm hw)
      linarith
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
      simpa using hb
    have h4 : ‖term c 1 ρ‖ = (WeilExplicit.zeroMult ρ : ℝ) * ‖gaussTest c 1 (gammaOf ρ)‖ := by
      unfold term
      rw [norm_mul, Complex.norm_natCast]
    have h5 : ‖term c 1 ρ‖ ≤ tailWeight c ρ := by
      rw [h4]
      exact mul_le_mul_of_nonneg_left h3 hm
    calc (WeilExplicit.zeroMult ρ : ℝ) * wsq c ρ * Real.exp (2 * lam * phi c ρ)
        ≤ Real.exp (2 * (lam - 1) * (1 / 4 - D ^ 2)) * ‖term c 1 ρ‖ := by rw [← h2]; exact h1
      _ ≤ Real.exp (2 * (lam - 1) * (1 / 4 - D ^ 2)) * tailWeight c ρ :=
          mul_le_mul_of_nonneg_left h5 (Real.exp_pos _).le
  · rw [term_eq_zero_of_not_nontrivial c lam hnt, norm_zero]
    exact mul_nonneg (Real.exp_pos _).le (tailWeight_nonneg c ρ)

/-- The tail sum over the complement of the window, lam >= 1:
‖tail‖ <= e^{2 (lam - 1)(1/4 - D^2)} constB c. -/
lemma tail_bound_window {c D : ℝ} (hD : 0 ≤ D) {lam : ℝ} (hlam : 1 ≤ lam) :
    ‖∑' ρ : ↥(winSet c D)ᶜ, term c lam ρ‖
      ≤ Real.exp (2 * (lam - 1) * (1 / 4 - D ^ 2)) * constB c := by
  rw [← tsum_tailWeight c]
  refine norm_tsum_subtype_le_mul_tsum (winSet c D)ᶜ (Real.exp_pos _).le (summable_tailWeight c)
    (tailWeight_nonneg c) fun ρ => ?_
  have hfar : D < |(ρ : ℂ).im - c| := by
    have h := ρ.2
    simp only [winSet, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at h
    exact h
  exact norm_term_le_tail hD hlam hfar

/-! ## F. The threshold inequality and the assembly. -/

/-- For lam >= lamThreshold, the tail envelope is below the near-term floor:
e^{2 (lam - 1)(1/4 - D^2)} B <= delta^2 e^{-2 lam d^2}. -/
lemma tail_le_near_of_threshold {c D d δ lam : ℝ} (hδ : 0 < δ) (hgap : d ^ 2 + 1 / 4 < D ^ 2)
    (hlam : lamThreshold c D d δ ≤ lam) :
    Real.exp (2 * (lam - 1) * (1 / 4 - D ^ 2)) * constB c
      ≤ δ ^ 2 * Real.exp (-(2 * lam * d ^ 2)) := by
  have hlam1 : 1 ≤ lam := le_trans (le_max_left _ _) hlam
  set κ : ℝ := D ^ 2 - 1 / 4 - d ^ 2 with hκ
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  set B : ℝ := constB c with hB
  have hden : 0 < 2 * κ * δ ^ 2 := by positivity
  have hlam2 : B * Real.exp (2 * (D ^ 2 - 1 / 4)) / (2 * κ * δ ^ 2) ≤ lam :=
    le_trans (le_max_right _ _) hlam
  have hlam3 : B * Real.exp (2 * (D ^ 2 - 1 / 4)) ≤ lam * (2 * κ * δ ^ 2) := by
    rwa [div_le_iff₀ hden] at hlam2
  -- e^{-2 lam kappa} (2 lam kappa) <= 1, from 1 + t <= e^t
  have hexpκ : Real.exp (-(2 * lam * κ)) * (2 * lam * κ) ≤ 1 := by
    have h1 : 1 + 2 * lam * κ ≤ Real.exp (2 * lam * κ) := by
      have := Real.add_one_le_exp (2 * lam * κ)
      linarith
    rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _), mul_one]
    linarith
  have hEsplit : Real.exp (2 * (lam - 1) * (1 / 4 - D ^ 2))
      = Real.exp (2 * (D ^ 2 - 1 / 4)) * Real.exp (-(2 * lam * κ))
          * Real.exp (-(2 * lam * d ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hκ]
    ring
  have hEκ : 0 ≤ Real.exp (-(2 * lam * κ)) := (Real.exp_pos _).le
  have hcore : Real.exp (2 * (D ^ 2 - 1 / 4)) * Real.exp (-(2 * lam * κ)) * B ≤ δ ^ 2 := by
    calc Real.exp (2 * (D ^ 2 - 1 / 4)) * Real.exp (-(2 * lam * κ)) * B
        = Real.exp (-(2 * lam * κ)) * (B * Real.exp (2 * (D ^ 2 - 1 / 4))) := by ring
      _ ≤ Real.exp (-(2 * lam * κ)) * (lam * (2 * κ * δ ^ 2)) :=
          mul_le_mul_of_nonneg_left hlam3 hEκ
      _ = (Real.exp (-(2 * lam * κ)) * (2 * lam * κ)) * δ ^ 2 := by ring
      _ ≤ 1 * δ ^ 2 := mul_le_mul_of_nonneg_right hexpκ (sq_nonneg _)
      _ = δ ^ 2 := one_mul _
  rw [hEsplit]
  calc Real.exp (2 * (D ^ 2 - 1 / 4)) * Real.exp (-(2 * lam * κ)) * Real.exp (-(2 * lam * d ^ 2)) * B
      = (Real.exp (2 * (D ^ 2 - 1 / 4)) * Real.exp (-(2 * lam * κ)) * B)
          * Real.exp (-(2 * lam * d ^ 2)) := by ring
    _ ≤ δ ^ 2 * Real.exp (-(2 * lam * d ^ 2)) :=
        mul_le_mul_of_nonneg_right hcore (Real.exp_pos _).le

/-- **The ladder-certified region of the Wall.**  If every nontrivial zero with ordinate within
D of c lies on the line (the Turing certification, carried as a hypothesis), and some certified
zero sits at distance between delta > 0 and d of c, with d^2 + 1/4 < D^2, then the Gaussian zero
sum F(c, lam) is nonnegative for every lam >= lamThreshold c D d delta
= max 1 (constB c e^{2 (D^2 - 1/4)} / (2 (D^2 - 1/4 - d^2) delta^2)).
NOT a statement about RH: outside the window nothing is assumed and nothing is concluded. -/
theorem gaussian_positivity_of_window {c D d δ lam : ℝ} (hD : 0 ≤ D) (hδ : 0 < δ)
    (hgap : d ^ 2 + 1 / 4 < D ^ 2) (hwin : WindowOnLine c D)
    (hnear : ∃ ρ : ℂ, IsNontrivialZero ρ ∧ δ ≤ |ρ.im - c| ∧ |ρ.im - c| ≤ d)
    (hlam : lamThreshold c D d δ ≤ lam) : 0 ≤ (zeroSide (gaussTest c lam)).re := by
  obtain ⟨ρ₁, h₁nt, hδ₁, hd₁⟩ := hnear
  have hlam1 : 1 ≤ lam := le_trans (le_max_left _ _) hlam
  have hlam0 : 0 < lam := by linarith
  have hd0 : 0 ≤ d := le_trans (abs_nonneg _) hd₁
  have hdD : d ≤ D := (pow_le_pow_iff_left₀ hd0 hD two_ne_zero).mp (by linarith)
  have h₁win : |ρ₁.im - c| ≤ D := hd₁.trans hdD
  have h₁line : ρ₁.re = 1 / 2 := hwin ρ₁ h₁nt h₁win
  have hnear' := near_term_ge hδ.le hlam0.le h₁nt h₁line hδ₁ hd₁
  have hwinre := re_window_ge_term hlam0 hwin h₁win
  have htail := tail_bound_window (c := c) hD hlam1
  have htailre : -(Real.exp (2 * (lam - 1) * (1 / 4 - D ^ 2)) * constB c)
      ≤ (∑' ρ : ↥(winSet c D)ᶜ, term c lam ρ).re := by
    have h := abs_le.mp (Complex.abs_re_le_norm (∑' ρ : ↥(winSet c D)ᶜ, term c lam ρ))
    linarith [h.1]
  have hkey := tail_le_near_of_threshold (c := c) hδ hgap hlam
  rw [zeroSide_split c D lam hlam0, Complex.add_re]
  linarith

/-- The concrete instance the memo uses: window half-width D = 2, a certified zero within d = 1
of c but at least delta away (kappa = 11/4), lam >= max 1 (constB c e^{15/2} / (11 delta^2 / 2)). -/
theorem gaussian_positivity_of_window_two {c δ lam : ℝ} (hδ : 0 < δ) (hwin : WindowOnLine c 2)
    (hnear : ∃ ρ : ℂ, IsNontrivialZero ρ ∧ δ ≤ |ρ.im - c| ∧ |ρ.im - c| ≤ 1)
    (hlam : lamThreshold c 2 1 δ ≤ lam) : 0 ≤ (zeroSide (gaussTest c lam)).re :=
  gaussian_positivity_of_window (by norm_num) hδ (by norm_num) hwin hnear hlam

/-! ## G. The dominance form: the FINITE certified window sum against the tail envelope.

The landscape numerics (docs/WALL_LANDSCAPE_2026-09-21.md, section 2) show that a SINGLE near term
essentially never beats the tail (a zero just inside D against one just outside), while the whole
window sum does, at every centre tested, for lam >= 0.27 (D = 2).  So the honest instrument
hypothesis is the computable finite inequality  tailEnvelope <= windowSum, evaluated on the
ladder's certified zeros (a certificate, cross-island), not the existence of one near zero. -/

/-- The FINITE certified window sum  Sum_{|Im rho - c| <= D} m(rho) (Im rho - c)^2 e^{-2 lam (Im rho - c)^2}
(the on-line value of each summand; under WindowOnLine it IS the window part of the zero side). -/
def windowSum (c D lam : ℝ) : ℝ :=
  ∑ ρ ∈ zeroWindow c D,
    (WeilExplicit.zeroMult ρ : ℝ) * ((ρ.im - c) ^ 2 * Real.exp (-(2 * lam) * (ρ.im - c) ^ 2))

lemma windowSum_nonneg (c D lam : ℝ) : 0 ≤ windowSum c D lam :=
  Finset.sum_nonneg fun ρ _ => by positivity

/-- The certified tail envelope  e^{2 (lam - 1)(1/4 - D^2)} constB c  (tail_bound_window, lam >= 1). -/
def tailEnvelope (c D lam : ℝ) : ℝ := Real.exp (2 * (lam - 1) * (1 / 4 - D ^ 2)) * constB c

lemma tailEnvelope_nonneg (c D lam : ℝ) : 0 ≤ tailEnvelope c D lam :=
  mul_nonneg (Real.exp_pos _).le (constB_nonneg c)

/-- Under WindowOnLine the window part of the zero side is EXACTLY the finite window sum. -/
lemma re_window_eq_windowSum {c D lam : ℝ} (hwin : WindowOnLine c D) :
    (∑' ρ : winSet c D, term c lam ρ).re = windowSum c D lam := by
  rw [tsum_subtype (winSet c D) (term c lam)]
  have hzero : ∀ ρ ∉ zeroWindow c D, (winSet c D).indicator (term c lam) ρ = 0 := by
    intro ρ hρ
    by_cases hw : ρ ∈ winSet c D
    · rw [Set.indicator_of_mem hw]
      apply term_eq_zero_of_not_nontrivial
      intro hnt
      exact hρ (mem_zeroWindow.mpr ⟨hnt, hw⟩)
    · exact Set.indicator_of_notMem hw _
  rw [tsum_eq_sum hzero, Complex.re_sum]
  unfold windowSum
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  have h := mem_zeroWindow.mp hρ
  rw [Set.indicator_of_mem (show ρ ∈ winSet c D from h.2), re_term_of_on_line c lam (hwin ρ h.1 h.2)]

/-- **The ladder-certified region, dominance form.**  If every nontrivial zero with ordinate
within D of c is on the line (the Turing certification) and the finite certified window sum
dominates the tail envelope at this lam >= 1 (a computable inequality on the certified zeros),
then F(c, lam) >= 0.  Both hypotheses are what a registry-level certificate supplies; nothing about
zeros outside the window is assumed or concluded. -/
theorem gaussian_positivity_of_window_dominance {c D lam : ℝ} (hD : 0 ≤ D) (hlam : 1 ≤ lam)
    (hwin : WindowOnLine c D) (hdom : tailEnvelope c D lam ≤ windowSum c D lam) :
    0 ≤ (zeroSide (gaussTest c lam)).re := by
  have hlam0 : 0 < lam := by linarith
  rw [zeroSide_split c D lam hlam0, Complex.add_re, re_window_eq_windowSum hwin]
  have htail := tail_bound_window (c := c) hD hlam
  have htailre : -(tailEnvelope c D lam) ≤ (∑' ρ : ↥(winSet c D)ᶜ, term c lam ρ).re := by
    have h := abs_le.mp (Complex.abs_re_le_norm (∑' ρ : ↥(winSet c D)ᶜ, term c lam ρ))
    unfold tailEnvelope
    linarith [h.1]
  linarith

/-- The dominance form is exact on the window: under WindowOnLine, F(c, lam) is the window sum
plus a tail of modulus at most tailEnvelope (so F >= windowSum - tailEnvelope, and the certificate
margin windowSum - tailEnvelope is a lower bound for F itself). -/
theorem re_zeroSide_ge_windowSum_sub {c D lam : ℝ} (hD : 0 ≤ D) (hlam : 1 ≤ lam)
    (hwin : WindowOnLine c D) :
    windowSum c D lam - tailEnvelope c D lam ≤ (zeroSide (gaussTest c lam)).re := by
  have hlam0 : 0 < lam := by linarith
  rw [zeroSide_split c D lam hlam0, Complex.add_re, re_window_eq_windowSum hwin]
  have htail := tail_bound_window (c := c) hD hlam
  have h := abs_le.mp (Complex.abs_re_le_norm (∑' ρ : ↥(winSet c D)ᶜ, term c lam ρ))
  unfold tailEnvelope
  linarith [h.1]

/-- The single-near-zero form (section F) is the special case of the dominance form in which the
window sum is bounded below by one term: near_term_ge + the term is a summand of windowSum. -/
lemma near_term_le_windowSum {c D lam : ℝ} {ρ₁ : ℂ} (h₁nt : IsNontrivialZero ρ₁)
    (h₁win : |ρ₁.im - c| ≤ D) :
    (WeilExplicit.zeroMult ρ₁ : ℝ) * ((ρ₁.im - c) ^ 2 * Real.exp (-(2 * lam) * (ρ₁.im - c) ^ 2))
      ≤ windowSum c D lam :=
  Finset.single_le_sum (f := fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℝ)
      * ((ρ.im - c) ^ 2 * Real.exp (-(2 * lam) * (ρ.im - c) ^ 2)))
    (fun ρ _ => by positivity) (mem_zeroWindow.mpr ⟨h₁nt, h₁win⟩)

end RvMBridge12
