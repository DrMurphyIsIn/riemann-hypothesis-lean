/-
  E6Bridge34 -- the prime-free window at L <= 1/10 (2026-09-23): assembly of the u-space route.

  For the goal node's test class (IsWeilTest g, tsupport g ⊆ Icc (-L) L) with 0 <= L <= 1/10:

      0 <= Re weilForm (autocorr g)                      (weil_positivity_window_tenth)

  UNCONDITIONALLY, from
    * Stage 0 (E6Bridge31): weilForm = archSide on the window;
    * the pole terms (section A): Re (W0 + W1) = (|ĝ(-i/2) + ĝ(i/2)|^2 - |ĝ(-i/2) - ĝ(i/2)|^2)/2
      >= 2 |∫ g|^2 - (2 D^2 + S^2/2) ||g||_1^2, D = e^{L/4} - e^{-L/4}, S = e^{L/2} - e^{-L/2}
      (ĝ(-i/2) + ĝ(i/2) - 2 ∫ g = ∫ g (e^{u/2} + e^{-u/2} - 2) is O(L^2) ||g||_1);
    * the series bound (E6Bridge32) with each kernel's Dirichlet bound (E6Bridge33), summed by
      induction on the truncation N (section B):
        (1/2pi) ∫ |ĝ|^2 psiR >= c_N f(0) + F_N(L) f(0) + k_N(2L) (2 L f(0) - |∫ g|^2),
        c_N = -gamma + sum_{n<N} (1/(n+1) - 2/b_n) - 4,  F_N(L) = 2 sum_b e^{-bL}/b,
        k_N(L) = sum_b e^{-bL},  b over {1/2} ∪ {b_n = 2n + 5/2 : n < N};
    * the numerics at N = 10 (section C): k_10(1/5) >= 2 (so k_10(2L)(2 L f(0) - |∫ g|^2)
      >= 4 L f(0) - 2 |∫ g|^2, and the |∫ g|^2 terms cancel against the pole terms),
      F_10(L) >= F_10(1/10) + 2 k_10(1/10)(1/10 - L) with k_10(1/10) >= 2 (tangent bound of e^{-bL}),
      F_10(1/10) >= 5.1499 ((1 - x/16)^16 <= e^{-x}), c_10 >= -4.2549, log pi <= 1.159,
      total margin >= 0.134 f(0).

  The true threshold of the statement is L ~ 0.36 (numerics in prime_free_window_numerics.py);
  the bound's own threshold is ~ 0.12.

  BEGIN REGISTRY STATEMENT
  theorem weil_positivity_window_tenth (g : ℝ → ℂ) (hg : WeilExplicit.IsWeilTest g) (L : ℝ)
      (hL : L ≤ 1 / 10) (hsupp : tsupport g ⊆ Set.Icc (-L) L) :
      0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re
  END REGISTRY STATEMENT

  No zeros, no RH progress.  conjecture1_proved = False.
-/
import E6Bridge33

open Zeta23 Complex MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace RvMBridge34
open WeilExplicit RvMBridge11 RvMBridge30 RvMBridge31 RvMBridge32 RvMBridge33

/-! ## A. The pole terms, refined. -/

lemma integrable_mul_cont {g : ℝ → ℂ} (hg : IsWeilTest g) {φ : ℝ → ℂ} (hφ : Continuous φ) :
    Integrable (fun u : ℝ => g u * φ u) := by
  have hcs : HasCompactSupport (fun u : ℝ => g u * φ u) :=
    hg.2.mono' ((Function.support_mul_subset_left _ _).trans (subset_tsupport g))
  exact (hg.1.continuous.mul hφ).integrable_of_hasCompactSupport hcs

/-- ĝ(-i/2) + ĝ(i/2) = ∫ g(u) (e^{u/2} + e^{-u/2}) du. -/
lemma paperFT_add_eq {g : ℝ → ℂ} (hg : IsWeilTest g) :
    paperFT g (-I / 2) + paperFT g (I / 2)
      = ∫ u : ℝ, g u * ((Real.exp (u / 2) + Real.exp (-(u / 2)) : ℝ) : ℂ) := by
  unfold paperFT
  rw [← integral_add (integrable_mul_cexp hg _) (integrable_mul_cexp hg _)]
  congr 1
  funext u
  have e1 : I * (-I / 2) = (1 / 2 : ℂ) := by
    rw [show I * (-I / 2) = -(I * I) / 2 by ring, Complex.I_mul_I]
    norm_num
  have e2 : I * (I / 2) = (-(1 / 2) : ℂ) := by
    rw [show I * (I / 2) = (I * I) / 2 by ring, Complex.I_mul_I]
    norm_num
  rw [e1, e2, show (1 / 2 : ℂ) * (u : ℂ) = ((u / 2 : ℝ) : ℂ) by push_cast; ring,
    show (-(1 / 2) : ℂ) * (u : ℂ) = ((-(u / 2) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp, ← Complex.ofReal_exp]
  push_cast
  ring

/-- (ĝ(-i/2) + ĝ(i/2)) - 2 ∫ g = ∫ g (e^{u/2} + e^{-u/2} - 2). -/
lemma paperFT_add_sub_eq {g : ℝ → ℂ} (hg : IsWeilTest g) :
    paperFT g (-I / 2) + paperFT g (I / 2) - 2 * ∫ u : ℝ, g u
      = ∫ u : ℝ, g u * ((Real.exp (u / 2) + Real.exp (-(u / 2)) - 2 : ℝ) : ℂ) := by
  rw [paperFT_add_eq hg, ← integral_const_mul,
    ← integral_sub (integrable_mul_cont hg (by fun_prop)) ((integrable_g hg).const_mul 2)]
  congr 1
  funext u
  push_cast
  ring

/-- On [-L, L], |e^{u/2} + e^{-u/2} - 2| <= (e^{L/4} - e^{-L/4})^2. -/
lemma abs_exp_add_sub_two_le {L : ℝ} (u : ℝ) (hu : u ∈ Set.Icc (-L) L) :
    |Real.exp (u / 2) + Real.exp (-(u / 2)) - 2| ≤ (Real.exp (L / 4) - Real.exp (-(L / 4))) ^ 2 := by
  have h1 : Real.exp (u / 4) * Real.exp (u / 4) = Real.exp (u / 2) := by
    rw [← Real.exp_add]
    ring_nf
  have h2 : Real.exp (-(u / 4)) * Real.exp (-(u / 4)) = Real.exp (-(u / 2)) := by
    rw [← Real.exp_add]
    ring_nf
  have h3 : Real.exp (u / 4) * Real.exp (-(u / 4)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hid : Real.exp (u / 2) + Real.exp (-(u / 2)) - 2
      = (Real.exp (u / 4) - Real.exp (-(u / 4))) ^ 2 := by
    nlinarith [h1, h2, h3]
  have hb := abs_exp_sub_le (L := L / 2) (u / 2)
    (by rw [Set.mem_Icc]; constructor <;> linarith [hu.1, hu.2])
  rw [show u / 2 / 2 = u / 4 by ring, show L / 2 / 2 = L / 4 by ring] at hb
  rw [hid, abs_of_nonneg (sq_nonneg _)]
  have h0 := abs_nonneg (Real.exp (u / 4) - Real.exp (-(u / 4)))
  calc (Real.exp (u / 4) - Real.exp (-(u / 4))) ^ 2
      = |Real.exp (u / 4) - Real.exp (-(u / 4))| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.exp (L / 4) - Real.exp (-(L / 4))) ^ 2 := pow_le_pow_left₀ h0 hb 2

/-- |(ĝ(-i/2) + ĝ(i/2)) - 2 ∫ g| <= D^2 A. -/
lemma norm_paperFT_add_sub_le {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) :
    ‖paperFT g (-I / 2) + paperFT g (I / 2) - 2 * ∫ u : ℝ, g u‖
      ≤ (Real.exp (L / 4) - Real.exp (-(L / 4))) ^ 2 * l1 g := by
  rw [paperFT_add_sub_eq hg]
  unfold l1
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le ((integrable_norm hg).const_mul _)
  filter_upwards with u
  rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]
  by_cases hu : u ∈ Set.Icc (-L) L
  · rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_exp_add_sub_two_le u hu) (norm_nonneg _)
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hu (hsupp h))]
    simp

lemma norm_integral_g_le_l1 (g : ℝ → ℂ) : ‖∫ u : ℝ, g u‖ ≤ l1 g :=
  norm_integral_le_integral_norm _

/-- THE REFINED POLE BOUND: Re (W0 + W1) >= 2 |∫ g|^2 - (2 D^2 + S^2/2) A^2. -/
theorem re_poles_ge_sq {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) :
    2 * ‖∫ u : ℝ, g u‖ ^ 2
      - (2 * (Real.exp (L / 4) - Real.exp (-(L / 4))) ^ 2
          + (Real.exp (L / 2) - Real.exp (-(L / 2))) ^ 2 / 2) * l1 g ^ 2
      ≤ (weilKernel (autocorr g) 0 + weilKernel (autocorr g) 1).re := by
  rw [weilKernel_autocorr_zero_eq hg, weilKernel_autocorr_one_eq hg]
  have hx := norm_sub_norm_le (2 * ∫ u : ℝ, g u) (paperFT g (-I / 2) + paperFT g (I / 2))
  rw [norm_sub_rev, Complex.norm_mul, Complex.norm_two] at hx
  have hy := norm_paperFT_add_sub_le hg hsupp
  have hdiff := norm_paperFT_sub_le hg hsupp
  have hGA := norm_integral_g_le_l1 g
  set a := paperFT g (-I / 2) with ha
  set b := paperFT g (I / 2) with hb
  set D := Real.exp (L / 4) - Real.exp (-(L / 4)) with hD
  set S := Real.exp (L / 2) - Real.exp (-(L / 2)) with hS
  set A := l1 g with hA
  set G := ‖∫ u : ℝ, g u‖ with hG
  have h1 : (b * (starRingEnd ℂ) a + a * (starRingEnd ℂ) b).re = 2 * (a * (starRingEnd ℂ) b).re := by
    have : b * (starRingEnd ℂ) a = (starRingEnd ℂ) (a * (starRingEnd ℂ) b) := by
      rw [map_mul, Complex.conj_conj, mul_comm]
    rw [this, Complex.add_re, Complex.conj_re]
    ring
  rw [h1]
  have h2 := Complex.normSq_add a b
  have h3 := Complex.normSq_sub a b
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h2 h3
  have hA0 : 0 ≤ A := l1_nonneg g
  have hG0 : 0 ≤ G := norm_nonneg _
  have hD0 : 0 ≤ D ^ 2 := sq_nonneg _
  have hdiff2 : ‖a - b‖ ^ 2 ≤ S ^ 2 * A ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hdiff 2
  have hsum : 2 * G - D ^ 2 * A ≤ ‖a + b‖ := by linarith
  have hsum2 : 4 * G ^ 2 - 4 * D ^ 2 * A ^ 2 ≤ ‖a + b‖ ^ 2 := by
    have hn0 := norm_nonneg (a + b)
    rcases le_or_gt (D ^ 2 * A) (2 * G) with hc | hc
    · have := pow_le_pow_left₀ (by linarith) hsum 2
      nlinarith [mul_nonneg hD0 hA0, mul_le_mul_of_nonneg_left hGA (mul_nonneg hD0 hA0)]
    · have hsq := sq_nonneg ‖a + b‖
      nlinarith [mul_le_mul_of_nonneg_left hGA (by linarith : 0 ≤ 4 * G),
        mul_le_mul_of_nonneg_left hc.le (by linarith : 0 ≤ 2 * A), mul_nonneg hD0 hA0]
  nlinarith

/-- D = e^{L/4} - e^{-L/4} <= 79/1560 for 0 <= L <= 1/10. -/
lemma exp_quarter_sub_le {L : ℝ} (_hL0 : 0 ≤ L) (hL : L ≤ 1 / 10) :
    Real.exp (L / 4) - Real.exp (-(L / 4)) ≤ 79 / 1560 := by
  have hpos := Real.exp_pos (L / 4)
  have h := Real.add_one_le_exp (-(L / 4))
  have h2 : 39 / 40 ≤ Real.exp (-(L / 4)) := by linarith
  rw [Real.exp_neg] at h
  have h3 : Real.exp (L / 4) * (1 - L / 4) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left h hpos.le
    rwa [mul_inv_cancel₀ hpos.ne', show -(L / 4) + 1 = 1 - L / 4 by ring] at this
  have h4 : Real.exp (L / 4) * (39 / 40) ≤ Real.exp (L / 4) * (1 - L / 4) :=
    mul_le_mul_of_nonneg_left (by linarith) hpos.le
  linarith

/-- S = e^{L/2} - e^{-L/2} <= 39/380 for 0 <= L <= 1/10. -/
lemma exp_half_sub_le' {L : ℝ} (_hL0 : 0 ≤ L) (hL : L ≤ 1 / 10) :
    Real.exp (L / 2) - Real.exp (-(L / 2)) ≤ 39 / 380 := by
  have hpos := Real.exp_pos (L / 2)
  have h := Real.add_one_le_exp (-(L / 2))
  have h2 : 19 / 20 ≤ Real.exp (-(L / 2)) := by linarith
  rw [Real.exp_neg] at h
  have h3 : Real.exp (L / 2) * (1 - L / 2) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left h hpos.le
    rwa [mul_inv_cancel₀ hpos.ne', show -(L / 2) + 1 = 1 - L / 2 by ring] at this
  have h4 : Real.exp (L / 2) * (19 / 20) ≤ Real.exp (L / 2) * (1 - L / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hpos.le
  linarith

/-- The pole terms at L <= 1/10: Re (W0 + W1) >= 2 |∫ g|^2 - (11/500) L M. -/
theorem re_poles_ge_tenth {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : L ≤ 1 / 10) (hsupp : tsupport g ⊆ Set.Icc (-L) L) :
    2 * ‖∫ u : ℝ, g u‖ ^ 2 - (11 / 500) * L * mass g
      ≤ (weilKernel (autocorr g) 0 + weilKernel (autocorr g) 1).re := by
  refine le_trans ?_ (re_poles_ge_sq hg hsupp)
  have hD := exp_quarter_sub_le hL0 hL
  have hS := exp_half_sub_le' hL0 hL
  have hD0 : 0 ≤ Real.exp (L / 4) - Real.exp (-(L / 4)) := by
    have := Real.exp_le_exp.mpr (show -(L / 4) ≤ L / 4 by linarith)
    linarith
  have hS0 : 0 ≤ Real.exp (L / 2) - Real.exp (-(L / 2)) := by
    have := Real.exp_le_exp.mpr (show -(L / 2) ≤ L / 2 by linarith)
    linarith
  have hD2 : (Real.exp (L / 4) - Real.exp (-(L / 4))) ^ 2 ≤ (79 / 1560) ^ 2 :=
    pow_le_pow_left₀ hD0 hD 2
  have hS2 : (Real.exp (L / 2) - Real.exp (-(L / 2))) ^ 2 ≤ (39 / 380) ^ 2 :=
    pow_le_pow_left₀ hS0 hS 2
  have hA2 := sq_l1_le hg hL0 hsupp
  have hA0 := sq_nonneg (l1 g)
  have hcoef : 2 * (Real.exp (L / 4) - Real.exp (-(L / 4))) ^ 2
      + (Real.exp (L / 2) - Real.exp (-(L / 2))) ^ 2 / 2 ≤ 11 / 1000 := by
    norm_num at hD2 hS2 ⊢
    linarith
  have hM := mass_nonneg g
  nlinarith [mul_le_mul_of_nonneg_right hcoef hA0, mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 11 / 1000) hL0) hM]

/-! ## B. The kernel sums and the archimedean bound at every truncation. -/

/-- c_N = -gamma + sum_{n<N} (1/(n+1) - 2/b_n) - 4. -/
def cN (N : ℕ) : ℝ :=
  -Real.eulerMascheroniConstant + ∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1) - 2 / bN n) - 4

/-- F_N(L) = 2 sum_b e^{-bL}/b over b ∈ {1/2} ∪ {b_n : n < N}. -/
def FN (N : ℕ) (L : ℝ) : ℝ :=
  2 * (Real.exp (-(1 / 2) * L) / (1 / 2))
    + ∑ n ∈ Finset.range N, 2 * (Real.exp (-bN n * L) / bN n)

/-- k_N(L) = sum_b e^{-bL}. -/
def kN (N : ℕ) (L : ℝ) : ℝ :=
  Real.exp (-(1 / 2) * L) + ∑ n ∈ Finset.range N, Real.exp (-bN n * L)

/-- The right-hand side of E6Bridge32 re_arch_integral_ge, with Re ∫ f K_b = M (2/b) - E_b. -/
def rhsN (g : ℝ → ℂ) (N : ℕ) : ℝ :=
  (-Real.eulerMascheroniConstant + ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1)) * mass g
    - (mass g * (2 / (1 / 2)) - Eb g (1 / 2))
    - ∑ n ∈ Finset.range N, (mass g * (2 / bN n) - Eb g (bN n))

lemma rhsN_eq {g : ℝ → ℂ} (N : ℕ) :
    rhsN g N = (-Real.eulerMascheroniConstant + ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1)) * mass g
      - (∫ u : ℝ, autocorr g u * (expK (1 / 2) u : ℂ)).re
      - ∑ n ∈ Finset.range N, (∫ u : ℝ, autocorr g u * (expK (bN n) u : ℂ)).re := by
  unfold rhsN Eb
  have : ∀ n ∈ Finset.range N, mass g * (2 / bN n)
      - (mass g * (2 / bN n) - (∫ u : ℝ, autocorr g u * (expK (bN n) u : ℂ)).re)
      = (∫ u : ℝ, autocorr g u * (expK (bN n) u : ℂ)).re := fun n _ => by ring
  rw [Finset.sum_congr rfl this]
  ring

/-- The induction: c_N M + F_N(L) M + k_N(2L) X <= rhsN, X = 2 L M - |∫ g|^2. -/
theorem lhs_le_rhsN {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ} (hL : 0 ≤ L)
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) (N : ℕ) :
    cN N * mass g + FN N L * mass g + kN N (2 * L) * (2 * L * mass g - ‖∫ u : ℝ, g u‖ ^ 2)
      ≤ rhsN g N := by
  induction N with
  | zero =>
    simp only [cN, FN, kN, rhsN, Finset.sum_range_zero]
    have h := Eb_ge hg hL hsupp (b := 1 / 2) (by norm_num)
    rw [show -2 * (1 / 2 : ℝ) * L = -(1 / 2) * (2 * L) by ring] at h
    have e : 2 * Real.exp (-(1 / 2) * L) / (1 / 2) = 2 * (Real.exp (-(1 / 2) * L) / (1 / 2)) := by
      ring
    rw [e] at h
    linarith
  | succ N ih =>
    simp only [cN, FN, kN, rhsN, Finset.sum_range_succ] at ih ⊢
    have h := Eb_ge hg hL hsupp (bN_pos N)
    rw [show -2 * bN N * L = -bN N * (2 * L) by ring] at h
    have e : 2 * Real.exp (-bN N * L) / bN N = 2 * (Real.exp (-bN N * L) / bN N) := by ring
    rw [e] at h
    nlinarith [ih, h]

/-- THE ARCHIMEDEAN BOUND at every truncation N. -/
theorem arch_ge_series {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ} (hL : 0 ≤ L)
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) (N : ℕ) :
    cN N * mass g + FN N L * mass g + kN N (2 * L) * (2 * L * mass g - ‖∫ u : ℝ, g u‖ ^ 2)
      ≤ (1 / (2 * Real.pi)) * ∫ r : ℝ, hsq g r * psiR r := by
  refine (lhs_le_rhsN hg hL hsupp N).trans ?_
  rw [rhsN_eq]
  exact re_arch_integral_ge hg N

/-! ## C. The numerics at N = 10. -/

/-- (1 - t/16)^16 <= e^{-t} for t <= 16. -/
lemma exp_neg_ge (t : ℝ) (ht : t ≤ 16) : (1 - t / 16) ^ 16 ≤ Real.exp (-t) := by
  have := Real.one_sub_div_pow_le_exp_neg (n := 16) (t := t) (by exact_mod_cast ht)
  simpa using this

lemma exp_neg_bN_ge (n : ℕ) (hn : n < 10) (L : ℝ) (_hL0 : 0 ≤ L) (hL : L ≤ 1 / 5) :
    (1 - bN n * L / 16) ^ 16 ≤ Real.exp (-bN n * L) := by
  have h := exp_neg_ge (bN n * L) (by
    unfold bN
    have : (n : ℝ) ≤ 9 := by exact_mod_cast (by omega : n ≤ 9)
    nlinarith)
  rw [neg_mul]
  exact h

/-- Termwise monotonicity of k_N in L. -/
lemma kN_mono (N : ℕ) {L₁ L₂ : ℝ} (h : L₁ ≤ L₂) : kN N L₂ ≤ kN N L₁ := by
  unfold kN
  refine add_le_add (Real.exp_le_exp.mpr (by linarith)) (Finset.sum_le_sum fun n _ => ?_)
  exact Real.exp_le_exp.mpr (by have := bN_pos n; nlinarith)

/-- k_10(1/5) >= 2. -/
lemma kN_fifth_ge : 2 ≤ kN 10 (1 / 5) := by
  unfold kN
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have h0 := exp_neg_ge (1 / 10) (by norm_num)
  have h := fun n hn => exp_neg_bN_ge n hn (1 / 5) (by norm_num) le_rfl
  have h1 := h 0 (by norm_num)
  have h2 := h 1 (by norm_num)
  have h3 := h 2 (by norm_num)
  have h4 := h 3 (by norm_num)
  have h5 := h 4 (by norm_num)
  have h6 := h 5 (by norm_num)
  have h7 := h 6 (by norm_num)
  have h8 := h 7 (by norm_num)
  have h9 := h 8 (by norm_num)
  have h10 := h 9 (by norm_num)
  have e0 : Real.exp (-(1 / 2) * (1 / 5)) = Real.exp (-(1 / 10)) := by norm_num
  rw [e0]
  unfold bN at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ⊢
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ⊢
  linarith

/-- k_10(1/10) >= 2. -/
lemma kN_tenth_ge : 2 ≤ kN 10 (1 / 10) := by
  unfold kN
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have h0 := exp_neg_ge (1 / 20) (by norm_num)
  have h := fun n hn => exp_neg_bN_ge n hn (1 / 10) (by norm_num) (by norm_num)
  have h1 := h 0 (by norm_num)
  have h2 := h 1 (by norm_num)
  have h3 := h 2 (by norm_num)
  have h4 := h 3 (by norm_num)
  have h5 := h 4 (by norm_num)
  have h6 := h 5 (by norm_num)
  have h7 := h 6 (by norm_num)
  have h8 := h 7 (by norm_num)
  have h9 := h 8 (by norm_num)
  have h10 := h 9 (by norm_num)
  have e0 : Real.exp (-(1 / 2) * (1 / 10)) = Real.exp (-(1 / 20)) := by norm_num
  rw [e0]
  unfold bN at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ⊢
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ⊢
  linarith

/-- F_10(1/10) >= 5.1499. -/
lemma FN_tenth_ge : 51499 / 10000 ≤ FN 10 (1 / 10) := by
  unfold FN
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have h0 := exp_neg_ge (1 / 20) (by norm_num)
  have h := fun n hn => exp_neg_bN_ge n hn (1 / 10) (by norm_num) (by norm_num)
  have h1 := h 0 (by norm_num)
  have h2 := h 1 (by norm_num)
  have h3 := h 2 (by norm_num)
  have h4 := h 3 (by norm_num)
  have h5 := h 4 (by norm_num)
  have h6 := h 5 (by norm_num)
  have h7 := h 6 (by norm_num)
  have h8 := h 7 (by norm_num)
  have h9 := h 8 (by norm_num)
  have h10 := h 9 (by norm_num)
  have e0 : Real.exp (-(1 / 2) * (1 / 10)) = Real.exp (-(1 / 20)) := by norm_num
  rw [e0]
  unfold bN at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ⊢
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ⊢
  linarith

/-- c_10 >= -4.2549. -/
lemma cN_ge : -42549 / 10000 ≤ cN 10 := by
  unfold cN
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  unfold bN
  have := eulerMascheroni_le
  norm_num at this ⊢
  linarith

/-- The tangent bound: F_10(L) >= F_10(1/10) + 2 k_10(1/10) (1/10 - L) (for every L; it is
used for L <= 1/10). -/
lemma FN_ge_tangent (L : ℝ) :
    FN 10 (1 / 10) + 2 * kN 10 (1 / 10) * (1 / 10 - L) ≤ FN 10 L := by
  have key : ∀ b : ℝ, 0 < b →
      2 * (Real.exp (-b * (1 / 10)) / b) + 2 * Real.exp (-b * (1 / 10)) * (1 / 10 - L)
        ≤ 2 * (Real.exp (-b * L) / b) := by
    intro b hb
    have h1 : Real.exp (-b * L) = Real.exp (-b * (1 / 10)) * Real.exp (b * (1 / 10 - L)) := by
      rw [← Real.exp_add]
      ring_nf
    have h2 : b * (1 / 10 - L) + 1 ≤ Real.exp (b * (1 / 10 - L)) := Real.add_one_le_exp _
    have h3 : 0 < Real.exp (-b * (1 / 10)) := Real.exp_pos _
    rw [h1]
    have e : 2 * (Real.exp (-b * (1 / 10)) / b) + 2 * Real.exp (-b * (1 / 10)) * (1 / 10 - L)
        = 2 * (Real.exp (-b * (1 / 10)) * (b * (1 / 10 - L) + 1) / b) := by
      field_simp
      ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply div_le_div_of_nonneg_right _ hb.le
    exact mul_le_mul_of_nonneg_left h2 h3.le
  have hsum : ∑ n ∈ Finset.range 10, (2 * (Real.exp (-bN n * (1 / 10)) / bN n)
        + 2 * Real.exp (-bN n * (1 / 10)) * (1 / 10 - L))
      ≤ ∑ n ∈ Finset.range 10, 2 * (Real.exp (-bN n * L) / bN n) :=
    Finset.sum_le_sum fun n _ => key (bN n) (bN_pos n)
  have h0 := key (1 / 2) (by norm_num)
  rw [Finset.sum_add_distrib] at hsum
  have e : ∑ n ∈ Finset.range 10, 2 * Real.exp (-bN n * (1 / 10)) * (1 / 10 - L)
      = 2 * (1 / 10 - L) * ∑ n ∈ Finset.range 10, Real.exp (-bN n * (1 / 10)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [e] at hsum
  unfold FN kN
  nlinarith [hsum, h0]

/-! ## D. The theorem at L <= 1/10. -/

/-- Re archSide (autocorr g) >= M [c_10 - log pi + F_10(1/10) + 2/5 - (11/500) L] for
0 <= L <= 1/10. -/
theorem re_archSide_autocorr_ge_tenth {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : L ≤ 1 / 10) (hsupp : tsupport g ⊆ Set.Icc (-L) L) :
    mass g * (cN 10 - Real.log Real.pi + FN 10 (1 / 10) + 2 / 5 - (11 / 500) * L)
      ≤ (archSide (autocorr g)).re := by
  unfold archSide
  rw [integral_archIntegrand_autocorr_eq hg, autocorr_zero]
  set W0 := weilKernel (autocorr g) 0 with hW0
  set W1 := weilKernel (autocorr g) 1 with hW1
  set J := ∫ r : ℝ, hsq g r * psiR r with hJ
  set M := mass g with hM
  set G2 := ‖∫ u : ℝ, g u‖ ^ 2 with hG2
  have hpoles := re_poles_ge_tenth hg hL0 hL hsupp
  rw [← hW0, ← hW1, ← hM, ← hG2] at hpoles
  have harch := arch_ge_series hg hL0 hsupp 10
  rw [← hJ, ← hM, ← hG2] at harch
  have hre : (W0 + W1 - (M : ℂ) * (Real.log Real.pi : ℂ)
      + (1 / (2 * (Real.pi : ℂ))) * (J : ℂ)).re
      = (W0 + W1).re - M * Real.log Real.pi + (1 / (2 * Real.pi)) * J := by
    rw [show (M : ℂ) * (Real.log Real.pi : ℂ) = ((M * Real.log Real.pi : ℝ) : ℂ) by
        push_cast; ring,
      show (1 / (2 * (Real.pi : ℂ))) * (J : ℂ) = (((1 / (2 * Real.pi)) * J : ℝ) : ℂ) by
        push_cast; ring]
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re]
  rw [hre]
  -- X = 2 L M - G2 >= 0 and k_10(2L) >= 2
  have hX : 0 ≤ 2 * L * M - G2 := by
    have h1 := norm_integral_g_le_l1 g
    have h2 := sq_l1_le hg hL0 hsupp
    have h0 := norm_nonneg (∫ u : ℝ, g u)
    rw [hG2, hM]
    nlinarith [pow_le_pow_left₀ h0 h1 2]
  have hk : 2 ≤ kN 10 (2 * L) := kN_fifth_ge.trans (kN_mono 10 (by linarith))
  have hkX : 2 * (2 * L * M - G2) ≤ kN 10 (2 * L) * (2 * L * M - G2) :=
    mul_le_mul_of_nonneg_right hk hX
  have hF := FN_ge_tangent L
  have hk2 := kN_tenth_ge
  have hFL : FN 10 (1 / 10) + 4 * (1 / 10 - L) ≤ FN 10 L := by
    have : 4 * (1 / 10 - L) ≤ 2 * kN 10 (1 / 10) * (1 / 10 - L) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  have hM0 := mass_nonneg g
  rw [← hM] at hM0
  nlinarith [mul_le_mul_of_nonneg_right hFL hM0]

/-- THE WINDOW AT L <= 1/10 (with 0 <= L). -/
theorem weil_positivity_window_tenth_of_nonneg {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hL0 : 0 ≤ L) (hL : L ≤ 1 / 10) (hsupp : tsupport g ⊆ Set.Icc (-L) L) :
    0 ≤ (weilForm (autocorr g)).re := by
  have hwin : 2 * L ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [weilForm_autocorr_eq_archSide hg hsupp hwin]
  refine le_trans ?_ (re_archSide_autocorr_ge_tenth hg hL0 hL hsupp)
  apply mul_nonneg (mass_nonneg g)
  have h1 := cN_ge
  have h2 := FN_tenth_ge
  have h3 := log_pi_le
  nlinarith

/-- THE WINDOW AT L <= 1/10 (registry shape, no sign condition on L). -/
theorem weil_positivity_window_tenth (g : ℝ → ℂ) (hg : IsWeilTest g) (L : ℝ)
    (hL : L ≤ 1 / 10) (hsupp : tsupport g ⊆ Set.Icc (-L) L) :
    0 ≤ (weilForm (autocorr g)).re := by
  have hsupp' : tsupport g ⊆ Set.Icc (-(max L 0)) (max L 0) :=
    hsupp.trans (Set.Icc_subset_Icc (by linarith [le_max_left L 0]) (le_max_left L 0))
  exact weil_positivity_window_tenth_of_nonneg hg (le_max_right L 0)
    (max_le hL (by norm_num)) hsupp'

end RvMBridge34
