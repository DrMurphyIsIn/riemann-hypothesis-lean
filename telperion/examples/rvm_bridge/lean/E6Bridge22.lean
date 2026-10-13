/-
  E6Bridge22 -- the GROWTH BOUND of the entire extension (obligation 1, parts B + C), 2026-09-21.

  TARGET.  RvMBridge20.XiDiffExtGrowthRight :
      ∃ C, ∀ s, 1/2 ≤ Re s → ‖xiDiffExt s‖ ≤ C (1 + log (2 + ‖s‖)),
  xiDiffExt the entire extension (E6Bridge20) of
      xiDiffReg s = deriv (logDeriv xi) s + Sum'_rho m(rho)/(s - rho)^2.

  THE THREE REGIONS and what is proved.
    (A) 1/2 ≤ Re s ≤ 2, |Im s| ≤ 6: compact, xiDiffExt continuous, bounded.         PROVED.
    (B) 1/2 ≤ Re s ≤ 2, |Im s| ≥ 6: xiDiffExt s = [deriv (logDeriv xi) s + Sum_{window} m/(s-rho)^2]
        + Sum_{far} m/(s-rho)^2 off the zeros, window = zeros with |Im rho - Im s| ≤ 2.  The far
        sum is ≤ 2 Sum m/(1 + (Im rho - Im s)^2) (PROVED); the bracket is the Landau-Cauchy disc
        bound (OBLIGATION StripDerivBound); the passage from non-zeros to the whole closed region
        is by continuity of xiDiffExt (PROVED, bound_of_bound_off_zeros).
    (C) Re s ≥ 2: no zeros, xiDiffExt = deriv (logDeriv xi) + Sum; the sum is ≤ Sum m/(1 + (Im rho
        - Im s)^2) since |s - rho|^2 ≥ 1 + (Im s - Im rho)^2 (PROVED); deriv (logDeriv xi) is bounded
        (RightDerivBound, PROVED in section G from E6Bridge21's pieces: the termwise formula
        -1/s^2 - 1/(s-1)^2 + (1/4) psi'(s/2) + (zeta'/zeta)'(s) on Re s > 1, the trigamma series
        bound ‖psi'(z)‖ ≤ Sum 1/(n+1/2)^2 for Re z ≥ 1, and ‖L(log * Lambda)(s)‖ ≤ Sum_n ‖term n at 2‖).
  Both sums are controlled by ONE classical inequality about the local zero count,
      LocalCountSum : ∃ C, ∀ a : ℝ, Sum'_rho m(rho)/(1 + (Im rho - a)^2) ≤ C (1 + log (2 + |a|))
  (OBLIGATION; on Re s ≥ 2 the sum is NOT O(1): near the ordinate of a zero it is of size 1, and
  there are O(log t) zeros per unit height, so O(log|Im s|) is the truth).  Its summability for
  every a is PROVED (summable_lcTerm).

  ASSEMBLY (PROVED): xiDiffExtGrowthRight_of (h1 : LocalCountSum) (h2 : StripDerivBound)
  (h3 : RightDerivBound) : XiDiffExtGrowthRight, and with RightDerivBound discharged,
  xiDiffExtGrowthRight_of_two h1 h2; hence with E6Bridge20/18/21 the derivative partial fraction
  xiLogDerivDerivEq_of_two h1 h2 : RvMBridge18.XiLogDerivDerivEq.  TWO obligations remain:
  LocalCountSum and StripDerivBound.

  2026-09-22: the complex-argument forms norm_term_le_of_two_le_re and deriv_logDeriv_xi_of_one_lt_re
  this module had re-proved now live in E6Bridge21 (RvMBridge21.*), whose real-axis forms are their
  corollaries; the compact bound uses the prelude's RvMBridgeXi.exists_bound_on_reProdIm.  Every
  node theorem here is unchanged, statement verbatim.

  conjecture1_proved = False.  Nothing here bears on RH.
-/
import E6Bridge20
import E6Bridge21
import RvMBridgeXi

open Zeta23 Complex MeasureTheory Filter Topology Metric
open scoped ComplexConjugate

noncomputable section

namespace RvMBridge22
open WeilExplicit RvMBridge18 RvMBridge20 RvMBridgeXi

/-! ## A. The local-count sum: summable for every centre; its log bound is the obligation. -/

/-- The local-count term m(rho) / (1 + (Im rho - a)^2). -/
def lcTerm (a : ℝ) (ρ : ℂ) : ℝ := (WeilExplicit.zeroMult ρ : ℝ) / (1 + (ρ.im - a) ^ 2)

lemma lcTerm_nonneg (a : ℝ) (ρ : ℂ) : 0 ≤ lcTerm a ρ := by
  unfold lcTerm; positivity

lemma lcTerm_le_majorant (a : ℝ) (ρ : ℂ) :
    lcTerm a ρ ≤ (WeilExplicit.zeroMult ρ : ℝ) * ((13 / 4 + 2 * a ^ 2) / (1 + Complex.normSq (gammaOf ρ))) := by
  unfold lcTerm
  by_cases h : IsNontrivialZero ρ
  · rw [div_eq_mul_one_div]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hγ := normSq_gammaOf_le ρ h.2.1 h.2.2
    have hγ0 := Complex.normSq_nonneg (gammaOf ρ)
    rw [div_le_div_iff₀ (by positivity) (by linarith)]
    have ht : ρ.im ^ 2 ≤ 2 * (ρ.im - a) ^ 2 + 2 * a ^ 2 := by nlinarith [sq_nonneg (ρ.im - 2 * a)]
    nlinarith [sq_nonneg (ρ.im - a), sq_nonneg a]
  · rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial h]
    simp

theorem summable_lcTerm (a : ℝ) : Summable (lcTerm a) :=
  (RvMBridgeGauss.summable_mult_div_one_add_normSq _).of_nonneg_of_le (lcTerm_nonneg a) (lcTerm_le_majorant a)

/-- **Obligation (local zero count).**  Sum_rho m(rho)/(1 + (Im rho - a)^2) = O(log (2 + |a|)):
O(log(|a| + k)) zeros in each unit window [a + k, a + k + 1) (Zeta23.RvM.zeta_local_zero_count)
against the weights 1/(1 + k^2). -/
def LocalCountSum : Prop :=
  ∃ C : ℝ, ∀ a : ℝ, ∑' ρ : ℂ, lcTerm a ρ ≤ C * (1 + Real.log (2 + |a|))

/-! ## B. The window at height Im s and the two sum comparisons. -/

/-- The nontrivial zeros within ordinate distance 2 of s. -/
def windowSet (s : ℂ) : Set ℂ := {ρ : ℂ | IsNontrivialZero ρ} ∩ {ρ : ℂ | |ρ.im - s.im| ≤ 2}

lemma windowSet_finite (s : ℂ) : (windowSet s).Finite := by
  refine (zetaSeam.finite_window (s.im - 3) (s.im + 2)).subset ?_
  rintro ρ ⟨hnt, hw⟩
  have hw' : |ρ.im - s.im| ≤ 2 := hw
  have h := abs_le.mp hw'
  exact ⟨hnt, by linarith [h.1], by linarith [h.2]⟩

/-- The window as a Finset. -/
def window (s : ℂ) : Finset ℂ := (windowSet_finite s).toFinset

lemma mem_window {s ρ : ℂ} : ρ ∈ window s ↔ IsNontrivialZero ρ ∧ |ρ.im - s.im| ≤ 2 := by
  unfold window
  rw [Set.Finite.mem_toFinset]
  rfl

/-- On Re s ≥ 2 every double-pole term is bounded by the local-count term. -/
lemma norm_polTerm_le_lcTerm_right {s : ℂ} (hs : 2 ≤ s.re) (ρ : ℂ) :
    ‖polTerm s ρ‖ ≤ lcTerm s.im ρ := by
  by_cases h : IsNontrivialZero ρ
  · rw [norm_polTerm]
    unfold lcTerm
    refine div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) ?_
    have hns : ‖s - ρ‖ ^ 2 = (s.re - ρ.re) ^ 2 + (s.im - ρ.im) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
      ring
    rw [hns]
    have hre := h.2.2
    have h1 : 1 ≤ (s.re - ρ.re) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (s.im - ρ.im), sq_nonneg (ρ.im - s.im)]
  · rw [polTerm_eq_zero_of_not_nontrivial h, norm_zero]
    exact lcTerm_nonneg _ _

/-- Off the window every double-pole term is bounded by twice the local-count term. -/
lemma norm_polTerm_le_lcTerm_far {s ρ : ℂ} (hρ : ρ ∉ window s) :
    ‖polTerm s ρ‖ ≤ 2 * lcTerm s.im ρ := by
  by_cases h : IsNontrivialZero ρ
  · have hfar : 2 < |ρ.im - s.im| := by
      by_contra hle
      exact hρ (mem_window.mpr ⟨h, not_lt.mp hle⟩)
    rw [norm_polTerm]
    unfold lcTerm
    have hd : (ρ.im - s.im) ^ 2 ≤ ‖s - ρ‖ ^ 2 := by
      have := Complex.abs_im_le_norm (s - ρ)
      rw [Complex.sub_im] at this
      have h2 : |s.im - ρ.im| ^ 2 = (s.im - ρ.im) ^ 2 := sq_abs _
      nlinarith [abs_nonneg (s.im - ρ.im)]
    have hd4 : 4 < (ρ.im - s.im) ^ 2 := by
      have := sq_abs (ρ.im - s.im)
      nlinarith [abs_nonneg (ρ.im - s.im)]
    have hpos : 0 < ‖s - ρ‖ ^ 2 := by linarith
    have key : 1 / ‖s - ρ‖ ^ 2 ≤ 2 / (1 + (ρ.im - s.im) ^ 2) := by
      rw [div_le_div_iff₀ hpos (by positivity)]
      nlinarith
    calc (WeilExplicit.zeroMult ρ : ℝ) / ‖s - ρ‖ ^ 2
        = (WeilExplicit.zeroMult ρ : ℝ) * (1 / ‖s - ρ‖ ^ 2) := by ring
      _ ≤ (WeilExplicit.zeroMult ρ : ℝ) * (2 / (1 + (ρ.im - s.im) ^ 2)) :=
          mul_le_mul_of_nonneg_left key (Nat.cast_nonneg _)
      _ = 2 * ((WeilExplicit.zeroMult ρ : ℝ) / (1 + (ρ.im - s.im) ^ 2)) := by ring
  · rw [polTerm_eq_zero_of_not_nontrivial h, norm_zero]
    have := lcTerm_nonneg s.im ρ
    linarith

/-- The sum on Re s ≥ 2 is bounded by the local-count sum at height Im s. -/
theorem norm_tsum_polTerm_le_right {s : ℂ} (hs : 2 ≤ s.re) :
    ‖∑' ρ : ℂ, polTerm s ρ‖ ≤ ∑' ρ : ℂ, lcTerm s.im ρ := by
  refine (norm_tsum_le_tsum_norm (summable_polTerm s).norm).trans ?_
  exact (summable_polTerm s).norm.tsum_le_tsum (norm_polTerm_le_lcTerm_right hs) (summable_lcTerm _)

/-- The far part of the sum is bounded by twice the local-count sum. -/
theorem norm_tsum_far_le (s : ℂ) :
    ‖∑' ρ : ↥(((window s : Finset ℂ) : Set ℂ)ᶜ), polTerm s ρ‖ ≤ 2 * ∑' ρ : ℂ, lcTerm s.im ρ := by
  have hsum : Summable (fun ρ : ↥(((window s : Finset ℂ) : Set ℂ)ᶜ) => ‖polTerm s ρ‖) :=
    (summable_polTerm s).norm.subtype _
  refine (norm_tsum_le_tsum_norm hsum).trans ?_
  have h2 : Summable (fun ρ : ↥(((window s : Finset ℂ) : Set ℂ)ᶜ) => 2 * lcTerm s.im ρ) :=
    ((summable_lcTerm s.im).mul_left 2).subtype _
  refine (hsum.tsum_le_tsum (fun ρ => norm_polTerm_le_lcTerm_far ρ.2) h2).trans ?_
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left
    (Summable.tsum_subtype_le (lcTerm s.im) _ (lcTerm_nonneg _) (summable_lcTerm _))
    (by norm_num : (0 : ℝ) ≤ 2)

/-! ## C. The two derivative obligations. -/

/-- **Obligation (strip, Landau-Cauchy).**  On the strip 1/4 ≤ Re s ≤ 9/4, |Im s| ≥ 5, off the
zeros, the derivative of logDeriv xi with the window double poles removed is O(log|Im s|):
Zeta23.WeilEF.zeta_logDeriv_partial_fraction (Landau) for zeta'/zeta on the disc D(s, 1/2), the
Stirling bound for logDeriv Gamma_R, the rational factors, and Cauchy's estimate for the derivative
of the O(log t) remainder.  Stated on a slightly larger closed region than (B) so that (B) is in
its interior and the bound passes to the zeros by continuity. -/
def StripDerivBound : Prop :=
  ∃ C : ℝ, ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 9 / 4 → 5 ≤ |s.im| → ¬ IsNontrivialZero s →
    ‖deriv (logDeriv xi) s + ∑ ρ ∈ window s, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2‖
      ≤ C * (1 + Real.log (2 + |s.im|))

/-- **Obligation (right half-plane).**  deriv (logDeriv xi) is bounded on Re s ≥ 2:
-1/s^2 - 1/(s-1)^2 + (1/4) psi'(s/2) + (zeta'/zeta)'(s), with psi' the trigamma series and
(zeta'/zeta)' = L(log * Lambda) absolutely convergent. -/
def RightDerivBound : Prop :=
  ∃ C : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖deriv (logDeriv xi) s‖ ≤ C

/-! ## D. From non-zeros to all points by continuity. -/

/-- A continuous bound on an open set valid off the zeros is valid everywhere on it. -/
theorem bound_of_bound_off_zeros {U : Set ℂ} (hU : IsOpen U) {B : ℂ → ℝ} (hB : Continuous B)
    (h : ∀ s ∈ U, ¬ IsNontrivialZero s → ‖xiDiffExt s‖ ≤ B s) :
    ∀ s ∈ U, ‖xiDiffExt s‖ ≤ B s := by
  intro s₀ hs₀
  by_cases hz : IsNontrivialZero s₀
  · obtain ⟨r, hr, H, -, hnoz, -, -⟩ := exists_local_form s₀
    have hcont : ContinuousAt (fun w => B w - ‖xiDiffExt w‖) s₀ :=
      (hB.sub xiDiffExt_differentiable.continuous.norm).continuousAt
    have hlim : Tendsto (fun w => B w - ‖xiDiffExt w‖) (𝓝[≠] s₀) (𝓝 (B s₀ - ‖xiDiffExt s₀‖)) :=
      hcont.continuousWithinAt.tendsto
    have hev : ∀ᶠ w in 𝓝[≠] s₀, 0 ≤ B w - ‖xiDiffExt w‖ := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [(hU.inter isOpen_ball).mem_nhds ⟨hs₀, mem_ball_self hr⟩] with w hw hne
      have := h w hw.1 (hnoz w hw.2 hne)
      linarith
    have := ge_of_tendsto hlim hev
    linarith
  · exact h s₀ hs₀ hz

/-! ## E. The three regions. -/

/-- Region (A): the compact rectangle. -/
theorem growth_compact :
    ∃ C : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 → |s.im| ≤ 6 → ‖xiDiffExt s‖ ≤ C := by
  obtain ⟨C, -, hC⟩ :=
    exists_bound_on_reProdIm xiDiffExt_differentiable.continuous (1 / 2) 2 (-6) 6
  exact ⟨C, fun s h1 h2 h3 => hC s h1 h2 (abs_le.mp h3).1 (abs_le.mp h3).2⟩

/-- Region (C): Re s ≥ 2. -/
theorem growth_right (h1 : LocalCountSum) (h3 : RightDerivBound) :
    ∃ C : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖xiDiffExt s‖ ≤ C * (1 + Real.log (2 + |s.im|)) := by
  obtain ⟨C₁, hC₁⟩ := h1
  obtain ⟨C₃, hC₃⟩ := h3
  refine ⟨max C₁ 0 + max C₃ 0, fun s hs => ?_⟩
  have hnz : ¬ IsNontrivialZero s := fun h => absurd h.2.2 (not_lt.mpr (by linarith))
  rw [xiDiffExt_eq hnz]
  unfold xiDiffReg
  have hL : 0 ≤ 1 + Real.log (2 + |s.im|) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + |s.im| by linarith [abs_nonneg s.im])
    linarith
  have hsum : ‖∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2‖
      ≤ max C₁ 0 * (1 + Real.log (2 + |s.im|)) := by
    refine (norm_tsum_polTerm_le_right hs).trans ((hC₁ s.im).trans ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hL
  have hder : ‖deriv (logDeriv xi) s‖ ≤ max C₃ 0 * (1 + Real.log (2 + |s.im|)) := by
    refine (hC₃ s hs).trans ?_
    have : max C₃ 0 ≤ max C₃ 0 * (1 + Real.log (2 + |s.im|)) := by
      have h0 : 0 ≤ max C₃ 0 := le_max_right _ _
      nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 + |s.im| by linarith [abs_nonneg s.im])]
    linarith [le_max_left C₃ 0]
  calc ‖deriv (logDeriv xi) s + ∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2‖
      ≤ ‖deriv (logDeriv xi) s‖ + ‖∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2‖ :=
        norm_add_le _ _
    _ ≤ max C₃ 0 * (1 + Real.log (2 + |s.im|)) + max C₁ 0 * (1 + Real.log (2 + |s.im|)) :=
        add_le_add hder hsum
    _ = (max C₁ 0 + max C₃ 0) * (1 + Real.log (2 + |s.im|)) := by ring

/-- The open region around (B) on which the strip obligation applies. -/
def stripOpen : Set ℂ := {s : ℂ | 1 / 4 < s.re ∧ s.re < 9 / 4 ∧ 5 < |s.im|}

lemma isOpen_stripOpen : IsOpen stripOpen := by
  unfold stripOpen
  refine (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt continuous_const (continuous_abs.comp Complex.continuous_im)))

/-- Region (B): the strip at large height, off the zeros first. -/
theorem growth_strip_off_zeros (h1 : LocalCountSum) (h2 : StripDerivBound) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ stripOpen, ¬ IsNontrivialZero s →
      ‖xiDiffExt s‖ ≤ C * (1 + Real.log (2 + |s.im|)) := by
  obtain ⟨C₁, hC₁⟩ := h1
  obtain ⟨C₂, hC₂⟩ := h2
  refine ⟨max C₂ 0 + 2 * max C₁ 0, by positivity, fun s hs hnz => ?_⟩
  obtain ⟨hre1, hre2, him⟩ := hs
  have hL : 0 ≤ 1 + Real.log (2 + |s.im|) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + |s.im| by linarith [abs_nonneg s.im])
    linarith
  rw [xiDiffExt_eq hnz]
  unfold xiDiffReg
  have hsplit := (summable_polTerm s).sum_add_tsum_compl (s := window s)
  have hsum : (∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2) = ∑' ρ : ℂ, polTerm s ρ := rfl
  rw [hsum, ← hsplit, ← add_assoc]
  have hbr := hC₂ s hre1.le hre2.le him.le hnz
  have hfar := norm_tsum_far_le s
  have hlc := hC₁ s.im
  calc ‖deriv (logDeriv xi) s + ∑ ρ ∈ window s, polTerm s ρ + ∑' ρ : ↥(((window s : Finset ℂ) : Set ℂ)ᶜ), polTerm s ρ‖
      ≤ ‖deriv (logDeriv xi) s + ∑ ρ ∈ window s, polTerm s ρ‖
        + ‖∑' ρ : ↥(((window s : Finset ℂ) : Set ℂ)ᶜ), polTerm s ρ‖ := norm_add_le _ _
    _ ≤ C₂ * (1 + Real.log (2 + |s.im|)) + 2 * (C₁ * (1 + Real.log (2 + |s.im|))) := by
        gcongr
        · exact hbr
        · exact hfar.trans (by gcongr)
    _ ≤ max C₂ 0 * (1 + Real.log (2 + |s.im|)) + 2 * (max C₁ 0 * (1 + Real.log (2 + |s.im|))) := by
        gcongr <;> exact le_max_left _ _
    _ = (max C₂ 0 + 2 * max C₁ 0) * (1 + Real.log (2 + |s.im|)) := by ring

/-- Region (B), all points (continuity across the zeros). -/
theorem growth_strip (h1 : LocalCountSum) (h2 : StripDerivBound) :
    ∃ C : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 → 6 ≤ |s.im| →
      ‖xiDiffExt s‖ ≤ C * (1 + Real.log (2 + |s.im|)) := by
  obtain ⟨C, -, hC⟩ := growth_strip_off_zeros h1 h2
  have hB : Continuous (fun s : ℂ => C * (1 + Real.log (2 + |s.im|))) := by
    refine continuous_const.mul (continuous_const.add ?_)
    refine (continuous_const.add (continuous_abs.comp Complex.continuous_im)).log ?_
    intro s
    show (2 : ℝ) + |s.im| ≠ 0
    positivity
  have hall := bound_of_bound_off_zeros isOpen_stripOpen hB hC
  refine ⟨C, fun s h1 h2 h3 => hall s ⟨by linarith, by linarith, by linarith⟩⟩

/-! ## F. Assembly. -/

lemma abs_im_le_norm' (s : ℂ) : Real.log (2 + |s.im|) ≤ Real.log (2 + ‖s‖) :=
  Real.log_le_log (by linarith [abs_nonneg s.im]) (by linarith [Complex.abs_im_le_norm s])

/-- **The growth bound, modulo the three named inequalities.** -/
theorem xiDiffExtGrowthRight_of (h1 : LocalCountSum) (h2 : StripDerivBound) (h3 : RightDerivBound) :
    XiDiffExtGrowthRight := by
  obtain ⟨CA, hA⟩ := growth_compact
  obtain ⟨CB, hB⟩ := growth_strip h1 h2
  obtain ⟨CC, hC⟩ := growth_right h1 h3
  set C : ℝ := max 0 (max CA (max CB CC)) with hCdef
  have hC0 : 0 ≤ C := le_max_left _ _
  have hCA : CA ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCB : CB ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hCC : CC ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  refine ⟨C, fun s hs => ?_⟩
  have hL0 : 0 ≤ Real.log (2 + ‖s‖) := Real.log_nonneg (by linarith [norm_nonneg s])
  have hL1 : 0 ≤ 1 + Real.log (2 + |s.im|) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + |s.im| by linarith [abs_nonneg s.im])
    linarith
  have hlog := abs_im_le_norm' s
  rcases le_or_gt 2 s.re with hre | hre
  · refine (hC s hre).trans ?_
    calc CC * (1 + Real.log (2 + |s.im|)) ≤ C * (1 + Real.log (2 + |s.im|)) :=
          mul_le_mul_of_nonneg_right hCC hL1
      _ ≤ C * (1 + Real.log (2 + ‖s‖)) := mul_le_mul_of_nonneg_left (by linarith) hC0
  · rcases le_or_gt 6 |s.im| with him | him
    · refine (hB s hs hre.le him).trans ?_
      calc CB * (1 + Real.log (2 + |s.im|)) ≤ C * (1 + Real.log (2 + |s.im|)) :=
            mul_le_mul_of_nonneg_right hCB hL1
        _ ≤ C * (1 + Real.log (2 + ‖s‖)) := mul_le_mul_of_nonneg_left (by linarith) hC0
    · refine (hA s hs hre.le him.le).trans ?_
      calc CA ≤ C := hCA
        _ = C * 1 := (mul_one C).symm
        _ ≤ C * (1 + Real.log (2 + ‖s‖)) := mul_le_mul_of_nonneg_left (by linarith) hC0

/-- Obligation 1 of E6Bridge18 modulo the three inequalities. -/
theorem xiDiffRegular_of_three (h1 : LocalCountSum) (h2 : StripDerivBound) (h3 : RightDerivBound) :
    RvMBridge18.XiDiffRegular :=
  xiDiffRegular_of_right (xiDiffExtGrowthRight_of h1 h2 h3)

/-- **The derivative partial fraction of xi'/xi, modulo the three inequalities** (obligation 2 is
discharged by E6Bridge21). -/
theorem xiLogDerivDerivEq_of_three (h1 : LocalCountSum) (h2 : StripDerivBound) (h3 : RightDerivBound) :
    RvMBridge18.XiLogDerivDerivEq :=
  RvMBridge18.xi_logDeriv_deriv_eq_of (xiDiffRegular_of_three h1 h2 h3) RvMBridge21.xi_logDeriv_deriv_decay

/-! ## G. The right half-plane obligation, DISCHARGED from E6Bridge21's pieces (the termwise
derivative on Re s > 1 is RvMBridge21.deriv_logDeriv_xi_of_one_lt_re, the term comparison is
RvMBridge21.norm_term_le_of_two_le_re). -/

/-- The trigamma constant T = Sum_n 1/(n + 1/2)^2. -/
def trigConst : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1 / 2) ^ 2

/-- ‖psi'(z)‖ ≤ T for Re z ≥ 1. -/
lemma norm_deriv_digamma_le {z : ℂ} (hz : 1 ≤ z.re) : ‖deriv Complex.digamma z‖ ≤ trigConst := by
  have hs := RvMBridge21.hasSum_trigamma_of_re_pos (by linarith : 1 / 2 < z.re)
  rw [← hs.tsum_eq]
  have hsum : Summable (fun n : ℕ => (1 : ℂ) / (z + n) ^ 2) :=
    RvMBridge21.summable_trigTerm (by linarith)
  refine (norm_tsum_le_tsum_norm hsum.norm).trans ?_
  exact hsum.norm.tsum_le_tsum (fun n => RvMBridge21.norm_trigTerm_le (by linarith) n)
    RvMBridge21.summable_trigBound

open scoped LSeries.notation ArithmeticFunction in
/-- The Dirichlet-series constant L2 = Sum_n ‖log n * Lambda(n) n^{-2}‖. -/
def dirConst : ℝ := ∑' n : ℕ, ‖LSeries.term (LSeries.logMul ↗Λ) (2 : ℂ) n‖

open scoped LSeries.notation ArithmeticFunction in
lemma summable_dirTerms : Summable (fun n : ℕ => ‖LSeries.term (LSeries.logMul ↗Λ) (2 : ℂ) n‖) :=
  summable_norm_iff.mpr (LSeriesSummable_logMul_of_lt_re (RvMBridge21.abscissa_vonMangoldt_lt (by simp)))

open scoped LSeries.notation ArithmeticFunction in
/-- ‖(zeta'/zeta)'(s)‖ ≤ L2 for Re s ≥ 2. -/
lemma norm_deriv_logDeriv_zeta_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖deriv (logDeriv riemannZeta) s‖ ≤ dirConst := by
  rw [RvMBridge21.deriv_logDeriv_zeta_eq (by linarith)]
  have hsum : Summable (fun n : ℕ => ‖LSeries.term (LSeries.logMul ↗Λ) s n‖) :=
    summable_dirTerms.of_nonneg_of_le (fun n => norm_nonneg _)
      (RvMBridge21.norm_term_le_of_two_le_re _ hs)
  unfold LSeries
  refine (norm_tsum_le_tsum_norm hsum).trans ?_
  exact hsum.tsum_le_tsum (RvMBridge21.norm_term_le_of_two_le_re _ hs) summable_dirTerms

/-- **Obligation (right half-plane) DISCHARGED.** -/
theorem rightDerivBound : RightDerivBound := by
  refine ⟨1 / 4 + 1 + (1 / 4) * trigConst + dirConst, fun s hs => ?_⟩
  rw [RvMBridge21.deriv_logDeriv_xi_of_one_lt_re (by linarith)]
  have hns : 2 ≤ ‖s‖ := hs.trans (Complex.re_le_norm s)
  have hns1 : 1 ≤ ‖s - 1‖ := by
    have := Complex.re_le_norm (s - 1)
    rw [Complex.sub_re, Complex.one_re] at this
    linarith
  have e1 : ‖(-1 : ℂ) / s ^ 2‖ ≤ 1 / 4 := by
    rw [norm_div, norm_neg, norm_one, norm_pow]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have e2 : ‖(1 : ℂ) / (s - 1) ^ 2‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_pow, div_le_one (by positivity)]
    nlinarith
  have e3 : ‖(1 / 4 : ℂ) * deriv Complex.digamma (s / 2)‖ ≤ (1 / 4) * trigConst := by
    rw [norm_mul]
    have h14 : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
    rw [h14]
    refine mul_le_mul_of_nonneg_left (norm_deriv_digamma_le ?_) (by norm_num)
    rw [Complex.div_re]
    simp only [Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_ofNat]
    linarith
  have e4 := norm_deriv_logDeriv_zeta_le hs
  calc ‖-1 / s ^ 2 - 1 / (s - 1) ^ 2 + (1 / 4 : ℂ) * deriv Complex.digamma (s / 2)
        + deriv (logDeriv riemannZeta) s‖
      ≤ ‖-1 / s ^ 2 - 1 / (s - 1) ^ 2 + (1 / 4 : ℂ) * deriv Complex.digamma (s / 2)‖
        + ‖deriv (logDeriv riemannZeta) s‖ := norm_add_le _ _
    _ ≤ (‖-1 / s ^ 2 - 1 / (s - 1) ^ 2‖ + ‖(1 / 4 : ℂ) * deriv Complex.digamma (s / 2)‖)
        + ‖deriv (logDeriv riemannZeta) s‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ((‖(-1 : ℂ) / s ^ 2‖ + ‖(1 : ℂ) / (s - 1) ^ 2‖) + ‖(1 / 4 : ℂ) * deriv Complex.digamma (s / 2)‖)
        + ‖deriv (logDeriv riemannZeta) s‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ ((1 / 4 + 1) + (1 / 4) * trigConst) + dirConst := by gcongr
    _ = 1 / 4 + 1 + (1 / 4) * trigConst + dirConst := by ring

/-- The growth bound modulo the TWO remaining inequalities. -/
theorem xiDiffExtGrowthRight_of_two (h1 : LocalCountSum) (h2 : StripDerivBound) :
    XiDiffExtGrowthRight :=
  xiDiffExtGrowthRight_of h1 h2 rightDerivBound

/-- The derivative partial fraction modulo the TWO remaining inequalities. -/
theorem xiLogDerivDerivEq_of_two (h1 : LocalCountSum) (h2 : StripDerivBound) :
    RvMBridge18.XiLogDerivDerivEq :=
  xiLogDerivDerivEq_of_three h1 h2 rightDerivBound

end RvMBridge22
