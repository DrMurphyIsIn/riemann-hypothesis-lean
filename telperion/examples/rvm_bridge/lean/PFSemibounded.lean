/-
  PFSemibounded -- the pole-free Weil form is semibounded iff RH (2026-10-14).

  * `rh_iff_poleFree_weil_semibounded`: RH holds iff there is a constant C with
        -C * ∫ ‖g‖^2 <= Re weilForm (g * g~)
    for every pole-free Weil test g (paperFT g (+-i/2) = 0).  Forward: positivity (C = 0).
    Converse: an off-line zero makes the weighted Gaussian zero sum of PFConverseB arbitrarily
    negative (`weighted_dominance_unbounded`: the pair term is -2K e^{2 lam M}), while the L^2
    norms of the pole-free approximants stay bounded by an lam-independent constant (Plancherel,
    `integral_norm_sq_eq`, and ‖qG c lam t‖ <= ‖qG c 1 t‖ on the real axis for lam >= 1).
  * `rh_iff_poleFree_weil_shift_semibounded`: for every real c, the same with the archimedean
    delta-shift  Re weilForm + c * ∫ ‖g‖^2  (a c delta at u = 0 adds c * (g * g~)(0)).  The truth
    of RH does not depend on the delta coefficient (gate 12.1 Theorem 2, hypothesis (F) removed).

  This is a soft strengthening of Weil's criterion, RH-equivalent; very likely classical.  Nothing
  here is progress on RH; conjecture1_proved = False.
-/
import PFConverseC

open Zeta23 Complex MeasureTheory Filter Topology
open scoped ComplexConjugate FourierTransform SchwartzMap

noncomputable section

namespace RvMBridgePF
open WeilExplicit RvMBridge6 RvMBridge7 RvMBridge8 RvMBridgeGauss

/-! ## A. Plancherel for Weil tests, in the paperFT normalisation. -/

lemma paperFT_real_eq_fourier (g : ℝ → ℂ) (t : ℝ) :
    paperFT g (t : ℂ) = 𝓕 g (-t / (2 * Real.pi)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold paperFT
  congr 1
  funext v
  rw [smul_eq_mul, mul_comm]
  congr 1
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-- ∫ ‖g‖^2 = (1/2π) ∫ ‖paperFT g t‖^2 dt. -/
theorem integral_norm_sq_eq {g : ℝ → ℂ} (hg : IsWeilTest g) :
    ∫ x, ‖g x‖ ^ 2 = (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖paperFT g (t : ℂ)‖ ^ 2 := by
  set f : 𝓢(ℝ, ℂ) := hg.2.toSchwartzMap hg.1 with hfdef
  have hP := SchwartzMap.integral_norm_sq_fourier f
  have hf : (f : ℝ → ℂ) = g := rfl
  rw [SchwartzMap.fourier_coe, hf] at hP
  have hcv : ∫ t : ℝ, ‖paperFT g (t : ℂ)‖ ^ 2 = 2 * Real.pi * ∫ ξ, ‖𝓕 g ξ‖ ^ 2 := by
    have h1 : ∫ t : ℝ, ‖paperFT g (t : ℂ)‖ ^ 2
        = ∫ t : ℝ, ‖𝓕 g (-1 / (2 * Real.pi) * t)‖ ^ 2 := by
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only
      rw [paperFT_real_eq_fourier]
      congr 3
      ring_nf
    have h2 := Measure.integral_comp_mul_left (fun ξ : ℝ => ‖𝓕 g ξ‖ ^ 2) (-1 / (2 * Real.pi))
    rw [h1, h2, smul_eq_mul]
    congr 1
    rw [show (-1 / (2 * Real.pi))⁻¹ = -(2 * Real.pi) by field_simp, abs_neg,
      abs_of_pos (by positivity)]
  rw [hcv, ← hP]
  field_simp

lemma norm_hermitianTransform_real (g : ℝ → ℂ) (t : ℝ) :
    ‖hermitianTransform g (t : ℂ)‖ = ‖paperFT g (t : ℂ)‖ ^ 2 := by
  rw [norm_hermitianTransform_eq, Complex.conj_ofReal, sq]

lemma continuous_paperFT_real {g : ℝ → ℂ} (hg : IsWeilTest g) :
    Continuous fun t : ℝ => paperFT g (t : ℂ) := by
  set f : 𝓢(ℝ, ℂ) := hg.2.toSchwartzMap hg.1 with hfdef
  have hf : (f : ℝ → ℂ) = g := rfl
  have h : (fun t : ℝ => paperFT g (t : ℂ)) = fun t => (𝓕 f) (-t / (2 * Real.pi)) := by
    funext t
    rw [paperFT_real_eq_fourier, SchwartzMap.fourier_coe, hf]
  rw [h]
  exact (𝓕 f).continuous.comp (by fun_prop)

/-! ## B. Norms of the pole-free approximants. -/

theorem tendsto_integral_norm_sq_ptest {c lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n => ∫ x, ‖ptest c lam n x‖ ^ 2) atTop
      (𝓝 ((1 / (2 * Real.pi)) * ∫ t : ℝ, ‖qG c lam (t : ℂ)‖)) := by
  obtain ⟨htest, -, ⟨D, hD⟩, hlim⟩ := weighted_approx (c := c) hlam
  have heq : ∀ n, ∫ x, ‖ptest c lam n x‖ ^ 2
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖hermitianTransform (ptest c lam n) (t : ℂ)‖ := by
    intro n
    rw [integral_norm_sq_eq (htest n)]
    simp_rw [norm_hermitianTransform_real]
  simp_rw [heq]
  refine Tendsto.const_mul _ ?_
  have him : ∀ t : ℝ, |(t : ℂ).im| ≤ 1 / 2 := fun t => by simp
  refine tendsto_integral_of_dominated_convergence (fun t : ℝ => D * (1 + t ^ 2)⁻¹)
    (fun n => ?_) (integrable_inv_one_add_sq.const_mul D)
    (fun n => Eventually.of_forall fun t => ?_) (Eventually.of_forall fun t => ?_)
  · simp_rw [norm_hermitianTransform_real]
    exact ((continuous_paperFT_real (htest n)).norm.pow 2).aestronglyMeasurable
  · rw [norm_norm]
    have h := hD n (t : ℂ) (him t)
    rw [Complex.normSq_ofReal] at h
    simpa [div_eq_mul_inv, sq] using h
  · exact (continuous_norm.tendsto _).comp (hlim (t : ℂ) (him t))

/-- On the real axis, ‖qG c lam t‖ <= Cq c / (1 + t^2) for lam >= 1. -/
lemma norm_qG_real_le (c : ℝ) {lam : ℝ} (hlam : 1 ≤ lam) (t : ℝ) :
    ‖qG c lam (t : ℂ)‖ ≤ Cq c * (1 + t ^ 2)⁻¹ := by
  have h1 : ‖qG c lam (t : ℂ)‖ ≤ ‖qG c 1 (t : ℂ)‖ := by
    unfold qG
    rw [norm_mul, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [norm_gaussTest, norm_gaussTest]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hlam) (sq_nonneg (t - c))]
  have h2 := norm_qG_one_mul_le c (z := (t : ℂ)) (by simp)
  rw [Complex.normSq_ofReal] at h2
  have hpos : 0 < 1 + t ^ 2 := by positivity
  refine h1.trans ?_
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  simpa [sq] using h2

/-- The lam-independent norm budget. -/
def normBudget (c : ℝ) : ℝ := (1 / (2 * Real.pi)) * ∫ t : ℝ, Cq c * (1 + t ^ 2)⁻¹

lemma normBudget_nonneg (c : ℝ) : 0 ≤ normBudget c := by
  unfold normBudget
  have := Cq_nonneg c
  have : 0 ≤ ∫ t : ℝ, Cq c * (1 + t ^ 2)⁻¹ := integral_nonneg fun t => by positivity
  positivity

lemma limit_norm_le_budget (c : ℝ) {lam : ℝ} (hlam : 1 ≤ lam) :
    (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖qG c lam (t : ℂ)‖ ≤ normBudget c := by
  unfold normBudget
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
    (integrable_inv_one_add_sq.const_mul _) (Eventually.of_forall fun t => norm_qG_real_le c hlam t)

/-! ## C. Unbounded weighted dominance (PFConverseB with the target -L in place of 0). -/

theorem weighted_dominance_unbounded (ρ₀ : ℂ) (h₀ : IsNontrivialZero ρ₀) (hre₀ : ρ₀.re ≠ 1 / 2) :
    ∃ c : ℝ, ∀ L : ℝ, 0 ≤ L → ∃ lam : ℝ, 1 ≤ lam ∧ (zeroSide (qG c lam)).re < -L := by
  obtain ⟨c, hcI, hcbad, hcim⟩ := exists_generic_centre' hre₀
  refine ⟨c, fun L hL => ?_⟩
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
  set lam₀ : ℝ := max 1 (max (A / (2 * η * K)) ((B + L) / (2 * M * K))) with hlam₀
  obtain ⟨lam, hlam, hphase⟩ := exists_lam_phase lam₀ hP0 hxy
  have hlam1 : 1 ≤ lam := (le_max_left _ _).trans hlam
  have hlamA : A / (2 * η * K) ≤ lam := ((le_max_left _ _).trans (le_max_right _ _)).trans hlam
  have hlamB : (B + L) / (2 * M * K) ≤ lam := ((le_max_right _ _).trans (le_max_right _ _)).trans hlam
  refine ⟨lam, hlam1, ?_⟩
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
  have hexpM : B + L < K * Real.exp (2 * lam * M) := by
    have h1 : (B + L) / K ≤ 2 * lam * M := by
      rw [div_le_iff₀ hK0]
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * M * K)).mp hlamB
      linarith
    have h2 : 2 * lam * M + 1 ≤ Real.exp (2 * lam * M) := Real.add_one_le_exp _
    have h3 : (B + L) / K < Real.exp (2 * lam * M) := by linarith
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

/-! ## D. The theorems. -/

/-- **Semibounded pole-free Weil form implies RH.** -/
theorem weil_semibounded_poleFree_implies_rh
    (hsb : ∃ C : ℝ, ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g → PoleFree g →
      -C * ∫ x, ‖g x‖ ^ 2 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re) :
    RiemannHypothesis := by
  obtain ⟨C₀, hC₀⟩ := hsb
  set C : ℝ := max C₀ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC : ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g → PoleFree g →
      -C * ∫ x, ‖g x‖ ^ 2 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re := by
    intro g hg hpf
    have h := hC₀ g hg hpf
    have hn : 0 ≤ ∫ x, ‖g x‖ ^ 2 := integral_nonneg fun x => by positivity
    have : -C * ∫ x, ‖g x‖ ^ 2 ≤ -C₀ * ∫ x, ‖g x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith [le_max_left C₀ 0]) hn
    linarith
  apply rh_of_all_on_line
  intro ρ₀ h₀
  by_contra hre
  obtain ⟨c, hdom⟩ := weighted_dominance_unbounded ρ₀ h₀ hre
  have hN := normBudget_nonneg c
  obtain ⟨lam, hlam1, hneg⟩ := hdom (C * normBudget c) (mul_nonneg hC0 hN)
  have hlam : 0 < lam := by linarith
  obtain ⟨htest, hpf, ⟨D, hD⟩, hlim⟩ := weighted_approx (c := c) hlam
  have hT : Tendsto (fun n => zeroSide (hermitianTransform (ptest c lam n))) atTop
      (𝓝 (zeroSide (qG c lam))) := by
    unfold zeroSide
    exact RvMBridgeGauss.tendsto_tsum_zeroMult_of_strip_bound hD hlim
  have hA := tendsto_integral_norm_sq_ptest (c := c) hlam
  have hbd : ∀ n, -C * ∫ x, ‖ptest c lam n x‖ ^ 2
      ≤ (zeroSide (hermitianTransform (ptest c lam n))).re := fun n => by
    rw [← weilForm_autocorr_eq_zeroSide (htest n)]
    exact hC _ (htest n) (hpf n)
  have hlimit : -C * ((1 / (2 * Real.pi)) * ∫ t : ℝ, ‖qG c lam (t : ℂ)‖)
      ≤ (zeroSide (qG c lam)).re :=
    le_of_tendsto_of_tendsto' (hA.const_mul (-C)) ((Complex.continuous_re.tendsto _).comp hT) hbd
  have hbudget := limit_norm_le_budget c hlam1
  have : -C * normBudget c ≤ -C * ((1 / (2 * Real.pi)) * ∫ t : ℝ, ‖qG c lam (t : ℂ)‖) := by
    have := mul_le_mul_of_nonneg_left hbudget hC0
    linarith
  linarith

/-- **RH iff the pole-free Weil form is semibounded** (bounded below by a multiple of ‖g‖^2). -/
theorem rh_iff_poleFree_weil_semibounded :
    RiemannHypothesis ↔ ∃ C : ℝ, ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g → PoleFree g →
      -C * ∫ x, ‖g x‖ ^ 2 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re := by
  refine ⟨fun h => ⟨0, fun g hg _ => ?_⟩, weil_semibounded_poleFree_implies_rh⟩
  have := RvMBridge5.rh_implies_weil_positivity h g hg
  simpa using this

/-- **The delta-shift does not decide RH.**  For every real c, RH iff the shifted form
Re weilForm + c ∫ ‖g‖^2 is semibounded on pole-free tests. -/
theorem rh_iff_poleFree_weil_shift_semibounded (c : ℝ) :
    RiemannHypothesis ↔ ∃ C : ℝ, ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g → PoleFree g →
      -C * ∫ x, ‖g x‖ ^ 2
        ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re + c * ∫ x, ‖g x‖ ^ 2 := by
  rw [rh_iff_poleFree_weil_semibounded]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C - c, fun g hg hpf => by have := hC g hg hpf; linarith⟩
  · rintro ⟨C, hC⟩
    exact ⟨C + c, fun g hg hpf => by have := hC g hg hpf; linarith⟩

end RvMBridgePF
