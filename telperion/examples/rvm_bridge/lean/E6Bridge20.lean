/-
  E6Bridge20 -- OBLIGATION 1 of E6Bridge18, RvMBridge18.XiDiffRegular: the regularised difference

      xiDiffReg s = deriv (logDeriv xi) s + Sum'_rho m(rho) / (s - rho)^2

  extends across the nontrivial zeros to an ENTIRE function, with logarithmic growth.
  (2026-09-21; the constant-free derivative partial fraction of xi'/xi.)

  PROVED HERE (kernel-checked, no `sorry`): the ENTIRE EXTENSION (part A of the plan).
    * xi_eq_zero_iff: xi vanishes exactly at the nontrivial zeros (strip: Lambda = Gamma_R * zeta;
      Re s >= 1: zeta and Gamma_R nonvanishing, xi 1 = 1/2; Re s <= 0: xi(1 - s) = xi(s)).
    * analyticOrderAt_xi_eq: the order of xi at s is the E8 divisor multiplicity m(s), for EVERY s
      (0 off the zeros; xi is not locally zero anywhere by the identity theorem and xi 1 = 1/2).
    * exists_ball_rest: around every point s0 the "rest" sum Sum'_{rho ≠ s0} m(rho)/(w - rho)^2 is
      differentiable on a small ball avoiding all other zeros (Weierstrass M-test,
      differentiableOn_tsum_of_summable_norm, with the local-count majorant of E6Bridge6 far
      from the ordinate of s0 and a finite exceptional set near it).
    * exists_local_form: near every s0, with xi = (z - s0)^m u (u analytic, u s0 ≠ 0, Mathlib
      analyticOrderAt_eq_natCast), logDeriv xi = m/(z - s0) + logDeriv u on the punctured ball, so
          xiDiffReg w = deriv (logDeriv u) w + Sum'_{rho ≠ s0} m(rho)/(w - rho)^2 =: H w
      for w ≠ s0 in the ball (and at s0 itself when s0 is not a zero): the double pole
      -m/(w - s0)^2 of deriv (logDeriv xi) is cancelled EXACTLY by the s0 term of the sum.
    * xiDiffExt := (if IsNontrivialZero s then limUnder (nhdsWithin s {s}ᶜ) xiDiffReg else
      xiDiffReg s) is Differentiable on all of C (xiDiffExt_differentiable) and agrees with
      xiDiffReg off the zeros (xiDiffExt_eq).
    * xiDiffExt_one_sub: the functional equation xiDiffExt (1 - s) = xiDiffExt s (from
      xi (1 - s) = xi s and the reflection symmetry rho -> 1 - rho of the divisor).

  NOT PROVED: the GROWTH bound, carried as the named obligation XiDiffExtGrowth (def : Prop):
  ‖xiDiffExt s‖ <= C (1 + log (2 + ‖s‖)).  By xiDiffExt_one_sub it suffices on Re s >= 1/2; the
  content is Landau's local partial fraction transferred to the derivative by Cauchy's estimate on
  1/2 <= Re s <= 2, |Im s| >= 6, and Dirichlet-series / Stirling bounds on Re s >= 2 (see the memo).
  xiDiffRegular_of : XiDiffExtGrowth -> XiDiffRegular is the assembly.

  2026-09-22: the xi vocabulary this module had re-proved in parallel with E6Bridge19 (xi_one_sub,
  xi_one, xi_eq_zero_iff, analyticAt_logDeriv, the logDeriv antisymmetry and its derivative form,
  oneSubEquiv / zeroMult_one_sub / tsum_polTerm_one_sub) now lives ONCE in the prelude RvMBridgeXi,
  which also holds the local unit factor computation (logDeriv_of_unit_factor) and the
  punctured-limit extension atom (ext_eventuallyEq_of_punctured) used below; every node theorem
  here is unchanged, statement verbatim.

  conjecture1_proved = False.  Nothing here bears on RH.
-/
import E6Bridge15
import E6Bridge18
import RvMBridgeXi
import Zeta23.WeilEF.XiLogDeriv

open Zeta23 Complex MeasureTheory Filter Topology Metric
open scoped ComplexConjugate

noncomputable section

namespace RvMBridge20
open WeilExplicit RvMBridge18 RvMBridgeXi

/-! ## A. The zero set and the order of xi (xi_one_sub, xi_one, xi_eq_zero_iff and
xi_ne_zero_of_not_nontrivial are the prelude's, RvMBridgeXi). -/

lemma xi_ne_zero_of_one_le_re {s : ℂ} (h : 1 ≤ s.re) : xi s ≠ 0 := by
  by_cases hs1 : s = 1
  · rw [hs1, xi_one]; norm_num
  · have hs0 : s ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at h; norm_num at h
    rw [xi_eq s hs0 hs1]
    have hpos : 0 < s.re := by linarith
    have hΛ : completedRiemannZeta s ≠ 0 := by
      rw [(Zeta23.WeilEF.completedZeta_eventuallyEq_mul hpos).eq_of_nhds]
      exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hpos) (riemannZeta_ne_zero_of_one_le_re h)
    exact mul_ne_zero (div_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) two_ne_zero) hΛ

/-- xi is not locally zero anywhere (identity theorem + xi 1 = 1/2). -/
lemma analyticOrderAt_xi_ne_top (s : ℂ) : analyticOrderAt xi s ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have hAn : AnalyticOnNhd ℂ xi Set.univ := fun z _ => xi_differentiable.analyticAt z
  have := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ s)
    htop (Set.mem_univ 1)
  rw [xi_one] at this
  norm_num at this

lemma analyticAt_completedZeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    AnalyticAt ℂ completedRiemannZeta s := by
  have hopen : IsOpen ({0, 1} : Set ℂ)ᶜ := (Set.toFinite _).isClosed.isOpen_compl
  have hmem : s ∈ ({0, 1} : Set ℂ)ᶜ := by simp [hs0, hs1]
  refine DifferentiableOn.analyticAt (s := ({0, 1} : Set ℂ)ᶜ) (fun z hz => ?_) (hopen.mem_nhds hmem)
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
  exact (differentiableAt_completedZeta hz.1 hz.2).differentiableWithinAt

/-- The order of xi at a nontrivial zero is the E8 multiplicity. -/
theorem analyticOrderAt_xi_eq_of_zero {ρ : ℂ} (h : IsNontrivialZero ρ) :
    analyticOrderAt xi ρ = (WeilExplicit.zeroMult ρ : ℕ∞) := by
  have hs0 : ρ ≠ 0 := fun h0 => by have := h.2.1; rw [h0, Complex.zero_re] at this; exact lt_irrefl _ this
  have hs1 : ρ ≠ 1 := fun h1 => by have := h.2.2; rw [h1, Complex.one_re] at this; exact lt_irrefl _ this
  have hev := xi_eventuallyEq hs0 hs1
  have hA1 : AnalyticAt ℂ (fun z : ℂ => z * (z - 1) / 2) ρ := by fun_prop
  have hA2 : AnalyticAt ℂ completedRiemannZeta ρ := analyticAt_completedZeta hs0 hs1
  have h0 : analyticOrderAt (fun z : ℂ => z * (z - 1) / 2) ρ = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (div_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) two_ne_zero))
  have hxi : analyticOrderAt xi ρ = analyticOrderAt riemannZeta ρ := by
    rw [analyticOrderAt_congr hev]
    change analyticOrderAt ((fun z : ℂ => z * (z - 1) / 2) * completedRiemannZeta) ρ = _
    rw [analyticOrderAt_mul hA1 hA2, h0, zero_add,
      (Zeta23.WeilEF.completedZeta_zeros_strip h.2.1 h.2.2).2]
  rw [RvMBridge4.zeroMult_eq_of_strip h.2.1 h.2.2]
  unfold Zeta23.zeroMult
  rw [← hxi]
  exact (ENat.natCast_toNat (analyticOrderAt_xi_ne_top ρ)).symm

/-- The order of xi at EVERY point is the E8 multiplicity (zero off the zeros). -/
theorem analyticOrderAt_xi_eq (s : ℂ) : analyticOrderAt xi s = (WeilExplicit.zeroMult s : ℕ∞) := by
  by_cases h : IsNontrivialZero s
  · exact analyticOrderAt_xi_eq_of_zero h
  · rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial h, Nat.cast_zero]
    exact analyticOrderAt_eq_zero.mpr (Or.inr (xi_ne_zero_of_not_nontrivial h))

/-! ## B. The rest sum is differentiable on a small ball around every point. -/

open scoped Classical in
/-- The double-pole term with the s0 term removed. -/
def restTerm (s₀ w ρ : ℂ) : ℂ := if ρ = s₀ then 0 else polTerm w ρ

lemma tsum_polTerm_eq (w s₀ : ℂ) :
    ∑' ρ : ℂ, polTerm w ρ = polTerm w s₀ + ∑' ρ : ℂ, restTerm s₀ w ρ := by
  classical
  exact (summable_polTerm w).tsum_eq_add_tsum_ite s₀

/-- The nontrivial zeros other than s0 within ordinate distance 2 of s0: finitely many. -/
def nearZeros (s₀ : ℂ) : Set ℂ :=
  ({ρ : ℂ | IsNontrivialZero ρ} ∩ {ρ : ℂ | |ρ.im - s₀.im| < 2}) \ {s₀}

lemma nearZeros_finite (s₀ : ℂ) : (nearZeros s₀).Finite := by
  refine ((zetaSeam.finite_window (s₀.im - 3) (s₀.im + 2)).subset ?_).subset Set.sdiff_subset
  rintro ρ ⟨hnt, hw⟩
  have hw' : |ρ.im - s₀.im| < 2 := hw
  have h := abs_lt.mp hw'
  exact ⟨hnt, by linarith [h.1], by linarith [h.2]⟩

/-- A ball around s0 avoiding all nontrivial zeros other than s0. -/
lemma exists_ball_avoid (s₀ : ℂ) :
    ∃ ε > 0, ε ≤ 1 ∧ ∀ ρ ∈ nearZeros s₀, ε ≤ dist ρ s₀ := by
  have hopen : IsOpen (nearZeros s₀)ᶜ := (nearZeros_finite s₀).isClosed.isOpen_compl
  have hmem : s₀ ∈ (nearZeros s₀)ᶜ := fun h => h.2 rfl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen s₀ hmem
  refine ⟨min ε 1, by positivity, min_le_right _ _, fun ρ hρ => ?_⟩
  by_contra hlt
  push Not at hlt
  have : ρ ∈ ball s₀ ε := by
    rw [mem_ball]
    exact lt_of_lt_of_le hlt (min_le_left _ _)
  exact hball this hρ

lemma polTerm_differentiableAt {w ρ : ℂ} (h : w ≠ ρ) :
    DifferentiableAt ℂ (fun w => polTerm w ρ) w := by
  unfold polTerm
  exact (differentiableAt_const _).div ((differentiableAt_id.sub_const ρ).pow 2)
    (pow_ne_zero 2 (sub_ne_zero.mpr h))

/-- The rest sum is differentiable on a ball around s0 that contains no zero other than s0. -/
theorem exists_ball_rest (s₀ : ℂ) :
    ∃ r > 0, DifferentiableOn ℂ (fun w => ∑' ρ : ℂ, restTerm s₀ w ρ) (ball s₀ r) ∧
      ∀ w ∈ ball s₀ r, w ≠ s₀ → ¬ IsNontrivialZero w := by
  classical
  obtain ⟨ε, hε, hε1, hfar⟩ := exists_ball_avoid s₀
  refine ⟨ε / 2, by positivity, ?_, ?_⟩
  · -- Weierstrass M-test
    set A : ℝ := 13 / 4 + 2 * (|s₀.im| + 1) ^ 2 with hA
    set u : ℂ → ℝ := fun ρ => (nearZeros s₀).indicator (fun ρ => 4 * (WeilExplicit.zeroMult ρ : ℝ) / ε ^ 2) ρ
      + (WeilExplicit.zeroMult ρ : ℝ) * (A / (1 + Complex.normSq (gammaOf ρ))) with hu
    have hu_sum : Summable u := by
      refine Summable.add ?_ (RvMBridgeGauss.summable_mult_div_one_add_normSq A)
      refine summable_of_ne_finset_zero (s := (nearZeros_finite s₀).toFinset) fun ρ hρ => ?_
      rw [Set.Finite.mem_toFinset] at hρ
      exact Set.indicator_of_notMem hρ _
    refine differentiableOn_tsum_of_summable_norm hu_sum (fun ρ => ?_) isOpen_ball
      (fun ρ w hw => ?_)
    · -- each term differentiable on the ball
      intro w hw
      unfold restTerm
      by_cases hρ : ρ = s₀
      · simp only [hρ, if_true]
        exact differentiableWithinAt_const _
      · simp only [hρ, if_false]
        by_cases hnt : IsNontrivialZero ρ
        · refine (polTerm_differentiableAt ?_).differentiableWithinAt
          intro hwρ
          subst hwρ
          rw [mem_ball] at hw
          by_cases hnear : |w.im - s₀.im| < 2
          · have := hfar w ⟨⟨hnt, hnear⟩, hρ⟩
            linarith
          · have h1 := Complex.abs_im_le_norm (w - s₀)
            rw [Complex.sub_im] at h1
            rw [dist_eq_norm] at hw
            push Not at hnear
            linarith
        · have : (fun w => polTerm w ρ) = fun _ => 0 := by
            funext w
            exact polTerm_eq_zero_of_not_nontrivial hnt
          rw [this]
          exact differentiableWithinAt_const _
    · -- the uniform bound
      rw [mem_ball, dist_eq_norm] at hw
      unfold restTerm
      by_cases hρ : ρ = s₀
      · simp only [hρ, if_true, norm_zero, hu]
        have := Complex.normSq_nonneg (gammaOf s₀)
        have h0 : 0 ≤ (nearZeros s₀).indicator (fun ρ => 4 * (WeilExplicit.zeroMult ρ : ℝ) / ε ^ 2) s₀ :=
          Set.indicator_nonneg (fun _ _ => by positivity) _
        have h1 : 0 ≤ (WeilExplicit.zeroMult s₀ : ℝ) * (A / (1 + Complex.normSq (gammaOf s₀))) := by
          rw [hA]; positivity
        linarith
      · simp only [hρ, if_false, hu]
        by_cases hnt : IsNontrivialZero ρ
        · have hmaj0 : 0 ≤ (WeilExplicit.zeroMult ρ : ℝ) * (A / (1 + Complex.normSq (gammaOf ρ))) := by
            have := Complex.normSq_nonneg (gammaOf ρ)
            rw [hA]; positivity
          by_cases hnear : |ρ.im - s₀.im| < 2
          · -- near: distance at least eps/2
            have hmem : ρ ∈ nearZeros s₀ := ⟨⟨hnt, hnear⟩, hρ⟩
            rw [Set.indicator_of_mem hmem]
            have hd := hfar ρ hmem
            rw [dist_eq_norm] at hd
            have hwρ : ε / 2 ≤ ‖w - ρ‖ := by
              have := norm_sub_le_norm_sub_add_norm_sub ρ w s₀
              have h2 : ‖ρ - w‖ = ‖w - ρ‖ := norm_sub_rev _ _
              linarith
            have hpos : 0 < ‖w - ρ‖ ^ 2 := pow_pos (lt_of_lt_of_le (by positivity) hwρ) 2
            have hle : ‖polTerm w ρ‖ ≤ 4 * (WeilExplicit.zeroMult ρ : ℝ) / ε ^ 2 := by
              rw [norm_polTerm]
              rw [div_le_div_iff₀ hpos (by positivity)]
              have hε2 : (ε / 2) ^ 2 ≤ ‖w - ρ‖ ^ 2 := by
                exact pow_le_pow_left₀ (by positivity) hwρ 2
              nlinarith [Nat.cast_nonneg (α := ℝ) (WeilExplicit.zeroMult ρ)]
            linarith
          · -- far: the local-count majorant, uniformly in w
            push Not at hnear
            have hnot : ρ ∉ nearZeros s₀ := fun hm => absurd hm.1.2 (not_lt.mpr hnear)
            rw [Set.indicator_of_notMem hnot, zero_add]
            have hwim : |w.im - s₀.im| ≤ 1 := by
              have h1 := Complex.abs_im_le_norm (w - s₀)
              rw [Complex.sub_im] at h1
              linarith
            have hfar1 : 1 ≤ |ρ.im - w.im| := by
              have := abs_sub_abs_le_abs_sub (ρ.im - s₀.im) (w.im - s₀.im)
              have h2 : ρ.im - s₀.im - (w.im - s₀.im) = ρ.im - w.im := by ring
              rw [h2] at this
              linarith
            have hb := norm_polTerm_le_majorant (s := w) hnt hfar1
            refine hb.trans ?_
            refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
            refine div_le_div_of_nonneg_right ?_ (by linarith [Complex.normSq_nonneg (gammaOf ρ)])
            rw [hA]
            have h3 : |w.im| ≤ |s₀.im| + 1 := by
              have := abs_sub_abs_le_abs_sub w.im s₀.im
              linarith
            have h4 : w.im ^ 2 ≤ (|s₀.im| + 1) ^ 2 := by
              rw [← sq_abs w.im]
              exact pow_le_pow_left₀ (abs_nonneg _) h3 2
            linarith
        · rw [polTerm_eq_zero_of_not_nontrivial hnt, norm_zero]
          have := Complex.normSq_nonneg (gammaOf ρ)
          have h0 : 0 ≤ (nearZeros s₀).indicator (fun ρ => 4 * (WeilExplicit.zeroMult ρ : ℝ) / ε ^ 2) ρ :=
            Set.indicator_nonneg (fun _ _ => by positivity) _
          have h1 : 0 ≤ (WeilExplicit.zeroMult ρ : ℝ) * (A / (1 + Complex.normSq (gammaOf ρ))) := by
            rw [hA]; positivity
          linarith
  · -- no other zero in the ball
    intro w hw hne hnt
    rw [mem_ball, dist_eq_norm] at hw
    have hnear : |w.im - s₀.im| < 2 := by
      have h1 := Complex.abs_im_le_norm (w - s₀)
      rw [Complex.sub_im] at h1
      linarith
    have := hfar w ⟨⟨hnt, hnear⟩, hne⟩
    rw [dist_eq_norm] at this
    linarith

/-! ## C. The local form of xiDiffReg at every point. -/

/-- The local unit factor: xi = (z - s0)^m u near s0 with u analytic, u s0 ≠ 0, m = zeroMult s0. -/
lemma exists_unit_factor (s₀ : ℂ) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u s₀ ∧ u s₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝 s₀, xi z = (z - s₀) ^ (WeilExplicit.zeroMult s₀) * u z := by
  obtain ⟨u, hu, hu0, hxu⟩ :=
    (xi_differentiable.analyticAt s₀).analyticOrderAt_eq_natCast.mp (analyticOrderAt_xi_eq s₀)
  exact ⟨u, hu, hu0, hxu.mono fun z hz => by rw [hz, smul_eq_mul]⟩

/-- The key local computation: on the ball where xi = (z - s0)^m u, at every w with
(w - s0)^m ≠ 0,  deriv (logDeriv xi) w = -m/(w - s0)^2 + deriv (logDeriv u) w. -/
lemma deriv_logDeriv_xi_local {s₀ : ℂ} {u : ℂ → ℂ} {ε : ℝ} (_hε : 0 < ε)
    (hxu : ∀ z, dist z s₀ < ε →
      xi z = (z - s₀) ^ (WeilExplicit.zeroMult s₀) * u z ∧ AnalyticAt ℂ u z ∧ u z ≠ 0)
    {w : ℂ} (hw : dist w s₀ < ε) (hpow : (w - s₀) ^ (WeilExplicit.zeroMult s₀) ≠ 0) :
    deriv (logDeriv xi) w
      = -(WeilExplicit.zeroMult s₀ : ℂ) / (w - s₀) ^ 2 + deriv (logDeriv u) w := by
  set m := WeilExplicit.zeroMult s₀ with hm
  by_cases hm0 : m = 0
  · -- no pole: xi = u on the ball
    have hev : logDeriv xi =ᶠ[𝓝 w] logDeriv u := by
      have hball : ∀ᶠ z in 𝓝 w, dist z s₀ < ε :=
        (isOpen_ball.mem_nhds (show w ∈ ball s₀ ε from hw))
      have hxiu : ∀ᶠ z in 𝓝 w, xi z = u z := by
        filter_upwards [hball] with z hz
        rw [(hxu z hz).1, hm0, pow_zero, one_mul]
      filter_upwards [hxiu.eventually_nhds] with z hz
      have hz' : xi =ᶠ[𝓝 z] u := hz
      rw [logDeriv_apply, logDeriv_apply, hz'.deriv_eq, hz'.self_of_nhds]
    rw [hev.deriv_eq, hm0]
    simp
  · -- a genuine pole: w ≠ s0
    have hw0 : w ≠ s₀ := by
      intro h
      rw [h, sub_self, zero_pow hm0] at hpow
      exact hpow rfl
    set V : Set ℂ := ball s₀ ε ∩ {z | z ≠ s₀} with hV
    have hVopen : IsOpen V := isOpen_ball.inter isOpen_ne
    have hwV : w ∈ V := ⟨hw, hw0⟩
    -- on V, logDeriv xi z = m / (z - s0) + logDeriv u z (the prelude's local unit factor)
    have hL : ∀ z ∈ V, logDeriv xi z = (m : ℂ) * (z - s₀)⁻¹ + logDeriv u z := fun z hz =>
      logDeriv_of_unit_factor hxu (mem_ball.mp hz.1) hz.2
    have hev : logDeriv xi =ᶠ[𝓝 w] fun z => (m : ℂ) * (z - s₀)⁻¹ + logDeriv u z := by
      filter_upwards [hVopen.mem_nhds hwV] with z hz
      exact hL z hz
    rw [hev.deriv_eq]
    have hd1 : HasDerivAt (fun z : ℂ => (m : ℂ) * (z - s₀)⁻¹) ((m : ℂ) * (-1 / (w - s₀) ^ 2)) w := by
      have := ((hasDerivAt_id w).sub_const s₀).inv (sub_ne_zero.mpr hw0)
      exact this.const_mul _
    have hd2 : HasDerivAt (logDeriv u) (deriv (logDeriv u) w) w :=
      (analyticAt_logDeriv (hxu w hw).2.1 (hxu w hw).2.2).differentiableAt.hasDerivAt
    rw [show (fun z : ℂ => (m : ℂ) * (z - s₀)⁻¹ + logDeriv u z)
        = (fun z : ℂ => (m : ℂ) * (z - s₀)⁻¹) + logDeriv u from rfl, (hd1.add hd2).deriv]
    ring

/-- **The local form.**  Around every s0 there are r > 0 and H differentiable on the ball such that
the ball contains no zero other than s0, xiDiffReg = H on the punctured ball, and also at s0 when
s0 is not a zero. -/
theorem exists_local_form (s₀ : ℂ) :
    ∃ r > 0, ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball s₀ r) ∧
      (∀ w ∈ ball s₀ r, w ≠ s₀ → ¬ IsNontrivialZero w) ∧
      (∀ w ∈ ball s₀ r, w ≠ s₀ → xiDiffReg w = H w) ∧
      (¬ IsNontrivialZero s₀ → xiDiffReg s₀ = H s₀) := by
  obtain ⟨u, hu, hu0, hxu⟩ := exists_unit_factor s₀
  have hall : ∀ᶠ z in 𝓝 s₀, xi z = (z - s₀) ^ (WeilExplicit.zeroMult s₀) * u z ∧
      AnalyticAt ℂ u z ∧ u z ≠ 0 :=
    hxu.and (hu.eventually_analyticAt.and (hu.continuousAt.eventually_ne hu0))
  obtain ⟨ε, hε, hεall⟩ := Metric.eventually_nhds_iff.mp hall
  obtain ⟨r₂, hr₂, hrest, hnoz⟩ := exists_ball_rest s₀
  refine ⟨min ε r₂, lt_min hε hr₂, fun w => deriv (logDeriv u) w + ∑' ρ : ℂ, restTerm s₀ w ρ,
    ?_, ?_, ?_, ?_⟩
  · -- H differentiable on the ball
    refine DifferentiableOn.add (fun w hw => ?_) (hrest.mono (ball_subset_ball (min_le_right _ _)))
    have hw' : dist w s₀ < ε := lt_of_lt_of_le (mem_ball.mp hw) (min_le_left _ _)
    exact ((analyticAt_logDeriv (hεall hw').2.1 (hεall hw').2.2).deriv).differentiableAt.differentiableWithinAt
  · intro w hw hne
    exact hnoz w (ball_subset_ball (min_le_right _ _) hw) hne
  · intro w hw hne
    have hw' : dist w s₀ < ε := lt_of_lt_of_le (mem_ball.mp hw) (min_le_left _ _)
    have hpow : (w - s₀) ^ (WeilExplicit.zeroMult s₀) ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hne)
    unfold xiDiffReg
    rw [show (∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / (w - ρ) ^ 2) = ∑' ρ : ℂ, polTerm w ρ from rfl,
      tsum_polTerm_eq w s₀, deriv_logDeriv_xi_local hε hεall hw' hpow]
    unfold polTerm
    ring
  · intro hs
    have hw' : dist s₀ s₀ < ε := by rw [dist_self]; exact hε
    have hpow : (s₀ - s₀) ^ (WeilExplicit.zeroMult s₀) ≠ 0 := by
      rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial hs, pow_zero]
      exact one_ne_zero
    unfold xiDiffReg
    rw [show (∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / (s₀ - ρ) ^ 2) = ∑' ρ : ℂ, polTerm s₀ ρ from rfl,
      tsum_polTerm_eq s₀ s₀, deriv_logDeriv_xi_local hε hεall hw' hpow]
    unfold polTerm
    ring

/-! ## D. The entire extension. -/

open scoped Classical in
/-- The extension of xiDiffReg across the zeros: the punctured limit at a zero, xiDiffReg elsewhere. -/
def xiDiffExt (s : ℂ) : ℂ :=
  if IsNontrivialZero s then limUnder (𝓝[≠] s) xiDiffReg else xiDiffReg s

theorem xiDiffExt_eq {s : ℂ} (hs : ¬ IsNontrivialZero s) : xiDiffExt s = xiDiffReg s := by
  unfold xiDiffExt
  rw [if_neg hs]

/-- Near every point, xiDiffExt agrees with the local analytic H. -/
theorem xiDiffExt_eventuallyEq (s₀ : ℂ) :
    ∃ H : ℂ → ℂ, DifferentiableAt ℂ H s₀ ∧ xiDiffExt =ᶠ[𝓝 s₀] H := by
  obtain ⟨r, hr, H, hH, hnoz, hpunct, hat⟩ := exists_local_form s₀
  have hHd : DifferentiableAt ℂ H s₀ :=
    (hH s₀ (mem_ball_self hr)).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  refine ⟨H, hHd, ext_eventuallyEq_of_punctured (P := IsNontrivialZero) (f := xiDiffReg) hr
    (fun _ hs => xiDiffExt_eq hs) (fun s hs => by unfold xiDiffExt; rw [if_pos hs])
    hHd.continuousAt (fun w hw hne => ⟨hnoz w hw hne, hpunct w hw hne⟩) hat⟩

/-- **xiDiffExt is entire.** -/
theorem xiDiffExt_differentiable : Differentiable ℂ xiDiffExt := by
  intro s₀
  obtain ⟨H, hH, hev⟩ := xiDiffExt_eventuallyEq s₀
  exact hev.differentiableAt_iff.mpr hH

/-! ## E. The functional equation xiDiffExt (1 - s) = xiDiffExt s. -/

lemma isNontrivialZero_one_sub_iff (s : ℂ) : IsNontrivialZero (1 - s) ↔ IsNontrivialZero s := by
  have key : ∀ z : ℂ, IsNontrivialZero z → IsNontrivialZero (1 - z) := by
    intro z hz
    have h1 := Zeta23.zeta_reflect_zero (conj z) (RvMBridge15.isNontrivialZero_conj hz)
    have h2 : reflect (conj z) = 1 - z := by
      unfold reflect
      rw [Complex.conj_conj]
    rwa [h2] at h1
  refine ⟨fun h => ?_, key s⟩
  have := key (1 - s) h
  rwa [sub_sub_cancel] at this

/-! logDeriv_xi_one_sub, deriv_logDeriv_xi_one_sub, oneSubEquiv, zeroMult_one_sub and
tsum_polTerm_one_sub are the prelude's (RvMBridgeXi). -/

theorem xiDiffReg_one_sub {s : ℂ} (hs : ¬ IsNontrivialZero s) : xiDiffReg (1 - s) = xiDiffReg s := by
  unfold xiDiffReg
  rw [deriv_logDeriv_xi_one_sub hs]
  congr 1
  exact tsum_polTerm_one_sub s

/-- **The functional equation of the extension.** -/
theorem xiDiffExt_one_sub (s : ℂ) : xiDiffExt (1 - s) = xiDiffExt s := by
  by_cases hs : IsNontrivialZero s
  · obtain ⟨r, hr, H, hH, hnoz, hpunct, hat⟩ := exists_local_form s
    have hc1 : ContinuousAt (fun w => xiDiffExt (1 - w)) s :=
      (xiDiffExt_differentiable.continuous.comp (continuous_const.sub continuous_id)).continuousAt
    have hc2 : ContinuousAt xiDiffExt s := xiDiffExt_differentiable.continuous.continuousAt
    have h1 : Tendsto (fun w => xiDiffExt (1 - w)) (𝓝[≠] s) (𝓝 (xiDiffExt (1 - s))) :=
      hc1.continuousWithinAt.tendsto
    have h2 : Tendsto xiDiffExt (𝓝[≠] s) (𝓝 (xiDiffExt s)) := hc2.continuousWithinAt.tendsto
    refine tendsto_nhds_unique h1 (h2.congr' ?_)
    rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with w hw hne
    have hw' := hnoz w hw hne
    have hw'' : ¬ IsNontrivialZero (1 - w) := fun h => hw' ((isNontrivialZero_one_sub_iff w).mp h)
    rw [xiDiffExt_eq hw', xiDiffExt_eq hw'', xiDiffReg_one_sub hw']
  · have hs' : ¬ IsNontrivialZero (1 - s) := fun h => hs ((isNontrivialZero_one_sub_iff s).mp h)
    rw [xiDiffExt_eq hs', xiDiffExt_eq hs, xiDiffReg_one_sub hs]

/-! ## F. The growth obligation, its half-plane reduction, and the assembly. -/

/-- **Obligation (growth).**  The entire extension has logarithmic growth. -/
def XiDiffExtGrowth : Prop :=
  ∃ C : ℝ, ∀ s : ℂ, ‖xiDiffExt s‖ ≤ C * (1 + Real.log (2 + ‖s‖))

/-- The same on the half-plane Re s >= 1/2 only (the functional equation supplies the rest). -/
def XiDiffExtGrowthRight : Prop :=
  ∃ C : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → ‖xiDiffExt s‖ ≤ C * (1 + Real.log (2 + ‖s‖))

theorem xiDiffExtGrowth_of_right (h : XiDiffExtGrowthRight) : XiDiffExtGrowth := by
  obtain ⟨C, hC⟩ := h
  have hC0 : 0 ≤ C := by
    have h2 := hC 2 (by norm_num)
    have hl : 0 < 1 + Real.log (2 + ‖(2 : ℂ)‖) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + ‖(2 : ℂ)‖ by linarith [norm_nonneg (2 : ℂ)])
      linarith
    by_contra hneg
    have hlt : C < 0 := not_le.mp hneg
    have : C * (1 + Real.log (2 + ‖(2 : ℂ)‖)) < 0 := mul_neg_of_neg_of_pos hlt hl
    linarith [norm_nonneg (xiDiffExt 2)]
  refine ⟨C * (1 + Real.log 2), fun s => ?_⟩
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hL : 0 ≤ Real.log (2 + ‖s‖) := Real.log_nonneg (by linarith [norm_nonneg s])
  rcases le_or_gt (1 / 2) s.re with hre | hre
  · refine (hC s hre).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (by linarith)
    nlinarith
  · have hre' : 1 / 2 ≤ (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    have h1 := hC (1 - s) hre'
    rw [xiDiffExt_one_sub] at h1
    refine h1.trans ?_
    have hn : ‖(1 : ℂ) - s‖ ≤ 1 + ‖s‖ := (norm_sub_le _ _).trans (by rw [norm_one])
    have hn0 := norm_nonneg (1 - s)
    have hlog : Real.log (2 + ‖1 - s‖) ≤ Real.log (2 + ‖s‖) + Real.log 2 := by
      rw [← Real.log_mul (by linarith [norm_nonneg s]) (by norm_num)]
      exact Real.log_le_log (by linarith) (by linarith [norm_nonneg s])
    have hprod : 0 ≤ C * Real.log 2 * Real.log (2 + ‖s‖) := mul_nonneg (mul_nonneg hC0 hlog2) hL
    calc C * (1 + Real.log (2 + ‖1 - s‖)) ≤ C * (1 + Real.log (2 + ‖s‖) + Real.log 2) :=
          mul_le_mul_of_nonneg_left (by linarith) hC0
      _ ≤ C * (1 + Real.log 2) * (1 + Real.log (2 + ‖s‖)) := by nlinarith [hprod]

/-- **Obligation 1 of E6Bridge18, modulo the growth bound.** -/
theorem xiDiffRegular_of (h : XiDiffExtGrowth) : XiDiffRegular :=
  ⟨xiDiffExt, xiDiffExt_differentiable, fun _ hs => xiDiffExt_eq hs, h⟩

theorem xiDiffRegular_of_right (h : XiDiffExtGrowthRight) : XiDiffRegular :=
  xiDiffRegular_of (xiDiffExtGrowth_of_right h)

end RvMBridge20
