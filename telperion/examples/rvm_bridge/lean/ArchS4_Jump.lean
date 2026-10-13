/-
  ArchS4_Jump -- stage S4 of the archimedean conceptual blueprint (2026-10-11), part 2:
  the jump lemma, Connes-Consani arXiv:2006.13771 Theorem 3.6 via Remark 3.7, in our variable.

  For a test h (IsWeilTest) and its Q-image g = h' - h/2 (S2: exactly the pole-free tests):
      autocorr g = -(autocorr h)'' + (autocorr h)/4                       (autocorr_lift)
  so CC's Q_+ = -∂² + 1/4 acts on the convolution square and CC's ξ is our h.  Remark 3.7 is a
  double integration by parts on each half-line against an even kernel Φ(|u|) with Φ ∈ C²(ℝ):
      ∫ A''(u) Φ(|u|) du = 2 Φ'(0) A(0) + ∫ A(u) Φ''(|u|) du                 (jump_ibp)
  (the boundary terms A'(0)Φ(0) cancel; the terms A(0)Φ'(0⁺) add because Φ(|·|) has slopes ∓Φ'(0)).
  With Φ = deltaE (ArchS4_Delta: deltaE'(0) = 1), D(f) := ∫ f(u) delta(e^{|u|}) du satisfies
      D(autocorr g) = -2 ‖h‖² + ∫ autocorr h · kappaD                      (jump_lemma)
                    = -2 ‖h‖² + ⟨h, K^δ_I h⟩,  K^δ_I(v, w) = kappaD (v - w) on I = [-L, L]
  (jump_lemma_window, jump_lemma_poleFree), kappaD x = -deltaE''(|x|) + deltaE(|x|)/4 = CC's
  (Q_+ delta)(e^{|x|}).  The kernel is real, symmetric, continuous and in L²(I × I).

  Bonus (S2 open item): mass g = mass h' + mass h / 4 (mass_lift).
  conjecture1_proved = False.  Nothing here is RH progress.
-/
import ArchS4_Delta
import ArchS2_QTrick

open Zeta23 MeasureTheory Set Complex
open scoped ComplexConjugate

noncomputable section

namespace ArchS4
open WeilExplicit RvMBridge31

/-! ## A. Regularity helpers. -/

lemma contDiff_one_of_test {h : ℝ → ℂ} (hh : IsWeilTest h) : ContDiff ℝ 1 h :=
  hh.1.of_le (by exact_mod_cast le_top)

lemma isWeilTest_deriv {h : ℝ → ℂ} (hh : IsWeilTest h) : IsWeilTest (deriv h) :=
  ⟨ArchS2.contDiff_deriv_of_test hh, hh.2.deriv⟩

lemma hasCompactSupport_conj {ψ : ℝ → ℂ} (hψ : HasCompactSupport ψ) :
    HasCompactSupport fun w => conj (ψ w) :=
  hψ.comp_left (map_zero _)

lemma integrable_shift_conj {φ ψ : ℝ → ℂ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (x : ℝ) :
    Integrable fun w => φ (x + w) * conj (ψ w) :=
  ((hφ.comp (continuous_const.add continuous_id)).mul
    (Complex.continuous_conj.comp hψ)).integrable_of_hasCompactSupport
    (hasCompactSupport_conj hψc).mul_left

/-! ## B. Derivatives of the autocorrelation. -/

/-- Translation form: autocorr h x = ∫ h(x + w) conj h(w) dw. -/
lemma autocorr_eq_shift (h : ℝ → ℂ) (x : ℝ) :
    autocorr h x = ∫ w : ℝ, h (x + w) * conj (h w) := by
  unfold autocorr
  rw [← integral_add_right_eq_self (μ := volume) (fun v => h v * conj (h (v - x))) x]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [add_comm w x, add_sub_cancel_left]

/-- Differentiation under the integral sign for ∫ φ(x + w) ψ(w) dw. -/
lemma hasDerivAt_shift {φ ψ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hψ : Integrable ψ) (x : ℝ) :
    HasDerivAt (fun x => ∫ w : ℝ, φ (x + w) * ψ w) (∫ w : ℝ, deriv φ (x + w) * ψ w) x := by
  have hd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hc' : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := hc'.bounded_above_of_compact_support hφc.deriv
  obtain ⟨C0, hC0⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := x)
    (F := fun x w => φ (x + w) * ψ w) (F' := fun x w => deriv φ (x + w) * ψ w)
    (bound := fun w => C * ‖ψ w‖) (s := univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun y =>
      (hφ.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable.mul hψ.1)
    (hψ.bdd_mul (hφ.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => hC0 _))
    ((hc'.comp (continuous_const.add continuous_id)).aestronglyMeasurable.mul hψ.1)
    (Filter.Eventually.of_forall fun w y _ => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))
    (hψ.norm.const_mul C)
    (Filter.Eventually.of_forall fun w y _ =>
      ((hd (y + w)).hasDerivAt.comp_add_const y w).mul_const (ψ w))
  exact key.2

lemma hasDerivAt_conj {ψ : ℝ → ℂ} {ψ' : ℂ} {w : ℝ} (h : HasDerivAt ψ ψ' w) :
    HasDerivAt (fun w => conj (ψ w)) (conj ψ') w := by
  have := h.star
  simpa using this

/-- Integration by parts moves the derivative across the shifted pairing. -/
lemma integral_shift_mul_conj_deriv {φ ψ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) (x : ℝ) :
    ∫ w : ℝ, φ (x + w) * conj (deriv ψ w) = -∫ w : ℝ, deriv φ (x + w) * conj (ψ w) := by
  have hdφ : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hdψ : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hu : ∀ w, HasDerivAt (fun w => φ (x + w)) (deriv φ (x + w)) w := fun w =>
    (hdφ (x + w)).hasDerivAt.comp_const_add x w
  have hv : ∀ w, HasDerivAt (fun w => conj (ψ w)) (conj (deriv ψ w)) w := fun w =>
    hasDerivAt_conj (hdψ w).hasDerivAt
  exact integral_mul_deriv_eq_deriv_mul_of_integrable (fun w _ => hu w) (fun w _ => hv w)
    (integrable_shift_conj hφ.continuous (hψ.continuous_deriv le_rfl) hψc.deriv x)
    (integrable_shift_conj (hφ.continuous_deriv le_rfl) hψ.continuous hψc x)
    (integrable_shift_conj hφ.continuous hψ.continuous hψc x)

lemma autocorr_fun_eq (h : ℝ → ℂ) : autocorr h = fun x => ∫ w : ℝ, h (x + w) * conj (h w) :=
  funext (autocorr_eq_shift h)

lemma integrable_conj_test {h : ℝ → ℂ} (hh : IsWeilTest h) : Integrable fun w => conj (h w) :=
  (Complex.continuous_conj.comp hh.1.continuous).integrable_of_hasCompactSupport
    (hasCompactSupport_conj hh.2)

lemma deriv_autocorr {h : ℝ → ℂ} (hh : IsWeilTest h) :
    deriv (autocorr h) = fun x => ∫ w : ℝ, deriv h (x + w) * conj (h w) := by
  funext x
  rw [autocorr_fun_eq]
  exact (hasDerivAt_shift (contDiff_one_of_test hh) hh.2 (integrable_conj_test hh) x).deriv

lemma deriv_deriv_autocorr {h : ℝ → ℂ} (hh : IsWeilTest h) :
    deriv (deriv (autocorr h)) = fun x => ∫ w : ℝ, deriv (deriv h) (x + w) * conj (h w) := by
  funext x
  rw [deriv_autocorr hh]
  exact (hasDerivAt_shift (contDiff_one_of_test (isWeilTest_deriv hh)) (isWeilTest_deriv hh).2
    (integrable_conj_test hh) x).deriv

/-- **CC's Q on the convolution square.**  autocorr (h' - h/2) = -(autocorr h)'' + (autocorr h)/4. -/
theorem autocorr_lift {g h : ℝ → ℂ} (hh : IsWeilTest h) (hgh : ∀ u, g u = deriv h u - h u / 2) :
    autocorr g = fun x => -deriv (deriv (autocorr h)) x + autocorr h x / 4 := by
  funext x
  have h1 := contDiff_one_of_test hh
  have h1' := contDiff_one_of_test (isWeilTest_deriv hh)
  have hc := hh.1.continuous
  have hc' := (isWeilTest_deriv hh).1.continuous
  have hc'' := (isWeilTest_deriv (isWeilTest_deriv hh)).1.continuous
  rw [deriv_deriv_autocorr hh, autocorr_eq_shift, autocorr_eq_shift]
  have hpt : (fun w => g (x + w) * conj (g w)) = fun w =>
      (deriv h (x + w) * conj (deriv h w) - deriv h (x + w) * conj (h w) / 2)
        - h (x + w) * conj (deriv h w) / 2 + h (x + w) * conj (h w) / 4 := by
    funext w
    rw [hgh, hgh, map_sub, map_div₀]
    simp only [Complex.conj_ofNat]
    ring
  rw [hpt, integral_add, integral_sub, integral_sub, integral_div, integral_div, integral_div,
    integral_shift_mul_conj_deriv h1' h1 hh.2, integral_shift_mul_conj_deriv h1 h1 hh.2]
  · ring
  · exact integrable_shift_conj hc' hc' (isWeilTest_deriv hh).2 x
  · exact (integrable_shift_conj hc' hc hh.2 x).div_const 2
  · exact (integrable_shift_conj hc' hc' (isWeilTest_deriv hh).2 x).sub
      ((integrable_shift_conj hc' hc hh.2 x).div_const 2)
  · exact (integrable_shift_conj hc hc' (isWeilTest_deriv hh).2 x).div_const 2
  · exact ((integrable_shift_conj hc' hc' (isWeilTest_deriv hh).2 x).sub
      ((integrable_shift_conj hc' hc hh.2 x).div_const 2)).sub
      ((integrable_shift_conj hc hc' (isWeilTest_deriv hh).2 x).div_const 2)
  · exact (integrable_shift_conj hc hc hh.2 x).div_const 4

/-- autocorr h 0 = ‖h‖² (as a complex number). -/
lemma autocorr_zero (h : ℝ → ℂ) : autocorr h 0 = ((mass h : ℝ) : ℂ) := by
  unfold autocorr mass
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [sub_zero, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]

/-- **Mass identity** (S2 open item): ‖h' - h/2‖² = ‖h'‖² + ‖h‖²/4. -/
theorem mass_lift {g h : ℝ → ℂ} (hh : IsWeilTest h) (hgh : ∀ u, g u = deriv h u - h u / 2) :
    mass g = mass (deriv h) + mass h / 4 := by
  have e := congrFun (autocorr_lift hh hgh) 0
  rw [deriv_deriv_autocorr hh, autocorr_zero, autocorr_zero] at e
  have ibp := integral_shift_mul_conj_deriv (contDiff_one_of_test (isWeilTest_deriv hh))
    (contDiff_one_of_test hh) hh.2 0
  simp only [zero_add] at ibp e
  have hm : ((mass (deriv h) : ℝ) : ℂ) = ∫ w : ℝ, deriv h w * conj (deriv h w) := by
    rw [← autocorr_zero, autocorr_eq_shift]; simp only [zero_add]
  rw [← hm] at ibp
  have : ((mass g : ℝ) : ℂ) = ((mass (deriv h) + mass h / 4 : ℝ) : ℂ) := by
    rw [e]; push_cast; linear_combination -ibp
  exact_mod_cast this

/-! ## C. Remark 3.7: integration by parts against an even kink kernel. -/

lemma exists_far {A : ℝ → ℂ} (hAc : HasCompactSupport A) :
    ∃ R, 0 < R ∧ ∀ u, R ≤ |u| → u ∉ tsupport A := by
  obtain ⟨R0, hR0⟩ := hAc.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R0 0 + 1, by positivity, fun u hu hmem => ?_⟩
  have := hR0 hmem
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  have := le_max_left R0 0
  linarith

lemma integral_eq_interval {F : ℝ → ℂ} {R : ℝ} (hR : 0 ≤ R) (hF : ∀ u, R ≤ |u| → F u = 0) :
    ∫ u, F u = ∫ u in (-R)..R, F u := by
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro u hu
  apply hF
  simp only [mem_Icc, not_and_or, not_le] at hu
  rcases hu with hu | hu
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

lemma interval_fold {F : ℝ → ℂ} (hF : Continuous F) (R : ℝ) :
    ∫ u in (-R)..R, F u = ∫ u in (0 : ℝ)..R, (F u + F (-u)) := by
  have hn : IntervalIntegrable (fun u => F (-u)) volume 0 R :=
    (hF.comp continuous_neg).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hF.intervalIntegrable _ _) hn,
    intervalIntegral.integral_comp_neg (fun u => F u), neg_zero, add_comm,
    intervalIntegral.integral_add_adjacent_intervals (hF.intervalIntegrable _ _)
      (hF.intervalIntegrable _ _)]

lemma contDiff_two_parts {𝕜F : Type*} [NormedAddCommGroup 𝕜F] [NormedSpace ℝ 𝕜F] {A : ℝ → 𝕜F}
    (hA : ContDiff ℝ 2 A) :
    Differentiable ℝ A ∧ Differentiable ℝ (deriv A) ∧ Continuous (deriv (deriv A)) := by
  obtain ⟨h1, -, h2⟩ := contDiff_succ_iff_deriv.1 (show ContDiff ℝ (1 + 1) A from hA)
  obtain ⟨h3, h4⟩ := contDiff_one_iff_deriv.1 h2
  exact ⟨h1, h3, h4⟩

/-- **CC Remark 3.7.**  For A ∈ C²_c(ℝ) and Φ ∈ C²(ℝ),
    ∫ A''(u) Φ(|u|) du = 2 Φ'(0) A(0) + ∫ A(u) Φ''(|u|) du. -/
theorem jump_ibp {A : ℝ → ℂ} (hA : ContDiff ℝ 2 A) (hAc : HasCompactSupport A)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 2 Φ) :
    ∫ u, deriv (deriv A) u * (Φ |u| : ℂ)
      = 2 * ((deriv Φ 0 : ℝ) : ℂ) * A 0 + ∫ u, A u * ((deriv (deriv Φ) |u| : ℝ) : ℂ) := by
  obtain ⟨hA1, hA2, hA3⟩ := contDiff_two_parts hA
  obtain ⟨hΦ1, hΦ2, hΦ3⟩ := contDiff_two_parts hΦ
  obtain ⟨R, hR, hfar⟩ := exists_far hAc
  have z0 : ∀ u, R ≤ |u| → A u = 0 := fun u hu => image_eq_zero_of_notMem_tsupport (hfar u hu)
  have z1 : ∀ u, R ≤ |u| → deriv A u = 0 := fun u hu =>
    image_eq_zero_of_notMem_tsupport (fun hm => hfar u hu (tsupport_deriv_subset hm))
  have z2 : ∀ u, R ≤ |u| → deriv (deriv A) u = 0 := fun u hu =>
    image_eq_zero_of_notMem_tsupport
      (fun hm => hfar u hu (tsupport_deriv_subset (tsupport_deriv_subset hm)))
  have cA := hA1.continuous
  have cA1 := hA2.continuous
  have cΦ := hΦ1.continuous
  have cΦ1 := hΦ2.continuous
  -- the even parts
  set E : ℝ → ℂ := fun u => A u + A (-u) with hE
  set E1 : ℝ → ℂ := fun u => deriv A u - deriv A (-u) with hE1
  set E2 : ℝ → ℂ := fun u => deriv (deriv A) u + deriv (deriv A) (-u) with hE2
  have dE : ∀ u, HasDerivAt E (E1 u) u := fun u => by
    have := (hA1 u).hasDerivAt.add ((hA1 (-u)).hasDerivAt.scomp u (hasDerivAt_neg u))
    exact this.congr_deriv (by simp only [hE1, neg_smul, one_smul]; ring)
  have dE1 : ∀ u, HasDerivAt E1 (E2 u) u := fun u => by
    have := (hA2 u).hasDerivAt.sub ((hA2 (-u)).hasDerivAt.scomp u (hasDerivAt_neg u))
    exact this.congr_deriv (by simp only [hE2, neg_smul, one_smul]; ring)
  have dP : ∀ u, HasDerivAt (fun u => (Φ u : ℂ)) ((deriv Φ u : ℝ) : ℂ) u := fun u =>
    (hΦ1 u).hasDerivAt.ofReal_comp
  have dP1 : ∀ u, HasDerivAt (fun u => ((deriv Φ u : ℝ) : ℂ)) ((deriv (deriv Φ) u : ℝ) : ℂ) u := fun u =>
    (hΦ2 u).hasDerivAt.ofReal_comp
  have cE : Continuous E := cA.add (cA.comp continuous_neg)
  have cE1 : Continuous E1 := cA1.sub (cA1.comp continuous_neg)
  have cE2 : Continuous E2 := hA3.add (hA3.comp continuous_neg)
  have cP2 : Continuous fun u => ((deriv (deriv Φ) u : ℝ) : ℂ) := Complex.continuous_ofReal.comp hΦ3
  have cP1 : Continuous fun u => ((deriv Φ u : ℝ) : ℂ) := Complex.continuous_ofReal.comp cΦ1
  -- left side folded onto [0, R]
  have hL : ∫ u, deriv (deriv A) u * (Φ |u| : ℂ) = ∫ u in (0 : ℝ)..R, (Φ u : ℂ) * E2 u := by
    rw [integral_eq_interval hR.le (fun u hu => by rw [z2 u hu, zero_mul]),
      interval_fold (F := fun u => deriv (deriv A) u * (Φ |u| : ℂ))
        (hA3.mul (Complex.continuous_ofReal.comp (cΦ.comp continuous_abs)))]
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le hR.le] at hu
    simp only [hE2, abs_neg, abs_of_nonneg hu.1]
    ring
  have hRt : ∫ u, A u * ((deriv (deriv Φ) |u| : ℝ) : ℂ)
      = ∫ u in (0 : ℝ)..R, ((deriv (deriv Φ) u : ℝ) : ℂ) * E u := by
    rw [integral_eq_interval hR.le (fun u hu => by rw [z0 u hu, zero_mul]),
      interval_fold (F := fun u => A u * ((deriv (deriv Φ) |u| : ℝ) : ℂ))
        (cA.mul (cP2.comp continuous_abs))]
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le hR.le] at hu
    simp only [hE, abs_neg, abs_of_nonneg hu.1]
    ring
  -- two integrations by parts on [0, R]
  have ibp1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := R)
    (fun u _ => dP u) (fun u _ => dE1 u) (cP1.intervalIntegrable _ _) (cE2.intervalIntegrable _ _)
  have ibp2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := R)
    (fun u _ => dP1 u) (fun u _ => dE u) (cP2.intervalIntegrable _ _) (cE1.intervalIntegrable _ _)
  have hRR : R ≤ |R| := le_abs_self R
  have hRR' : R ≤ |-R| := by rw [abs_neg]; exact hRR
  have e1R : E1 R = 0 := by simp only [hE1, z1 R hRR, z1 (-R) hRR', sub_zero]
  have e1z : E1 0 = 0 := by simp only [hE1, neg_zero, sub_self]
  have eR : E R = 0 := by simp only [hE, z0 R hRR, z0 (-R) hRR', add_zero]
  have ez : E 0 = 2 * A 0 := by simp only [hE, neg_zero]; ring
  rw [hL, hRt, ibp1, e1R, e1z]
  have ibp2' : ∫ u in (0 : ℝ)..R, ((deriv Φ u : ℝ) : ℂ) * E1 u
      = -(((deriv Φ 0 : ℝ) : ℂ) * (2 * A 0)) - ∫ u in (0 : ℝ)..R, ((deriv (deriv Φ) u : ℝ) : ℂ) * E u := by
    rw [ibp2, eR, ez]; ring
  rw [ibp2']
  ring

/-! ## D. The jump lemma. -/

/-- CC's (Q_+ delta)(e^{|x|}), the even function equal to (-∂² + 1/4) delta(e^x) for x > 0. -/
def kappaD (x : ℝ) : ℝ := -deriv (deriv deltaE) |x| + deltaE |x| / 4

/-- The kernel of K^δ_I: K^δ(v, w) = kappaD (v - w). -/
def KdeltaI (v w : ℝ) : ℝ := kappaD (v - w)

lemma contDiff_two_deltaE : ContDiff ℝ 2 deltaE := by exact_mod_cast contDiff_infty.1 contDiff_deltaE 2

/-- The jump lemma for a general C² kernel Φ (CC (59) with f = autocorr h). -/
theorem jump_lemma_general {g h : ℝ → ℂ} (hh : IsWeilTest h) (hgh : ∀ u, g u = deriv h u - h u / 2)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 2 Φ) :
    ∫ u, autocorr g u * (Φ |u| : ℂ)
      = -2 * ((deriv Φ 0 : ℝ) : ℂ) * (mass h : ℂ)
        + ∫ u, autocorr h u * ((-deriv (deriv Φ) |u| + Φ |u| / 4 : ℝ) : ℂ) := by
  have hA := RvMBridge5.isWeilTest_autocorr hh
  have hA2 : ContDiff ℝ 2 (autocorr h) := by exact_mod_cast contDiff_infty.1 hA.1 2
  obtain ⟨-, -, hA3⟩ := contDiff_two_parts hA2
  obtain ⟨hΦ1, -, hΦ3⟩ := contDiff_two_parts hΦ
  have cA := hA.1.continuous
  have cΦa : Continuous fun u => (Φ |u| : ℂ) :=
    Complex.continuous_ofReal.comp (hΦ1.continuous.comp continuous_abs)
  have cΦ2a : Continuous fun u => ((deriv (deriv Φ) |u| : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hΦ3.comp continuous_abs)
  have i1 : Integrable fun u => deriv (deriv (autocorr h)) u * (Φ |u| : ℂ) :=
    (hA3.mul cΦa).integrable_of_hasCompactSupport (hA.2.deriv.deriv.mul_right)
  have i2 : Integrable fun u => autocorr h u * (Φ |u| : ℂ) :=
    (cA.mul cΦa).integrable_of_hasCompactSupport hA.2.mul_right
  have i3 : Integrable fun u => autocorr h u * ((deriv (deriv Φ) |u| : ℝ) : ℂ) :=
    (cA.mul cΦ2a).integrable_of_hasCompactSupport hA.2.mul_right
  have key := jump_ibp hA2 hA.2 hΦ
  rw [autocorr_lift hh hgh, autocorr_zero] at *
  have lhs : ∫ u, (-deriv (deriv (autocorr h)) u + autocorr h u / 4) * (Φ |u| : ℂ)
      = -(∫ u, deriv (deriv (autocorr h)) u * (Φ |u| : ℂ))
        + (∫ u, autocorr h u * (Φ |u| : ℂ)) / 4 := by
    have e1 : (fun u => (-deriv (deriv (autocorr h)) u + autocorr h u / 4) * (Φ |u| : ℂ))
        = fun u => -(deriv (deriv (autocorr h)) u * (Φ |u| : ℂ))
          + autocorr h u * (Φ |u| : ℂ) / 4 := by
      funext u; ring
    rw [e1, integral_add (f := fun u => -(deriv (deriv (autocorr h)) u * (Φ |u| : ℂ)))
      (g := fun u => autocorr h u * (Φ |u| : ℂ) / 4) i1.neg (i2.div_const 4),
      integral_neg, integral_div]
  have rhs : ∫ u, autocorr h u * ((-deriv (deriv Φ) |u| + Φ |u| / 4 : ℝ) : ℂ)
      = -(∫ u, autocorr h u * ((deriv (deriv Φ) |u| : ℝ) : ℂ))
        + (∫ u, autocorr h u * (Φ |u| : ℂ)) / 4 := by
    have e2 : (fun u => autocorr h u * ((-deriv (deriv Φ) |u| + Φ |u| / 4 : ℝ) : ℂ))
        = fun u => -(autocorr h u * ((deriv (deriv Φ) |u| : ℝ) : ℂ))
          + autocorr h u * (Φ |u| : ℂ) / 4 := by
      funext u; push_cast; ring
    rw [e2, integral_add (f := fun u => -(autocorr h u * ((deriv (deriv Φ) |u| : ℝ) : ℂ)))
      (g := fun u => autocorr h u * (Φ |u| : ℂ) / 4) i3.neg (i2.div_const 4),
      integral_neg, integral_div]
  have key' : ∫ u, deriv (deriv (autocorr h)) u * (Φ |u| : ℂ)
      = 2 * ((deriv Φ 0 : ℝ) : ℂ) * (mass h : ℂ)
        + ∫ u, autocorr h u * ((deriv (deriv Φ) |u| : ℝ) : ℂ) := key
  rw [lhs, rhs, key']
  ring

/-- **The jump lemma (CC Thm 3.6, in our variable).**  For a test h and g = h' - h/2,
    D(autocorr g) = -2 ‖h‖² + ∫ autocorr h · kappaD. -/
theorem jump_lemma {g h : ℝ → ℂ} (hh : IsWeilTest h) (hgh : ∀ u, g u = deriv h u - h u / 2) :
    ∫ u, autocorr g u * (deltaE |u| : ℂ)
      = -2 * (mass h : ℂ) + ∫ u, autocorr h u * (kappaD u : ℂ) := by
  rw [jump_lemma_general hh hgh contDiff_two_deltaE, deriv_deltaE_zero]
  simp only [kappaD, Complex.ofReal_one]
  ring

/-! ## E. The quadratic form of K^δ_I on I = [-L, L]. -/

lemma continuous_kappaD : Continuous kappaD := by
  obtain ⟨hΦ1, -, hΦ3⟩ := contDiff_two_parts contDiff_two_deltaE
  exact ((hΦ3.comp continuous_abs).neg).add ((hΦ1.continuous.comp continuous_abs).div_const 4)

lemma kappaD_neg (x : ℝ) : kappaD (-x) = kappaD x := by simp [kappaD]

/-- K^δ is symmetric. -/
theorem KdeltaI_symm (v w : ℝ) : KdeltaI v w = KdeltaI w v := by
  unfold KdeltaI; rw [← kappaD_neg, neg_sub]

theorem continuous_KdeltaI : Continuous fun p : ℝ × ℝ => KdeltaI p.1 p.2 :=
  continuous_kappaD.comp (continuous_fst.sub continuous_snd)

/-- The square I × I. -/
abbrev boxI (L : ℝ) : Set (ℝ × ℝ) := Icc (-L) L ×ˢ Icc (-L) L

instance isFiniteMeasure_boxI (L : ℝ) : IsFiniteMeasure (volume.restrict (boxI L)) :=
  isFiniteMeasure_restrict.mpr (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne

/-- K^δ is square integrable on I × I (it is continuous on a compact set). -/
theorem memLp_KdeltaI (L : ℝ) :
    MemLp (fun p : ℝ × ℝ => KdeltaI p.1 p.2) 2 (volume.restrict (boxI L)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc : IsCompact (boxI L)).exists_bound_of_continuousOn
    continuous_KdeltaI.continuousOn
  refine MemLp.of_bound continuous_KdeltaI.aestronglyMeasurable C ?_
  exact (ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)).mono fun p hp => hC p hp

theorem integrable_sq_KdeltaI (L : ℝ) :
    Integrable (fun p : ℝ × ℝ => KdeltaI p.1 p.2 ^ 2) (volume.restrict (boxI L)) :=
  (memLp_two_iff_integrable_sq continuous_KdeltaI.aestronglyMeasurable).1 (memLp_KdeltaI L)

lemma zero_of_not_mem {h : ℝ → ℂ} {L : ℝ} (hsupp : tsupport h ⊆ Icc (-L) L) {v : ℝ}
    (hv : v ∉ Icc (-L) L) : h v = 0 :=
  image_eq_zero_of_notMem_tsupport fun hm => hv (hsupp hm)

/-- The pairing ∫ autocorr h · k is the bilinear form of the kernel k(v - w), for an even
    continuous k, written on I × I in the convention ⟨h, K h⟩ = ∫∫ conj h(v) K(v,w) h(w). -/
theorem autocorr_pairing_eq_box {h : ℝ → ℂ} (hh : IsWeilTest h) {L : ℝ}
    (hsupp : tsupport h ⊆ Icc (-L) L) {k : ℝ → ℝ} (hk : Continuous k) (hev : ∀ x, k (-x) = k x) :
    ∫ u, autocorr h u * (k u : ℂ)
      = ∫ p in boxI L, conj (h p.1) * (k (p.1 - p.2) : ℂ) * h p.2 := by
  have ch := hh.1.continuous
  have ck : Continuous fun u => (k u : ℂ) := Complex.continuous_ofReal.comp hk
  -- integrability of (u, v) ↦ h v conj h (v - u) k u on ℝ²
  have hint1 : Integrable (Function.uncurry fun (u v : ℝ) => h v * conj (h (v - u)) * (k u : ℂ))
      (volume.prod volume) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((ch.comp continuous_snd).mul (Complex.continuous_conj.comp
        (ch.comp (continuous_snd.sub continuous_fst)))).mul (ck.comp continuous_fst)
    · refine HasCompactSupport.intro (K := Icc (-(2 * |L|)) (2 * |L|) ×ˢ Icc (-L) L)
        (isCompact_Icc.prod isCompact_Icc) (fun p hp => ?_)
      simp only [Function.uncurry]
      by_cases h2 : p.2 ∈ Icc (-L) L
      · have h1 : p.1 ∉ Icc (-(2 * |L|)) (2 * |L|) := fun h1 => hp ⟨h1, h2⟩
        have : p.2 - p.1 ∉ Icc (-L) L := by
          intro hm
          apply h1
          have := neg_abs_le L; have := le_abs_self L
          constructor <;> linarith [hm.1, hm.2, h2.1, h2.2]
        rw [zero_of_not_mem hsupp this]; simp
      · rw [zero_of_not_mem hsupp h2]; simp
  have hint2 : Integrable (fun p : ℝ × ℝ => h p.1 * conj (h p.2) * (k (p.1 - p.2) : ℂ))
      (volume.prod volume) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((ch.comp continuous_fst).mul (Complex.continuous_conj.comp (ch.comp continuous_snd))).mul
        (ck.comp (continuous_fst.sub continuous_snd))
    · refine HasCompactSupport.intro (K := boxI L) (isCompact_Icc.prod isCompact_Icc) (fun p hp => ?_)
      by_cases h1 : p.1 ∈ Icc (-L) L
      · have h2 : p.2 ∉ Icc (-L) L := fun h2 => hp ⟨h1, h2⟩
        rw [zero_of_not_mem hsupp h2]; simp
      · rw [zero_of_not_mem hsupp h1]; simp
  calc ∫ u, autocorr h u * (k u : ℂ)
      = ∫ u, ∫ v, h v * conj (h (v - u)) * (k u : ℂ) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        simp only [autocorr]
        rw [integral_mul_const]
    _ = ∫ v, ∫ u, h v * conj (h (v - u)) * (k u : ℂ) := integral_integral_swap hint1
    _ = ∫ v, ∫ w, h v * conj (h w) * (k (v - w) : ℂ) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        simp only
        rw [← integral_sub_left_eq_self (fun w => h v * conj (h w) * (k (v - w) : ℂ)) volume v]
        simp only [sub_sub_cancel]
    _ = ∫ p : ℝ × ℝ, h p.1 * conj (h p.2) * (k (p.1 - p.2) : ℂ) ∂(volume.prod volume) :=
        (integral_prod _ hint2).symm
    _ = ∫ p : ℝ × ℝ, conj (h p.1) * (k (p.1 - p.2) : ℂ) * h p.2 ∂(volume.prod volume) := by
        rw [← integral_prod_swap]
        refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        simp only [Prod.fst_swap, Prod.snd_swap]
        rw [← hev, neg_sub]
        ring
    _ = ∫ p in boxI L, conj (h p.1) * (k (p.1 - p.2) : ℂ) * h p.2 := by
        rw [← Measure.volume_eq_prod, setIntegral_eq_integral_of_forall_compl_eq_zero]
        intro p hp
        by_cases h1 : p.1 ∈ Icc (-L) L
        · have h2 : p.2 ∉ Icc (-L) L := fun h2 => hp ⟨h1, h2⟩
          rw [zero_of_not_mem hsupp h2]; simp
        · rw [zero_of_not_mem hsupp h1]; simp

/-- **The jump lemma on the window**: D(autocorr g) = -2‖h‖² + ⟨h, K^δ_I h⟩, I = [-L, L]. -/
theorem jump_lemma_window {g h : ℝ → ℂ} (hh : IsWeilTest h) (hgh : ∀ u, g u = deriv h u - h u / 2)
    {L : ℝ} (hsupp : tsupport h ⊆ Icc (-L) L) :
    ∫ u, autocorr g u * (deltaE |u| : ℂ)
      = -2 * (mass h : ℂ) + ∫ p in boxI L, conj (h p.1) * (KdeltaI p.1 p.2 : ℂ) * h p.2 := by
  rw [jump_lemma hh hgh, autocorr_pairing_eq_box hh hsupp continuous_kappaD kappaD_neg]
  rfl

/-- **The jump lemma for the pole-free class** (S2 + S4): for a window test g with
    paperFT g (I/2) = 0, with ξ = qLift g L (the unique lift, g = ξ' - ξ/2):
    D(autocorr g) = -2‖ξ‖² + ⟨ξ, K^δ_I ξ⟩. -/
theorem jump_lemma_poleFree {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Icc (-L) L) (h0 : paperFT g (I / 2) = 0) :
    ∫ u, autocorr g u * (deltaE |u| : ℂ)
      = -2 * (mass (ArchS2.qLift g L) : ℂ)
        + ∫ p in boxI L, conj (ArchS2.qLift g L p.1) * (KdeltaI p.1 p.2 : ℂ)
            * ArchS2.qLift g L p.2 :=
  jump_lemma_window (ArchS2.isWeilTest_qLift hg hsupp h0) (ArchS2.qLift_rel hg L)
    (ArchS2.tsupport_qLift hg hsupp h0)

end ArchS4
