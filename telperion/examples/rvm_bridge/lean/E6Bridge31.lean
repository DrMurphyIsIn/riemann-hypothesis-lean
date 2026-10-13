/-
  E6Bridge31 -- the prime-free window of the MIRRORMERE goal node (2026-09-23).

  The goal node (E6Bridge9 zeta_comb_membership_iff_rh) reads RH as
      for all g, IsWeilTest g -> 0 <= Re weilForm (autocorr g),   weilForm f = archSide f - primeSide f.
  This file works on the goal node's OWN test class restricted to a window of supports:

    Stage 0 (theorem primeSide_autocorr_eq_zero, weilForm_autocorr_eq_archSide):
      if tsupport g ⊆ Icc (-L) L and 2 L <= log 2 then primeSide (autocorr g) = 0, so on the
      window the Weil functional IS the archimedean side.  (tsupport (autocorr g) ⊆ Icc (-2L) (2L)
      by Zeta23's tsupport_weilTest_subset; for n >= 2, log n >= log 2 >= 2L, and continuity kills
      the boundary point log 2; Lambda(0) = Lambda(1) = 0.)

    Stage 1 (theorem weil_positivity_narrow_support), UNCONDITIONAL with explicit constants:
      if tsupport g ⊆ Icc (-L) L and L <= 1/14 then 0 <= Re weilForm (autocorr g).
      Archimedean dominance: with f = autocorr g, M = f(0) = ||g||_2^2 and A = ||g||_1,
        |ĝ(r)| <= A and A^2 <= 2 L M (AM-GM under the integral with a free parameter, i.e.
        Cauchy-Schwarz against the indicator of [-L, L]), so h(r) = |ĝ(r)|^2 <= 2 L M;
        ∫ |ĝ|^2 = 2 pi M (Fourier inversion at the origin, E6Bridge4 inversion_zero);
        the two pole terms are ĝ(i/2) conj ĝ(-i/2) + its conjugate = 2 Re (ĝ(-i/2) conj ĝ(i/2))
        >= -|ĝ(-i/2) - ĝ(i/2)|^2 / 2 (polarization), and ĝ(-i/2) - ĝ(i/2) = ∫ g (e^{u/2} - e^{-u/2})
        is at most (e^{L/2} - e^{-L/2}) A, so the pole terms cost only (55/756)^2 L M at L <= 1/14
        (an O(L^3) loss instead of the O(L) Cauchy-Schwarz loss);
        a 19-band layer cake over the E6Bridge30 floors of psiR(r) = Re psi(1/4 + i r/2) gives
          (1/2pi) ∫ |ĝ|^2 psiR >= M [ 2.3499 - (2 L / pi) * 24.67252 ].
      At L = 1/14 the total is >= M [2.3499 - log pi - 1.1225 - 0.0004] >= 0.068 M >= 0.
      (Numerics: the true threshold of this bound is L = 0.076; the true threshold of the
      statement itself is L ~ 0.36; see telperion/docs/PRIME_FREE_WINDOW_PLAN_2026-09-23.md.)

    Stage 2 (NOT proved; two named Props, no `sorry`):
      PrimeFreeWindowPositivity      -- the full window 2L <= log 2 on the goal node's class;
      PrimeFreeWindowPositivityPoleFree -- the same with the pole condition paperFT g (i/2) = 0,
                                        which is the Yoshida (1992) / Connes-Consani (2021, arXiv
                                        2006.13771, Theorem 1) archimedean positivity theorem.
      The goal-node-class statement has numerical margin 1.3e-3 of ||g||^2 at 2L = log 2 (it is
      the floor of the zero sum sum_rho |ĝ(gamma_rho)|^2 over window-supported tests), which no
      elementary route reaches; the literature theorem is the pole-free one.  Section F records
      the reductions: the full statement is equivalent to positivity of archSide alone on the
      window (Stage 0), and on the pole-free class archSide loses its two pole terms.

  Nothing here involves the zeros; no RH progress is claimed.  conjecture1_proved = False.
-/
import E6Bridge5
import E6Bridge30

open Zeta23 Complex MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace RvMBridge31
open WeilExplicit RvMBridge11 RvMBridge30

/-! ## A. Stage 0: the prime side vanishes on the window. -/

/-- A continuous function whose closed support lies in Icc a b vanishes at every x >= b. -/
lemma eq_zero_of_tsupport_subset_Icc_right {f : ℝ → ℂ} {a b : ℝ} (hf : Continuous f)
    (hs : tsupport f ⊆ Set.Icc a b) {x : ℝ} (hx : b ≤ x) : f x = 0 := by
  by_contra h
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hf.continuousAt.eventually_ne h)
  have hne : f (x + ε / 2) ≠ 0 := hball (by rw [Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
  have hmem : x + ε / 2 ∈ tsupport f := subset_tsupport f (Function.mem_support.mpr hne)
  have := (hs hmem).2
  linarith

/-- ... and at every x <= a. -/
lemma eq_zero_of_tsupport_subset_Icc_left {f : ℝ → ℂ} {a b : ℝ} (hf : Continuous f)
    (hs : tsupport f ⊆ Set.Icc a b) {x : ℝ} (hx : x ≤ a) : f x = 0 := by
  by_contra h
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hf.continuousAt.eventually_ne h)
  have hne : f (x - ε / 2) ≠ 0 := hball (by rw [Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
  have hmem : x - ε / 2 ∈ tsupport f := subset_tsupport f (Function.mem_support.mpr hne)
  have := (hs hmem).1
  linarith

/-- The autocorrelation of a test supported in [-L, L] is supported in [-2L, 2L]. -/
lemma tsupport_autocorr_subset {g : ℝ → ℂ} {L : ℝ} (hg : tsupport g ⊆ Set.Icc (-L) L) :
    tsupport (autocorr g) ⊆ Set.Icc (-(2 * L)) (2 * L) := by
  rw [RvMBridge5.autocorr_eq_weilTest]
  have h : tsupport g ⊆ Set.Icc (-((2 * L) / 2)) ((2 * L) / 2) := by
    rwa [show (2 * L) / 2 = L by ring]
  exact Zeta23.EF.tsupport_weilTest_subset h h

/-- STAGE 0: on the window 2L <= log 2 the prime side of the autocorrelation vanishes. -/
theorem primeSide_autocorr_eq_zero {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) (hL : 2 * L ≤ Real.log 2) :
    primeSide (autocorr g) = 0 := by
  have hf : Continuous (autocorr g) := (RvMBridge5.isWeilTest_autocorr hg).1.continuous
  have hts := tsupport_autocorr_subset hsupp
  unfold primeSide
  have hz : (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
      * (autocorr g (Real.log n) + autocorr g (-Real.log n))) = fun _ => 0 := by
    funext n
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · simp
      · simp [ArithmeticFunction.vonMangoldt_apply_one]
    · have hlog : Real.log 2 ≤ Real.log n :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      have h1 : autocorr g (Real.log n) = 0 :=
        eq_zero_of_tsupport_subset_Icc_right hf hts (by linarith)
      have h2 : autocorr g (-Real.log n) = 0 :=
        eq_zero_of_tsupport_subset_Icc_left hf hts (by linarith)
      rw [h1, h2]
      simp
  rw [hz, tsum_zero]

/-- On the window the Weil functional is the archimedean side. -/
theorem weilForm_autocorr_eq_archSide {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) (hL : 2 * L ≤ Real.log 2) :
    weilForm (autocorr g) = archSide (autocorr g) := by
  unfold weilForm
  rw [primeSide_autocorr_eq_zero hg hsupp hL, sub_zero]

/-! ## B. The L^2 mass and the pointwise bound |f(u)| <= f(0). -/

/-- M = ||g||_2^2. -/
def mass (g : ℝ → ℂ) : ℝ := ∫ u : ℝ, ‖g u‖ ^ 2

lemma mass_nonneg (g : ℝ → ℂ) : 0 ≤ mass g :=
  integral_nonneg fun u => by positivity

lemma integrable_normSq {g : ℝ → ℂ} (hg : IsWeilTest g) :
    Integrable (fun u : ℝ => ‖g u‖ ^ 2) := by
  have hc : Continuous fun u : ℝ => ‖g u‖ ^ 2 := by
    have := hg.1.continuous
    fun_prop
  exact hc.integrable_of_hasCompactSupport
    (hg.2.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp))

/-- f(0) = M. -/
lemma autocorr_zero (g : ℝ → ℂ) : autocorr g 0 = (mass g : ℂ) := by
  unfold autocorr mass
  rw [← integral_complex_ofReal]
  congr 1
  funext v
  rw [sub_zero, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- |f(u)| <= M: AM-GM under the integral plus translation invariance. -/
lemma norm_autocorr_le {g : ℝ → ℂ} (hg : IsWeilTest g) (u : ℝ) :
    ‖autocorr g u‖ ≤ mass g := by
  unfold autocorr
  have hi := integrable_normSq hg
  have hi' : Integrable (fun v : ℝ => ‖g (v - u)‖ ^ 2) := hi.comp_sub_right u
  calc ‖∫ v : ℝ, g v * (starRingEnd ℂ) (g (v - u))‖
      ≤ ∫ v : ℝ, (‖g v‖ ^ 2 + ‖g (v - u)‖ ^ 2) / 2 := by
        apply norm_integral_le_of_norm_le ((hi.add hi').div_const 2)
        filter_upwards with v
        rw [Complex.norm_mul, Complex.norm_conj]
        show ‖g v‖ * ‖g (v - u)‖ ≤ (‖g v‖ ^ 2 + ‖g (v - u)‖ ^ 2) / 2
        nlinarith [two_mul_le_add_sq ‖g v‖ ‖g (v - u)‖]
    _ = mass g := by
        rw [integral_div, integral_add hi hi',
          integral_sub_right_eq_self (fun v : ℝ => ‖g v‖ ^ 2) u]
        unfold mass
        ring

/-! ## C. The transform bounds: |ĝ| <= A = ||g||_1, A^2 <= 2 L M, and the pole terms. -/

/-- A = ||g||_1. -/
def l1 (g : ℝ → ℂ) : ℝ := ∫ u : ℝ, ‖g u‖

lemma l1_nonneg (g : ℝ → ℂ) : 0 ≤ l1 g := integral_nonneg fun u => norm_nonneg _

lemma integrable_norm {g : ℝ → ℂ} (hg : IsWeilTest g) : Integrable (fun u : ℝ => ‖g u‖) :=
  (hg.1.continuous.integrable_of_hasCompactSupport hg.2).norm

/-- AM-GM under the integral with a free parameter t > 0: A <= t M / 2 + L / t. -/
lemma l1_le {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ} (hL : 0 ≤ L)
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) {t : ℝ} (ht : 0 < t) :
    l1 g ≤ t * mass g / 2 + L / t := by
  unfold l1
  have hi := integrable_normSq hg
  have hi2 : Integrable (fun u : ℝ => t * ‖g u‖ ^ 2 / 2) := (hi.const_mul t).div_const 2
  have hind : Integrable ((Set.Icc (-L) L).indicator (fun _ : ℝ => 1 / (2 * t))) :=
    (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integrable_indicator
      measurableSet_Icc
  calc ∫ u : ℝ, ‖g u‖
      ≤ ∫ u : ℝ, (t * ‖g u‖ ^ 2 / 2 + (Set.Icc (-L) L).indicator (fun _ : ℝ => 1 / (2 * t)) u) := by
        apply integral_mono (integrable_norm hg) (hi2.add hind)
        intro u
        show ‖g u‖ ≤ t * ‖g u‖ ^ 2 / 2 + (Set.Icc (-L) L).indicator (fun _ : ℝ => 1 / (2 * t)) u
        by_cases hu : u ∈ Set.Icc (-L) L
        · rw [Set.indicator_of_mem hu]
          have h0 : 0 ≤ (t * ‖g u‖ - 1) ^ 2 / (2 * t) := by positivity
          have e : (t * ‖g u‖ - 1) ^ 2 / (2 * t) = t * ‖g u‖ ^ 2 / 2 + 1 / (2 * t) - ‖g u‖ := by
            field_simp
            ring
          linarith
        · rw [Set.indicator_of_notMem hu, image_eq_zero_of_notMem_tsupport (fun h => hu (hsupp h))]
          simp
    _ = t * mass g / 2 + L / t := by
        rw [integral_add hi2 hind, integral_div, integral_const_mul,
          integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc, smul_eq_mul,
          max_eq_left (by linarith)]
        unfold mass
        field_simp
        ring

/-- Cauchy-Schwarz against the indicator of [-L, L]: A^2 <= 2 L M. -/
lemma sq_l1_le {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ} (hL : 0 ≤ L)
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) : l1 g ^ 2 ≤ 2 * L * mass g := by
  have hA0 := l1_nonneg g
  have hM0 := mass_nonneg g
  rcases eq_or_lt_of_le hA0 with hA | hA
  · rw [← hA, sq, mul_zero]
    positivity
  rcases eq_or_lt_of_le hM0 with hM | hM
  · -- M = 0: A <= L / t for every t > 0, so A <= L / (2L/A + 1), i.e. 2L + A <= L: absurd.
    exfalso
    have h := l1_le hg hL hsupp (t := 2 * L / l1 g + 1) (by positivity)
    rw [← hM, mul_zero, zero_div, zero_add, le_div_iff₀ (by positivity)] at h
    have e : l1 g * (2 * L / l1 g + 1) = 2 * L + l1 g := by
      field_simp
    rw [e] at h
    linarith
  · -- M > 0: t = A / M gives A <= A / 2 + L M / A, i.e. A^2 <= 2 L M.
    have h := l1_le hg hL hsupp (t := l1 g / mass g) (div_pos hA hM)
    have e : l1 g / mass g * mass g / 2 + L / (l1 g / mass g) = l1 g / 2 + L * mass g / l1 g := by
      field_simp
    rw [e] at h
    have h2 : l1 g / 2 ≤ L * mass g / l1 g := by linarith
    rw [div_le_div_iff₀ (by norm_num) hA] at h2
    nlinarith

/-- |ĝ(z)| <= A for every real r (the phase has modulus one). -/
lemma norm_paperFT_le_l1 (g : ℝ → ℂ) (r : ℝ) : ‖paperFT g r‖ ≤ l1 g := by
  unfold paperFT l1
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext u
  rw [Complex.norm_mul, Complex.norm_exp]
  simp

/-- The square transform h(r) = |ĝ(r)|^2, as a real function. -/
def hsq (g : ℝ → ℂ) (r : ℝ) : ℝ := ‖paperFT g r‖ ^ 2

lemma hsq_nonneg (g : ℝ → ℂ) (r : ℝ) : 0 ≤ hsq g r := by unfold hsq; positivity

/-- paperFT (autocorr g) r = h(r). -/
lemma paperFT_autocorr_eq {g : ℝ → ℂ} (hg : IsWeilTest g) (r : ℝ) :
    paperFT (autocorr g) r = (hsq g r : ℂ) := by
  rw [← RvMBridge4.weilKernel_line, RvMBridge5.weilKernel_autocorr_line hg]
  unfold hsq
  push_cast
  ring

/-- h(r) <= 2 L M. -/
lemma hsq_le {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ} (hL : 0 ≤ L)
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) (r : ℝ) : hsq g r ≤ 2 * L * mass g := by
  unfold hsq
  have h1 := norm_paperFT_le_l1 g r
  have h2 := sq_l1_le hg hL hsupp
  have h0 := norm_nonneg (paperFT g r)
  nlinarith

/-- The two pole terms of the autocorrelation: W0 = ĝ(i/2) conj ĝ(-i/2). -/
lemma weilKernel_autocorr_zero_eq {g : ℝ → ℂ} (hg : IsWeilTest g) :
    weilKernel (autocorr g) 0 = paperFT g (I / 2) * (starRingEnd ℂ) (paperFT g (-I / 2)) := by
  have hc := hg.1.continuous
  rw [RvMBridge4.weilKernel_zero, RvMBridge5.autocorr_eq_weilTest,
    Zeta23.EF.paperFT_weilTest hc hc hg.2 hg.2]
  have : (starRingEnd ℂ) (I / 2) = -I / 2 := by
    rw [map_div₀, Complex.conj_I, map_ofNat]
  rw [this]

/-- ... and W1 = ĝ(-i/2) conj ĝ(i/2). -/
lemma weilKernel_autocorr_one_eq {g : ℝ → ℂ} (hg : IsWeilTest g) :
    weilKernel (autocorr g) 1 = paperFT g (-I / 2) * (starRingEnd ℂ) (paperFT g (I / 2)) := by
  have hc := hg.1.continuous
  rw [RvMBridge4.weilKernel_one, RvMBridge5.autocorr_eq_weilTest,
    Zeta23.EF.paperFT_weilTest hc hc hg.2 hg.2]
  have : (starRingEnd ℂ) (-I / 2) = I / 2 := by
    rw [map_div₀, map_neg, Complex.conj_I, map_ofNat]
    ring
  rw [this]

/-- Polarization: Re (W0 + W1) = 2 Re (a conj b) >= -|a - b|^2 / 2, a = ĝ(-i/2), b = ĝ(i/2). -/
lemma re_poles_ge {g : ℝ → ℂ} (hg : IsWeilTest g) :
    -(Complex.normSq (paperFT g (-I / 2) - paperFT g (I / 2)) / 2)
      ≤ (weilKernel (autocorr g) 0 + weilKernel (autocorr g) 1).re := by
  rw [weilKernel_autocorr_zero_eq hg, weilKernel_autocorr_one_eq hg]
  set a := paperFT g (-I / 2)
  set b := paperFT g (I / 2)
  have h1 : (b * (starRingEnd ℂ) a + a * (starRingEnd ℂ) b).re = 2 * (a * (starRingEnd ℂ) b).re := by
    have : b * (starRingEnd ℂ) a = (starRingEnd ℂ) (a * (starRingEnd ℂ) b) := by
      rw [map_mul, Complex.conj_conj, mul_comm]
    rw [this, Complex.add_re, Complex.conj_re]
    ring
  rw [h1]
  have h2 := Complex.normSq_add a b
  have h3 := Complex.normSq_sub a b
  have h4 := Complex.normSq_nonneg (a + b)
  linarith

lemma integrable_mul_cexp {g : ℝ → ℂ} (hg : IsWeilTest g) (z : ℂ) :
    Integrable (fun u : ℝ => g u * cexp (I * z * (u : ℂ))) := by
  have hcs : HasCompactSupport (fun u : ℝ => g u * cexp (I * z * (u : ℂ))) :=
    hg.2.mono' ((Function.support_mul_subset_left _ _).trans (subset_tsupport g))
  exact (hg.1.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hcs

/-- ĝ(-i/2) - ĝ(i/2) = ∫ g(u) (e^{u/2} - e^{-u/2}) du. -/
lemma paperFT_sub_eq {g : ℝ → ℂ} (hg : IsWeilTest g) :
    paperFT g (-I / 2) - paperFT g (I / 2)
      = ∫ u : ℝ, g u * ((Real.exp (u / 2) - Real.exp (-(u / 2)) : ℝ) : ℂ) := by
  unfold paperFT
  rw [← integral_sub (integrable_mul_cexp hg _) (integrable_mul_cexp hg _)]
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

/-- On [-L, L], |e^{u/2} - e^{-u/2}| <= e^{L/2} - e^{-L/2}. -/
lemma abs_exp_sub_le {L : ℝ} (u : ℝ) (hu : u ∈ Set.Icc (-L) L) :
    |Real.exp (u / 2) - Real.exp (-(u / 2))| ≤ Real.exp (L / 2) - Real.exp (-(L / 2)) := by
  have h1 := Real.exp_le_exp.mpr (show u / 2 ≤ L / 2 by linarith [hu.2])
  have h2 := Real.exp_le_exp.mpr (show -(L / 2) ≤ -(u / 2) by linarith [hu.2])
  have h3 := Real.exp_le_exp.mpr (show -(L / 2) ≤ u / 2 by linarith [hu.1])
  have h4 := Real.exp_le_exp.mpr (show -(u / 2) ≤ L / 2 by linarith [hu.1])
  rw [abs_le]
  constructor <;> linarith

/-- |ĝ(-i/2) - ĝ(i/2)| <= (e^{L/2} - e^{-L/2}) A. -/
lemma norm_paperFT_sub_le {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) :
    ‖paperFT g (-I / 2) - paperFT g (I / 2)‖ ≤ (Real.exp (L / 2) - Real.exp (-(L / 2))) * l1 g := by
  rw [paperFT_sub_eq hg]
  unfold l1
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le ((integrable_norm hg).const_mul _)
  filter_upwards with u
  rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]
  by_cases hu : u ∈ Set.Icc (-L) L
  · rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_exp_sub_le u hu) (norm_nonneg _)
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hu (hsupp h))]
    simp

/-- e^{L/2} - e^{-L/2} <= 55/756 for 0 <= L <= 1/14 (from 1 - x <= e^{-x}). -/
lemma exp_half_sub_le {L : ℝ} (hL0 : 0 ≤ L) (hL : L ≤ 1 / 14) :
    Real.exp (L / 2) - Real.exp (-(L / 2)) ≤ 55 / 756 := by
  have hpos := Real.exp_pos (L / 2)
  have h := Real.add_one_le_exp (-(L / 2))
  have h2 : 27 / 28 ≤ Real.exp (-(L / 2)) := by linarith
  rw [Real.exp_neg] at h
  have h3 : Real.exp (L / 2) * (1 - L / 2) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left h hpos.le
    rwa [mul_inv_cancel₀ hpos.ne', show -(L / 2) + 1 = 1 - L / 2 by ring] at this
  have h4 : Real.exp (L / 2) * (27 / 28) ≤ Real.exp (L / 2) * (1 - L / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hpos.le
  linarith

/-- The pole terms cost at most (55/756)^2 L M for L <= 1/14. -/
lemma re_poles_ge_of_le {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ} (hL0 : 0 ≤ L) (hL : L ≤ 1 / 14)
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) :
    -((55 / 756) ^ 2 * L * mass g)
      ≤ (weilKernel (autocorr g) 0 + weilKernel (autocorr g) 1).re := by
  refine le_trans ?_ (re_poles_ge hg)
  rw [Complex.normSq_eq_norm_sq]
  have h1 := norm_paperFT_sub_le hg hsupp
  have h2 := exp_half_sub_le hL0 hL
  have hA := l1_nonneg g
  have hA2 := sq_l1_le hg hL0 hsupp
  have h0 := norm_nonneg (paperFT g (-I / 2) - paperFT g (I / 2))
  have h3 : ‖paperFT g (-I / 2) - paperFT g (I / 2)‖ ≤ (55 / 756) * l1 g :=
    h1.trans (mul_le_mul_of_nonneg_right h2 hA)
  have h4 : ‖paperFT g (-I / 2) - paperFT g (I / 2)‖ ^ 2 ≤ ((55 / 756) * l1 g) ^ 2 :=
    pow_le_pow_left₀ h0 h3 2
  nlinarith

/-! ## D. The archimedean integral as a real integral; its mass. -/

lemma archIntegrand_autocorr_eq {g : ℝ → ℂ} (hg : IsWeilTest g) (r : ℝ) :
    archIntegrand (autocorr g) r = ((hsq g r * psiR r : ℝ) : ℂ) := by
  unfold archIntegrand psiR
  rw [RvMBridge5.weilKernel_autocorr_line hg]
  unfold hsq
  push_cast
  ring

lemma integral_archIntegrand_autocorr_eq {g : ℝ → ℂ} (hg : IsWeilTest g) :
    ∫ r : ℝ, archIntegrand (autocorr g) r = ((∫ r : ℝ, hsq g r * psiR r : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  congr 1
  funext r
  exact archIntegrand_autocorr_eq hg r

lemma integrable_hsq_mul_psiR {g : ℝ → ℂ} (hg : IsWeilTest g) :
    Integrable (fun r : ℝ => hsq g r * psiR r) := by
  have h := RvMBridge4.integrable_archIntegrand (RvMBridge5.isWeilTest_autocorr hg)
  rw [show archIntegrand (autocorr g) = fun r => ((hsq g r * psiR r : ℝ) : ℂ) from
    funext (archIntegrand_autocorr_eq hg)] at h
  have h2 := h.re
  simpa using h2

lemma integrable_hsq {g : ℝ → ℂ} (hg : IsWeilTest g) : Integrable (hsq g) := by
  have h := RvMBridge4.integrable_paperFT (RvMBridge5.isWeilTest_autocorr hg)
  rw [show (fun t : ℝ => paperFT (autocorr g) t) = fun r => ((hsq g r : ℝ) : ℂ) from
    funext (paperFT_autocorr_eq hg)] at h
  have h2 := h.re
  simpa using h2

/-- ∫ |ĝ|^2 = 2 pi M: Fourier inversion at the origin applied to f = autocorr g. -/
lemma integral_hsq {g : ℝ → ℂ} (hg : IsWeilTest g) :
    ∫ r : ℝ, hsq g r = 2 * Real.pi * mass g := by
  have h := RvMBridge4.inversion_zero (RvMBridge5.isWeilTest_autocorr hg)
  rw [autocorr_zero, show (fun r : ℝ => paperFT (autocorr g) r) = fun r => ((hsq g r : ℝ) : ℂ) from
    funext (paperFT_autocorr_eq hg), integral_complex_ofReal] at h
  have h2 : (((1 / (2 * Real.pi)) * ∫ r : ℝ, hsq g r : ℝ) : ℂ) = (mass g : ℂ) := by
    rw [← h]
    push_cast
    ring
  have h3 := Complex.ofReal_inj.mp h2
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp at h3
  linarith

/-! ## E. The layer cake for a bounded nonnegative weight (generic form of E6Bridge30 Cake). -/

/-- The window mass of a weight bounded by S: ∫_{|r| < rho} μ <= 2 rho S. -/
lemma setIntegral_le_of_le {μ : ℝ → ℝ} {S : ℝ} (hμ0 : ∀ r, 0 ≤ μ r) (hμS : ∀ r, μ r ≤ S)
    {ρ : ℝ} (hρ : 0 ≤ ρ) : ∫ r in Set.Ioo (-ρ) ρ, μ r ≤ 2 * ρ * S := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioo (-ρ) ρ)
    (f := μ) (C := S)
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)
    (fun r _ => by rw [Real.norm_eq_abs, abs_of_nonneg (hμ0 r)]; exact hμS r)
  rw [Real.volume_real_Ioo_of_le (by linarith), Real.norm_eq_abs] at h
  calc ∫ r in Set.Ioo (-ρ) ρ, μ r ≤ |∫ r in Set.Ioo (-ρ) ρ, μ r| := le_abs_self _
    _ ≤ S * (ρ - -ρ) := h
    _ = 2 * ρ * S := by ring

/-- The layer-cake invariant for a weight μ: an integrable minorant ℓ of psiR that equals φ
beyond |r| >= ρ, with ∫ μ ℓ >= B. -/
def CakeW (μ : ℝ → ℝ) (φ ρ B : ℝ) : Prop :=
  ∃ ℓ : ℝ → ℝ, (∀ r, ℓ r ≤ psiR r) ∧ (∀ r, ρ ≤ |r| → ℓ r = φ)
    ∧ Integrable (fun r => μ r * ℓ r) ∧ B ≤ ∫ r, μ r * ℓ r

lemma cakeW_base {μ : ℝ → ℝ} (hμi : Integrable μ) {φ : ℝ} (hφ : ∀ r, φ ≤ psiR r) :
    CakeW μ φ 0 (φ * ∫ r, μ r) :=
  ⟨fun _ => φ, hφ, fun _ _ => rfl, hμi.mul_const φ,
    by rw [integral_mul_const, mul_comm]⟩

/-- One more band: a new edge ρ' >= ρ with a new floor φ' >= φ, φ' <= psiR ρ'. -/
lemma cakeW_step {μ : ℝ → ℝ} {S : ℝ} (hμi : Integrable μ) (hμ0 : ∀ r, 0 ≤ μ r)
    (hμS : ∀ r, μ r ≤ S) {φ ρ B φ' ρ' : ℝ} (h : CakeW μ φ ρ B)
    (hφ : φ ≤ φ') (hρ : ρ ≤ ρ') (hρ' : 0 ≤ ρ') (hψ : φ' ≤ psiR ρ') :
    CakeW μ φ' ρ' (B + (φ' - φ) * ((∫ r, μ r) - 2 * ρ' * S)) := by
  obtain ⟨ℓ, hle, hconst, hint, hB⟩ := h
  have hind : Integrable ((Set.Ioo (-ρ') ρ').indicator μ) := hμi.indicator measurableSet_Ioo
  have hfun : (fun r => μ r * (ℓ r + (φ' - φ) * (1 - (Set.Ioo (-ρ') ρ').indicator 1 r)))
      = fun r => μ r * ℓ r + (φ' - φ) * μ r
        - (φ' - φ) * (Set.Ioo (-ρ') ρ').indicator μ r := by
    funext r
    by_cases hr : r ∈ Set.Ioo (-ρ') ρ'
    · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr, Pi.one_apply]
      ring
    · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr]
      ring
  have hint2 : Integrable (fun r => μ r * ℓ r + (φ' - φ) * μ r) := hint.add (hμi.const_mul _)
  have hind2 : Integrable (fun r => (φ' - φ) * (Set.Ioo (-ρ') ρ').indicator μ r) :=
    hind.const_mul _
  refine ⟨fun r => ℓ r + (φ' - φ) * (1 - (Set.Ioo (-ρ') ρ').indicator 1 r), ?_, ?_, ?_, ?_⟩
  · intro r
    show ℓ r + (φ' - φ) * (1 - (Set.Ioo (-ρ') ρ').indicator 1 r) ≤ psiR r
    by_cases hr : r ∈ Set.Ioo (-ρ') ρ'
    · rw [Set.indicator_of_mem hr, Pi.one_apply, sub_self, mul_zero, add_zero]
      exact hle r
    · rw [Set.indicator_of_notMem hr, sub_zero, mul_one]
      have hr' : ρ' ≤ |r| := by rwa [mem_Ioo_abs, not_lt] at hr
      have h1 := hconst r (hρ.trans hr')
      have h2 := psiR_mono hρ' hr'
      linarith
  · intro r hr
    show ℓ r + (φ' - φ) * (1 - (Set.Ioo (-ρ') ρ').indicator 1 r) = φ'
    have hnot : r ∉ Set.Ioo (-ρ') ρ' := by rw [mem_Ioo_abs]; exact not_lt.mpr hr
    rw [Set.indicator_of_notMem hnot, hconst r (hρ.trans hr)]
    ring
  · rw [hfun]
    exact hint2.sub hind2
  · rw [hfun, integral_sub hint2 hind2, integral_add hint (hμi.const_mul _), integral_const_mul,
      integral_const_mul, integral_indicator measurableSet_Ioo]
    have hwin := setIntegral_le_of_le hμ0 hμS hρ'
    have hδ : 0 ≤ φ' - φ := by linarith
    have := mul_le_mul_of_nonneg_left hwin hδ
    linarith

lemma cakeW_integral {μ : ℝ → ℝ} (hμ0 : ∀ r, 0 ≤ μ r) (hμψ : Integrable (fun r => μ r * psiR r))
    {φ ρ B : ℝ} (h : CakeW μ φ ρ B) : B ≤ ∫ r, μ r * psiR r := by
  obtain ⟨ℓ, hle, -, hint, hB⟩ := h
  refine hB.trans (integral_mono hint hμψ fun r => ?_)
  exact mul_le_mul_of_nonneg_left (hle r) (hμ0 r)

/-- Σ_k (phi_k - phi_{k-1}) rho_k over the nineteen E6Bridge30 bands (radii 0.5 .. 21.1). -/
def bandSumAll : ℝ := 2467252 / 100000

lemma bandSumAll_eq : bandSumAll
    = (-21913 / 10000 - (-8463 / 2000)) * (1 / 2)
      + (-9069 / 5000 - (-21913 / 10000)) * (3 / 5)
      + (-2633 / 2500 - (-9069 / 5000)) * (9 / 10)
      + (-4233 / 10000 - (-2633 / 2500)) * (7 / 5)
      + (-681 / 2000 - (-4233 / 10000)) * (3 / 2)
      + (1691 / 10000 - (-681 / 2000)) * (12 / 5)
      + (3621 / 10000 - 1691 / 10000) * (29 / 10)
      + (1451 / 2500 - 3621 / 10000) * (18 / 5)
      + (9303 / 10000 - 1451 / 2500) * (51 / 10)
      + (12333 / 10000 - 9303 / 10000) * (69 / 10)
      + (6907 / 5000 - 12333 / 10000) * 8
      + (14881 / 10000 - 6907 / 5000) * (89 / 10)
      + (1709 / 1000 - 14881 / 10000) * (111 / 10)
      + (1753 / 1000 - 1709 / 1000) * (58 / 5)
      + (9523 / 5000 - 1753 / 1000) * (27 / 2)
      + (10371 / 5000 - 9523 / 5000) * 16
      + (5201 / 2500 - 10371 / 5000) * (161 / 10)
      + (22403 / 10000 - 5201 / 2500) * (189 / 10)
      + (23499 / 10000 - 22403 / 10000) * (211 / 10) := by
  unfold bandSumAll
  norm_num

/-- THE NINETEEN-BAND LOWER BOUND for a nonnegative integrable weight μ <= S of total mass T:
∫ μ psiR >= 2.3499 T - 2 S bandSumAll (bandSumAll = 24.67252). -/
theorem integral_mul_psiR_ge_bands {μ : ℝ → ℝ} {S : ℝ} (hμi : Integrable μ) (hμ0 : ∀ r, 0 ≤ μ r)
    (hμS : ∀ r, μ r ≤ S) (hμψ : Integrable (fun r => μ r * psiR r)) :
    (23499 / 10000) * (∫ r, μ r) - 2 * S * bandSumAll ≤ ∫ r, μ r * psiR r := by
  have h0 : CakeW μ (-8463 / 2000) 0 ((-8463 / 2000) * ∫ r, μ r) :=
    cakeW_base hμi fun r => (psiR_floor_0.trans (psiR_mono le_rfl (abs_nonneg r)))
  have h1 := cakeW_step hμi hμ0 hμS h0 (by norm_num) (by norm_num) (by norm_num) psiR_floor_s1
  have h2 := cakeW_step hμi hμ0 hμS h1 (by norm_num) (by norm_num) (by norm_num) psiR_floor_1
  have h3 := cakeW_step hμi hμ0 hμS h2 (by norm_num) (by norm_num) (by norm_num) psiR_floor_s2
  have h4 := cakeW_step hμi hμ0 hμS h3 (by norm_num) (by norm_num) (by norm_num) psiR_floor_2
  have h5 := cakeW_step hμi hμ0 hμS h4 (by norm_num) (by norm_num) (by norm_num) psiR_floor_s3
  have h6 := cakeW_step hμi hμ0 hμS h5 (by norm_num) (by norm_num) (by norm_num) psiR_floor_s4
  have h7 := cakeW_step hμi hμ0 hμS h6 (by norm_num) (by norm_num) (by norm_num) psiR_floor_3
  have h8 := cakeW_step hμi hμ0 hμS h7 (by norm_num) (by norm_num) (by norm_num) psiR_floor_s5
  have h9 := cakeW_step hμi hμ0 hμS h8 (by norm_num) (by norm_num) (by norm_num) psiR_floor_4
  have h10 := cakeW_step hμi hμ0 hμS h9 (by norm_num) (by norm_num) (by norm_num) psiR_floor_s7
  have h11 := cakeW_step hμi hμ0 hμS h10 (by norm_num) (by norm_num) (by norm_num) psiR_floor_5
  have h12 := cakeW_step hμi hμ0 hμS h11 (by norm_num) (by norm_num) (by norm_num) psiR_floor_s8
  have h13 := cakeW_step hμi hμ0 hμS h12 (by norm_num) (by norm_num) (by norm_num) psiR_floor_s9
  have h14 := cakeW_step hμi hμ0 hμS h13 (by norm_num) (by norm_num) (by norm_num) psiR_floor_6
  have h15 := cakeW_step hμi hμ0 hμS h14 (by norm_num) (by norm_num) (by norm_num) psiR_floor_s10
  have h16 := cakeW_step hμi hμ0 hμS h15 (by norm_num) (by norm_num) (by norm_num) psiR_floor_7
  have h17 := cakeW_step hμi hμ0 hμS h16 (by norm_num) (by norm_num) (by norm_num) psiR_floor_s11
  have h18 := cakeW_step hμi hμ0 hμS h17 (by norm_num) (by norm_num) (by norm_num) psiR_floor_s12
  have h19 := cakeW_step hμi hμ0 hμS h18 (by norm_num) (by norm_num) (by norm_num) psiR_floor_8
  have h := cakeW_integral hμ0 hμψ h19
  rw [bandSumAll_eq]
  set T := ∫ r, μ r
  linarith

/-! ## F. Stage 1: assembly. -/

/-- log pi <= 1.159 (log x <= x - 1 at x = pi / e). -/
lemma log_pi_le : Real.log Real.pi ≤ 1159 / 1000 := by
  have he := Real.exp_one_gt_d9
  have hpi := Real.pi_lt_d2
  have hpos : 0 < Real.pi / Real.exp 1 := by positivity
  have h1 := Real.log_le_sub_one_of_pos hpos
  rw [Real.log_div Real.pi_ne_zero (Real.exp_pos 1).ne', Real.log_exp] at h1
  have h2 : Real.pi / Real.exp 1 ≤ 3.15 / 2.7182818283 := by
    rw [div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]
    nlinarith
  have h3 : (3.15 : ℝ) / 2.7182818283 ≤ 1159 / 1000 := by norm_num
  linarith

/-- Re archSide (autocorr g) >= M [phi_top - log pi - (2 L / pi) bandSumAll - (55/756)^2 L]
for 0 <= L <= 1/14. -/
theorem re_archSide_autocorr_ge {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : L ≤ 1 / 14) (hsupp : tsupport g ⊆ Set.Icc (-L) L) :
    mass g * ((23499 / 10000) - Real.log Real.pi - (2 * L / Real.pi) * bandSumAll
        - (55 / 756) ^ 2 * L)
      ≤ (archSide (autocorr g)).re := by
  unfold archSide
  rw [integral_archIntegrand_autocorr_eq hg, autocorr_zero]
  set W0 := weilKernel (autocorr g) 0 with hW0
  set W1 := weilKernel (autocorr g) 1 with hW1
  set J := ∫ r : ℝ, hsq g r * psiR r with hJ
  set M := mass g with hM
  have hpoles := re_poles_ge_of_le hg hL0 hL hsupp
  rw [← hW0, ← hW1, ← hM] at hpoles
  have hJge := integral_mul_psiR_ge_bands (integrable_hsq hg) (hsq_nonneg g) (hsq_le hg hL0 hsupp)
    (integrable_hsq_mul_psiR hg)
  rw [integral_hsq hg, ← hJ, ← hM] at hJge
  have hre : (W0 + W1 - (M : ℂ) * (Real.log Real.pi : ℂ)
      + (1 / (2 * (Real.pi : ℂ))) * (J : ℂ)).re
      = (W0 + W1).re - M * Real.log Real.pi + (1 / (2 * Real.pi)) * J := by
    rw [show (M : ℂ) * (Real.log Real.pi : ℂ) = ((M * Real.log Real.pi : ℝ) : ℂ) by
        push_cast; ring,
      show (1 / (2 * (Real.pi : ℂ))) * (J : ℂ) = (((1 / (2 * Real.pi)) * J : ℝ) : ℂ) by
        push_cast; ring]
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re]
  rw [hre]
  have hpi := Real.pi_pos
  have hJ' : (1 / (2 * Real.pi)) * ((23499 / 10000) * (2 * Real.pi * M)
      - 2 * (2 * L * M) * bandSumAll) ≤ (1 / (2 * Real.pi)) * J :=
    mul_le_mul_of_nonneg_left hJge (by positivity)
  have hid : (1 / (2 * Real.pi)) * ((23499 / 10000) * (2 * Real.pi * M)
      - 2 * (2 * L * M) * bandSumAll)
      = (23499 / 10000) * M - (2 * L / Real.pi) * bandSumAll * M := by
    field_simp
  rw [hid] at hJ'
  nlinarith

/-- STAGE 1, the theorem at L <= 1/14 with 0 <= L: the Weil functional of the goal node's test
class is nonnegative for every test supported in [-L, L]. -/
theorem weil_positivity_narrow_support_of_nonneg {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hL0 : 0 ≤ L) (hL : L ≤ 1 / 14) (hsupp : tsupport g ⊆ Set.Icc (-L) L) :
    0 ≤ (weilForm (autocorr g)).re := by
  have hwin : 2 * L ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [weilForm_autocorr_eq_archSide hg hsupp hwin]
  refine le_trans ?_ (re_archSide_autocorr_ge hg hL0 hL hsupp)
  apply mul_nonneg (mass_nonneg g)
  have hlog := log_pi_le
  have hpi := Real.pi_gt_d2
  have h2 : (2 * L / Real.pi) * bandSumAll ≤ (2 * (1 / 14) / 3.14) * bandSumAll := by
    unfold bandSumAll
    have : 2 * L / Real.pi ≤ 2 * (1 / 14) / 3.14 := by
      rw [div_le_div_iff₀ Real.pi_pos (by norm_num)]
      nlinarith
    nlinarith
  have h3 : (55 / 756 : ℝ) ^ 2 * L ≤ (55 / 756) ^ 2 * (1 / 14) :=
    mul_le_mul_of_nonneg_left hL (by positivity)
  unfold bandSumAll at h2 ⊢
  norm_num at h2 h3 ⊢
  linarith

/-- STAGE 1 (registry shape, no sign condition on L): tsupport g ⊆ Icc (-L) L with L <= 1/14
gives 0 <= Re weilForm (autocorr g).  (For L < 0 the support condition already forces g = 0;
the proof passes through L' = max L 0.) -/
theorem weil_positivity_narrow_support {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hL : L ≤ 1 / 14) (hsupp : tsupport g ⊆ Set.Icc (-L) L) :
    0 ≤ (weilForm (autocorr g)).re := by
  have hsupp' : tsupport g ⊆ Set.Icc (-(max L 0)) (max L 0) :=
    hsupp.trans (Set.Icc_subset_Icc (by linarith [le_max_left L 0]) (le_max_left L 0))
  exact weil_positivity_narrow_support_of_nonneg hg (le_max_right L 0)
    (max_le hL (by norm_num)) hsupp'

/-! ## G. Stage 2: the named Props and the reductions. -/

/-- THE PRIME-FREE WINDOW STATEMENT on the goal node's own test class: Weil positivity for every
smooth compactly supported g with tsupport g ⊆ Icc (-L) L and 2 L <= log 2.  NOT proved here
(numerical margin 1.3e-3 of ||g||_2^2 at the edge 2L = log 2; it is the floor of the zero sum). -/
def PrimeFreeWindowPositivity : Prop :=
  ∀ (g : ℝ → ℂ) (L : ℝ), IsWeilTest g → tsupport g ⊆ Set.Icc (-L) L → 2 * L ≤ Real.log 2 →
    0 ≤ (weilForm (autocorr g)).re

/-- The same statement for the archimedean side alone. -/
def PrimeFreeWindowArchPositivity : Prop :=
  ∀ (g : ℝ → ℂ) (L : ℝ), IsWeilTest g → tsupport g ⊆ Set.Icc (-L) L → 2 * L ≤ Real.log 2 →
    0 ≤ (archSide (autocorr g)).re

/-- The Yoshida (1992) / Connes-Consani (2021, Theorem 1) class: the pole condition
ĝ(i/2) = 0 (paperFT g (I / 2) = 0) removes both pole terms of archSide (autocorr g). -/
def PrimeFreeWindowPositivityPoleFree : Prop :=
  ∀ (g : ℝ → ℂ) (L : ℝ), IsWeilTest g → tsupport g ⊆ Set.Icc (-L) L → 2 * L ≤ Real.log 2 →
    paperFT g (I / 2) = 0 → 0 ≤ (archSide (autocorr g)).re

/-- Stage 0 in Prop form: the window statement is the archimedean statement. -/
theorem primeFreeWindow_iff_arch : PrimeFreeWindowPositivity ↔ PrimeFreeWindowArchPositivity := by
  constructor
  · intro h g L hg hsupp hL
    have := h g L hg hsupp hL
    rwa [weilForm_autocorr_eq_archSide hg hsupp hL] at this
  · intro h g L hg hsupp hL
    rw [weilForm_autocorr_eq_archSide hg hsupp hL]
    exact h g L hg hsupp hL

/-- The pole-free class is contained in the full class. -/
theorem primeFreeWindow_imp_poleFree :
    PrimeFreeWindowPositivity → PrimeFreeWindowPositivityPoleFree := by
  intro h g L hg hsupp hL _
  have := h g L hg hsupp hL
  rwa [weilForm_autocorr_eq_archSide hg hsupp hL] at this

/-- The two pole terms of the autocorrelation factor through ĝ(i/2): with paperFT g (I/2) = 0
both vanish (h(i/2) = ĝ(i/2) conj ĝ(-i/2) and h(-i/2) = ĝ(-i/2) conj ĝ(i/2)). -/
theorem poles_vanish {g : ℝ → ℂ} (hg : IsWeilTest g) (h0 : paperFT g (I / 2) = 0) :
    weilKernel (autocorr g) 0 = 0 ∧ weilKernel (autocorr g) 1 = 0 := by
  have hc := hg.1.continuous
  constructor
  · rw [RvMBridge4.weilKernel_zero, RvMBridge5.autocorr_eq_weilTest,
      Zeta23.EF.paperFT_weilTest hc hc hg.2 hg.2, h0, zero_mul]
  · rw [RvMBridge4.weilKernel_one, RvMBridge5.autocorr_eq_weilTest,
      Zeta23.EF.paperFT_weilTest hc hc hg.2 hg.2]
    have : (starRingEnd ℂ) (-I / 2) = I / 2 := by
      rw [map_div₀, map_neg, Complex.conj_I, map_ofNat]
      ring
    rw [this, h0, map_zero, mul_zero]

/-- On the pole-free class the archimedean side is the log-pi term plus the digamma integral. -/
theorem archSide_autocorr_poleFree {g : ℝ → ℂ} (hg : IsWeilTest g) (h0 : paperFT g (I / 2) = 0) :
    archSide (autocorr g) = -(mass g : ℂ) * (Real.log Real.pi : ℂ)
      + (1 / (2 * (Real.pi : ℂ))) * ((∫ r : ℝ, hsq g r * psiR r : ℝ) : ℂ) := by
  unfold archSide
  obtain ⟨hz, ho⟩ := poles_vanish hg h0
  rw [hz, ho, autocorr_zero, integral_archIntegrand_autocorr_eq hg]
  ring

end RvMBridge31
