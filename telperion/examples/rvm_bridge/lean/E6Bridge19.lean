/-
  E6Bridge19 -- LiValue: the TAYLOR BOOKKEEPING and the ASSEMBLY (2026-09-21; rh campaign node
  RH_bl_explicit_formula = B7, value half; consumes E6Bridge15's vocabulary VERBATIM).

  E6Bridge15 proved the convergence half of Bombieri-Lagarias and left ONE named obligation,
      LiValue n : liLimit n = archSide n + finiteSide n.
  This module proves LiValue n (0 < n) MODULO two named analytic Props (def : Prop, no `sorry`):

    RvMBridge18.XiLogDerivDerivEq : for every s that is not a nontrivial zero,
        deriv (logDeriv xi) s = -Sum'_rho m(rho) / (s - rho)^2        (the analytic heart; xi =
        RvMBridge18.xi; E6Bridge18/20/21 reduce it to the ONE growth obligation
        RvMBridge20.XiDiffExtGrowthRight, so liValue_of_growth is one obligation away; the
        Lambda-form LambdaDerivPartialFraction with the explicit pole terms +1/s^2 + 1/(s-1)^2 is
        carried too and proved EQUIVALENT);
    NoRealZeroInUnitInterval : zeta(sigma) /= 0 for real 0 < sigma < 1 (used ONLY to integrate
        deriv (logDeriv xi) along the real segment [0, 1] to pin the constant of integration).

  The bookkeeping (all kernel-checked here):
    (1) power sums from the derivative: for k : N, given XiLogDerivDerivEq,
        (k+1) * powerSum (k+2) = -(iteratedDeriv k (deriv (logDeriv xi)) 0) / k!
        (term-by-term differentiation of the zero sum on a ball around 0 free of zeros;
        the radius is min(1, min over the finitely many zeros with |Im| < 1) -- no numerics);
    (2) the paired first power sum: pairedPowerSum1 = Sum' m(rho) Re(1/rho) = -logDeriv xi 0
        (FTC on [0,1] under NoRealZeroInUnitInterval, dominated interchange, the reflection
        rho -> 1 - conj rho to fold Sum' m (1/rho + 1/(1-rho)) into 2 Sum' m Re(1/rho), and the
        antisymmetry logDeriv xi (1 - s) = -logDeriv xi s);
    (3) the closed forms at s = 1: logDeriv xi = 1/s - (log pi)/2 + (1/2) psi(s/2) + logDeriv zeta_1
        near 1 (Mathlib riemannZeta_1 = (s-1) zeta, entire, zeta_1(1) = 1, zeta_1'(1) = gamma),
        so zetaLogDerivReg = -logDeriv zeta_1 near 1 and eta j is its Taylor data; the digamma
        tower at 1/2 from Zeta23's partial-fraction series: psi(1/2) = -gamma - 2 log 2 and
        d^k/ds^k [psi(s/2)] at 1 = (-1)^(k+1) 2 k! (1 - 2^-(k+1)) zeta(k+1) for k >= 1 (odd-index
        zeta sums via tsum_even_add_odd);
    (4) assembly: liLimit n = Sum_{j=1}^n (-1)^(j+1) C(n,j) Sum' m Re(rho^-j) (binomial through
        the tsum), Taylor data at 0 <-> at 1 by the antisymmetry (iteratedDeriv_comp_neg), and the
        finite-sum rearrangement that is EXACTLY archSide n + finiteSide n as RHDefs writes them.

  Numerics (mpmath, dps 30, docs/LIVALUE_TAYLOR_2026-09-21.md): archSide n + finiteSide n agrees
  with Li's lambda_n from the generating function to 1e-27 (n = 1..8) and with the first 2000
  zeros + tail to 1e-6 (n = 1..4); lambda_1 = 0.0230957089661... = 1 + gamma/2 - (log 4 pi)/2.

  2026-09-22: the shared xi vocabulary this module had re-proved in parallel with E6Bridge20 (the
  reflection xi(1-s) = xi(s), xi_eq_zero_iff, the logDeriv antisymmetry and its derivative form,
  the involution rho -> 1 - rho, the 9/4 strip inequalities, the zeroBound majorant atom, the
  countable / closed zero set, eq_of_continuousAt_of_eventually_ne) now lives ONCE in the prelude
  RvMBridgeXi; every node theorem below is unchanged, statement verbatim.

  conjecture1_proved = False.  Nothing here says anything about whether RH holds.
-/
import E6Bridge15
import E6Bridge20
import E6Bridge21
import RvMBridgeXi
import Zeta23.RvM.CountByIntegral
import Zeta23.RvM.GammaSide
import Zeta23.GammaFacts.Series

open Zeta23 Complex MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace RvMBridge19
open WeilExplicit RvMBridge15 RvMBridge15.BombieriLagarias
open RvMBridge18 (xi xi_differentiable xi_eq XiLogDerivDerivEq)
open RvMBridgeXi

/-! ## 0. xi (= RvMBridge18.xi, entire, = s(s-1)/2 Lambda(s) off {0, 1}; its reflection, values at
0 and 1, analyticity and zero set are the prelude's RvMBridgeXi.xi_one_sub / xi_zero / xi_one /
xi_analyticAt / xi_eq_zero_iff), the partial-fraction Props, the real-segment Prop. -/

/-- The analytic heart is RvMBridge18.XiLogDerivDerivEq (xi form): for every s that is not a
nontrivial zero, deriv (logDeriv xi) s = -Sum' m(rho)/(s - rho)^2.  Restated here for the record. -/
theorem xiLogDerivDerivEq_def : XiLogDerivDerivEq = (∀ s : ℂ, ¬ IsNontrivialZero s →
    deriv (logDeriv xi) s = -∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2) := rfl

/-- The analytic heart, Lambda form: the same identity for completedRiemannZeta, which has simple
poles at 0 and 1, hence the explicit terms +1/s^2 + 1/(s-1)^2 and the exclusion of 0, 1. -/
def LambdaDerivPartialFraction : Prop := ∀ s : ℂ, s ≠ 0 → s ≠ 1 → ¬ IsNontrivialZero s →
  deriv (logDeriv completedRiemannZeta) s
    = -∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2 + 1 / s ^ 2 + 1 / (s - 1) ^ 2

/-- zeta has no zero on the real segment (0, 1). -/
def NoRealZeroInUnitInterval : Prop := ∀ σ : ℝ, 0 < σ → σ < 1 → riemannZeta (σ : ℂ) ≠ 0

/-! ## 1. Generic machinery: summability over the zeros by a local-count majorant, and
term-by-term iterated differentiation of a series on a ball. -/

/-! The majorant atom (smallZeros, smallZeros_finite, zeroBound, summable_zeroBound,
norm_le_zeroBound, summable_of_zeroBound) and the strip inequalities inv_normSq_le_majorant /
inv_im_sq_le_majorant are the prelude's (RvMBridgeXi), statements unchanged. -/

lemma one_le_norm_of_nontrivial {ρ : ℂ} (him : 1 ≤ |ρ.im|) : 1 ≤ ‖ρ‖ :=
  him.trans (Complex.abs_im_le_norm ρ)

lemma norm_pos_of_nontrivial {ρ : ℂ} (h : IsNontrivialZero ρ) : 0 < ‖ρ‖ := by
  rw [norm_pos_iff]
  intro h0
  have := h.2.1
  rw [h0, Complex.zero_re] at this
  exact lt_irrefl _ this

/-- Term-by-term iterated differentiation of a series on a ball: if g (k+1) i is the derivative
of g k i on the ball with summable uniform bounds u k, then the k-th derivative of the sum of the
g 0 i is the sum of the g k i, on the ball. -/
theorem iteratedDeriv_tsum_ball {ι : Type*} (g : ℕ → ι → ℂ → ℂ) (u : ℕ → ι → ℝ) (c : ℂ) (r : ℝ)
    (hsum : ∀ k, Summable (u k))
    (hderiv : ∀ k i s, s ∈ Metric.ball c r → HasDerivAt (g k i) (g (k + 1) i s) s)
    (hbound : ∀ k i s, s ∈ Metric.ball c r → ‖g k i s‖ ≤ u k i) :
    ∀ k s, s ∈ Metric.ball c r → iteratedDeriv k (fun z => ∑' i, g 0 i z) s = ∑' i, g k i s := by
  intro k
  induction k with
  | zero => intro s _; simp
  | succ k ih =>
    intro s hs
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv k (fun z => ∑' i, g 0 i z) =ᶠ[𝓝 s] fun z => ∑' i, g k i z := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hs] with z hz
      exact ih z hz
    rw [hev.deriv_eq]
    refine HasDerivAt.deriv ?_
    refine hasDerivAt_tsum_of_isPreconnected (hsum (k + 1)) Metric.isOpen_ball
      (convex_ball c r).isPreconnected (fun i y hy => hderiv k i y hy)
      (fun i y hy => hbound (k + 1) i y hy) hs ?_ hs
    exact Summable.of_norm_bounded (hsum k) (fun i => hbound k i s hs)

/-- The sum of a termwise-differentiable series with summable uniform bounds is analytic on
the ball. -/
theorem analyticAt_tsum_ball {ι : Type*} (g : ℕ → ι → ℂ → ℂ) (u : ℕ → ι → ℝ) (c : ℂ) (r : ℝ)
    (hsum : ∀ k, Summable (u k))
    (hderiv : ∀ k i s, s ∈ Metric.ball c r → HasDerivAt (g k i) (g (k + 1) i s) s)
    (hbound : ∀ k i s, s ∈ Metric.ball c r → ‖g k i s‖ ≤ u k i)
    {s : ℂ} (hs : s ∈ Metric.ball c r) : AnalyticAt ℂ (fun z => ∑' i, g 0 i z) s := by
  refine DifferentiableOn.analyticAt (s := Metric.ball c r) ?_ (Metric.isOpen_ball.mem_nhds hs)
  intro y hy
  refine (hasDerivAt_tsum_of_isPreconnected (hsum 1) Metric.isOpen_ball
    (convex_ball c r).isPreconnected (fun i z hz => hderiv 0 i z hz)
    (fun i z hz => hbound 1 i z hz) hy ?_ hy).differentiableAt.differentiableWithinAt
  exact Summable.of_norm_bounded (hsum 0) (fun i => hbound 0 i y hy)

/-! ## 2. Power sums from the derivative (deliverable 1). -/

/-- A radius r with 0 < r <= 1 and r <= |rho| for every nontrivial zero: min over the finitely
many zeros with |Im rho| < 1 (all others have |rho| >= |Im rho| >= 1).  No numerics. -/
lemma exists_zero_radius : ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ ρ, IsNontrivialZero ρ → r ≤ ‖ρ‖ := by
  by_cases hF : smallZeros_finite.toFinset.Nonempty
  · obtain ⟨ρ₀, hρ₀, hmin⟩ := smallZeros_finite.toFinset.exists_min_image (fun ρ => ‖ρ‖) hF
    rw [Set.Finite.mem_toFinset] at hρ₀
    refine ⟨min 1 ‖ρ₀‖, lt_min one_pos (norm_pos_of_nontrivial hρ₀.1), min_le_left _ _, ?_⟩
    intro ρ hρ
    by_cases him : |ρ.im| < 1
    · exact (min_le_right _ _).trans (hmin ρ (by rw [Set.Finite.mem_toFinset]; exact ⟨hρ, him⟩))
    · exact (min_le_left _ _).trans (one_le_norm_of_nontrivial (not_lt.mp him))
  · refine ⟨1, one_pos, le_rfl, fun ρ hρ => ?_⟩
    by_cases him : |ρ.im| < 1
    · exact absurd ⟨ρ, by rw [Set.Finite.mem_toFinset]; exact ⟨hρ, him⟩⟩ hF
    · exact one_le_norm_of_nontrivial (not_lt.mp him)

/-- The zero-free radius about 0. -/
def zeroRadius : ℝ := Classical.choose exists_zero_radius

lemma zeroRadius_pos : 0 < zeroRadius := (Classical.choose_spec exists_zero_radius).1
lemma zeroRadius_le_one : zeroRadius ≤ 1 := (Classical.choose_spec exists_zero_radius).2.1
lemma zeroRadius_le {ρ : ℂ} (h : IsNontrivialZero ρ) : zeroRadius ≤ ‖ρ‖ :=
  (Classical.choose_spec exists_zero_radius).2.2 ρ h

/-- The ball |s| < zeroRadius/2 contains no nontrivial zero. -/
lemma not_nontrivialZero_of_mem_ball {s : ℂ} (hs : s ∈ Metric.ball (0 : ℂ) (zeroRadius / 2)) :
    ¬ IsNontrivialZero s := by
  intro h
  rw [Metric.mem_ball, dist_zero_right] at hs
  linarith [zeroRadius_le h, zeroRadius_pos]

/-- On the ball, |s - rho| >= |rho|/2 for every nontrivial zero rho. -/
lemma norm_sub_ge_half {s ρ : ℂ} (hs : s ∈ Metric.ball (0 : ℂ) (zeroRadius / 2))
    (h : IsNontrivialZero ρ) : ‖ρ‖ / 2 ≤ ‖s - ρ‖ := by
  rw [Metric.mem_ball, dist_zero_right] at hs
  have h1 := zeroRadius_le h
  have h2 := norm_sub_norm_le ρ s
  rw [norm_sub_rev] at h2
  linarith

/-- (-1)^k (k+1)!, the k-th derivative coefficient of (s - rho)^{-2}. -/
def coef (k : ℕ) : ℂ := (-1) ^ k * ((k + 1).factorial : ℂ)

lemma coef_succ (k : ℕ) : coef (k + 1) = coef k * (-((k : ℂ) + 2)) := by
  unfold coef
  rw [Nat.factorial_succ (k + 1)]
  push_cast
  ring

lemma coef_zero : coef 0 = 1 := by simp [coef]

lemma norm_coef (k : ℕ) : ‖coef k‖ = ((k + 1).factorial : ℝ) := by
  unfold coef
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast]

/-- The k-th derivative of m(rho)/(s - rho)^2 in s. -/
def zterm (k : ℕ) (ρ s : ℂ) : ℂ :=
  (WeilExplicit.zeroMult ρ : ℂ) * coef k * (s - ρ) ^ (-((k : ℤ) + 2))

lemma zterm_zero_eq (ρ s : ℂ) : zterm 0 ρ s = (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2 := by
  unfold zterm
  rw [coef_zero, mul_one]
  simp [zpow_neg, div_eq_mul_inv]

lemma zterm_eq_zero_of_not_nontrivial {k : ℕ} {ρ : ℂ} (h : ¬ IsNontrivialZero ρ) (s : ℂ) :
    zterm k ρ s = 0 := by
  unfold zterm
  rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial h]
  simp

lemma hasDerivAt_zterm (k : ℕ) (ρ : ℂ) {s : ℂ} (hne : s ≠ ρ) :
    HasDerivAt (zterm k ρ) (zterm (k + 1) ρ s) s := by
  have hne' : s - ρ ≠ 0 := sub_ne_zero.mpr hne
  have h1 := ((hasDerivAt_zpow (-((k : ℤ) + 2)) (s - ρ) (Or.inl hne')).comp s
    ((hasDerivAt_id s).sub_const ρ)).const_mul ((WeilExplicit.zeroMult ρ : ℂ) * coef k)
  have hfun : zterm k ρ = fun y => (WeilExplicit.zeroMult ρ : ℂ) * coef k
      * ((fun x => x ^ (-((k : ℤ) + 2))) ∘ fun x => id x - ρ) y := by
    funext y; simp [zterm, Function.comp]
  rw [hfun]
  refine h1.congr_deriv ?_
  rw [show (-((k : ℤ) + 2) - 1) = -(((k + 1 : ℕ) : ℤ) + 2) by push_cast; ring]
  unfold zterm
  rw [coef_succ]
  push_cast
  ring

/-- The norm of the k-th term on the ball: <= m (k+1)! 2^(k+2) / |rho|^(k+2). -/
lemma norm_zterm_le {k : ℕ} {ρ s : ℂ} (hs : s ∈ Metric.ball (0 : ℂ) (zeroRadius / 2))
    (h : IsNontrivialZero ρ) :
    ‖zterm k ρ s‖ ≤ (WeilExplicit.zeroMult ρ : ℝ) * ((k + 1).factorial : ℝ) * 2 ^ (k + 2)
      / ‖ρ‖ ^ (k + 2) := by
  have hρ := norm_pos_of_nontrivial h
  have hhalf := norm_sub_ge_half hs h
  have hsρ : 0 < ‖s - ρ‖ := by linarith
  unfold zterm
  rw [norm_mul, norm_mul, Complex.norm_natCast, norm_coef, norm_zpow,
    show (-((k : ℤ) + 2)) = -((k + 2 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  have h1 : (‖ρ‖ / 2) ^ (k + 2) ≤ ‖s - ρ‖ ^ (k + 2) := pow_le_pow_left₀ (by positivity) hhalf _
  have h2 : (‖s - ρ‖ ^ (k + 2))⁻¹ ≤ 2 ^ (k + 2) / ‖ρ‖ ^ (k + 2) := by
    rw [show (2 : ℝ) ^ (k + 2) / ‖ρ‖ ^ (k + 2) = ((‖ρ‖ / 2) ^ (k + 2))⁻¹ by rw [div_pow, inv_div]]
    exact inv_anti₀ (by positivity) h1
  calc (WeilExplicit.zeroMult ρ : ℝ) * ((k + 1).factorial : ℝ) * (‖s - ρ‖ ^ (k + 2))⁻¹
      ≤ (WeilExplicit.zeroMult ρ : ℝ) * ((k + 1).factorial : ℝ) * (2 ^ (k + 2) / ‖ρ‖ ^ (k + 2)) := by
        gcongr
    _ = _ := by ring

/-- The uniform summable bound for the k-th terms on the ball. -/
def zbound (k : ℕ) : ℂ → ℝ :=
  zeroBound (((k + 1).factorial : ℝ) * 2 ^ (k + 2) * (9 / 4))
    (fun ρ => (WeilExplicit.zeroMult ρ : ℝ) * ((k + 1).factorial : ℝ) * 2 ^ (k + 2)
      / zeroRadius ^ (k + 2))

lemma summable_zbound (k : ℕ) : Summable (zbound k) := summable_zeroBound _ _

lemma norm_zterm_le_zbound (k : ℕ) (ρ : ℂ) {s : ℂ}
    (hs : s ∈ Metric.ball (0 : ℂ) (zeroRadius / 2)) : ‖zterm k ρ s‖ ≤ zbound k ρ := by
  refine norm_le_zeroBound (fun ρ h => zterm_eq_zero_of_not_nontrivial h s) ?_ ?_ (by positivity) ρ
  · intro ρ h _
    refine (norm_zterm_le hs h).trans ?_
    have hr := zeroRadius_pos
    have hρ := norm_pos_of_nontrivial h
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    exact pow_le_pow_left₀ hr.le (zeroRadius_le h) _
  · intro ρ h him
    refine (norm_zterm_le hs h).trans ?_
    have hρ1 := one_le_norm_of_nontrivial him
    have hρ := norm_pos_of_nontrivial h
    have hmaj := inv_normSq_le_majorant h him
    rw [Complex.normSq_eq_norm_sq] at hmaj
    have hpow : ‖ρ‖ ^ 2 ≤ ‖ρ‖ ^ (k + 2) := pow_le_pow_right₀ hρ1 (by omega)
    calc (WeilExplicit.zeroMult ρ : ℝ) * ((k + 1).factorial : ℝ) * 2 ^ (k + 2) / ‖ρ‖ ^ (k + 2)
        ≤ (WeilExplicit.zeroMult ρ : ℝ) * ((k + 1).factorial : ℝ) * 2 ^ (k + 2) / ‖ρ‖ ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
      _ = (WeilExplicit.zeroMult ρ : ℝ) * (((k + 1).factorial : ℝ) * 2 ^ (k + 2) * (1 / ‖ρ‖ ^ 2)) := by
          ring
      _ ≤ (WeilExplicit.zeroMult ρ : ℝ) * (((k + 1).factorial : ℝ) * 2 ^ (k + 2)
            * ((9 / 4) / (1 + Complex.normSq (gammaOf ρ)))) := by
          gcongr
      _ = _ := by ring

/-- The power sums Sum' m(rho) rho^{-j}. -/
def powerSum (j : ℕ) : ℂ := ∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / ρ ^ j

lemma powerSum_term_eq_zero_of_not_nontrivial {j : ℕ} {ρ : ℂ} (h : ¬ IsNontrivialZero ρ) :
    (WeilExplicit.zeroMult ρ : ℂ) / ρ ^ j = 0 := by
  rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial h]; simp

/-- For j >= 2 the power sums converge absolutely. -/
theorem summable_powerSum {j : ℕ} (hj : 2 ≤ j) :
    Summable (fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℂ) / ρ ^ j) := by
  refine summable_of_zeroBound (C := 9 / 4)
    (b := fun ρ => ‖(WeilExplicit.zeroMult ρ : ℂ) / ρ ^ j‖)
    (fun ρ h => powerSum_term_eq_zero_of_not_nontrivial h) (fun ρ _ _ => le_rfl) ?_ (by norm_num)
  intro ρ h him
  have hρ1 := one_le_norm_of_nontrivial him
  have hmaj := inv_normSq_le_majorant h him
  rw [Complex.normSq_eq_norm_sq] at hmaj
  rw [norm_div, norm_pow, Complex.norm_natCast, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  refine le_trans ?_ hmaj
  rw [one_div]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hρ1 hj)

/-- The power sums are real: conjugation is a symmetry of the divisor. -/
theorem powerSum_conj (j : ℕ) : conj (powerSum j) = powerSum j := by
  unfold powerSum
  rw [← Complex.star_def, tsum_star]
  calc ∑' ρ : ℂ, star ((WeilExplicit.zeroMult ρ : ℂ) / ρ ^ j)
      = ∑' ρ : ℂ, (WeilExplicit.zeroMult (conjEquiv ρ) : ℂ) / (conjEquiv ρ) ^ j := by
        congr 1; funext ρ
        rw [Complex.star_def, map_div₀, map_pow, Complex.conj_natCast]
        simp only [conjEquiv, Equiv.coe_fn_mk, RvMBridge15.zeroMult_conj]
    _ = ∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / ρ ^ j :=
        conjEquiv.tsum_eq (fun ρ => (WeilExplicit.zeroMult ρ : ℂ) / ρ ^ j)

lemma powerSum_re (j : ℕ) : ((powerSum j).re : ℂ) = powerSum j :=
  Complex.conj_eq_iff_re.mp (powerSum_conj j)

/-- At s = 0 the k-th term is m (k+1)! / rho^(k+2). -/
lemma zterm_at_zero (k : ℕ) (ρ : ℂ) :
    zterm k ρ 0 = ((k + 1).factorial : ℂ) * ((WeilExplicit.zeroMult ρ : ℂ) / ρ ^ (k + 2)) := by
  unfold zterm coef
  rw [zero_sub, show (-((k : ℤ) + 2)) = -((k + 2 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
    zpow_natCast]
  have h1 : (-ρ) ^ (k + 2) = (-1) ^ k * ρ ^ (k + 2) := by rw [neg_pow ρ, pow_add]; norm_num
  have h2 : ((-1 : ℂ) ^ k)⁻¹ = (-1) ^ k := by rw [← inv_pow]; norm_num
  rw [h1, mul_inv, h2]
  have h3 : (-1 : ℂ) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  linear_combination ((WeilExplicit.zeroMult ρ : ℂ) * ((k + 1).factorial : ℂ) * (ρ ^ (k + 2))⁻¹) * h3

lemma tsum_zterm_zero (k : ℕ) : ∑' ρ : ℂ, zterm k ρ 0 = ((k + 1).factorial : ℂ) * powerSum (k + 2) := by
  unfold powerSum
  rw [← tsum_mul_left]
  congr 1; funext ρ
  exact zterm_at_zero k ρ

/-- Near 0, deriv (logDeriv xi) is the zero series (given the partial fraction). -/
lemma deriv_logDeriv_xi_eventuallyEq (hP : XiLogDerivDerivEq) :
    deriv (logDeriv xi) =ᶠ[𝓝 (0 : ℂ)] fun z => -∑' ρ : ℂ, zterm 0 ρ z := by
  have hmem : Metric.ball (0 : ℂ) (zeroRadius / 2) ∈ 𝓝 (0 : ℂ) :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by linarith [zeroRadius_pos]))
  filter_upwards [hmem] with z hz
  rw [hP z (not_nontrivialZero_of_mem_ball hz)]
  congr 1
  exact tsum_congr fun ρ => (zterm_zero_eq ρ z).symm

/-- The iterated derivatives of the zero series at 0. -/
lemma iteratedDeriv_tsum_zterm (k : ℕ) :
    iteratedDeriv k (fun z => ∑' ρ : ℂ, zterm 0 ρ z) 0 = ∑' ρ : ℂ, zterm k ρ 0 := by
  refine iteratedDeriv_tsum_ball zterm zbound 0 (zeroRadius / 2) summable_zbound ?_ ?_ k 0
    (Metric.mem_ball_self (by linarith [zeroRadius_pos]))
  · intro k ρ s hs
    by_cases h : IsNontrivialZero ρ
    · refine hasDerivAt_zterm k ρ ?_
      intro hsρ
      exact not_nontrivialZero_of_mem_ball hs (hsρ ▸ h)
    · have h1 : zterm k ρ = fun _ => 0 := funext (zterm_eq_zero_of_not_nontrivial h)
      rw [h1, zterm_eq_zero_of_not_nontrivial h]
      exact hasDerivAt_const _ _
  · intro k ρ s hs
    exact norm_zterm_le_zbound k ρ hs

/-- **Deliverable (1).**  (k+1) Sum' m(rho) rho^{-(k+2)} = -F^{(k)}(0)/k!, F = deriv (logDeriv xi). -/
theorem powerSum_eq_taylor (hP : XiLogDerivDerivEq) (k : ℕ) :
    ((k : ℂ) + 1) * powerSum (k + 2)
      = -(iteratedDeriv k (deriv (logDeriv xi)) 0) / (k.factorial : ℂ) := by
  rw [(deriv_logDeriv_xi_eventuallyEq hP).iteratedDeriv_eq k, iteratedDeriv_fun_neg,
    iteratedDeriv_tsum_zterm, tsum_zterm_zero, neg_neg, Nat.factorial_succ]
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  push_cast
  rw [eq_div_iff hk]
  ring

/-- Corollary: the Taylor coefficients of logDeriv xi at 0 are the negated power sums. -/
theorem powerSum_eq_neg_taylor (hP : XiLogDerivDerivEq) (k : ℕ) :
    powerSum (k + 2) = -(iteratedDeriv (k + 1) (logDeriv xi) 0) / ((k + 1).factorial : ℂ) := by
  have h := powerSum_eq_taylor hP k
  rw [iteratedDeriv_succ', Nat.factorial_succ]
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  push_cast
  rw [div_mul_eq_div_div_swap, ← h, mul_div_cancel_left₀ _ hk1]

/-! ## 3. The paired first power sum (deliverable 2). -/

/-- The paired power sums Sum' m(rho) Re(rho^{-j}). -/
def pairedPowerSum (j : ℕ) : ℂ :=
  ∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) * (((1 / ρ ^ j).re : ℝ) : ℂ)

lemma pairedPowerSum_term_eq_zero_of_not_nontrivial {j : ℕ} {ρ : ℂ} (h : ¬ IsNontrivialZero ρ) :
    (WeilExplicit.zeroMult ρ : ℂ) * (((1 / ρ ^ j).re : ℝ) : ℂ) = 0 := by
  rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial h]; simp

/-- On a large zero, |Re rho^{-j}| <= 1/|rho|^2 for every j >= 1 (j = 1 is where the strip pays). -/
lemma abs_re_inv_pow_le {ρ : ℂ} (h : IsNontrivialZero ρ) (him : 1 ≤ |ρ.im|) {j : ℕ} (hj : 1 ≤ j) :
    |(1 / ρ ^ j).re| ≤ 1 / Complex.normSq ρ := by
  have hρ1 := one_le_norm_of_nontrivial him
  have hns : 0 < Complex.normSq ρ := by rw [Complex.normSq_eq_norm_sq]; positivity
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · have hj1 : j = 1 := by omega
    subst hj1
    rw [pow_one, one_div, Complex.inv_re, abs_of_nonneg (div_nonneg h.2.1.le hns.le)]
    exact div_le_div_of_nonneg_right h.2.2.le hns.le
  · calc |(1 / ρ ^ j).re| ≤ ‖1 / ρ ^ j‖ := Complex.abs_re_le_norm _
      _ = 1 / ‖ρ‖ ^ j := by rw [norm_div, norm_one, norm_pow]
      _ ≤ 1 / ‖ρ‖ ^ 2 := by
          gcongr
      _ = 1 / Complex.normSq ρ := by rw [Complex.normSq_eq_norm_sq]

/-- For j >= 1 the paired power sums converge absolutely. -/
theorem summable_pairedPowerSum {j : ℕ} (hj : 1 ≤ j) :
    Summable (fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℂ) * (((1 / ρ ^ j).re : ℝ) : ℂ)) := by
  refine summable_of_zeroBound (C := 9 / 4)
    (b := fun ρ => ‖(WeilExplicit.zeroMult ρ : ℂ) * (((1 / ρ ^ j).re : ℝ) : ℂ)‖)
    (fun ρ h => pairedPowerSum_term_eq_zero_of_not_nontrivial h) (fun ρ _ _ => le_rfl) ?_
    (by norm_num)
  intro ρ h him
  rw [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  exact (abs_re_inv_pow_le h him hj).trans (inv_normSq_le_majorant h him)

/-- For j >= 2 the paired power sum IS the power sum (which is real). -/
theorem pairedPowerSum_eq_powerSum {j : ℕ} (hj : 2 ≤ j) : pairedPowerSum j = powerSum j := by
  have h1 : pairedPowerSum j = (((powerSum j).re : ℝ) : ℂ) := by
    unfold pairedPowerSum powerSum
    rw [Complex.re_tsum (summable_powerSum hj), Complex.ofReal_tsum]
    congr 1; funext ρ
    rw [show (WeilExplicit.zeroMult ρ : ℂ) / ρ ^ j = (WeilExplicit.zeroMult ρ : ℂ) * (1 / ρ ^ j) by
      ring, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    push_cast; ring
  rw [h1, powerSum_re]

/-! The antisymmetry logDeriv_xi_one_sub and the analyticity logDeriv_xi_analyticAt /
hasDerivAt_logDeriv_xi are the prelude's (RvMBridgeXi). -/

/-- Under NoRealZeroInUnitInterval, xi does not vanish on the real segment [0, 1]. -/
lemma xi_ne_zero_on_segment (hR : NoRealZeroInUnitInterval) (σ : ℝ) :
    xi (σ : ℂ) ≠ 0 := by
  rw [Ne, xi_eq_zero_iff]
  rintro ⟨hz, hre, hre1⟩
  rw [Complex.ofReal_re] at hre hre1
  exact hR σ hre hre1 hz

/-- Under NoRealZeroInUnitInterval every nontrivial zero has nonzero imaginary part. -/
lemma im_ne_zero_of_nontrivial (hR : NoRealZeroInUnitInterval) {ρ : ℂ} (h : IsNontrivialZero ρ) :
    ρ.im ≠ 0 := by
  intro him
  have hρ : ρ = ((ρ.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  have h' := h.1
  rw [hρ] at h'
  exact hR ρ.re h.2.1 h.2.2 h'

lemma ofReal_ne_of_im_ne_zero {ρ : ℂ} (h : ρ.im ≠ 0) (σ : ℝ) : (σ : ℂ) ≠ ρ := by
  intro hσ
  apply h
  rw [← hσ, Complex.ofReal_im]

lemma abs_im_le_norm_ofReal_sub (ρ : ℂ) (σ : ℝ) : |ρ.im| ≤ ‖(σ : ℂ) - ρ‖ := by
  have := Complex.abs_im_le_norm ((σ : ℂ) - ρ)
  rwa [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at this

/-- The uniform bound on the segment: ‖m/(sigma - rho)^2‖ <= m / (Im rho)^2. -/
lemma norm_zterm_zero_ofReal_le {ρ : ℂ} (hρ : ρ.im ≠ 0) (σ : ℝ) :
    ‖zterm 0 ρ σ‖ ≤ (WeilExplicit.zeroMult ρ : ℝ) / ρ.im ^ 2 := by
  rw [zterm_zero_eq, norm_div, Complex.norm_natCast, norm_pow]
  have h1 := abs_im_le_norm_ofReal_sub ρ σ
  have h2 : ρ.im ^ 2 ≤ ‖(σ : ℂ) - ρ‖ ^ 2 := by
    rw [← sq_abs ρ.im]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h3 : 0 < ρ.im ^ 2 := by positivity
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) h3 h2

/-- The summable bound for the segment interchange. -/
def segBound : ℂ → ℝ := zeroBound (9 / 4) (fun ρ => (WeilExplicit.zeroMult ρ : ℝ) / ρ.im ^ 2)

lemma norm_zterm_zero_ofReal_le_segBound (hR : NoRealZeroInUnitInterval) (ρ : ℂ) (σ : ℝ) :
    ‖zterm 0 ρ σ‖ ≤ segBound ρ := by
  refine norm_le_zeroBound (fun ρ h => zterm_eq_zero_of_not_nontrivial h _)
    (fun ρ h _ => norm_zterm_zero_ofReal_le (im_ne_zero_of_nontrivial hR h) σ) ?_ (by norm_num) ρ
  intro ρ h him
  refine (norm_zterm_zero_ofReal_le (im_ne_zero_of_nontrivial hR h) σ).trans ?_
  rw [div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (inv_im_sq_le_majorant h him) (Nat.cast_nonneg _)

/-- Each term is continuous along the real axis (the pole is off the axis, or the term is 0). -/
lemma continuous_zterm_zero_ofReal (hR : NoRealZeroInUnitInterval) (ρ : ℂ) :
    Continuous (fun σ : ℝ => zterm 0 ρ σ) := by
  by_cases h : IsNontrivialZero ρ
  · have hne := im_ne_zero_of_nontrivial hR h
    unfold zterm
    refine continuous_const.mul ?_
    refine Continuous.zpow₀ (Complex.continuous_ofReal.sub continuous_const) _ fun σ => Or.inl ?_
    exact sub_ne_zero.mpr (ofReal_ne_of_im_ne_zero hne σ)
  · simp only [zterm_eq_zero_of_not_nontrivial h]
    exact continuous_const

/-- The segment integral of a term: int_0^1 m/(sigma - rho)^2 = -(m/(1 - rho) + m/rho). -/
lemma integral_zterm_zero (hR : NoRealZeroInUnitInterval) (ρ : ℂ) :
    ∫ σ in (0 : ℝ)..1, zterm 0 ρ σ
      = -((WeilExplicit.zeroMult ρ : ℂ) / (1 - ρ) + (WeilExplicit.zeroMult ρ : ℂ) / ρ) := by
  by_cases h : IsNontrivialZero ρ
  · have hne := im_ne_zero_of_nontrivial hR h
    have hρ0 : ρ ≠ 0 := fun h0 => hne (by rw [h0, Complex.zero_im])
    have hρ1 : (1 : ℂ) - ρ ≠ 0 := fun h1 => hne (by
      have : ρ = 1 := by linear_combination -h1
      rw [this, Complex.one_im])
    -- antiderivative G(z) = -m (z - rho)^{-1}
    have hG : ∀ σ : ℝ, HasDerivAt (fun τ : ℝ => -(WeilExplicit.zeroMult ρ : ℂ) * ((τ : ℂ) - ρ) ^ (-1 : ℤ))
        (zterm 0 ρ σ) σ := by
      intro σ
      have hσ : (σ : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (ofReal_ne_of_im_ne_zero hne σ)
      have h1 := ((hasDerivAt_zpow (-1) ((σ : ℂ) - ρ) (Or.inl hσ)).comp (σ : ℂ)
        ((hasDerivAt_id (σ : ℂ)).sub_const ρ)).const_mul (-(WeilExplicit.zeroMult ρ : ℂ))
      have h2 := h1.comp_ofReal
      refine h2.congr_deriv ?_
      unfold zterm
      rw [coef_zero, show (-(((0 : ℕ) : ℤ) + 2)) = (-1 - 1 : ℤ) by norm_num]
      simp only [mul_one]
      push_cast
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun σ _ => hG σ)
      ((continuous_zterm_zero_ofReal hR ρ).intervalIntegrable _ _)]
    simp only [Complex.ofReal_one, Complex.ofReal_zero, zero_sub, zpow_neg, zpow_one]
    field_simp
    ring
  · simp only [zterm_eq_zero_of_not_nontrivial h, RvMBridge4.zeroMult_eq_zero_of_not_nontrivial h]
    simp

lemma support_zterm_subset (k : ℕ) (s : ℂ) :
    Function.support (fun ρ : ℂ => zterm k ρ s) ⊆ {ρ : ℂ | IsNontrivialZero ρ} := by
  intro ρ hρ
  by_contra h
  exact hρ (zterm_eq_zero_of_not_nontrivial h s)

/-- The interchange on the segment: the zero series integrates termwise, and the resulting
family is summable (the interchange runs over the COUNTABLE zero set, then is transported back
to the family indexed by C, which is supported on the zeros). -/
lemma hasSum_integral_zterm (hR : NoRealZeroInUnitInterval) :
    HasSum (fun ρ : ℂ => ∫ σ in (0 : ℝ)..1, zterm 0 ρ σ)
      (∫ σ in (0 : ℝ)..1, ∑' ρ : ℂ, zterm 0 ρ σ) := by
  set Z : Set ℂ := {ρ : ℂ | IsNontrivialZero ρ} with hZ
  have : Countable Z := nontrivialZeros_countable.to_subtype
  have hsupp : Function.support (fun ρ : ℂ => ∫ σ in (0 : ℝ)..1, zterm 0 ρ σ) ⊆ Z := by
    intro ρ hρ
    by_contra h
    apply hρ
    simp only [zterm_eq_zero_of_not_nontrivial h]
    simp
  rw [← hasSum_subtype_iff_of_support_subset hsupp]
  have hZ' : ∀ σ : ℝ, ∑' ρ : Z, zterm 0 (ρ : ℂ) σ = ∑' ρ : ℂ, zterm 0 ρ σ := fun σ =>
    tsum_subtype_eq_of_support_subset (support_zterm_subset 0 σ)
  simp_rw [← hZ']
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (F := fun (ρ : Z) (σ : ℝ) =>
    zterm 0 (ρ : ℂ) σ) (fun ρ _ => segBound ρ)
    (fun ρ => (continuous_zterm_zero_ofReal hR ρ).aestronglyMeasurable) ?_ ?_ ?_ ?_
  · intro ρ
    exact Filter.Eventually.of_forall fun σ _ => norm_zterm_zero_ofReal_le_segBound hR ρ σ
  · exact Filter.Eventually.of_forall fun σ _ => (summable_zeroBound _ _).subtype _
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun σ _ => Summable.hasSum ?_
    exact (Summable.of_norm_bounded (summable_zeroBound _ _)
      (fun ρ => norm_zterm_zero_ofReal_le_segBound hR ρ σ)).subtype _

/-- The symmetric sum S = Sum' m (1/rho + 1/(1-rho)) equals logDeriv xi 1 - logDeriv xi 0. -/
theorem tsum_inv_add_inv_one_sub (hP : XiLogDerivDerivEq) (hR : NoRealZeroInUnitInterval) :
    HasSum (fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℂ) / ρ + (WeilExplicit.zeroMult ρ : ℂ) / (1 - ρ))
      (logDeriv xi 1 - logDeriv xi 0) := by
  have hseg : ∀ σ : ℝ, σ ∈ Set.uIcc (0 : ℝ) 1 → xi (σ : ℂ) ≠ 0 := fun σ _ =>
    xi_ne_zero_on_segment hR σ
  -- FTC for logDeriv xi along [0, 1]
  have hcont : ContinuousOn (fun σ : ℝ => deriv (logDeriv xi) (σ : ℂ)) (Set.uIcc (0 : ℝ) 1) := by
    intro σ hσ
    have := ((logDeriv_xi_analyticAt (hseg σ hσ)).deriv.continuousAt).comp
      Complex.continuous_ofReal.continuousAt
    exact this.continuousWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun σ : ℝ => logDeriv xi (σ : ℂ)) (f' := fun σ : ℝ => deriv (logDeriv xi) (σ : ℂ))
    (fun σ hσ => (hasDerivAt_logDeriv_xi (hseg σ hσ)).comp_ofReal)
    hcont.intervalIntegrable
  simp only [Complex.ofReal_one, Complex.ofReal_zero] at hftc
  -- the integrand is the negated zero series on the segment
  have hint : ∫ σ in (0 : ℝ)..1, deriv (logDeriv xi) (σ : ℂ)
      = -∫ σ in (0 : ℝ)..1, ∑' ρ : ℂ, zterm 0 ρ σ := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    have hnz : ¬ IsNontrivialZero (σ : ℂ) := fun hz => hseg σ hσ ((xi_eq_zero_iff _).mpr hz)
    rw [hP _ hnz]
    congr 1
    exact tsum_congr fun ρ => (zterm_zero_eq ρ σ).symm
  have hsum := hasSum_integral_zterm hR
  simp only [integral_zterm_zero hR] at hsum
  have hsum' := hsum.neg
  simp only [neg_neg] at hsum'
  rw [← hftc, hint]
  have hfun : (fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℂ) / ρ + (WeilExplicit.zeroMult ρ : ℂ) / (1 - ρ))
      = fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℂ) / (1 - ρ) + (WeilExplicit.zeroMult ρ : ℂ) / ρ := by
    funext ρ; ring
  rw [hfun]
  exact hsum'

/-- The reflection fold: the antisymmetric family m (1/(1-rho) - 1/conj rho) sums to 0. -/
def refTerm (ρ : ℂ) : ℂ := (WeilExplicit.zeroMult ρ : ℂ) * (1 / (1 - ρ) - 1 / conj ρ)

lemma refTerm_reflect (ρ : ℂ) : refTerm (reflect ρ) = -refTerm ρ := by
  unfold refTerm
  rw [RvMBridge6.zeroMult_reflect]
  have h1 : (1 : ℂ) - reflect ρ = conj ρ := by unfold reflect; ring
  have h2 : conj (reflect ρ) = 1 - ρ := by unfold reflect; rw [map_sub, map_one, Complex.conj_conj]
  rw [h1, h2]
  ring

lemma refTerm_eq_zero_of_not_nontrivial {ρ : ℂ} (h : ¬ IsNontrivialZero ρ) : refTerm ρ = 0 := by
  unfold refTerm
  rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial h]; simp

lemma summable_refTerm : Summable refTerm := by
  refine summable_of_zeroBound (C := 9 / 4) (b := fun ρ => ‖refTerm ρ‖)
    (fun ρ h => refTerm_eq_zero_of_not_nontrivial h) (fun ρ _ _ => le_rfl) ?_ (by norm_num)
  intro ρ h him
  have hρ0 : ρ ≠ 0 := fun h0 => by
    have := h.2.1; rw [h0, Complex.zero_re] at this; exact lt_irrefl _ this
  have hρ1 : (1 : ℂ) - ρ ≠ 0 := fun h1 => by
    have : ρ = 1 := by linear_combination -h1
    have h2 := h.2.2; rw [this, Complex.one_re] at h2; exact lt_irrefl _ h2
  have hc : conj ρ ≠ 0 := by rwa [Ne, map_eq_zero]
  unfold refTerm
  rw [norm_mul, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have hre : (ρ.re : ℂ) = (ρ + conj ρ) / 2 := by rw [Complex.add_conj]; push_cast; ring
  have hid : 1 / (1 - ρ) - 1 / conj ρ = (2 * (ρ.re : ℂ) - 1) / ((1 - ρ) * conj ρ) := by
    rw [div_sub_div _ _ hρ1 hc, hre]; ring
  rw [hid, norm_div, norm_mul, Complex.norm_conj]
  have hnum : ‖2 * (ρ.re : ℂ) - 1‖ ≤ 1 := by
    rw [show (2 * (ρ.re : ℂ) - 1) = ((2 * ρ.re - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_le]
    constructor <;> linarith [h.2.1, h.2.2]
  have him' : |ρ.im| ≤ ‖1 - ρ‖ := by
    have := Complex.abs_im_le_norm (1 - ρ)
    rwa [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at this
  have himρ : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
  have hpos : 0 < |ρ.im| := by linarith
  have hden : |ρ.im| * |ρ.im| ≤ ‖1 - ρ‖ * ‖ρ‖ := mul_le_mul him' himρ (abs_nonneg _) (norm_nonneg _)
  calc ‖2 * (ρ.re : ℂ) - 1‖ / (‖1 - ρ‖ * ‖ρ‖) ≤ 1 / (|ρ.im| * |ρ.im|) :=
        div_le_div₀ zero_le_one hnum (by positivity) hden
      _ = 1 / ρ.im ^ 2 := by rw [← sq, sq_abs]
      _ ≤ _ := inv_im_sq_le_majorant h him

lemma tsum_refTerm : ∑' ρ : ℂ, refTerm ρ = 0 := by
  have h : ∑' ρ : ℂ, refTerm ρ = ∑' ρ : ℂ, refTerm (RvMBridge6.reflectEquiv ρ) :=
    (RvMBridge6.reflectEquiv.tsum_eq refTerm).symm
  have h2 : ∀ ρ, refTerm (RvMBridge6.reflectEquiv ρ) = -refTerm ρ := fun ρ => refTerm_reflect ρ
  simp_rw [h2, tsum_neg] at h
  linear_combination (1 / 2 : ℂ) * h

/-- **Deliverable (2).**  Sum' m(rho) Re(1/rho) = -logDeriv xi 0 (given the partial fraction and the
real-segment nonvanishing). -/
theorem pairedPowerSum_one_eq (hP : XiLogDerivDerivEq) (hR : NoRealZeroInUnitInterval) :
    pairedPowerSum 1 = -logDeriv xi 0 := by
  have hS := tsum_inv_add_inv_one_sub hP hR
  have hanti : logDeriv xi 1 = -logDeriv xi 0 := by
    have := logDeriv_xi_one_sub 0
    rwa [sub_zero] at this
  -- fold: m(1/rho + 1/(1-rho)) = 2 m Re(1/rho) + refTerm rho
  have hfold : ∀ ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / ρ + (WeilExplicit.zeroMult ρ : ℂ) / (1 - ρ)
      = 2 * ((WeilExplicit.zeroMult ρ : ℂ) * (((1 / ρ ^ 1).re : ℝ) : ℂ)) + refTerm ρ := by
    intro ρ
    unfold refTerm
    have h1 : (((1 / ρ ^ 1).re : ℝ) : ℂ) = (1 / ρ + conj (1 / ρ)) / 2 := by
      rw [Complex.add_conj, pow_one]; push_cast; ring
    rw [h1, map_div₀, map_one]
    ring
  have hpaired := summable_pairedPowerSum (j := 1) le_rfl
  have hsum2 : HasSum (fun ρ : ℂ => 2 * ((WeilExplicit.zeroMult ρ : ℂ) * (((1 / ρ ^ 1).re : ℝ) : ℂ))
      + refTerm ρ) (2 * pairedPowerSum 1 + 0) := by
    rw [← tsum_refTerm]
    unfold pairedPowerSum
    rw [← tsum_mul_left]
    exact (hpaired.mul_left 2).hasSum.add summable_refTerm.hasSum
  simp_rw [hfold] at hS
  have := hS.unique hsum2
  rw [hanti] at this
  linear_combination -this / 2

/-! ## 4. The closed forms at s = 1 (deliverable 3): eta from riemannZeta_1, the digamma tower
at 1/2 from the partial-fraction series, and logDeriv xi near 1. -/

/-! ### 4a. zetaLogDerivReg = -logDeriv riemannZeta_1 near 1. -/

/-- For s /= 1 with zeta_1(s) /= 0: logDeriv zeta s = -1/(s-1) + logDeriv zeta_1 s. -/
lemma logDeriv_zeta_eq_near_one {s : ℂ} (hs1 : s ≠ 1) (hz : riemannZeta₁ s ≠ 0) :
    logDeriv riemannZeta s = -(1 / (s - 1)) + logDeriv riemannZeta₁ s := by
  have hev : riemannZeta =ᶠ[𝓝 s] fun u => (u - 1)⁻¹ * riemannZeta₁ u := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (show s ∈ ({1}ᶜ : Set ℂ) from hs1)] with u hu
    exact riemannZeta_eq_inv_sub_mul hu
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have heq : logDeriv riemannZeta s = logDeriv (fun u => (u - 1)⁻¹ * riemannZeta₁ u) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  have hd : HasDerivAt (fun u : ℂ => (u - 1)⁻¹) (-1 / (s - 1) ^ 2) s :=
    ((hasDerivAt_id' s).sub_const 1).inv hs1'
  rw [heq, logDeriv_mul (f := fun u : ℂ => (u - 1)⁻¹) (g := riemannZeta₁) s (inv_ne_zero hs1') hz
    hd.differentiableAt (differentiable_riemannZeta₁ s)]
  congr 1
  rw [logDeriv_apply, hd.deriv]
  field_simp

/-- zetaLogDerivReg agrees with -logDeriv zeta_1 on a neighbourhood of 1 (including at 1, where
both are -gamma: deriv_riemannZeta_1_one). -/
lemma zetaLogDerivReg_eventuallyEq :
    zetaLogDerivReg =ᶠ[𝓝 (1 : ℂ)] fun s => -logDeriv riemannZeta₁ s := by
  filter_upwards [riemannZeta₁_ne_zero_of_near_one] with s hs
  by_cases hs1 : s = 1
  · subst hs1
    unfold zetaLogDerivReg
    rw [Function.update_self, logDeriv_apply, deriv_riemannZeta₁_one, riemannZeta₁_one, div_one]
  · unfold zetaLogDerivReg
    rw [Function.update_of_ne hs1, logDeriv_zeta_eq_near_one hs1 hs]
    ring

lemma logDeriv_zeta₁_analyticAt : AnalyticAt ℂ (logDeriv riemannZeta₁) 1 := by
  have h : logDeriv riemannZeta₁ = fun z => deriv riemannZeta₁ z / riemannZeta₁ z :=
    funext (logDeriv_apply riemannZeta₁)
  rw [h]
  exact (differentiable_riemannZeta₁.analyticAt 1).deriv.div (differentiable_riemannZeta₁.analyticAt 1)
    (by rw [riemannZeta₁_one]; exact one_ne_zero)

/-- eta j = -(logDeriv zeta_1)^{(j)}(1) / j!. -/
theorem eta_eq (j : ℕ) : BombieriLagarias.eta j = -(iteratedDeriv j (logDeriv riemannZeta₁) 1) / (j.factorial : ℂ) := by
  unfold BombieriLagarias.eta
  rw [zetaLogDerivReg_eventuallyEq.iteratedDeriv_eq, iteratedDeriv_fun_neg, neg_div]

/-! ### 4b. The digamma tower at 1/2. -/

/-- The k-th derivative coefficient of -2/(s + 2n + 2): -2 (-1)^k k!. -/
def dcoef (k : ℕ) : ℂ := -2 * (-1) ^ k * (k.factorial : ℂ)

lemma dcoef_succ (k : ℕ) : dcoef (k + 1) = dcoef k * (-((k : ℂ) + 1)) := by
  unfold dcoef
  rw [Nat.factorial_succ]
  push_cast
  ring

lemma norm_dcoef (k : ℕ) : ‖dcoef k‖ = 2 * (k.factorial : ℝ) := by
  unfold dcoef
  rw [norm_mul, norm_mul, norm_neg, norm_pow, norm_neg, norm_one, one_pow, mul_one,
    Complex.norm_natCast, Complex.norm_ofNat]

/-- The k-th derivative in s of the digamma series term 1/(n+1) - 1/(s/2 + n + 1)
= 1/(n+1) - 2/(s + 2n + 2). -/
def dterm : ℕ → ℕ → ℂ → ℂ
  | 0, n, s => 1 / ((n : ℂ) + 1) + dcoef 0 * (s + 2 * n + 2) ^ (-1 : ℤ)
  | k + 1, n, s => dcoef (k + 1) * (s + 2 * n + 2) ^ (-((k : ℤ) + 2))

/-- The ball about 1 of radius 1/2. -/
lemma re_pos_of_mem_ball {s : ℂ} (hs : s ∈ Metric.ball (1 : ℂ) (1 / 2)) : 1 / 2 < s.re := by
  rw [Metric.mem_ball, Complex.dist_eq] at hs
  have := Complex.abs_re_le_norm (s - 1)
  rw [Complex.sub_re, Complex.one_re] at this
  have := (abs_lt.mp (this.trans_lt hs)).1
  linarith

lemma norm_le_of_mem_ball {s : ℂ} (hs : s ∈ Metric.ball (1 : ℂ) (1 / 2)) : ‖s‖ ≤ 3 / 2 := by
  rw [Metric.mem_ball, Complex.dist_eq] at hs
  have := norm_sub_norm_le s 1
  rw [norm_one] at this
  linarith

lemma norm_shift_ge {s : ℂ} (hs : s ∈ Metric.ball (1 : ℂ) (1 / 2)) (n : ℕ) :
    2 * ((n : ℝ) + 1) ≤ ‖s + 2 * n + 2‖ := by
  have h1 := re_pos_of_mem_ball hs
  have h2 := Complex.re_le_norm (s + 2 * n + 2)
  simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.natCast_re,
    Complex.natCast_im, mul_zero, sub_zero] at h2
  linarith

lemma shift_ne_zero {s : ℂ} (hs : s ∈ Metric.ball (1 : ℂ) (1 / 2)) (n : ℕ) : s + 2 * n + 2 ≠ 0 := by
  intro h
  have := norm_shift_ge hs n
  rw [h, norm_zero] at this
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

lemma hasDerivAt_dterm (k n : ℕ) {s : ℂ} (hs : s ∈ Metric.ball (1 : ℂ) (1 / 2)) :
    HasDerivAt (dterm k n) (dterm (k + 1) n s) s := by
  have hne := shift_ne_zero hs n
  have hlin : HasDerivAt (fun y : ℂ => id y + 2 * n + 2) 1 s := by
    simpa using ((hasDerivAt_id s).add_const (2 * (n : ℂ))).add_const 2
  cases k with
  | zero =>
    have hfun : dterm 0 n = fun y => 1 / ((n : ℂ) + 1)
        + dcoef 0 * ((fun x : ℂ => x ^ (-1 : ℤ)) ∘ fun y => id y + 2 * n + 2) y := by
      funext y; simp only [dterm, Function.comp_apply, id_eq]
    rw [hfun]
    refine ((((hasDerivAt_zpow (-1) _ (Or.inl hne)).comp s hlin).const_mul (dcoef 0)).const_add
      (1 / ((n : ℂ) + 1))).congr_deriv ?_
    simp only [dterm, dcoef, mul_one]
    norm_num
  | succ k =>
    have hfun : dterm (k + 1) n = fun y => dcoef (k + 1)
        * ((fun x : ℂ => x ^ (-((k : ℤ) + 2))) ∘ fun y => id y + 2 * n + 2) y := by
      funext y; rfl
    rw [hfun]
    refine (((hasDerivAt_zpow (-((k : ℤ) + 2)) _ (Or.inl hne)).comp s hlin).const_mul
      (dcoef (k + 1))).congr_deriv ?_
    simp only [dterm, mul_one]
    rw [dcoef_succ (k + 1), show (-((k : ℤ) + 2) - 1) = -(((k + 1 : ℕ) : ℤ) + 2) by push_cast; ring]
    push_cast
    ring

/-- The uniform bound on the ball: 2 k! / (n+1)^2. -/
def dbound (k n : ℕ) : ℝ := 2 * (k.factorial : ℝ) / ((n : ℝ) + 1) ^ 2

lemma summable_dbound (k : ℕ) : Summable (dbound k) := by
  have h : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    refine h.congr fun n => ?_
    push_cast; ring
  have e : dbound k = fun n : ℕ => 2 * (k.factorial : ℝ) * (1 / ((n : ℝ) + 1) ^ 2) := by
    funext n; unfold dbound; ring
  rw [e]
  exact h.mul_left _

lemma norm_dterm_le (k n : ℕ) {s : ℂ} (hs : s ∈ Metric.ball (1 : ℂ) (1 / 2)) :
    ‖dterm k n s‖ ≤ dbound k n := by
  have hge := norm_shift_ge hs n
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hne := shift_ne_zero hs n
  cases k with
  | zero =>
    have hid : dterm 0 n s = s / (((n : ℂ) + 1) * (s + 2 * n + 2)) := by
      simp only [dterm, dcoef]
      have hn1' : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast hn1.ne'
      rw [zpow_neg_one, eq_div_iff (mul_ne_zero hn1' hne), one_div]
      have e1 : ((n : ℂ) + 1)⁻¹ * ((n : ℂ) + 1) = 1 := inv_mul_cancel₀ hn1'
      have e2 : (s + 2 * n + 2)⁻¹ * (s + 2 * n + 2) = 1 := inv_mul_cancel₀ hne
      linear_combination (s + 2 * n + 2) * e1 + (-2 * ((n : ℂ) + 1)) * e2
    rw [hid, norm_div, norm_mul, show ((n : ℂ) + 1) = ((n + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn1]
    unfold dbound
    rw [Nat.factorial_zero, Nat.cast_one, mul_one]
    have hs' := norm_le_of_mem_ball hs
    calc ‖s‖ / (((n : ℝ) + 1) * ‖s + 2 * n + 2‖) ≤ (3 / 2) / (((n : ℝ) + 1) * (2 * ((n : ℝ) + 1))) :=
          div_le_div₀ (by positivity) hs' (by positivity) (by gcongr)
      _ ≤ 2 / ((n : ℝ) + 1) ^ 2 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  | succ k =>
    simp only [dterm]
    rw [norm_mul, norm_dcoef, norm_zpow, show (-((k : ℤ) + 2)) = -((k + 2 : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast]
    unfold dbound
    have h1 : ((n : ℝ) + 1) ^ 2 ≤ ‖s + 2 * n + 2‖ ^ (k + 2) := by
      calc ((n : ℝ) + 1) ^ 2 ≤ (2 * ((n : ℝ) + 1)) ^ 2 := by gcongr; linarith
        _ ≤ (2 * ((n : ℝ) + 1)) ^ (k + 2) := pow_le_pow_right₀ (by linarith) (by omega)
        _ ≤ ‖s + 2 * n + 2‖ ^ (k + 2) := pow_le_pow_left₀ (by positivity) hge _
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) h1) (by positivity)

/-- The digamma tail function D(s) = Sum'_n (1/(n+1) - 2/(s + 2n + 2)). -/
def dtail (s : ℂ) : ℂ := ∑' n : ℕ, dterm 0 n s

lemma iteratedDeriv_dtail (k : ℕ) : iteratedDeriv k dtail 1 = ∑' n : ℕ, dterm k n 1 :=
  iteratedDeriv_tsum_ball dterm dbound 1 (1 / 2) summable_dbound
    (fun k n s hs => hasDerivAt_dterm k n hs) (fun k n s hs => norm_dterm_le k n hs) k 1
    (Metric.mem_ball_self (by norm_num))

lemma dtail_analyticAt : AnalyticAt ℂ dtail 1 :=
  analyticAt_tsum_ball dterm dbound 1 (1 / 2) summable_dbound
    (fun k n s hs => hasDerivAt_dterm k n hs) (fun k n s hs => norm_dterm_le k n hs)
    (Metric.mem_ball_self (by norm_num))

/-- On the ball, s/2 is not an integer. -/
lemma half_mem_integerComplement {s : ℂ} (hs : s ∈ Metric.ball (1 : ℂ) (1 / 2)) :
    s / 2 ∈ Complex.integerComplement := by
  rw [Complex.integerComplement_eq]
  rintro ⟨m, hm⟩
  have h1 := re_pos_of_mem_ball hs
  have h2 : s.re < 3 / 2 := by
    rw [Metric.mem_ball, Complex.dist_eq] at hs
    have := Complex.abs_re_le_norm (s - 1)
    rw [Complex.sub_re, Complex.one_re] at this
    have := (abs_lt.mp (this.trans_lt hs)).2
    linarith
  have hre : (m : ℝ) = s.re / 2 := by
    have := congrArg Complex.re hm
    simpa using this
  have h3 : (0 : ℝ) < m := by rw [hre]; linarith
  have h4 : (m : ℝ) < 1 := by rw [hre]; linarith
  have h3' : (0 : ℤ) < m := by exact_mod_cast h3
  have h4' : m < (1 : ℤ) := by exact_mod_cast h4
  omega

/-- psi(s/2) = -gamma - 2/s + D(s) on the ball (Zeta23's digamma partial fractions at z = s/2). -/
lemma psiHalf_eq {s : ℂ} (hs : s ∈ Metric.ball (1 : ℂ) (1 / 2)) :
    Complex.digamma (s / 2) = -(Real.eulerMascheroniConstant : ℂ) + (-2) * s⁻¹ + dtail s := by
  have h := Zeta23.DigammaSeries.digamma_series (half_mem_integerComplement hs)
  rw [h]
  have hs0 : s ≠ 0 := fun h0 => by
    have := re_pos_of_mem_ball hs; rw [h0, Complex.zero_re] at this; linarith
  have hD : dtail s = ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (s / 2 + n + 1)) := by
    unfold dtail
    refine tsum_congr fun n => ?_
    have hne := shift_ne_zero hs n
    have hne' : s / 2 + n + 1 ≠ 0 := by
      intro h0; apply hne; linear_combination 2 * h0
    simp only [dterm, dcoef, zpow_neg_one]
    field_simp
    ring
  rw [hD]
  field_simp
  ring

lemma psiHalf_eventuallyEq :
    (fun s : ℂ => Complex.digamma (s / 2)) =ᶠ[𝓝 (1 : ℂ)]
      fun s => -(Real.eulerMascheroniConstant : ℂ) + (-2) * s⁻¹ + dtail s := by
  filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num :
    (0 : ℝ) < 1 / 2))] with s hs
  exact psiHalf_eq hs

lemma psiHalf_analyticAt : AnalyticAt ℂ (fun s : ℂ => Complex.digamma (s / 2)) 1 := by
  refine AnalyticAt.congr ?_ psiHalf_eventuallyEq.symm
  refine (analyticAt_const.add (analyticAt_const.mul ?_)).add dtail_analyticAt
  exact analyticAt_id.inv one_ne_zero

lemma summable_inv_nat_pow {m : ℕ} (hm : 2 ≤ m) : Summable (fun n : ℕ => 1 / (n : ℂ) ^ m) := by
  have h := Real.summable_one_div_nat_pow.mpr (show 1 < m by omega)
  have h' := Complex.summable_ofReal.mpr h
  refine h'.congr fun n => ?_
  push_cast; ring

lemma summable_even_inv_pow {m : ℕ} (hm : 2 ≤ m) :
    Summable (fun n : ℕ => 1 / ((2 * n : ℕ) : ℂ) ^ m) :=
  (summable_inv_nat_pow hm).comp_injective (mul_right_injective₀ two_ne_zero)

lemma summable_odd_inv_pow' {m : ℕ} (hm : 2 ≤ m) :
    Summable (fun n : ℕ => 1 / ((2 * n + 1 : ℕ) : ℂ) ^ m) :=
  (summable_inv_nat_pow hm).comp_injective (fun a b h => by omega)

lemma summable_odd_inv_pow {m : ℕ} (hm : 2 ≤ m) :
    Summable (fun n : ℕ => 1 / (2 * (n : ℂ) + 1) ^ m) :=
  (summable_odd_inv_pow' hm).congr fun n => by push_cast; ring

/-- Sum over the odd naturals: Sum'_n 1/(2n+1)^m = (1 - 2^{-m}) zeta(m) for m >= 2. -/
theorem tsum_odd_inv_pow {m : ℕ} (hm : 2 ≤ m) :
    ∑' n : ℕ, 1 / (2 * (n : ℂ) + 1) ^ m = (1 - 1 / (2 : ℂ) ^ m) * riemannZeta m := by
  have hsplit := tsum_even_add_odd (f := fun n : ℕ => 1 / (n : ℂ) ^ m) (summable_even_inv_pow hm)
    (summable_odd_inv_pow' hm)
  have hζ : riemannZeta m = ∑' n : ℕ, 1 / (n : ℂ) ^ m := zeta_nat_eq_tsum_of_gt_one (by omega)
  have he : ∑' n : ℕ, 1 / ((2 * n : ℕ) : ℂ) ^ m = (1 / (2 : ℂ) ^ m) * riemannZeta m := by
    rw [hζ, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    push_cast
    rw [mul_pow, one_div_mul_one_div]
  have ho : ∑' n : ℕ, 1 / ((2 * n + 1 : ℕ) : ℂ) ^ m = ∑' n : ℕ, 1 / (2 * (n : ℂ) + 1) ^ m :=
    tsum_congr fun n => by push_cast; ring
  rw [he, ho, ← hζ] at hsplit
  linear_combination hsplit

/-- The k-th derivative of psi(s/2) at s = 1, k >= 1: -2 (-1)^k k! (1 - 2^{-(k+1)}) zeta(k+1). -/
theorem iteratedDeriv_psiHalf (k : ℕ) :
    iteratedDeriv (k + 1) (fun s : ℂ => Complex.digamma (s / 2)) 1
      = -2 * (-1) ^ (k + 1) * ((k + 1).factorial : ℂ) * (1 - 1 / (2 : ℂ) ^ (k + 2))
        * riemannZeta ((k + 2 : ℕ) : ℂ) := by
  rw [psiHalf_eventuallyEq.iteratedDeriv_eq]
  have h1 : AnalyticAt ℂ (fun s : ℂ => -(Real.eulerMascheroniConstant : ℂ) + (-2) * s⁻¹) 1 :=
    analyticAt_const.add (analyticAt_const.mul (analyticAt_id.inv one_ne_zero))
  rw [show (fun s : ℂ => -(Real.eulerMascheroniConstant : ℂ) + (-2) * s⁻¹ + dtail s)
      = (fun s : ℂ => -(Real.eulerMascheroniConstant : ℂ) + (-2) * s⁻¹) + dtail from rfl,
    iteratedDeriv_add h1.contDiffAt dtail_analyticAt.contDiffAt,
    iteratedDeriv_const_add (Nat.succ_pos k), iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate,
    iter_deriv_inv, iteratedDeriv_dtail]
  -- the tail at 1: Sum'_n dcoef (k+1) / (2n+3)^(k+2)
  have htail : ∑' n : ℕ, dterm (k + 1) n 1
      = dcoef (k + 1) * ∑' n : ℕ, 1 / (2 * ((n + 1 : ℕ) : ℂ) + 1) ^ (k + 2) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [dterm]
    rw [show (-((k : ℤ) + 2)) = -((k + 2 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
    push_cast
    ring
  rw [htail]
  have hodd := summable_odd_inv_pow (m := k + 2) (by omega)
  have hshift := hodd.tsum_eq_zero_add
  rw [tsum_odd_inv_pow (by omega)] at hshift
  simp only [Nat.cast_zero, mul_zero, zero_add, one_pow, div_one] at hshift
  have hshift' : ∑' n : ℕ, 1 / (2 * ((n + 1 : ℕ) : ℂ) + 1) ^ (k + 2)
      = (1 - 1 / (2 : ℂ) ^ (k + 2)) * riemannZeta ((k + 2 : ℕ) : ℂ) - 1 := by
    rw [hshift]; ring
  rw [hshift']
  unfold dcoef
  rw [one_zpow]
  simp only [Nat.succ_eq_add_one]
  push_cast
  ring

/-- The digamma-side Taylor coefficients at 1: A k := (d^k/ds^k)[-(log pi)/2 + (1/2) psi(s/2)](1)/k!. -/
def archCoeff (k : ℕ) : ℂ :=
  iteratedDeriv k (fun s : ℂ => -(Real.log Real.pi : ℂ) / 2 + (1 / 2 : ℂ) * Complex.digamma (s / 2)) 1
    / (k.factorial : ℂ)

lemma archFn_analyticAt :
    AnalyticAt ℂ (fun s : ℂ => -(Real.log Real.pi : ℂ) / 2 + (1 / 2 : ℂ) * Complex.digamma (s / 2)) 1 :=
  analyticAt_const.add (analyticAt_const.mul psiHalf_analyticAt)

theorem archCoeff_zero :
    archCoeff 0 = -(Real.log Real.pi : ℂ) / 2 - (Real.log 2 : ℂ) - (Real.eulerMascheroniConstant : ℂ) / 2 := by
  unfold archCoeff
  rw [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, Complex.digamma_one_half,
    Complex.ofReal_log zero_le_two]
  push_cast
  ring

theorem archCoeff_succ (k : ℕ) :
    archCoeff (k + 1) = (-1) ^ (k + 2) * (1 - 1 / (2 : ℂ) ^ (k + 2)) * riemannZeta ((k + 2 : ℕ) : ℂ) := by
  unfold archCoeff
  rw [iteratedDeriv_const_add (Nat.succ_pos k), iteratedDeriv_const_mul_field, iteratedDeriv_psiHalf]
  have hk : ((k + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast (k + 1).factorial_ne_zero
  field_simp
  ring

/-! ### 4c. logDeriv xi near 1 and its Taylor coefficients. -/

/-- The closed form of logDeriv xi at s /= 0, 1 with zeta(s) /= 0 and Re s > 0. -/
lemma logDeriv_xi_eq_closed {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hζ : riemannZeta s ≠ 0)
    (hre : 0 < s.re) (hz1 : riemannZeta₁ s ≠ 0) :
    logDeriv xi s = 1 / s + (-(Real.log Real.pi : ℂ) / 2 + (1 / 2 : ℂ) * Complex.digamma (s / 2))
      + logDeriv riemannZeta₁ s := by
  have hev : xi =ᶠ[𝓝 s] fun u => (u * (u - 1) / 2) * completedRiemannZeta u := by
    have hopen : IsOpen (({0, 1} : Set ℂ)ᶜ) := (Set.toFinite _).isClosed.isOpen_compl
    filter_upwards [hopen.mem_nhds (by simp [hs0, hs1])] with u hu
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hu
    exact xi_eq u hu.1 hu.2
  have hΛ : completedRiemannZeta s ≠ 0 := by
    rw [Ne, RvM.completedRiemannZeta_eq_zero_iff]
    exact fun h => hζ h.1
  have hpoly : s * (s - 1) / 2 ≠ 0 := by
    have := sub_ne_zero.mpr hs1
    simp [hs0, this]
  have heq : logDeriv xi s = logDeriv (fun u => (u * (u - 1) / 2) * completedRiemannZeta u) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [heq, logDeriv_mul s hpoly hΛ (by fun_prop) (differentiableAt_completedZeta hs0 hs1),
    Zeta23.WeilEF.logDeriv_completedZeta s hs1 hζ hre, Zeta23.RvM.logDeriv_Gammaℝ hre,
    logDeriv_zeta_eq_near_one hs1 hz1]
  have hd : HasDerivAt (fun u : ℂ => u * (u - 1) / 2) ((2 * s - 1) / 2) s := by
    have := ((hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)).div_const 2
    refine this.congr_deriv ?_
    simp only [id_eq]; ring
  rw [logDeriv_apply, hd.deriv]
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp
  ring

/-- The closed-form function near 1. -/
def closedFn (s : ℂ) : ℂ :=
  1 / s + (-(Real.log Real.pi : ℂ) / 2 + (1 / 2 : ℂ) * Complex.digamma (s / 2)) + logDeriv riemannZeta₁ s

lemma closedFn_analyticAt : AnalyticAt ℂ closedFn 1 := by
  unfold closedFn
  exact ((analyticAt_const.div analyticAt_id one_ne_zero).add archFn_analyticAt).add
    logDeriv_zeta₁_analyticAt

/-- logDeriv xi = closedFn on a neighbourhood of 1 (the punctured identity extends by continuity,
both sides being analytic at 1: xi(1) = 1/2 /= 0). -/
theorem logDeriv_xi_eventuallyEq_one : logDeriv xi =ᶠ[𝓝 (1 : ℂ)] closedFn := by
  have hpunct : ∀ᶠ s in 𝓝 (1 : ℂ), s ≠ 1 → logDeriv xi s = closedFn s := by
    have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [riemannZeta_eventually_ne_zero_nhds_one, riemannZeta₁_ne_zero_of_near_one,
      hopen.mem_nhds (by simp)] with s hζ hz1 hre hs1
    have hs0 : s ≠ 0 := fun h => by simp [h] at hre
    exact logDeriv_xi_eq_closed hs0 hs1 hζ hre hz1
  have hL : ContinuousAt (logDeriv xi) 1 :=
    (logDeriv_xi_analyticAt (by rw [xi_one]; norm_num)).continuousAt
  have hR : ContinuousAt closedFn 1 := closedFn_analyticAt.continuousAt
  have hat : logDeriv xi 1 = closedFn 1 := eq_of_continuousAt_of_eventually_ne hL hR hpunct
  filter_upwards [hpunct] with s hs
  by_cases hs1 : s = 1
  · rw [hs1]; exact hat
  · exact hs hs1

/-- The Taylor coefficients of logDeriv xi at 1. -/
def taylorOne (k : ℕ) : ℂ := iteratedDeriv k (logDeriv xi) 1 / (k.factorial : ℂ)

lemma iteratedDeriv_one_div (k : ℕ) : iteratedDeriv k (fun s : ℂ => 1 / s) 1 = (-1) ^ k * (k.factorial : ℂ) := by
  rw [show (fun s : ℂ => 1 / s) = Inv.inv from funext fun s => one_div s, iteratedDeriv_eq_iterate,
    iter_deriv_inv, one_zpow, mul_one]

/-- **Deliverable (3).**  taylorOne k = (-1)^k + archCoeff k - eta k. -/
theorem taylorOne_eq (k : ℕ) : taylorOne k = (-1) ^ k + archCoeff k - BombieriLagarias.eta k := by
  unfold taylorOne
  rw [logDeriv_xi_eventuallyEq_one.iteratedDeriv_eq]
  have h1 : AnalyticAt ℂ (fun s : ℂ => 1 / s) 1 := analyticAt_const.div analyticAt_id one_ne_zero
  rw [show closedFn = ((fun s : ℂ => 1 / s)
      + fun s : ℂ => -(Real.log Real.pi : ℂ) / 2 + (1 / 2 : ℂ) * Complex.digamma (s / 2))
      + logDeriv riemannZeta₁ from rfl,
    iteratedDeriv_add (h1.add archFn_analyticAt).contDiffAt logDeriv_zeta₁_analyticAt.contDiffAt,
    iteratedDeriv_add h1.contDiffAt archFn_analyticAt.contDiffAt, iteratedDeriv_one_div, eta_eq]
  unfold archCoeff
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  field_simp
  ring

/-! ## 5. Assembly (deliverable 4). -/

/-- The Taylor coefficients of logDeriv xi at 0. -/
def taylorZero (k : ℕ) : ℂ := iteratedDeriv k (logDeriv xi) 0 / (k.factorial : ℂ)

lemma iter_deriv_comp_add_const (f : ℂ → ℂ) (a : ℂ) (k : ℕ) :
    deriv^[k] (fun x => f (x + a)) = fun x => deriv^[k] f (x + a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    funext x
    rw [Function.iterate_succ_apply']
    exact deriv_comp_add_const _ _ _

/-- Taylor data at 0 from Taylor data at 1, by the antisymmetry logDeriv xi (1-s) = -logDeriv xi s. -/
theorem taylorZero_eq (k : ℕ) : taylorZero k = (-1) ^ (k + 1) * taylorOne k := by
  unfold taylorZero taylorOne
  set g : ℂ → ℂ := fun u => logDeriv xi (u + 1) with hg
  have hfun : logDeriv xi = fun s => -g (-s) := by
    funext s
    simp only [hg]
    rw [show -s + 1 = 1 - s by ring, logDeriv_xi_one_sub, neg_neg]
  have h1 : iteratedDeriv k (logDeriv xi) 0 = -((-1 : ℂ) ^ k * iteratedDeriv k g 0) := by
    rw [hfun, iteratedDeriv_fun_neg, iteratedDeriv_comp_neg, neg_zero, smul_eq_mul]
  have h2 : iteratedDeriv k g 0 = iteratedDeriv k (logDeriv xi) 1 := by
    rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, hg, iter_deriv_comp_add_const]
    simp
  rw [h1, h2]
  ring

/-- Every paired power sum is a negated Taylor coefficient at 0 (j = 1 from the segment, j >= 2 from
the derivative). -/
theorem pairedPowerSum_succ_eq (hP : XiLogDerivDerivEq) (hR : NoRealZeroInUnitInterval) (m : ℕ) :
    pairedPowerSum (m + 1) = -taylorZero m := by
  cases m with
  | zero =>
    rw [pairedPowerSum_one_eq hP hR]
    unfold taylorZero
    rw [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  | succ k =>
    rw [pairedPowerSum_eq_powerSum (by omega), powerSum_eq_neg_taylor hP k]
    unfold taylorZero
    rw [neg_div]

/-- Re K_n(rho) = Sum_{m<n} (-1)^m C(n,m+1) Re(rho^{-(m+1)}). -/
lemma liKernel_re (n : ℕ) (ρ : ℂ) :
    (liKernel n ρ).re = ∑ m ∈ Finset.range n, ((-1 : ℝ) ^ m * (n.choose (m + 1) : ℝ)) * (1 / ρ ^ (m + 1)).re := by
  rw [liKernel_eq_sum, Complex.neg_re, Complex.re_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h : (n.choose (m + 1) : ℂ) * (-1 / ρ) ^ (m + 1)
      = ((((-1 : ℝ) ^ (m + 1) * (n.choose (m + 1) : ℝ)) : ℝ) : ℂ) * (1 / ρ ^ (m + 1)) := by
    rw [neg_div, neg_pow, div_pow, one_pow]
    push_cast
    ring
  rw [h, Complex.re_ofReal_mul]
  ring

/-- The paired family expands binomially into the paired power sums. -/
lemma liPaired_eq_sum (n : ℕ) (ρ : ℂ) :
    liPaired n ρ = ∑ m ∈ Finset.range n, (((-1 : ℂ) ^ m * (n.choose (m + 1) : ℂ))
      * ((WeilExplicit.zeroMult ρ : ℂ) * (((1 / ρ ^ (m + 1)).re : ℝ) : ℂ))) := by
  unfold liPaired
  rw [liKernel_re]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-- liLimit n = Sum_{m<n} (-1)^m C(n,m+1) pairedPowerSum (m+1). -/
theorem liLimit_eq_sum (n : ℕ) :
    liLimit n = ∑ m ∈ Finset.range n, ((-1 : ℂ) ^ m * (n.choose (m + 1) : ℂ)) * pairedPowerSum (m + 1) := by
  unfold liLimit
  simp_rw [liPaired_eq_sum]
  rw [Summable.tsum_finsetSum]
  · refine Finset.sum_congr rfl fun m _ => ?_
    unfold pairedPowerSum
    rw [tsum_mul_left]
  · intro m _
    exact (summable_pairedPowerSum (Nat.succ_pos m)).mul_left _

/-- liLimit n = Sum_{m<n} C(n,m+1) taylorOne m (Bombieri-Lagarias' Taylor face). -/
theorem liLimit_eq_taylorOne (hP : XiLogDerivDerivEq) (hR : NoRealZeroInUnitInterval) (n : ℕ) :
    liLimit n = ∑ m ∈ Finset.range n, (n.choose (m + 1) : ℂ) * taylorOne m := by
  rw [liLimit_eq_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [pairedPowerSum_succ_eq hP hR, taylorZero_eq]
  have h : (-1 : ℂ) ^ m * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
  linear_combination ((n.choose (m + 1) : ℂ) * taylorOne m) * h

/-- Sum_{m<n} C(n,m+1) (-1)^m = 1 for n >= 1 (the j = 1 .. n alternating binomial sum). -/
lemma sum_choose_alt {n : ℕ} (hn : 0 < n) :
    ∑ m ∈ Finset.range n, (n.choose (m + 1) : ℂ) * (-1) ^ m = 1 := by
  have h := Int.alternating_sum_range_choose_of_ne hn.ne'
  have h' : ∑ m ∈ Finset.range (n + 1), ((-1 : ℂ) ^ m * (n.choose m : ℂ)) = 0 := by
    exact_mod_cast h
  rw [Finset.sum_range_succ'] at h'
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one] at h'
  have h2 : ∑ m ∈ Finset.range n, (n.choose (m + 1) : ℂ) * (-1) ^ m
      = -∑ m ∈ Finset.range n, ((-1 : ℂ) ^ (m + 1) * (n.choose (m + 1) : ℂ)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [h2]
  linear_combination -h'

/-- The eta sum, reindexed onto Icc 1 n. -/
lemma sum_choose_eta (n : ℕ) :
    ∑ m ∈ Finset.range n, (n.choose (m + 1) : ℂ) * BombieriLagarias.eta m
      = ∑ j ∈ Finset.Icc 1 n, (n.choose j : ℂ) * BombieriLagarias.eta (j - 1) := by
  have hI : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hI, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Nat.add_sub_cancel_left, add_comm 1 m]

/-- The archimedean sum: Sum_{m<n} C(n,m+1) archCoeff m as archSide n writes it. -/
lemma sum_choose_archCoeff (n' : ℕ) :
    ∑ m ∈ Finset.range (n' + 1), ((n' + 1).choose (m + 1) : ℂ) * archCoeff m
      = -(((n' + 1 : ℕ) : ℂ) / 2) * ((Real.eulerMascheroniConstant : ℂ) + (Real.log Real.pi : ℂ)
          + 2 * (Real.log 2 : ℂ))
        + ∑ j ∈ Finset.Icc 2 (n' + 1),
            (-1 : ℂ) ^ j * ((n' + 1).choose j : ℂ) * (1 - 1 / (2 : ℂ) ^ j) * riemannZeta (j : ℂ) := by
  rw [Finset.sum_range_succ', archCoeff_zero, Nat.choose_one_right]
  have hI : Finset.Icc 2 (n' + 1) = Finset.Ico 2 (n' + 2) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hI, Finset.sum_Ico_eq_sum_range, show n' + 2 - 2 = n' by omega]
  have hsum : ∑ m ∈ Finset.range n', ((n' + 1).choose (m + 1 + 1) : ℂ) * archCoeff (m + 1)
      = ∑ k ∈ Finset.range n', (-1 : ℂ) ^ (2 + k) * ((n' + 1).choose (2 + k) : ℂ)
          * (1 - 1 / (2 : ℂ) ^ (2 + k)) * riemannZeta ((2 + k : ℕ) : ℂ) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [archCoeff_succ, add_comm 2 m]
    ring
  rw [hsum]
  push_cast
  ring

/-- **Deliverable (4): LiValue n**, modulo the two named Props. -/
theorem liValue_of (hP : XiLogDerivDerivEq) (hR : NoRealZeroInUnitInterval) (n : ℕ)
    (hn : 0 < n) : LiValue n := by
  unfold LiValue
  rw [liLimit_eq_taylorOne hP hR]
  simp_rw [taylorOne_eq]
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hsplit : ∑ m ∈ Finset.range (n' + 1), ((n' + 1).choose (m + 1) : ℂ)
      * ((-1) ^ m + archCoeff m - BombieriLagarias.eta m)
      = ∑ m ∈ Finset.range (n' + 1), ((n' + 1).choose (m + 1) : ℂ) * (-1) ^ m
        + ∑ m ∈ Finset.range (n' + 1), ((n' + 1).choose (m + 1) : ℂ) * archCoeff m
        - ∑ m ∈ Finset.range (n' + 1), ((n' + 1).choose (m + 1) : ℂ) * BombieriLagarias.eta m := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hsplit, sum_choose_alt hn, sum_choose_archCoeff, sum_choose_eta]
  unfold BombieriLagarias.archSide BombieriLagarias.finiteSide
  push_cast
  ring

/-- The node RH_bl_explicit_formula, verbatim, from the two named Props. -/
theorem bl_explicit_formula_of_partialFraction (hP : XiLogDerivDerivEq)
    (hR : NoRealZeroInUnitInterval) (n : ℕ) (hn : 0 < n) :
    Tendsto (liZeroSum n) atTop (𝓝 (BombieriLagarias.archSide n + BombieriLagarias.finiteSide n)) :=
  RvMBridge15.bl_explicit_formula_of hn (liValue_of hP hR n hn)

/-! ## 6. The Lambda form of the partial fraction is equivalent to the xi form. -/

/-- Off {0, 1} and off the zeros: logDeriv xi = 1/s + 1/(s-1) + logDeriv Lambda. -/
lemma logDeriv_xi_eq_lambda {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hz : ¬ IsNontrivialZero s) :
    logDeriv xi s = 1 / s + 1 / (s - 1) + logDeriv completedRiemannZeta s := by
  have hev : xi =ᶠ[𝓝 s] fun u => (u * (u - 1) / 2) * completedRiemannZeta u := by
    have hopen : IsOpen (({0, 1} : Set ℂ)ᶜ) := (Set.toFinite _).isClosed.isOpen_compl
    filter_upwards [hopen.mem_nhds (by simp [hs0, hs1])] with u hu
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hu
    exact xi_eq u hu.1 hu.2
  have hΛ : completedRiemannZeta s ≠ 0 := by
    rw [Ne, RvM.completedRiemannZeta_eq_zero_iff]; exact hz
  have hpoly : s * (s - 1) / 2 ≠ 0 := by
    have := sub_ne_zero.mpr hs1
    simp [hs0, this]
  have heq : logDeriv xi s = logDeriv (fun u => (u * (u - 1) / 2) * completedRiemannZeta u) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [heq, logDeriv_mul s hpoly hΛ (by fun_prop) (differentiableAt_completedZeta hs0 hs1)]
  have hd : HasDerivAt (fun u : ℂ => u * (u - 1) / 2) ((2 * s - 1) / 2) s := by
    have := ((hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)).div_const 2
    refine this.congr_deriv ?_
    simp only [id_eq]; ring
  rw [logDeriv_apply, hd.deriv]
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp
  ring

lemma logDeriv_xi_eventuallyEq_lambda {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hz : ¬ IsNontrivialZero s) :
    logDeriv xi =ᶠ[𝓝 s] fun u => 1 / u + 1 / (u - 1) + logDeriv completedRiemannZeta u := by
  have hopen : IsOpen (({0, 1} : Set ℂ)ᶜ ∩ {u : ℂ | IsNontrivialZero u}ᶜ) :=
    (Set.toFinite _).isClosed.isOpen_compl.inter isClosed_zeros.isOpen_compl
  filter_upwards [hopen.mem_nhds ⟨by simp [hs0, hs1], hz⟩] with u hu
  obtain ⟨hu, huz⟩ := hu
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hu
  exact logDeriv_xi_eq_lambda hu.1 hu.2 huz

lemma logDeriv_lambda_analyticAt {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hz : ¬ IsNontrivialZero s) :
    AnalyticAt ℂ (logDeriv completedRiemannZeta) s := by
  have h : logDeriv completedRiemannZeta = fun z => deriv completedRiemannZeta z / completedRiemannZeta z :=
    funext (logDeriv_apply completedRiemannZeta)
  rw [h]
  have hΛ : completedRiemannZeta s ≠ 0 := by
    rw [Ne, RvM.completedRiemannZeta_eq_zero_iff]; exact hz
  exact (RvM.analyticAt_completedRiemannZeta hs0 hs1).deriv.div
    (RvM.analyticAt_completedRiemannZeta hs0 hs1) hΛ

/-- deriv (logDeriv Lambda) = deriv (logDeriv xi) + 1/s^2 + 1/(s-1)^2 off {0, 1} and off the zeros. -/
theorem deriv_logDeriv_lambda_eq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hz : ¬ IsNontrivialZero s) :
    deriv (logDeriv completedRiemannZeta) s = deriv (logDeriv xi) s + 1 / s ^ 2 + 1 / (s - 1) ^ 2 := by
  rw [(logDeriv_xi_eventuallyEq_lambda hs0 hs1 hz).deriv_eq]
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have h1 : HasDerivAt (fun u : ℂ => 1 / u) (-(1 / s ^ 2)) s := by
    have := (hasDerivAt_id' s).inv hs0
    refine this.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · exact Filter.Eventually.of_forall fun u => one_div u
    · field_simp
  have h2 : HasDerivAt (fun u : ℂ => 1 / (u - 1)) (-(1 / (s - 1) ^ 2)) s := by
    have := ((hasDerivAt_id' s).sub_const 1).inv hs1'
    refine this.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · exact Filter.Eventually.of_forall fun u => one_div (u - 1)
    · field_simp
  have h3 : HasDerivAt (logDeriv completedRiemannZeta) (deriv (logDeriv completedRiemannZeta) s) s :=
    (logDeriv_lambda_analyticAt hs0 hs1 hz).differentiableAt.hasDerivAt
  have h := (h1.add h2).add h3
  rw [show (fun u : ℂ => 1 / u + 1 / (u - 1) + logDeriv completedRiemannZeta u)
      = ((fun u : ℂ => 1 / u) + fun u : ℂ => 1 / (u - 1)) + logDeriv completedRiemannZeta from rfl,
    h.deriv]
  ring

/-- xi form implies Lambda form. -/
theorem lambdaDerivPartialFraction_of_xi (h : XiLogDerivDerivEq) : LambdaDerivPartialFraction := by
  intro s hs0 hs1 hz
  rw [deriv_logDeriv_lambda_eq hs0 hs1 hz, h s hz]

/-! eq_of_continuousAt_of_eventually_ne, oneSubEquiv, zeroMult_one_sub, tsum_zero_series_one_sub
and deriv_logDeriv_xi_one_sub are the prelude's (RvMBridgeXi). -/

/-- Lambda form implies xi form: off {0,1} by the pole bookkeeping; at 0 and 1 by continuity
(both sides analytic there) and the s -> 1 - s symmetry. -/
theorem xiDerivPartialFraction_of_lambda (h : LambdaDerivPartialFraction) : XiLogDerivDerivEq := by
  have hoff : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → ¬ IsNontrivialZero s →
      deriv (logDeriv xi) s = -∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2 := by
    intro s hs0 hs1 hz
    have := h s hs0 hs1 hz
    rw [deriv_logDeriv_lambda_eq hs0 hs1 hz] at this
    linear_combination this
  have hG : ∀ s : ℂ, (∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2) = ∑' ρ : ℂ, zterm 0 ρ s :=
    fun s => tsum_congr fun ρ => (zterm_zero_eq ρ s).symm
  have h0 : deriv (logDeriv xi) 0 = -∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / (0 - ρ) ^ 2 := by
    rw [hG]
    have hr := zeroRadius_pos
    have hL : ContinuousAt (deriv (logDeriv xi)) 0 :=
      (logDeriv_xi_analyticAt (by rw [xi_zero]; norm_num)).deriv.continuousAt
    have hR : ContinuousAt (fun z => -∑' ρ : ℂ, zterm 0 ρ z) 0 :=
      (analyticAt_tsum_ball zterm zbound 0 (zeroRadius / 2) summable_zbound
        (fun k ρ s hs => by
          by_cases hρ : IsNontrivialZero ρ
          · exact hasDerivAt_zterm k ρ fun hsρ => not_nontrivialZero_of_mem_ball hs (hsρ ▸ hρ)
          · have h1 : zterm k ρ = fun _ => 0 := funext (zterm_eq_zero_of_not_nontrivial hρ)
            rw [h1, zterm_eq_zero_of_not_nontrivial hρ]
            exact hasDerivAt_const _ _)
        (fun k ρ s hs => norm_zterm_le_zbound k ρ hs)
        (Metric.mem_ball_self (by linarith))).continuousAt.neg
    refine eq_of_continuousAt_of_eventually_ne hL hR ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by linarith :
      (0 : ℝ) < zeroRadius / 2))] with z hz hz0
    have hz1 : z ≠ 1 := by
      intro h1
      rw [Metric.mem_ball, dist_zero_right, h1, norm_one] at hz
      linarith [zeroRadius_le_one]
    rw [hoff z hz0 hz1 (not_nontrivialZero_of_mem_ball hz), hG]
  intro s hz
  by_cases hs0 : s = 0
  · subst hs0; exact h0
  by_cases hs1 : s = 1
  · subst hs1
    have h1 := tsum_zero_series_one_sub 0
    rw [sub_zero] at h1
    rw [h1, ← h0, ← deriv_logDeriv_xi_one_sub (s := 0) (by simp [IsNontrivialZero]), sub_zero]
  exact hoff s hs0 hs1 hz

/-- **The two forms are equivalent.** -/
theorem xiDerivPartialFraction_iff : XiLogDerivDerivEq ↔ LambdaDerivPartialFraction :=
  ⟨lambdaDerivPartialFraction_of_xi, xiDerivPartialFraction_of_lambda⟩

/-- LiValue from the Lambda form. -/
theorem liValue_of_lambda (hP : LambdaDerivPartialFraction) (hR : NoRealZeroInUnitInterval) (n : ℕ)
    (hn : 0 < n) : LiValue n :=
  liValue_of (xiDerivPartialFraction_of_lambda hP) hR n hn

/-! ## 7. One obligation away: through E6Bridge20/21 the partial fraction rests on the single
growth bound RvMBridge20.XiDiffExtGrowthRight. -/

/-- LiValue n from the ONE remaining analytic obligation (plus the real-segment Prop). -/
theorem liValue_of_growth (h : RvMBridge20.XiDiffExtGrowthRight) (hR : NoRealZeroInUnitInterval)
    (n : ℕ) (hn : 0 < n) : LiValue n :=
  liValue_of (RvMBridge21.xi_logDeriv_deriv_eq_of_regular (RvMBridge20.xiDiffRegular_of_right h))
    hR n hn

/-- The node RH_bl_explicit_formula from the one growth obligation plus the real-segment Prop. -/
theorem bl_explicit_formula_of_growth (h : RvMBridge20.XiDiffExtGrowthRight)
    (hR : NoRealZeroInUnitInterval) (n : ℕ) (hn : 0 < n) :
    Tendsto (liZeroSum n) atTop (𝓝 (BombieriLagarias.archSide n + BombieriLagarias.finiteSide n)) :=
  RvMBridge15.bl_explicit_formula_of hn (liValue_of_growth h hR n hn)

end RvMBridge19
