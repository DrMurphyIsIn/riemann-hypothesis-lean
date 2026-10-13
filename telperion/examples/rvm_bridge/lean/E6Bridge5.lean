/-
  E6Bridge5 -- the forward half of Weil's criterion on this island's vocabulary (2026-09-20):
  the Riemann Hypothesis (Mathlib's `RiemannHypothesis`) implies the Weil positivity

      0 <= Re [ archSide (g * g~) - primeSide (g * g~) ]

  for every smooth compactly supported test g : R -> C, where g * g~ is the Hermitian
  autocorrelation (g~ u = conj (g (-u))).

  WHAT IS CONSUMED (all unconditional, #print axioms = [propext, Classical.choice, Quot.sound]):
    RvMBridge4.limit_explicit_formula        (the E8 node: the Weil/Guinand explicit formula as a
                                              HasSum over ALL rho : C with the divisor weight)
    RvMBridge4.weilKernel_line               (H_g(1/2 + i r) = paperFT g r)
    RvMBridge4.zeroMult_eq_zero_of_not_nontrivial
    Zeta23.RH_implies_on_line                (Mathlib's RiemannHypothesis puts every nontrivial
                                              zero on Re = 1/2)
    Zeta23.EF.paperFT_weilTest               (the transform of a convolution f * g~ factors as
                                              h_f(z) * conj (h_g (conj z)))
    Zeta23.EF.weilTest_hasCompactSupport, Zeta23.EF.continuous_tilde
    HasCompactSupport.contDiff_convolution_left (Mathlib: the convolution of a C^n compactly
                                              supported function with a locally integrable one
                                              is C^n)

  THE ARGUMENT: under RH every zero with nonzero multiplicity is rho = 1/2 + i gamma with gamma
  real, so the zero-side summand at rho is  m(rho) * h_g(gamma) * conj (h_g(gamma))
  = m(rho) * |h_g(gamma)|^2, a nonnegative real.  The explicit formula sums these to
  archSide - primeSide, so the real part of the sum is nonnegative (HasSum.nonneg after taking
  real parts with Complex.hasSum_re).  Off the line the summand h_g(gamma) conj(h_g(conj gamma))
  is not a square modulus, which is exactly why RH is load-bearing (see the probes).

  The two definitions in namespace WeilExplicit are the AUTHORED block for the registry node
  (autocorr, weilForm); the six E8 definitions (IsWeilTest, weilKernel, zeroMult, archIntegrand,
  archSide, primeSide) are imported from E6Bridge4 and NOT redefined.

  BEGIN REGISTRY STATEMENT
  theorem rh_implies_weil_positivity (hRH : RiemannHypothesis) :
      ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g →
        0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re
  END REGISTRY STATEMENT

  No RH progress is claimed: this is the forward half of Weil's criterion (RH implies
  positivity), not the converse.  conjecture1_proved = False.
-/
import E6Bridge4

open Zeta23 Complex MeasureTheory
open scoped ComplexConjugate Convolution

noncomputable section

namespace WeilExplicit
open MeasureTheory Complex

/-- The Hermitian autocorrelation g * g~ with g~ u = conj (g (-u)). -/
noncomputable def autocorr (g : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ v : ℝ, g v * (starRingEnd ℂ) (g (v - u))

/-- The Weil functional read from the primes side. -/
noncomputable def weilForm (f : ℝ → ℂ) : ℂ := archSide f - primeSide f

end WeilExplicit

namespace RvMBridge5
open WeilExplicit

/-! ## A. The autocorrelation is Zeta23's Weil test function g * g~. -/

/-- autocorr g = weilTest g g: unfolding Mathlib's convolution, tilde g (u - v) = conj (g (v - u)). -/
lemma autocorr_eq_weilTest (g : ℝ → ℂ) : autocorr g = Zeta23.EF.weilTest g g := by
  funext u
  unfold autocorr Zeta23.EF.weilTest
  rw [MeasureTheory.convolution_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [ContinuousLinearMap.mul_apply', Zeta23.EF.tilde, neg_sub]

/-- The autocorrelation of an E8 test function is again an E8 test function: smooth because
the convolution of a smooth compactly supported function with a locally integrable one is
smooth, compactly supported because both factors are. -/
lemma isWeilTest_autocorr {g : ℝ → ℂ} (hg : IsWeilTest g) : IsWeilTest (autocorr g) := by
  rw [autocorr_eq_weilTest]
  refine ⟨?_, Zeta23.EF.weilTest_hasCompactSupport hg.2 hg.2⟩
  unfold Zeta23.EF.weilTest
  exact hg.2.contDiff_convolution_left _ hg.1
    (Zeta23.EF.continuous_tilde hg.1.continuous).locallyIntegrable

/-! ## B. Under RH every zero-side summand is a nonnegative real. -/

/-- A nontrivial zero rho lies on the line under RH, so rho = 1/2 + i (Im rho). -/
lemma eq_half_add_im_of_rh (hRH : RiemannHypothesis) {ρ : ℂ} (h : IsNontrivialZero ρ) :
    ρ = 1 / 2 + (ρ.im : ℂ) * I := by
  have hre : ρ.re = 1 / 2 := Zeta23.RH_implies_on_line hRH h
  apply Complex.ext <;> simp [hre]

/-- On the line the transform of the autocorrelation is a square modulus:
H_{g * g~}(1/2 + i r) = |h_g(r)|^2. -/
lemma weilKernel_autocorr_line {g : ℝ → ℂ} (hg : IsWeilTest g) (r : ℝ) :
    weilKernel (autocorr g) (1 / 2 + (r : ℂ) * I) = ((‖paperFT g r‖ : ℂ)) ^ 2 := by
  rw [RvMBridge4.weilKernel_line, autocorr_eq_weilTest,
    Zeta23.EF.paperFT_weilTest hg.1.continuous hg.1.continuous hg.2 hg.2,
    Complex.conj_ofReal, Complex.mul_conj']

/-- Each summand m(rho) * H_{g * g~}(rho) of the explicit formula has nonnegative real part
under RH: zero off the nontrivial zeros, m(rho) |h_g(Im rho)|^2 on them. -/
lemma term_re_nonneg (hRH : RiemannHypothesis) {g : ℝ → ℂ} (hg : IsWeilTest g) (ρ : ℂ) :
    0 ≤ ((WeilExplicit.zeroMult ρ : ℂ) * weilKernel (autocorr g) ρ).re := by
  by_cases hz : IsNontrivialZero ρ
  · have hk : weilKernel (autocorr g) ρ = weilKernel (autocorr g) (1 / 2 + (ρ.im : ℂ) * I) := by
      rw [← eq_half_add_im_of_rh hRH hz]
    rw [hk, weilKernel_autocorr_line hg]
    have hcast : (WeilExplicit.zeroMult ρ : ℂ) * ((‖paperFT g ρ.im‖ : ℂ)) ^ 2
        = (((WeilExplicit.zeroMult ρ : ℝ) * ‖paperFT g ρ.im‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast, Complex.ofReal_re]
    positivity
  · rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial hz]
    simp

/-! ## C. The node statement, verbatim: RH implies Weil positivity. -/

theorem rh_implies_weil_positivity (hRH : RiemannHypothesis) :
    ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g →
      0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re := by
  intro g hg
  have hsum := (RvMBridge4.limit_explicit_formula _ (isWeilTest_autocorr hg)).2
  have hre := Complex.hasSum_re hsum
  unfold WeilExplicit.weilForm
  exact hre.nonneg (fun ρ => term_re_nonneg hRH hg ρ)

end RvMBridge5
