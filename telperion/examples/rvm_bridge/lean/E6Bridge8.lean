/-
  E6Bridge8 -- discharge of the named obligation O1' = RvMBridge6.GaussianApprox (2026-09-21):
  Gaussian approximation on the strip by smooth compactly supported tests.  Pure Fourier
  analysis; no zeta, no zeros, nothing about RH (conjecture1_proved = False is untouched).

  The witness.  For a centre c and lam > 0 put b := 1/(4 lam) and

      phi(u) := K * u * exp (-b u^2 - i c u),      K := (2 lam i (pi/b)^{1/2})^{-1},

  so that paperFT phi z = (z - c) exp (-lam (z - c)^2) =: gaussHalf c lam z for EVERY z : C
  (one integration by parts against Mathlib's fourierIntegral_gaussian).  The tests are
  g_n(u) := phi(u) * chi(u/(n+1)) with chi a ContDiffBump at 0 (rIn = 1, rOut = 2), which are
  smooth with compact support.  On the strip |Im z| <= 1/2:
    * paperFT (g n) z -> paperFT phi z by dominated convergence (majorant |phi(u)| e^{|u|/2});
    * ‖paperFT (g n) z‖ <= 2 M / (1 + ‖z‖) uniformly in n, by one integration by parts in u
      (the derivative of g_n is bounded against a fixed Gaussian majorant) combined with the
      trivial bound;
  and then hermitianTransform (g n) z = paperFT (g n) z * conj (paperFT (g n) (conj z)) converges
  to gaussHalf z * conj (gaussHalf (conj z)) = gaussTest c lam z with the bound
  4 M^2 / (1 + ‖z‖)^2 <= 4 M^2 / (1 + normSq z).
-/
import E6Bridge6
import RvMBridgeGauss

open Zeta23 Complex MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace RvMBridge8
open WeilExplicit RvMBridgeGauss

/-! ## A/B. The Gaussian integrability calculus (integrable_exp_quadratic, _abs, abs_pow_le_exp,
integrable_abs_pow_mul_exp_quadratic_abs, integrable_mul_cexp_quadratic) and the transform of
u exp (-b u^2) at a complex frequency (integral_mul_cexp_gaussian_fourier, one integration by
parts against fourierIntegral_gaussian) live in the prelude RvMBridgeGauss, sections A and B
(formerly here). -/

/-! ## C. The witness phi and its transform. -/

/-- b = 1/(4 lam): the Gaussian width whose transform has width lam. -/
def gaussB (lam : ℝ) : ℝ := 1 / (4 * lam)

lemma gaussB_pos {lam : ℝ} (hlam : 0 < lam) : 0 < gaussB lam := by
  unfold gaussB; positivity

/-- The normalising constant K = (2 lam i (pi/b)^{1/2})^{-1}. -/
def gaussK (lam : ℝ) : ℂ :=
  (2 * (lam : ℂ) * I * ((Real.pi : ℂ) / (gaussB lam : ℂ)) ^ (1 / 2 : ℂ))⁻¹

/-- phi(u) = K u exp (-b u^2 - i c u): the (non-compactly-supported) inverse transform of
gaussHalf. -/
def gaussPhi (c lam : ℝ) (u : ℝ) : ℂ :=
  gaussK lam * (u : ℂ) * cexp (-(gaussB lam : ℂ) * (u : ℂ) ^ 2 - I * c * u)

/-- h(z) = (z - c) exp (-lam (z - c)^2), the Hermitian square root of gaussTest. -/
def gaussHalf (c lam : ℝ) (z : ℂ) : ℂ :=
  (z - c) * cexp (-(lam : ℂ) * (z - c) ^ 2)

/-- gaussTest c lam z = h z * conj (h (conj z))  (re-proof of the blind auditor's
Audit6_GaussShape.audit_gaussTest_shape inside the library). -/
lemma gaussTest_eq_half_mul_conj (c lam : ℝ) (z : ℂ) :
    RvMBridge6.gaussTest c lam z = gaussHalf c lam z * conj (gaussHalf c lam (conj z)) := by
  unfold RvMBridge6.gaussTest gaussHalf
  simp only [map_mul, map_sub, map_neg, map_pow, Complex.conj_conj, Complex.conj_ofReal,
    ← Complex.exp_conj]
  have h : (-(2 * (lam : ℂ)) * (z - c) ^ 2)
      = (-(lam : ℂ) * (z - c) ^ 2) + (-(lam : ℂ) * (z - c) ^ 2) := by ring
  rw [h, Complex.exp_add]
  ring

lemma gaussK_ne_zero {lam : ℝ} (hlam : 0 < lam) : gaussK lam ≠ 0 := by
  unfold gaussK
  apply inv_ne_zero
  have hb := gaussB_pos hlam
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast hlam.ne')) I_ne_zero) ?_
  rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
  left
  exact div_ne_zero (by exact_mod_cast Real.pi_ne_zero) (by exact_mod_cast hb.ne')

/-- The transform identity, for every z : C: paperFT phi z = gaussHalf c lam z. -/
theorem paperFT_gaussPhi {c lam : ℝ} (hlam : 0 < lam) (z : ℂ) :
    paperFT (gaussPhi c lam) z = gaussHalf c lam z := by
  have hb := gaussB_pos hlam
  have hb0 : (gaussB lam : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hlam0 : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  unfold paperFT gaussPhi
  have h1 : (fun u : ℝ => gaussK lam * (u : ℂ) * cexp (-(gaussB lam : ℂ) * (u : ℂ) ^ 2 - I * c * u)
      * cexp (I * z * u))
      = fun u : ℝ => gaussK lam * ((u : ℂ) * cexp (-(gaussB lam : ℂ) * u ^ 2) * cexp (I * (z - c) * u)) := by
    funext u
    have : cexp (-(gaussB lam : ℂ) * (u : ℂ) ^ 2 - I * c * u) * cexp (I * z * u)
        = cexp (-(gaussB lam : ℂ) * u ^ 2) * cexp (I * (z - c) * u) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      ring
    rw [mul_assoc, this]
    ring
  rw [h1, integral_const_mul, integral_mul_cexp_gaussian_fourier hb (z - c)]
  unfold gaussHalf gaussK
  set S := ((Real.pi : ℂ) / (gaussB lam : ℂ)) ^ (1 / 2 : ℂ) with hS
  have hS0 : S ≠ 0 := by
    rw [hS, Ne, Complex.cpow_eq_zero_iff, not_and_or]
    left
    exact div_ne_zero (by exact_mod_cast Real.pi_ne_zero) hb0
  have hexp : cexp (-(z - c) ^ 2 / (4 * (gaussB lam : ℂ))) = cexp (-(lam : ℂ) * (z - c) ^ 2) := by
    congr 1
    unfold gaussB
    push_cast
    field_simp
  rw [hexp]
  unfold gaussB
  push_cast
  field_simp
  ring

/-! ## D. The cutoff, the tests g_n, and the pointwise limit on the strip. -/

/-- A smooth bump at 0 on R: 1 on [-1, 1], supported in [-2, 2], values in [0, 1]. -/
def bump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- chi_n(u) = bump (u / (n + 1)): 1 for |u| <= n + 1, 0 for |u| >= 2 (n + 1). -/
def cutoff (n : ℕ) (u : ℝ) : ℝ := bump (u / ((n : ℝ) + 1))

/-- The tests: g_n = phi * chi_n. -/
def gaussTests (c lam : ℝ) (n : ℕ) (u : ℝ) : ℂ := gaussPhi c lam u * (cutoff n u : ℂ)

lemma cutoff_nonneg (n : ℕ) (u : ℝ) : 0 ≤ cutoff n u := bump.nonneg

lemma cutoff_le_one (n : ℕ) (u : ℝ) : cutoff n u ≤ 1 := bump.le_one

lemma abs_cutoff_le_one (n : ℕ) (u : ℝ) : |cutoff n u| ≤ 1 := by
  rw [abs_of_nonneg (cutoff_nonneg n u)]; exact cutoff_le_one n u

lemma cutoff_eq_one {n : ℕ} {u : ℝ} (hu : |u| ≤ (n : ℝ) + 1) : cutoff n u = 1 := by
  apply bump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  show |u| / ((n : ℝ) + 1) ≤ 1
  rw [div_le_one (by positivity)]
  exact hu

lemma cutoff_eq_zero {n : ℕ} {u : ℝ} (hu : 2 * ((n : ℝ) + 1) ≤ |u|) : cutoff n u = 0 := by
  apply bump.zero_of_le_dist
  rw [dist_zero_right, Real.norm_eq_abs, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  show (2 : ℝ) ≤ |u| / ((n : ℝ) + 1)
  rw [le_div_iff₀ (by positivity)]
  exact hu

lemma contDiff_cutoff (n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => (cutoff n u : ℂ)) := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutoff n) :=
    bump.contDiff.comp (contDiff_id.div_const _)
  exact Complex.ofRealCLM.contDiff.comp h

lemma hasCompactSupport_cutoff (n : ℕ) : HasCompactSupport (fun u : ℝ => (cutoff n u : ℂ)) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(2 * ((n : ℝ) + 1))) (b := 2 * ((n : ℝ) + 1)))
    fun u hu => ?_
  have : 2 * ((n : ℝ) + 1) ≤ |u| := by
    rw [Set.mem_Icc, not_and_or] at hu
    rcases hu with h | h
    · have h' := not_le.mp h
      rw [abs_of_neg (by linarith)]
      linarith
    · have h' := not_le.mp h
      rw [abs_of_pos (by linarith)]
      linarith
  simp [cutoff_eq_zero this]

lemma contDiff_gaussPhi (c lam : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gaussPhi c lam) := by
  unfold gaussPhi
  have hof : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => (u : ℂ)) := Complex.ofRealCLM.contDiff
  refine (contDiff_const.mul hof).mul (ContDiff.cexp ?_)
  exact (contDiff_const.mul (hof.pow 2)).sub (contDiff_const.mul hof)

theorem isWeilTest_gaussTests (c lam : ℝ) (n : ℕ) : IsWeilTest (gaussTests c lam n) := by
  refine ⟨(contDiff_gaussPhi c lam).mul (contDiff_cutoff n), ?_⟩
  exact (hasCompactSupport_cutoff n).mul_left

/-- ‖phi u‖ = ‖K‖ |u| exp (-b u^2). -/
lemma norm_gaussPhi (c lam : ℝ) (u : ℝ) :
    ‖gaussPhi c lam u‖ = ‖gaussK lam‖ * |u| * Real.exp (-gaussB lam * u ^ 2) := by
  unfold gaussPhi
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  congr 2
  simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, pow_two]

/-- On the strip |Im z| <= 1/2, ‖exp (i z u)‖ <= exp (|u| / 2). -/
lemma norm_cexp_I_mul_le {z : ℂ} (hz : |z.im| ≤ 1 / 2) (u : ℝ) :
    ‖cexp (I * z * u)‖ ≤ Real.exp ((1 / 2) * |u|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : (I * z * (u : ℂ)).re = -(z.im * u) := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
  rw [hre]
  have h1 : -(z.im * u) ≤ |z.im * u| := neg_le_abs _
  have h2 : |z.im * u| = |z.im| * |u| := abs_mul _ _
  have h3 : |z.im| * |u| ≤ (1 / 2) * |u| := mul_le_mul_of_nonneg_right hz (abs_nonneg u)
  linarith

/-- The strip majorant for the tests: ‖g_n u exp (i z u)‖ <= ‖K‖ |u| exp (-b u^2 + |u|/2). -/
lemma norm_gaussTests_mul_le {c lam : ℝ} {z : ℂ} (hz : |z.im| ≤ 1 / 2) (n : ℕ) (u : ℝ) :
    ‖gaussTests c lam n u * cexp (I * z * u)‖
      ≤ ‖gaussK lam‖ * (|u| ^ 1 * Real.exp (-gaussB lam * u ^ 2 + (1 / 2) * |u|)) := by
  unfold gaussTests
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_gaussPhi, pow_one,
    Real.exp_add]
  have h1 := abs_cutoff_le_one n u
  have h2 := norm_cexp_I_mul_le hz u
  have hK := norm_nonneg (gaussK lam)
  have hu := abs_nonneg u
  have he := (Real.exp_pos (-gaussB lam * u ^ 2)).le
  have he2 := (Real.exp_pos ((1 / 2) * |u|)).le
  calc ‖gaussK lam‖ * |u| * Real.exp (-gaussB lam * u ^ 2) * |cutoff n u| * ‖cexp (I * z * u)‖
      ≤ ‖gaussK lam‖ * |u| * Real.exp (-gaussB lam * u ^ 2) * 1 * Real.exp ((1 / 2) * |u|) := by
        gcongr
    _ = ‖gaussK lam‖ * (|u| * (Real.exp (-gaussB lam * u ^ 2) * Real.exp ((1 / 2) * |u|))) := by
        ring

/-- The same majorant for phi itself (chi_n <= 1 dropped). -/
lemma norm_gaussPhi_mul_le {c lam : ℝ} {z : ℂ} (hz : |z.im| ≤ 1 / 2) (u : ℝ) :
    ‖gaussPhi c lam u * cexp (I * z * u)‖
      ≤ ‖gaussK lam‖ * (|u| ^ 1 * Real.exp (-gaussB lam * u ^ 2 + (1 / 2) * |u|)) := by
  rw [norm_mul, norm_gaussPhi, pow_one, Real.exp_add]
  have h2 := norm_cexp_I_mul_le hz u
  have hK := norm_nonneg (gaussK lam)
  have hu := abs_nonneg u
  have he := (Real.exp_pos (-gaussB lam * u ^ 2)).le
  calc ‖gaussK lam‖ * |u| * Real.exp (-gaussB lam * u ^ 2) * ‖cexp (I * z * u)‖
      ≤ ‖gaussK lam‖ * |u| * Real.exp (-gaussB lam * u ^ 2) * Real.exp ((1 / 2) * |u|) := by
        gcongr
    _ = _ := by ring

lemma integrable_majorant {lam : ℝ} (hlam : 0 < lam) (m : ℕ) (K : ℝ) :
    Integrable (fun u : ℝ => K * (|u| ^ m * Real.exp (-gaussB lam * u ^ 2 + (1 / 2) * |u|))) :=
  (integrable_abs_pow_mul_exp_quadratic_abs (gaussB_pos hlam) (1 / 2) m).const_mul K

/-- Pointwise limit of the transforms on the strip (dominated convergence; chi_n(u) = 1 once
n + 1 >= |u|). -/
theorem paperFT_gaussTests_tendsto {c lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    Tendsto (fun n => paperFT (gaussTests c lam n) z) atTop (𝓝 (gaussHalf c lam z)) := by
  rw [← paperFT_gaussPhi hlam z]
  unfold paperFT
  refine tendsto_integral_of_dominated_convergence
    (fun u => ‖gaussK lam‖ * (|u| ^ 1 * Real.exp (-gaussB lam * u ^ 2 + (1 / 2) * |u|)))
    (fun n => ?_) (integrable_majorant hlam 1 _)
    (fun n => Filter.Eventually.of_forall fun u => norm_gaussTests_mul_le hz n u)
    (Filter.Eventually.of_forall fun u => ?_)
  · have hc : Continuous (gaussTests c lam n) :=
      (isWeilTest_gaussTests c lam n).1.continuous
    exact (hc.mul (by fun_prop)).aestronglyMeasurable
  · apply tendsto_const_nhds.congr'
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    refine ⟨⌈|u|⌉₊, fun n hn => ?_⟩
    unfold gaussTests
    have h1 : cutoff n u = 1 := cutoff_eq_one (by
      have := Nat.le_ceil |u|
      have : (⌈|u|⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
      linarith)
    simp [h1]

/-! ## E. The truncation-uniform bound: one integration by parts in u. -/

/-- The derivative of phi: K exp (-b u^2 - i c u) (1 + u (-2 b u - i c)). -/
def gaussPhi' (c lam : ℝ) (u : ℝ) : ℂ :=
  gaussK lam * (cexp (-(gaussB lam : ℂ) * (u : ℂ) ^ 2 - I * c * u)
    * (1 + (u : ℂ) * (-(gaussB lam : ℂ) * (2 * u) - I * c)))

lemma hasDerivAt_gaussPhi (c lam : ℝ) (u : ℝ) :
    HasDerivAt (gaussPhi c lam) (gaussPhi' c lam u) u := by
  have hE : HasDerivAt (fun x : ℂ => -(gaussB lam : ℂ) * x ^ 2 - I * c * x)
      (-(gaussB lam : ℂ) * (2 * u) - I * c) (u : ℂ) := by
    have := ((hasDerivAt_pow 2 (u : ℂ)).const_mul (-(gaussB lam : ℂ))).sub
      ((hasDerivAt_id (u : ℂ)).const_mul (I * c))
    refine this.congr_deriv ?_
    push_cast
    ring
  have h := (((hasDerivAt_id (u : ℂ)).mul hE.cexp).const_mul (gaussK lam)).comp_ofReal
  unfold gaussPhi gaussPhi'
  convert h using 1
  · funext y
    simp only [Pi.mul_apply, id]
    ring
  · simp only [id]
    ring

/-- ‖phi' u‖ <= ‖K‖ exp (-b u^2) (1 + 2 b u^2 + |c| |u|). -/
lemma norm_gaussPhi'_le {c lam : ℝ} (hlam : 0 < lam) (u : ℝ) :
    ‖gaussPhi' c lam u‖
      ≤ ‖gaussK lam‖ * Real.exp (-gaussB lam * u ^ 2) * (1 + 2 * gaussB lam * u ^ 2 + |c| * |u|) := by
  unfold gaussPhi'
  rw [norm_mul, norm_mul, Complex.norm_exp]
  have hre : (-(gaussB lam : ℂ) * (u : ℂ) ^ 2 - I * c * u).re = -gaussB lam * u ^ 2 := by
    simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, pow_two]
  rw [hre, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  calc ‖1 + (u : ℂ) * (-(gaussB lam : ℂ) * (2 * u) - I * c)‖
      ≤ ‖(1 : ℂ)‖ + ‖(u : ℂ) * (-(gaussB lam : ℂ) * (2 * u) - I * c)‖ := norm_add_le _ _
    _ = 1 + |u| * ‖-(gaussB lam : ℂ) * (2 * u) - I * c‖ := by
        rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 1 + |u| * (‖-(gaussB lam : ℂ) * (2 * u)‖ + ‖I * (c : ℂ)‖) := by
        gcongr
        exact norm_sub_le _ _
    _ = 1 + |u| * (2 * |gaussB lam| * |u| + |c|) := by
        rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Complex.norm_real, norm_mul,
          Complex.norm_I, Complex.norm_real, Complex.norm_ofNat, Real.norm_eq_abs,
          Real.norm_eq_abs, Real.norm_eq_abs]
        ring
    _ = 1 + 2 * gaussB lam * u ^ 2 + |c| * |u| := by
        rw [abs_of_pos (gaussB_pos hlam)]
        have : |u| * |u| = u ^ 2 := by rw [← sq, sq_abs]
        rw [← this]
        ring

/-- A uniform bound on the derivative of the bump. -/
lemma exists_deriv_bump_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, |deriv (bump : ℝ → ℝ) y| ≤ B := by
  have hc : Continuous (deriv (bump : ℝ → ℝ)) :=
    (bump.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support bump.hasCompactSupport.deriv
  refine ⟨max B 0, le_max_right _ _, fun y => ?_⟩
  exact (Real.norm_eq_abs _ ▸ hB y).trans (le_max_left _ _)

lemma hasDerivAt_cutoff (n : ℕ) (u : ℝ) :
    HasDerivAt (fun u : ℝ => (cutoff n u : ℂ))
      (((deriv (bump : ℝ → ℝ) (u / ((n : ℝ) + 1)) * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) u := by
  have hb : HasDerivAt (bump : ℝ → ℝ) (deriv (bump : ℝ → ℝ) (u / ((n : ℝ) + 1)))
      (u / ((n : ℝ) + 1)) :=
    (((bump.contDiff (n := 1)).differentiable one_ne_zero) _).hasDerivAt
  have h := (hb.comp u ((hasDerivAt_id u).div_const ((n : ℝ) + 1))).ofReal_comp
  convert h using 1
  funext y
  simp [cutoff, Function.comp]

lemma hasDerivAt_gaussTests (c lam : ℝ) (n : ℕ) (u : ℝ) :
    HasDerivAt (gaussTests c lam n)
      (gaussPhi' c lam u * (cutoff n u : ℂ)
        + gaussPhi c lam u * ((deriv (bump : ℝ → ℝ) (u / ((n : ℝ) + 1)) * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ))
      u :=
  (hasDerivAt_gaussPhi c lam u).mul (hasDerivAt_cutoff n u)

/-- The derivative majorant D(u) = ‖K‖ (E + 2 b |u|^2 E + (|c| + B) |u| E), E = exp (-b u^2 + |u|/2):
integrable, and it dominates ‖g_n'(u) exp (i z u)‖ on the strip, uniformly in n. -/
def derivMajorant (c lam B : ℝ) (u : ℝ) : ℝ :=
  ‖gaussK lam‖ * (|u| ^ 0 * Real.exp (-gaussB lam * u ^ 2 + (1 / 2) * |u|))
    + (‖gaussK lam‖ * (2 * gaussB lam)) * (|u| ^ 2 * Real.exp (-gaussB lam * u ^ 2 + (1 / 2) * |u|))
    + (‖gaussK lam‖ * (|c| + B)) * (|u| ^ 1 * Real.exp (-gaussB lam * u ^ 2 + (1 / 2) * |u|))

lemma integrable_derivMajorant {lam : ℝ} (hlam : 0 < lam) (c B : ℝ) :
    Integrable (derivMajorant c lam B) :=
  ((integrable_majorant hlam 0 _).add (integrable_majorant hlam 2 _)).add
    (integrable_majorant hlam 1 _)

lemma norm_deriv_gaussTests_mul_le {c lam B : ℝ} (hlam : 0 < lam) (hB0 : 0 ≤ B)
    (hB : ∀ y : ℝ, |deriv (bump : ℝ → ℝ) y| ≤ B) {z : ℂ} (hz : |z.im| ≤ 1 / 2) (n : ℕ) (u : ℝ) :
    ‖(gaussPhi' c lam u * (cutoff n u : ℂ)
        + gaussPhi c lam u * ((deriv (bump : ℝ → ℝ) (u / ((n : ℝ) + 1)) * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ))
      * cexp (I * z * u)‖ ≤ derivMajorant c lam B u := by
  have hK := norm_nonneg (gaussK lam)
  have hu := abs_nonneg u
  have hb := gaussB_pos hlam
  have hE := (Real.exp_pos (-gaussB lam * u ^ 2)).le
  have hez := norm_cexp_I_mul_le hz u
  have hez0 := norm_nonneg (cexp (I * z * u))
  have h1 := norm_gaussPhi'_le (c := c) hlam u
  have h2 : ‖gaussPhi c lam u‖ = ‖gaussK lam‖ * |u| * Real.exp (-gaussB lam * u ^ 2) :=
    norm_gaussPhi c lam u
  have hchi := abs_cutoff_le_one n u
  have hd : |deriv (bump : ℝ → ℝ) (u / ((n : ℝ) + 1)) * (1 / ((n : ℝ) + 1))| ≤ B := by
    rw [abs_mul]
    have h1n : |1 / ((n : ℝ) + 1)| ≤ 1 := by
      rw [abs_of_pos (by positivity), div_le_one (by positivity)]
      linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    calc |deriv (bump : ℝ → ℝ) (u / ((n : ℝ) + 1))| * |1 / ((n : ℝ) + 1)|
        ≤ B * 1 := mul_le_mul (hB _) h1n (abs_nonneg _) hB0
      _ = B := mul_one B
  -- the norm of the bracket
  have hbr : ‖gaussPhi' c lam u * (cutoff n u : ℂ)
        + gaussPhi c lam u * ((deriv (bump : ℝ → ℝ) (u / ((n : ℝ) + 1)) * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ)‖
      ≤ ‖gaussK lam‖ * Real.exp (-gaussB lam * u ^ 2) * (1 + 2 * gaussB lam * u ^ 2 + |c| * |u|)
        + ‖gaussK lam‖ * |u| * Real.exp (-gaussB lam * u ^ 2) * B := by
    calc _ ≤ ‖gaussPhi' c lam u * (cutoff n u : ℂ)‖
          + ‖gaussPhi c lam u * ((deriv (bump : ℝ → ℝ) (u / ((n : ℝ) + 1)) * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ)‖ :=
          norm_add_le _ _
      _ = ‖gaussPhi' c lam u‖ * |cutoff n u|
          + ‖gaussPhi c lam u‖ * |deriv (bump : ℝ → ℝ) (u / ((n : ℝ) + 1)) * (1 / ((n : ℝ) + 1))| := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs]
      _ ≤ ‖gaussPhi' c lam u‖ * 1 + ‖gaussPhi c lam u‖ * B := by gcongr
      _ ≤ _ := by rw [h2, mul_one]; gcongr
  rw [norm_mul]
  calc _ ≤ (‖gaussK lam‖ * Real.exp (-gaussB lam * u ^ 2) * (1 + 2 * gaussB lam * u ^ 2 + |c| * |u|)
        + ‖gaussK lam‖ * |u| * Real.exp (-gaussB lam * u ^ 2) * B) * Real.exp ((1 / 2) * |u|) := by
        gcongr
    _ = derivMajorant c lam B u := by
        unfold derivMajorant
        rw [Real.exp_add]
        have : |u| ^ 2 = u ^ 2 := sq_abs u
        rw [this]
        ring

/-- Integration by parts: i z * paperFT g z = -∫ g'(u) exp (i z u) du for g compactly supported
with continuous derivative g'. -/
theorem I_mul_paperFT_eq {g g' : ℝ → ℂ} (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g')
    (hsupp : HasCompactSupport g) (z : ℂ) :
    I * z * paperFT g z = -∫ x : ℝ, g' x * cexp (I * z * x) := by
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt
  have hg'eq : g' = deriv g := funext fun x => ((hg x).deriv).symm
  have hsupp' : HasCompactSupport g' := hg'eq ▸ hsupp.deriv
  have hv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => cexp (I * z * (x : ℂ)))
      (cexp (I * z * (x : ℂ)) * (I * z)) x := by
    intro x
    have := (((hasDerivAt_id (x : ℂ)).const_mul (I * z)).cexp).comp_ofReal
    simpa using this
  have hcv : Continuous (fun x : ℝ => cexp (I * z * (x : ℂ))) := by fun_prop
  have hi1 : Integrable (g * fun x : ℝ => cexp (I * z * (x : ℂ)) * (I * z)) :=
    (hgc.mul (hcv.mul continuous_const)).integrable_of_hasCompactSupport hsupp.mul_right
  have hi2 : Integrable (g' * fun x : ℝ => cexp (I * z * (x : ℂ))) :=
    (hg'.mul hcv).integrable_of_hasCompactSupport hsupp'.mul_right
  have hi3 : Integrable (g * fun x : ℝ => cexp (I * z * (x : ℂ))) :=
    (hgc.mul hcv).integrable_of_hasCompactSupport hsupp.mul_right
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hg x) (fun x _ => hv x)
    hi1 hi2 hi3
  unfold paperFT
  rw [← key, ← integral_const_mul]
  congr 1
  funext x
  ring

/-- ‖z‖ ‖paperFT (g n) z‖ <= ∫ D on the strip, uniformly in n. -/
theorem norm_mul_paperFT_gaussTests_le {c lam B : ℝ} (hlam : 0 < lam) (hB0 : 0 ≤ B)
    (hB : ∀ y : ℝ, |deriv (bump : ℝ → ℝ) y| ≤ B) {z : ℂ} (hz : |z.im| ≤ 1 / 2) (n : ℕ) :
    ‖z‖ * ‖paperFT (gaussTests c lam n) z‖ ≤ ∫ u : ℝ, derivMajorant c lam B u := by
  have hd := hasDerivAt_gaussTests c lam n
  have hcont : Continuous (fun u => gaussPhi' c lam u * (cutoff n u : ℂ)
      + gaussPhi c lam u * ((deriv (bump : ℝ → ℝ) (u / ((n : ℝ) + 1)) * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) := by
    have h1 : Continuous (gaussPhi' c lam) := by
      have : gaussPhi' c lam = deriv (gaussPhi c lam) :=
        funext fun u => ((hasDerivAt_gaussPhi c lam u).deriv).symm
      rw [this]
      exact (contDiff_infty.mp (contDiff_gaussPhi c lam) 1).continuous_deriv le_rfl
    have h2 : Continuous (fun u : ℝ => (cutoff n u : ℂ)) := (contDiff_cutoff n).continuous
    have h3 : Continuous (gaussPhi c lam) := (contDiff_gaussPhi c lam).continuous
    have h4 : Continuous (fun u : ℝ => ((deriv (bump : ℝ → ℝ) (u / ((n : ℝ) + 1)) * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) := by
      have hb : Continuous (deriv (bump : ℝ → ℝ)) := (bump.contDiff (n := 1)).continuous_deriv le_rfl
      exact Complex.continuous_ofReal.comp ((hb.comp (continuous_id.div_const _)).mul continuous_const)
    exact (h1.mul h2).add (h3.mul h4)
  have hid := I_mul_paperFT_eq hd hcont (isWeilTest_gaussTests c lam n).2 z
  have hnorm : ‖z‖ * ‖paperFT (gaussTests c lam n) z‖ = ‖I * z * paperFT (gaussTests c lam n) z‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
  rw [hnorm, hid, norm_neg]
  exact norm_integral_le_of_norm_le (integrable_derivMajorant hlam c B)
    (Filter.Eventually.of_forall fun u => norm_deriv_gaussTests_mul_le hlam hB0 hB hz n u)

/-- The trivial bound ‖paperFT (g n) z‖ <= ∫ ‖K‖ |u| e^{-b u^2 + |u|/2} on the strip. -/
theorem norm_paperFT_gaussTests_le {c lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : |z.im| ≤ 1 / 2) (n : ℕ) :
    ‖paperFT (gaussTests c lam n) z‖
      ≤ ∫ u : ℝ, ‖gaussK lam‖ * (|u| ^ 1 * Real.exp (-gaussB lam * u ^ 2 + (1 / 2) * |u|)) := by
  unfold paperFT
  exact norm_integral_le_of_norm_le (integrable_majorant hlam 1 _)
    (Filter.Eventually.of_forall fun u => norm_gaussTests_mul_le hz n u)

/-- Combining the two bounds: ‖paperFT (g n) z‖ <= 2 M / (1 + ‖z‖) on the strip, M independent of n. -/
theorem exists_paperFT_gaussTests_bound {c lam : ℝ} (hlam : 0 < lam) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n (z : ℂ), |z.im| ≤ 1 / 2 →
      ‖paperFT (gaussTests c lam n) z‖ ≤ 2 * M / (1 + ‖z‖) := by
  obtain ⟨B, hB0, hB⟩ := exists_deriv_bump_bound
  set M0 := ∫ u : ℝ, ‖gaussK lam‖ * (|u| ^ 1 * Real.exp (-gaussB lam * u ^ 2 + (1 / 2) * |u|)) with hM0
  set M1 := ∫ u : ℝ, derivMajorant c lam B u with hM1
  have hM0nn : 0 ≤ M0 := by
    rw [hM0]
    exact integral_nonneg fun u => by positivity
  have hM1nn : 0 ≤ M1 := by
    rw [hM1]
    refine integral_nonneg fun u => ?_
    unfold derivMajorant
    have := abs_nonneg c
    have := gaussB_pos hlam
    positivity
  refine ⟨max M0 M1, le_max_of_le_left hM0nn, fun n z hz => ?_⟩
  have h0 := norm_paperFT_gaussTests_le (c := c) hlam hz n
  have h1 := norm_mul_paperFT_gaussTests_le (c := c) hlam hB0 hB hz n
  rw [← hM0] at h0
  rw [← hM1] at h1
  have hz0 := norm_nonneg z
  have hle0 : M0 ≤ max M0 M1 := le_max_left _ _
  have hle1 : M1 ≤ max M0 M1 := le_max_right _ _
  rw [le_div_iff₀ (by positivity)]
  rcases le_or_gt ‖z‖ 1 with hz1 | hz1
  · nlinarith [norm_nonneg (paperFT (gaussTests c lam n) z)]
  · nlinarith [norm_nonneg (paperFT (gaussTests c lam n) z)]

/-! ## F. Assembly: GaussianApprox. -/

lemma norm_hermitianTransform_eq (g : ℝ → ℂ) (z : ℂ) :
    ‖RvMBridge6.hermitianTransform g z‖ = ‖paperFT g z‖ * ‖paperFT g (conj z)‖ := by
  unfold RvMBridge6.hermitianTransform
  rw [norm_mul, Complex.norm_conj]

/-- **O1' discharged.**  RvMBridge6.GaussianApprox holds: the tests g_n = phi chi_n are Weil tests,
their Hermitian transforms converge to gaussTest c lam pointwise on the strip |Im z| <= 1/2, with
the n-uniform bound 4 M^2 / (1 + normSq z) there. -/
theorem gaussian_approx : RvMBridge6.GaussianApprox := by
  intro c lam hlam
  obtain ⟨M, hM, hbound⟩ := exists_paperFT_gaussTests_bound (c := c) hlam
  refine ⟨gaussTests c lam, isWeilTest_gaussTests c lam, ⟨4 * M ^ 2, fun n z hz => ?_⟩,
    fun z hz => ?_⟩
  · have hzc : |(conj z).im| ≤ 1 / 2 := by rwa [Complex.conj_im, abs_neg]
    have h1 := hbound n z hz
    have h2 := hbound n (conj z) hzc
    rw [Complex.norm_conj] at h2
    rw [norm_hermitianTransform_eq]
    have hz0 := norm_nonneg z
    have hpos : 0 < 1 + ‖z‖ := by positivity
    calc ‖paperFT (gaussTests c lam n) z‖ * ‖paperFT (gaussTests c lam n) (conj z)‖
        ≤ (2 * M / (1 + ‖z‖)) * (2 * M / (1 + ‖z‖)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (div_nonneg (by linarith) hpos.le)
      _ = 4 * M ^ 2 / (1 + ‖z‖) ^ 2 := by field_simp; ring
      _ ≤ 4 * M ^ 2 / (1 + Complex.normSq z) := by
          have hns := Complex.normSq_nonneg z
          apply div_le_div_of_nonneg_left (by positivity) (by linarith)
          rw [Complex.normSq_eq_norm_sq]
          nlinarith
  · have hzc : |(conj z).im| ≤ 1 / 2 := by rwa [Complex.conj_im, abs_neg]
    rw [gaussTest_eq_half_mul_conj]
    unfold RvMBridge6.hermitianTransform
    exact (paperFT_gaussTests_tendsto hlam hz).mul
      ((Complex.continuous_conj.tendsto _).comp (paperFT_gaussTests_tendsto hlam hzc))

end RvMBridge8
