/-
  E6Bridge10 -- the Wall in two real parameters (seam A, 2026-09-21).

  Deliverable 1 (the seam).  Every quantifier over the infinite-dimensional test class is gone:

      RiemannHypothesis  <->  GaussianPositivity
                          :=  forall c lam : R, 0 < lam ->
                                0 <= Re Sum_rho m(rho) (gamma_rho - c)^2 exp (-2 lam (gamma_rho - c)^2)

  Forward: under RH gamma_rho = Im rho is real (Zeta23.RH_implies_on_line), each summand is
  m(rho) times a nonnegative real, the family is summable (RvMBridge6.summable_gauss_zeroSide),
  so the real part of the sum is nonnegative.  Converse: the contrapositive of the discharged
  Gaussian dominance (RvMBridge7.gaussian_dominance): an off-line zero makes some
  Re zeroSide (gaussTest c lam) < 0.  Composed with E6Bridge9's dictionary theorem this gives
  GaussianPositivity <-> Weil positivity on Hermitian autocorrelations.

  Deliverable 2 (the Gaussian explicit formula, i.e. the PRIME-SIDE form of the Wall).  With
  phi := RvMBridge8.gaussPhi c lam (the non-compactly-supported Gaussian-derivative test) and
  f := autocorr phi its Hermitian autocorrelation,

      zeroSide (gaussTest c lam) = archSide f - primeSide f,

  obtained by passing n -> infinity in the E8 explicit formula for the truncations
  g_n := gaussTests c lam n (each an IsWeilTest): the zero side converges by Tannery against the
  local zero count (the complex form of E6Bridge6's transfer), the prime side by dominated
  convergence against a Gaussian-in-log-n majorant, the archimedean side by dominated convergence
  in u (Gaussian majorant of autocorr (g n), uniform in n) and in r (the n-uniform strip bound of
  E6Bridge8 against the O(log|r|) digamma growth carried by Zeta23's majorant lemma).
  Consequently

      RiemannHypothesis  <->  forall c lam, 0 < lam ->
                                Re primeSide (autocorr phi_{c,lam}) <= Re archSide (autocorr phi_{c,lam}).

  WHAT THIS IS NOT: a proof of RH, or of either side.  An equivalence between RH and a
  two-parameter family of inequalities is a change of coordinates on the Wall, not a crossing.
  conjecture1_proved = False.
-/
import E6Bridge9
import RvMBridgeGauss

open Zeta23 Complex MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace RvMBridge10
open WeilExplicit RvMBridge6 RvMBridge8 RvMBridgeGauss

/-! ## A. Deliverable 1: the two-parameter Wall. -/

/-- Gaussian positivity: the Wall in two real parameters. -/
def GaussianPositivity : Prop :=
  ∀ (c lam : ℝ), 0 < lam → 0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re

/-- On the real axis the Gaussian test is the nonnegative real (x - c)^2 exp (-2 lam (x - c)^2). -/
lemma gaussTest_ofReal (c lam x : ℝ) :
    gaussTest c lam (x : ℂ) = (((x - c) ^ 2 * Real.exp (-(2 * lam) * (x - c) ^ 2) : ℝ) : ℂ) := by
  unfold gaussTest
  push_cast
  ring_nf

lemma gaussTest_ofReal_re_nonneg (c lam x : ℝ) : 0 ≤ (gaussTest c lam (x : ℂ)).re := by
  rw [gaussTest_ofReal, Complex.ofReal_re]
  positivity

/-- Under RH the ordinate gamma_rho of a nontrivial zero is the real number Im rho. -/
lemma gammaOf_eq_im_of_rh (hRH : RiemannHypothesis) {ρ : ℂ} (h : IsNontrivialZero ρ) :
    gammaOf ρ = (ρ.im : ℂ) := by
  have hre : ρ.re = 1 / 2 := Zeta23.RH_implies_on_line hRH h
  apply Complex.ext
  · rw [Zeta23.WeilEF.gammaOf_re, Complex.ofReal_re]
  · rw [Zeta23.WeilEF.gammaOf_im, Complex.ofReal_im, hre]
    ring

/-- Under RH every Gaussian zero-side summand has nonnegative real part. -/
lemma gauss_term_re_nonneg (hRH : RiemannHypothesis) (c lam : ℝ) (ρ : ℂ) :
    0 ≤ ((WeilExplicit.zeroMult ρ : ℂ) * gaussTest c lam (gammaOf ρ)).re := by
  by_cases hz : IsNontrivialZero ρ
  · rw [gammaOf_eq_im_of_rh hRH hz, gaussTest_ofReal, ← Complex.ofReal_natCast,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    positivity
  · rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial hz]
    simp

/-- Forward half: RH implies Gaussian positivity. -/
theorem rh_implies_gaussian_positivity (hRH : RiemannHypothesis) : GaussianPositivity := by
  intro c lam hlam
  have hsum := (summable_gauss_zeroSide c lam hlam).hasSum
  have hre := Complex.hasSum_re hsum
  exact hre.nonneg (fun ρ => gauss_term_re_nonneg hRH c lam ρ)

/-- Converse half: Gaussian positivity implies RH (contrapositive of gaussian_dominance). -/
theorem gaussian_positivity_implies_rh (hGP : GaussianPositivity) : RiemannHypothesis := by
  apply rh_of_all_on_line
  intro ρ₀ hρ₀
  by_contra hre
  obtain ⟨c, lam, hlam, hneg⟩ := RvMBridge7.gaussian_dominance ρ₀ hρ₀ hre
  linarith [hGP c lam hlam]

/-- **The two-parameter Wall.** -/
theorem rh_iff_gaussian_positivity : RiemannHypothesis ↔ GaussianPositivity :=
  ⟨rh_implies_gaussian_positivity, gaussian_positivity_implies_rh⟩

/-- Gaussian positivity is Weil positivity on Hermitian autocorrelations (via the dictionary
theorem of E6Bridge9). -/
theorem gaussian_positivity_iff_weil_positivity :
    GaussianPositivity ↔ (∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g →
      0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re) :=
  rh_iff_gaussian_positivity.symm.trans RvMBridge9.zeta_comb_membership_iff_rh.symm

/-! ## B. The truncated tests g_n = gaussTests c lam n and the COMPLEX zero-side limit
(E6Bridge6's Tannery transfer exports only the real part; the same argument gives the
complex limit, needed to identify the limit of the explicit formula). -/

/-- The n-uniform strip bound for the Hermitian transforms of the truncations (re-assembled from
E6Bridge8's exists_paperFT_gaussTests_bound, as inside gaussian_approx). -/
lemma exists_hermitian_gaussTests_bound (c lam : ℝ) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n (z : ℂ), |z.im| ≤ 1 / 2 →
      ‖hermitianTransform (gaussTests c lam n) z‖ ≤ C / (1 + Complex.normSq z) := by
  obtain ⟨M, hM, hbound⟩ := exists_paperFT_gaussTests_bound (c := c) hlam
  refine ⟨4 * M ^ 2, by positivity, fun n z hz => ?_⟩
  have hzc : |(conj z).im| ≤ 1 / 2 := by rwa [Complex.conj_im, abs_neg]
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

/-- Pointwise limit of the Hermitian transforms on the strip. -/
lemma hermitianTransform_gaussTests_tendsto {c lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) :
    Tendsto (fun n => hermitianTransform (gaussTests c lam n) z) atTop (𝓝 (gaussTest c lam z)) := by
  have hzc : |(conj z).im| ≤ 1 / 2 := by rwa [Complex.conj_im, abs_neg]
  rw [gaussTest_eq_half_mul_conj]
  unfold hermitianTransform
  exact (paperFT_gaussTests_tendsto hlam hz).mul
    ((Complex.continuous_conj.tendsto _).comp (paperFT_gaussTests_tendsto hlam hzc))

/-- The complex zero-side limit (Tannery against the local zero count). -/
theorem zeroSide_gaussTests_tendsto (c lam : ℝ) (hlam : 0 < lam) :
    Tendsto (fun n => zeroSide (hermitianTransform (gaussTests c lam n))) atTop
      (𝓝 (zeroSide (gaussTest c lam))) := by
  obtain ⟨C, -, hC⟩ := exists_hermitian_gaussTests_bound c lam hlam
  unfold zeroSide
  exact tendsto_tsum_zeroMult_of_strip_bound hC
    fun z hz => hermitianTransform_gaussTests_tendsto hlam hz

/-! ## C. The autocorrelations: a Gaussian majorant uniform in n, and the pointwise limit
autocorr (g n) u -> autocorr phi u. -/

lemma continuous_gaussPhi (c lam : ℝ) : Continuous (gaussPhi c lam) :=
  (contDiff_gaussPhi c lam).continuous

/-- The truncation is dominated by phi (chi_n <= 1). -/
lemma norm_gaussTests_le (c lam : ℝ) (n : ℕ) (u : ℝ) :
    ‖gaussTests c lam n u‖ ≤ ‖gaussPhi c lam u‖ := by
  unfold gaussTests
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (norm_nonneg _) (abs_cutoff_le_one n u)

/-- The v-majorant of the autocorrelation integrand at lag u:
‖K‖^2 ((v - u/2)^2 + u^2/4) exp (-2b (v - u/2)^2) exp (-(b/2) u^2). -/
def vMaj (lam u v : ℝ) : ℝ :=
  ‖gaussK lam‖ ^ 2 * (((v - u / 2) ^ 2 + u ^ 2 / 4) * Real.exp (-(2 * gaussB lam) * (v - u / 2) ^ 2))
    * Real.exp (-(gaussB lam / 2) * u ^ 2)

/-- |phi v| |phi (v - u)| <= vMaj u v: |v||v-u| <= (v^2 + (v-u)^2)/2 and
v^2 + (v-u)^2 = 2 (v - u/2)^2 + u^2/2. -/
lemma norm_phi_mul_phi_le (c lam u v : ℝ) :
    ‖gaussPhi c lam v‖ * ‖gaussPhi c lam (v - u)‖ ≤ vMaj lam u v := by
  rw [norm_gaussPhi, norm_gaussPhi]
  have hexp : Real.exp (-gaussB lam * v ^ 2) * Real.exp (-gaussB lam * (v - u) ^ 2)
      = Real.exp (-(2 * gaussB lam) * (v - u / 2) ^ 2) * Real.exp (-(gaussB lam / 2) * u ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hprod : |v| * |v - u| ≤ (v - u / 2) ^ 2 + u ^ 2 / 4 := by
    have h1 : |v| ^ 2 = v ^ 2 := sq_abs v
    have h2 : |v - u| ^ 2 = (v - u) ^ 2 := sq_abs _
    nlinarith [sq_nonneg (|v| - |v - u|)]
  unfold vMaj
  calc ‖gaussK lam‖ * |v| * Real.exp (-gaussB lam * v ^ 2)
        * (‖gaussK lam‖ * |v - u| * Real.exp (-gaussB lam * (v - u) ^ 2))
      = ‖gaussK lam‖ ^ 2 * (|v| * |v - u|)
        * (Real.exp (-gaussB lam * v ^ 2) * Real.exp (-gaussB lam * (v - u) ^ 2)) := by ring
    _ ≤ ‖gaussK lam‖ ^ 2 * ((v - u / 2) ^ 2 + u ^ 2 / 4)
        * (Real.exp (-gaussB lam * v ^ 2) * Real.exp (-gaussB lam * (v - u) ^ 2)) := by gcongr
    _ = _ := by rw [hexp]; ring

/-- (w^2 + a) exp (-beta w^2) is integrable for beta > 0. -/
lemma integrable_sq_add_mul_gauss {β : ℝ} (hβ : 0 < β) (a : ℝ) :
    Integrable (fun w : ℝ => (w ^ 2 + a) * Real.exp (-β * w ^ 2)) := by
  have h2 := integrable_abs_pow_mul_exp_quadratic_abs hβ 0 2
  have h0 := integrable_exp_quadratic hβ 0
  refine (h2.add (h0.const_mul a)).congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [Pi.add_apply, sq_abs, zero_mul, add_zero]
  ring

lemma integrable_vMaj {lam : ℝ} (hlam : 0 < lam) (u : ℝ) : Integrable (vMaj lam u) := by
  have hb : 0 < 2 * gaussB lam := by have := gaussB_pos hlam; positivity
  have h := ((integrable_sq_add_mul_gauss hb (u ^ 2 / 4)).comp_sub_right (u / 2)).const_mul
    (‖gaussK lam‖ ^ 2)
  exact h.mul_const (Real.exp (-(gaussB lam / 2) * u ^ 2))

/-- I0 = ∫ exp (-2b w^2), I2 = ∫ w^2 exp (-2b w^2): the two Gaussian moments of the majorant. -/
def gaussI0 (lam : ℝ) : ℝ := ∫ w : ℝ, Real.exp (-(2 * gaussB lam) * w ^ 2)

def gaussI2 (lam : ℝ) : ℝ := ∫ w : ℝ, w ^ 2 * Real.exp (-(2 * gaussB lam) * w ^ 2)

lemma gaussI0_nonneg (lam : ℝ) : 0 ≤ gaussI0 lam :=
  integral_nonneg fun _ => (Real.exp_pos _).le

lemma gaussI2_nonneg (lam : ℝ) : 0 ≤ gaussI2 lam :=
  integral_nonneg fun w => by positivity

/-- The Gaussian majorant of every autocorr (g n) at lag u, uniform in n:
‖K‖^2 (I2 + (I0/4) u^2) exp (-(b/2) u^2). -/
def autocorrMaj (lam u : ℝ) : ℝ :=
  ‖gaussK lam‖ ^ 2 * (gaussI2 lam + gaussI0 lam / 4 * u ^ 2) * Real.exp (-(gaussB lam / 2) * u ^ 2)

lemma autocorrMaj_nonneg (lam u : ℝ) : 0 ≤ autocorrMaj lam u := by
  unfold autocorrMaj
  have := gaussI0_nonneg lam
  have := gaussI2_nonneg lam
  positivity

lemma autocorrMaj_neg (lam u : ℝ) : autocorrMaj lam (-u) = autocorrMaj lam u := by
  simp only [autocorrMaj, neg_sq]

lemma integral_vMaj {lam : ℝ} (hlam : 0 < lam) (u : ℝ) :
    ∫ v : ℝ, vMaj lam u v = autocorrMaj lam u := by
  have hb : 0 < 2 * gaussB lam := by have := gaussB_pos hlam; positivity
  unfold vMaj
  rw [integral_mul_const, integral_const_mul]
  have hshift : ∫ v : ℝ, ((v - u / 2) ^ 2 + u ^ 2 / 4) * Real.exp (-(2 * gaussB lam) * (v - u / 2) ^ 2)
      = ∫ w : ℝ, (w ^ 2 + u ^ 2 / 4) * Real.exp (-(2 * gaussB lam) * w ^ 2) :=
    integral_sub_right_eq_self
      (fun w => (w ^ 2 + u ^ 2 / 4) * Real.exp (-(2 * gaussB lam) * w ^ 2)) (u / 2)
  have hsplit : ∫ w : ℝ, (w ^ 2 + u ^ 2 / 4) * Real.exp (-(2 * gaussB lam) * w ^ 2)
      = gaussI2 lam + u ^ 2 / 4 * gaussI0 lam := by
    unfold gaussI2 gaussI0
    have h2 := integrable_abs_pow_mul_exp_quadratic_abs hb 0 2
    have h0 := integrable_exp_quadratic hb 0
    have h2' : Integrable (fun w : ℝ => w ^ 2 * Real.exp (-(2 * gaussB lam) * w ^ 2)) := by
      refine h2.congr (Filter.Eventually.of_forall fun w => ?_)
      simp only [sq_abs, zero_mul, add_zero]
    have h0' : Integrable (fun w : ℝ => Real.exp (-(2 * gaussB lam) * w ^ 2)) := by
      refine h0.congr (Filter.Eventually.of_forall fun w => ?_)
      simp only [zero_mul, add_zero]
    rw [← integral_const_mul, ← integral_add h2' (h0'.const_mul _)]
    congr 1
    funext w
    ring
  rw [hshift, hsplit]
  unfold autocorrMaj
  ring

/-- The autocorrelation integrand of a truncation is dominated by vMaj. -/
lemma norm_gaussTests_mul_conj_le (c lam : ℝ) (n : ℕ) (u v : ℝ) :
    ‖gaussTests c lam n v * conj (gaussTests c lam n (v - u))‖ ≤ vMaj lam u v := by
  rw [norm_mul, Complex.norm_conj]
  calc ‖gaussTests c lam n v‖ * ‖gaussTests c lam n (v - u)‖
      ≤ ‖gaussPhi c lam v‖ * ‖gaussPhi c lam (v - u)‖ :=
        mul_le_mul (norm_gaussTests_le c lam n v) (norm_gaussTests_le c lam n (v - u))
          (norm_nonneg _) (norm_nonneg _)
    _ ≤ vMaj lam u v := norm_phi_mul_phi_le c lam u v

/-- ‖autocorr (g n) u‖ <= autocorrMaj lam u, uniformly in n. -/
theorem norm_autocorr_gaussTests_le {c lam : ℝ} (hlam : 0 < lam) (n : ℕ) (u : ℝ) :
    ‖autocorr (gaussTests c lam n) u‖ ≤ autocorrMaj lam u := by
  unfold autocorr
  rw [← integral_vMaj hlam u]
  exact norm_integral_le_of_norm_le (integrable_vMaj hlam u)
    (Filter.Eventually.of_forall fun v => norm_gaussTests_mul_conj_le c lam n u v)

/-- Pointwise: autocorr (g n) u -> autocorr phi u (dominated convergence in v; the integrand
is eventually constant in n once n + 1 >= max (|v|, |v - u|)). -/
theorem autocorr_gaussTests_tendsto {c lam : ℝ} (hlam : 0 < lam) (u : ℝ) :
    Tendsto (fun n => autocorr (gaussTests c lam n) u) atTop
      (𝓝 (autocorr (gaussPhi c lam) u)) := by
  unfold autocorr
  refine tendsto_integral_of_dominated_convergence (vMaj lam u) (fun n => ?_)
    (integrable_vMaj hlam u)
    (fun n => Filter.Eventually.of_forall fun v => norm_gaussTests_mul_conj_le c lam n u v)
    (Filter.Eventually.of_forall fun v => ?_)
  · have hc : Continuous (gaussTests c lam n) := (isWeilTest_gaussTests c lam n).1.continuous
    exact (hc.mul (Complex.continuous_conj.comp
      (hc.comp (continuous_id.sub continuous_const)))).aestronglyMeasurable
  · apply tendsto_const_nhds.congr'
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    refine ⟨⌈|v|⌉₊ + ⌈|v - u|⌉₊, fun n hn => ?_⟩
    have hn1 : (⌈|v|⌉₊ : ℝ) ≤ n := by exact_mod_cast (by omega : ⌈|v|⌉₊ ≤ n)
    have hn2 : (⌈|v - u|⌉₊ : ℝ) ≤ n := by exact_mod_cast (by omega : ⌈|v - u|⌉₊ ≤ n)
    have h1 : cutoff n v = 1 := cutoff_eq_one (by linarith [Nat.le_ceil |v|])
    have h2 : cutoff n (v - u) = 1 := cutoff_eq_one (by linarith [Nat.le_ceil |v - u|])
    unfold gaussTests
    simp [h1, h2]

/-! ## D. The prime side passes to the limit: dominated convergence in n against
Lambda(k)/sqrt k times a Gaussian in log k. -/

/-- The summable majorant of the prime-side terms. -/
def primeBound (lam : ℝ) (k : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt k / Real.sqrt k) * (2 * autocorrMaj lam (Real.log k))

lemma primeBound_nonneg (lam : ℝ) (k : ℕ) : 0 ≤ primeBound lam k := by
  unfold primeBound
  have := autocorrMaj_nonneg lam (Real.log k)
  have := ArithmeticFunction.vonMangoldt_nonneg (n := k)
  positivity

lemma norm_primeTerm_le {c lam : ℝ} (hlam : 0 < lam) (n k : ℕ) :
    ‖((ArithmeticFunction.vonMangoldt k / Real.sqrt k : ℝ) : ℂ)
      * (autocorr (gaussTests c lam n) (Real.log k) + autocorr (gaussTests c lam n) (-Real.log k))‖
      ≤ primeBound lam k := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))]
  unfold primeBound
  gcongr
  calc ‖autocorr (gaussTests c lam n) (Real.log k) + autocorr (gaussTests c lam n) (-Real.log k)‖
      ≤ ‖autocorr (gaussTests c lam n) (Real.log k)‖
        + ‖autocorr (gaussTests c lam n) (-Real.log k)‖ := norm_add_le _ _
    _ ≤ autocorrMaj lam (Real.log k) + autocorrMaj lam (-Real.log k) :=
        add_le_add (norm_autocorr_gaussTests_le hlam n _) (norm_autocorr_gaussTests_le hlam n _)
    _ = 2 * autocorrMaj lam (Real.log k) := by rw [autocorrMaj_neg]; ring

/-- Sum_k Lambda(k)/sqrt k * 2 M(log k) < infinity: for k >= exp (12/b) the Gaussian factor is
<= k^{-6}, Lambda(k)/sqrt k <= log k <= k and (log k)^2 <= k^2, so the term is <= D k^{-3}. -/
theorem summable_primeBound {lam : ℝ} (hlam : 0 < lam) : Summable (primeBound lam) := by
  have hb : 0 < gaussB lam := gaussB_pos hlam
  have hI0 := gaussI0_nonneg lam
  have hI2 := gaussI2_nonneg lam
  set D : ℝ := 2 * ‖gaussK lam‖ ^ 2 * (gaussI2 lam + gaussI0 lam / 4) with hD
  refine Summable.of_norm_bounded_eventually (g := fun k : ℕ => D * ((k : ℝ) ^ 3)⁻¹)
    ((Real.summable_nat_pow_inv.mpr (by norm_num)).mul_left D) ?_
  rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop]
  refine ⟨⌈Real.exp (12 / gaussB lam)⌉₊ + 1, fun k hk => ?_⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hkpos : (0 : ℝ) < k := by linarith
  have hlogk : 12 / gaussB lam ≤ Real.log k := by
    rw [Real.le_log_iff_exp_le hkpos]
    calc Real.exp (12 / gaussB lam) ≤ ⌈Real.exp (12 / gaussB lam)⌉₊ := Nat.le_ceil _
      _ ≤ k := by exact_mod_cast (by omega : ⌈Real.exp (12 / gaussB lam)⌉₊ ≤ k)
  have hlog0 : 0 ≤ Real.log k := Real.log_nonneg hk1
  have hlogk_le : Real.log k ≤ k := by linarith [Real.log_le_sub_one_of_pos hkpos]
  have hΛ : ArithmeticFunction.vonMangoldt k / Real.sqrt k ≤ k := by
    calc ArithmeticFunction.vonMangoldt k / Real.sqrt k ≤ ArithmeticFunction.vonMangoldt k :=
          div_le_self ArithmeticFunction.vonMangoldt_nonneg (Real.one_le_sqrt.mpr hk1)
      _ ≤ Real.log k := ArithmeticFunction.vonMangoldt_le_log
      _ ≤ k := hlogk_le
  have hexp : Real.exp (-(gaussB lam / 2) * Real.log k ^ 2) ≤ ((k : ℝ) ^ 6)⁻¹ := by
    have h12 : 12 ≤ Real.log k * gaussB lam := by
      rwa [div_le_iff₀ hb] at hlogk
    have h6 : 6 * Real.log k ≤ (gaussB lam / 2) * Real.log k ^ 2 := by nlinarith
    calc Real.exp (-(gaussB lam / 2) * Real.log k ^ 2)
        ≤ Real.exp (-(6 * Real.log k)) := Real.exp_le_exp.mpr (by linarith)
      _ = ((k : ℝ) ^ 6)⁻¹ := by
          rw [Real.exp_neg, show (6 : ℝ) * Real.log k = ((6 : ℕ) : ℝ) * Real.log k by norm_num,
            Real.exp_nat_mul, Real.exp_log hkpos]
  have hlogsq : Real.log k ^ 2 ≤ (k : ℝ) ^ 2 := pow_le_pow_left₀ hlog0 hlogk_le 2
  have hk2 : 1 ≤ (k : ℝ) ^ 2 := one_le_pow₀ hk1
  have hI2k : gaussI2 lam + gaussI0 lam / 4 * (k : ℝ) ^ 2 ≤ (gaussI2 lam + gaussI0 lam / 4) * (k : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hI2 (sub_nonneg.mpr hk2)]
  rw [Real.norm_eq_abs, abs_of_nonneg (primeBound_nonneg lam k)]
  unfold primeBound autocorrMaj
  calc ArithmeticFunction.vonMangoldt k / Real.sqrt k
        * (2 * (‖gaussK lam‖ ^ 2 * (gaussI2 lam + gaussI0 lam / 4 * Real.log k ^ 2)
          * Real.exp (-(gaussB lam / 2) * Real.log k ^ 2)))
      ≤ (k : ℝ) * (2 * (‖gaussK lam‖ ^ 2 * (gaussI2 lam + gaussI0 lam / 4 * (k : ℝ) ^ 2)
          * ((k : ℝ) ^ 6)⁻¹)) := by gcongr
    _ ≤ (k : ℝ) * (2 * (‖gaussK lam‖ ^ 2 * ((gaussI2 lam + gaussI0 lam / 4) * (k : ℝ) ^ 2)
          * ((k : ℝ) ^ 6)⁻¹)) := by gcongr
    _ = D * ((k : ℝ) ^ 3)⁻¹ := by
        rw [hD]
        field_simp

/-- The prime side of the truncations converges to the prime side of autocorr phi. -/
theorem primeSide_gaussTests_tendsto {c lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n => primeSide (autocorr (gaussTests c lam n))) atTop
      (𝓝 (primeSide (autocorr (gaussPhi c lam)))) := by
  unfold primeSide
  refine tendsto_tsum_of_dominated_convergence (summable_primeBound hlam) (fun k => ?_)
    (Filter.Eventually.of_forall fun n k => norm_primeTerm_le hlam n k)
  exact ((autocorr_gaussTests_tendsto hlam _).add (autocorr_gaussTests_tendsto hlam _)).const_mul _

/-! ## E. The archimedean side passes to the limit. -/

lemma continuous_autocorr_gaussTests (c lam : ℝ) (n : ℕ) :
    Continuous (autocorr (gaussTests c lam n)) :=
  (RvMBridge5.isWeilTest_autocorr (isWeilTest_gaussTests c lam n)).1.continuous

/-- The u-majorant of the kernel integrand on |Re s - 1/2| <= 1/2. -/
def kernelMaj (lam u : ℝ) : ℝ := autocorrMaj lam u * Real.exp ((1 / 2) * |u|)

lemma integrable_kernelMaj {lam : ℝ} (hlam : 0 < lam) : Integrable (kernelMaj lam) := by
  have hb : 0 < gaussB lam / 2 := half_pos (gaussB_pos hlam)
  have h0 := integrable_abs_pow_mul_exp_quadratic_abs hb (1 / 2) 0
  have h2 := integrable_abs_pow_mul_exp_quadratic_abs hb (1 / 2) 2
  refine ((h0.const_mul (‖gaussK lam‖ ^ 2 * gaussI2 lam)).add
    (h2.const_mul (‖gaussK lam‖ ^ 2 * (gaussI0 lam / 4)))).congr
    (Filter.Eventually.of_forall fun u => ?_)
  simp only [Pi.add_apply, kernelMaj, autocorrMaj, pow_zero, sq_abs, one_mul, Real.exp_add]
  ring

lemma norm_kernel_term_le {c lam : ℝ} (hlam : 0 < lam) {s : ℂ} (hs : |s.re - 1 / 2| ≤ 1 / 2)
    (n : ℕ) (u : ℝ) :
    ‖autocorr (gaussTests c lam n) u * Complex.exp ((s - 1 / 2) * (u : ℂ))‖ ≤ kernelMaj lam u := by
  rw [norm_mul, Complex.norm_exp]
  have hre : ((s - 1 / 2) * (u : ℂ)).re = (s.re - 1 / 2) * u := by
    simp [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [hre]
  unfold kernelMaj
  have hexp : (s.re - 1 / 2) * u ≤ 1 / 2 * |u| := by
    calc (s.re - 1 / 2) * u ≤ |(s.re - 1 / 2) * u| := le_abs_self _
      _ = |s.re - 1 / 2| * |u| := abs_mul _ _
      _ ≤ 1 / 2 * |u| := mul_le_mul_of_nonneg_right hs (abs_nonneg u)
  exact mul_le_mul (norm_autocorr_gaussTests_le hlam n u) (Real.exp_le_exp.mpr hexp)
    (Real.exp_pos _).le (autocorrMaj_nonneg lam u)

/-- weilKernel (autocorr (g n)) s -> weilKernel (autocorr phi) s on |Re s - 1/2| <= 1/2. -/
theorem weilKernel_gaussTests_tendsto {c lam : ℝ} (hlam : 0 < lam) {s : ℂ}
    (hs : |s.re - 1 / 2| ≤ 1 / 2) :
    Tendsto (fun n => weilKernel (autocorr (gaussTests c lam n)) s) atTop
      (𝓝 (weilKernel (autocorr (gaussPhi c lam)) s)) := by
  unfold weilKernel
  refine tendsto_integral_of_dominated_convergence (kernelMaj lam) (fun n => ?_)
    (integrable_kernelMaj hlam)
    (fun n => Filter.Eventually.of_forall fun u => norm_kernel_term_le hlam hs n u)
    (Filter.Eventually.of_forall fun u => ?_)
  · exact ((continuous_autocorr_gaussTests c lam n).mul (by fun_prop)).aestronglyMeasurable
  · exact (autocorr_gaussTests_tendsto hlam u).mul_const _

lemma gammaOf_half_add (r : ℝ) : gammaOf (1 / 2 + (r : ℂ) * I) = r := by
  unfold gammaOf
  rw [div_eq_iff Complex.I_ne_zero]
  ring

/-- The n-uniform C/(1 + r^2) bound of the transforms of the autocorrelations on the line. -/
lemma exists_paperFT_autocorr_gaussTests_bound (c lam : ℝ) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n (r : ℝ), ‖paperFT (autocorr (gaussTests c lam n)) r‖ ≤ C / (1 + r ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_hermitian_gaussTests_bound c lam hlam
  refine ⟨C, hC0, fun n r => ?_⟩
  rw [← RvMBridge4.weilKernel_line, weilKernel_autocorr (isWeilTest_gaussTests c lam n),
    gammaOf_half_add]
  have h := hC n r (by rw [Complex.ofReal_im, abs_zero]; norm_num)
  rwa [Complex.normSq_ofReal, ← pow_two] at h

/-- The r-majorant of the archimedean integrand: C/(1+r^2) times the two Gamma_R log-derivative
factors plus log pi, in the shape Zeta23's majorant lemma delivers. -/
def archBound (C : ℝ) (r : ℝ) : ℝ :=
  ‖((C / (1 + r ^ 2) : ℝ) : ℂ) * logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) : ℂ) + (r : ℂ) * I)‖
    + ‖((C / (1 + (-r) ^ 2) : ℝ) : ℂ) * logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) : ℂ) + ((-r : ℝ) : ℂ) * I)‖
    + C / (1 + r ^ 2) * Real.log Real.pi

lemma integrable_archBound {C : ℝ} (hC : 0 ≤ C) : Integrable (archBound C) := by
  have hcont : Continuous (fun t : ℝ => ((C / (1 + t ^ 2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (continuous_const.div (by fun_prop) (fun t => by positivity))
  have hb : ∀ t : ℝ, ‖((C / (1 + t ^ 2) : ℝ) : ℂ)‖ ≤ C / (1 + t ^ 2) := fun t => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 := Zeta23.WeilEF.integrable_mul_logDeriv_Gammaℝ_of_decay hcont hC hb (σ := 1 / 2)
    (by norm_num) (by norm_num)
  have h2 := h1.comp_neg
  have h3 : Integrable (fun t : ℝ => C / (1 + t ^ 2) * Real.log Real.pi) := by
    refine ((integrable_inv_one_add_sq.const_mul C).mul_const (Real.log Real.pi)).congr
      (Filter.Eventually.of_forall fun t => ?_)
    simp only [div_eq_mul_inv]
  exact (h1.norm.add h2.norm).add h3

lemma norm_archIntegrand_le {c lam C : ℝ}
    (hC : ∀ n (r : ℝ), ‖paperFT (autocorr (gaussTests c lam n)) r‖ ≤ C / (1 + r ^ 2))
    (n : ℕ) (r : ℝ) :
    ‖archIntegrand (autocorr (gaussTests c lam n)) r‖ ≤ archBound C r := by
  rw [RvMBridge4.archIntegrand_eq, RvMBridge4.gammaBracket_eq]
  have hlogpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hh := hC n r
  have hpos : 0 ≤ C / (1 + r ^ 2) := le_trans (norm_nonneg _) hh
  unfold archBound
  have hL : (((1 / 2 : ℝ) : ℂ) + ((-r : ℝ) : ℂ) * I) = 1 / 2 - (r : ℂ) * I := by push_cast; ring
  have hL' : (((1 / 2 : ℝ) : ℂ) + (r : ℂ) * I) = 1 / 2 + (r : ℂ) * I := by push_cast; ring
  rw [hL, hL', neg_sq, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hpos]
  set h := paperFT (autocorr (gaussTests c lam n)) r
  set Lp := logDeriv Complex.Gammaℝ (1 / 2 + (r : ℂ) * I)
  set Lm := logDeriv Complex.Gammaℝ (1 / 2 - (r : ℂ) * I)
  calc ‖h * (Lp + Lm) + h * ((Real.log Real.pi : ℝ) : ℂ)‖
      ≤ ‖h * (Lp + Lm)‖ + ‖h * ((Real.log Real.pi : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ ‖h‖ * (‖Lp‖ + ‖Lm‖) + ‖h‖ * Real.log Real.pi := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogpi]
        gcongr
        exact norm_add_le _ _
    _ ≤ C / (1 + r ^ 2) * (‖Lp‖ + ‖Lm‖) + C / (1 + r ^ 2) * Real.log Real.pi := by gcongr
    _ = _ := by ring

/-- ∫ archIntegrand (autocorr (g n)) -> ∫ archIntegrand (autocorr phi). -/
theorem archIntegral_gaussTests_tendsto {c lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n => ∫ r : ℝ, archIntegrand (autocorr (gaussTests c lam n)) r) atTop
      (𝓝 (∫ r : ℝ, archIntegrand (autocorr (gaussPhi c lam)) r)) := by
  obtain ⟨C, hC0, hC⟩ := exists_paperFT_autocorr_gaussTests_bound c lam hlam
  refine tendsto_integral_of_dominated_convergence (archBound C)
    (fun n => (RvMBridge4.integrable_archIntegrand
      (RvMBridge5.isWeilTest_autocorr (isWeilTest_gaussTests c lam n))).aestronglyMeasurable)
    (integrable_archBound hC0)
    (fun n => Filter.Eventually.of_forall fun r => norm_archIntegrand_le hC n r)
    (Filter.Eventually.of_forall fun r => ?_)
  unfold archIntegrand
  refine (weilKernel_gaussTests_tendsto hlam (s := 1 / 2 + (r : ℂ) * I) ?_).mul_const _
  simp [Complex.add_re, Complex.mul_re]

/-- The archimedean side of the truncations converges to that of autocorr phi. -/
theorem archSide_gaussTests_tendsto {c lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n => archSide (autocorr (gaussTests c lam n))) atTop
      (𝓝 (archSide (autocorr (gaussPhi c lam)))) := by
  unfold archSide
  refine (((weilKernel_gaussTests_tendsto hlam (s := 0) (by norm_num)).add
    (weilKernel_gaussTests_tendsto hlam (s := 1) (by norm_num))).sub
    ((autocorr_gaussTests_tendsto hlam 0).mul_const _)).add
    ((archIntegral_gaussTests_tendsto hlam).const_mul _)

/-! ## F. Deliverable 2: the Gaussian explicit formula, and the prime-side form of the Wall. -/

/-- **The Gaussian explicit formula.**  The Gaussian-weighted zero sum IS the archimedean side
minus the prime side of the Hermitian autocorrelation of phi_{c,lam} = gaussPhi c lam. -/
theorem zeroSide_gaussTest_eq (c lam : ℝ) (hlam : 0 < lam) :
    RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)
      = WeilExplicit.archSide (WeilExplicit.autocorr (RvMBridge8.gaussPhi c lam))
        - WeilExplicit.primeSide (WeilExplicit.autocorr (RvMBridge8.gaussPhi c lam)) := by
  have hL : Tendsto (fun n => weilForm (autocorr (gaussTests c lam n))) atTop
      (𝓝 (archSide (autocorr (gaussPhi c lam)) - primeSide (autocorr (gaussPhi c lam)))) := by
    unfold weilForm
    exact (archSide_gaussTests_tendsto hlam).sub (primeSide_gaussTests_tendsto hlam)
  have hR := zeroSide_gaussTests_tendsto c lam hlam
  have heq : (fun n => weilForm (autocorr (gaussTests c lam n)))
      = fun n => zeroSide (hermitianTransform (gaussTests c lam n)) :=
    funext fun n => weilForm_autocorr_eq_zeroSide (isWeilTest_gaussTests c lam n)
  rw [heq] at hL
  exact tendsto_nhds_unique hR hL

/-- Gaussian positivity in prime-side form: for every centre and width the archimedean side of
autocorr phi_{c,lam} dominates its prime side (real parts). -/
theorem gaussian_positivity_iff_prime_le_arch :
    GaussianPositivity ↔ ∀ (c lam : ℝ), 0 < lam →
      (WeilExplicit.primeSide (WeilExplicit.autocorr (RvMBridge8.gaussPhi c lam))).re
        ≤ (WeilExplicit.archSide (WeilExplicit.autocorr (RvMBridge8.gaussPhi c lam))).re := by
  unfold GaussianPositivity
  refine forall_congr' fun c => forall_congr' fun lam => imp_congr_right fun hlam => ?_
  rw [zeroSide_gaussTest_eq c lam hlam, Complex.sub_re, sub_nonneg]

/-- **The Wall, prime-side form**: RH iff arch_{c,lam} >= prime_{c,lam} for all c and lam > 0. -/
theorem rh_iff_gaussian_prime_le_arch :
    RiemannHypothesis ↔ ∀ (c lam : ℝ), 0 < lam →
      (WeilExplicit.primeSide (WeilExplicit.autocorr (RvMBridge8.gaussPhi c lam))).re
        ≤ (WeilExplicit.archSide (WeilExplicit.autocorr (RvMBridge8.gaussPhi c lam))).re :=
  rh_iff_gaussian_positivity.trans gaussian_positivity_iff_prime_le_arch

end RvMBridge10
