/-
  PFConverseA -- pole-free Weil converse, part A (2026-10-12): the pole-free test family.

  For a centre c and lam > 0 let g_n = gaussTests c lam n = phi * chi_n (E6Bridge8) and put
      t_n := g_n'' - g_n / 4.
  Two integrations by parts give paperFT t_n z = -(z^2 + 1/4) paperFT g_n z for every z, so
  t_n is EXACTLY pole-free (paperFT t_n (+-i/2) = 0), and
      hermitianTransform t_n z = (z^2 + 1/4)^2 hermitianTransform g_n z
                              -> (z^2 + 1/4)^2 gaussTest c lam z      on the strip.
  A third derivative gives the truncation-uniform bound ‖paperFT t_n z‖ <= 2 M / (1 + ‖z‖) on the
  strip, hence ‖hermitianTransform t_n z‖ <= 4 M^2 / (1 + normSq z): the Tannery majorant of
  E6Bridge6 section H applies unchanged.

  Calculus: functions K * P(u) * exp (-b u^2 - i c u) with P a complex polynomial are closed under
  d/du (P -> P' + P * (-2 b X - i c)); the cutoff derivatives are iterated derivatives of the bump,
  uniformly bounded.  No zeta, no zeros.  Nothing here is progress on RH; conjecture1_proved = False.
-/
import E6Bridge8

open Zeta23 Complex MeasureTheory Filter Topology Polynomial
open scoped ComplexConjugate

noncomputable section

namespace RvMBridgePF
open WeilExplicit RvMBridge6 RvMBridge8 RvMBridgeGauss

/-! ## A. Polynomial times Gaussian. -/

/-- E(u) = exp (-b u^2 - i c u). -/
def gE (c b : ℝ) (u : ℝ) : ℂ := cexp (-(b : ℂ) * (u : ℂ) ^ 2 - I * c * u)

/-- K P(u) E(u). -/
def gp (K : ℂ) (c b : ℝ) (P : ℂ[X]) (u : ℝ) : ℂ := K * P.eval (u : ℂ) * gE c b u

/-- The derivative operator on the polynomial factor. -/
def dop (c b : ℝ) (P : ℂ[X]) : ℂ[X] :=
  derivative P + P * (Polynomial.C (-(2 * (b : ℂ))) * X - Polynomial.C (I * c))

lemma hasDerivAt_gE (c b u : ℝ) :
    HasDerivAt (gE c b) (gE c b u * (-(2 * (b : ℂ)) * u - I * c)) u := by
  have hE : HasDerivAt (fun x : ℂ => -(b : ℂ) * x ^ 2 - I * c * x)
      (-(b : ℂ) * (2 * u) - I * c) (u : ℂ) := by
    have := ((hasDerivAt_pow 2 (u : ℂ)).const_mul (-(b : ℂ))).sub
      ((hasDerivAt_id (u : ℂ)).const_mul (I * c))
    refine this.congr_deriv ?_
    push_cast
    ring
  have h := hE.cexp.comp_ofReal
  unfold gE
  convert h using 1
  ring

lemma hasDerivAt_gp (K : ℂ) (c b : ℝ) (P : ℂ[X]) (u : ℝ) :
    HasDerivAt (gp K c b P) (gp K c b (dop c b P) u) u := by
  have hP : HasDerivAt (fun x : ℝ => P.eval (x : ℂ)) (P.derivative.eval (u : ℂ)) u :=
    (Polynomial.hasDerivAt P (u : ℂ)).comp_ofReal
  have h := ((hP.const_mul K).mul (hasDerivAt_gE c b u))
  have heq : gp K c b P = fun y : ℝ => K * P.eval (y : ℂ) * gE c b y := rfl
  rw [heq]
  refine h.congr_deriv ?_
  unfold gp dop
  simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X]
  ring

lemma continuous_gp (K : ℂ) (c b : ℝ) (P : ℂ[X]) : Continuous (gp K c b P) := by
  unfold gp gE
  have h1 : Continuous (fun x : ℝ => P.eval (x : ℂ)) :=
    (Polynomial.continuous P).comp Complex.continuous_ofReal
  fun_prop

lemma contDiff_gp (K : ℂ) (c b : ℝ) (P : ℂ[X]) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gp K c b P) := by
  unfold gp gE
  have hof : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => (u : ℂ)) :=
    Complex.ofRealCLM.contDiff
  have hP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => P.eval (u : ℂ)) := by
    have : (fun u : ℝ => P.eval (u : ℂ))
        = fun u : ℝ => ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * (u : ℂ) ^ i := by
      funext u; exact eval_eq_sum_range _
    rw [this]
    exact ContDiff.sum fun i _ => contDiff_const.mul (hof.pow i)
  refine (contDiff_const.mul hP).mul (ContDiff.cexp ?_)
  exact (contDiff_const.mul (hof.pow 2)).sub (contDiff_const.mul hof)

/-- |P|(u) := Sum_i ‖coeff_i‖ |u|^i, a majorant for ‖P(u)‖. -/
def pabs (P : ℂ[X]) (u : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖ * |u| ^ i

lemma pabs_nonneg (P : ℂ[X]) (u : ℝ) : 0 ≤ pabs P u :=
  Finset.sum_nonneg fun i _ => by positivity

lemma norm_eval_le_pabs (P : ℂ[X]) (u : ℝ) : ‖P.eval (u : ℂ)‖ ≤ pabs P u := by
  rw [eval_eq_sum_range]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  unfold pabs
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]

lemma norm_gE (c b u : ℝ) : ‖gE c b u‖ = Real.exp (-b * u ^ 2) := by
  unfold gE
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, pow_two]

lemma norm_gp_le (K : ℂ) (c b : ℝ) (P : ℂ[X]) (u : ℝ) :
    ‖gp K c b P u‖ ≤ ‖K‖ * pabs P u * Real.exp (-b * u ^ 2) := by
  unfold gp
  rw [norm_mul, norm_mul, norm_gE]
  gcongr
  exact norm_eval_le_pabs P u

/-- The integrable majorant |P|(u) exp (-b u^2 + |u|/2). -/
lemma integrable_pabs_mul {b : ℝ} (hb : 0 < b) (P : ℂ[X]) :
    Integrable (fun u : ℝ => pabs P u * Real.exp (-b * u ^ 2 + (1 / 2) * |u|)) := by
  unfold pabs
  simp only [Finset.sum_mul]
  refine integrable_finsetSum _ fun i _ => ?_
  have := (integrable_abs_pow_mul_exp_quadratic_abs hb (1 / 2) i).const_mul ‖P.coeff i‖
  refine this.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only
  ring

/-! ## B. Cutoff derivatives. -/

lemma contDiff_bump_nat (k : ℕ) : ContDiff ℝ (k : WithTop ℕ∞) (bump : ℝ → ℝ) := bump.contDiff

lemma hasCompactSupport_iteratedDeriv_bump (k : ℕ) :
    HasCompactSupport (iteratedDeriv k (bump : ℝ → ℝ)) := by
  induction k with
  | zero => simpa using bump.hasCompactSupport
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv

lemma exists_iteratedDeriv_bump_bound (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, |iteratedDeriv k (bump : ℝ → ℝ) y| ≤ B := by
  have hc : Continuous (iteratedDeriv k (bump : ℝ → ℝ)) :=
    ContDiff.continuous_iteratedDeriv' k (contDiff_bump_nat k)
  obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support (hasCompactSupport_iteratedDeriv_bump k)
  exact ⟨max B 0, le_max_right _ _, fun y => (Real.norm_eq_abs _ ▸ hB y).trans (le_max_left _ _)⟩

/-- A uniform bound on the k-th derivative of the bump. -/
def Bd (k : ℕ) : ℝ := Classical.choose (exists_iteratedDeriv_bump_bound k)

lemma Bd_nonneg (k : ℕ) : 0 ≤ Bd k := (Classical.choose_spec (exists_iteratedDeriv_bump_bound k)).1

lemma abs_iteratedDeriv_bump_le (k : ℕ) (y : ℝ) : |iteratedDeriv k (bump : ℝ → ℝ) y| ≤ Bd k :=
  (Classical.choose_spec (exists_iteratedDeriv_bump_bound k)).2 y

/-- The k-th derivative of chi_n: bump^{(k)}(u/(n+1)) (1/(n+1))^k. -/
def cd (k n : ℕ) (u : ℝ) : ℂ :=
  ((iteratedDeriv k (bump : ℝ → ℝ) (u / ((n : ℝ) + 1)) * (1 / ((n : ℝ) + 1)) ^ k : ℝ) : ℂ)

lemma cd_zero (n : ℕ) (u : ℝ) : cd 0 n u = (cutoff n u : ℂ) := by
  simp [cd, cutoff]

lemma hasDerivAt_cd (k n : ℕ) (u : ℝ) : HasDerivAt (cd k n) (cd (k + 1) n u) u := by
  have hdiff : Differentiable ℝ (iteratedDeriv k (bump : ℝ → ℝ)) :=
    ContDiff.differentiable_iteratedDeriv' k (contDiff_bump_nat (k + 1))
  have hb : HasDerivAt (iteratedDeriv k (bump : ℝ → ℝ))
      (iteratedDeriv (k + 1) (bump : ℝ → ℝ) (u / ((n : ℝ) + 1))) (u / ((n : ℝ) + 1)) := by
    rw [iteratedDeriv_succ]
    exact (hdiff _).hasDerivAt
  have h := ((hb.comp u ((hasDerivAt_id u).div_const ((n : ℝ) + 1))).mul_const
    ((1 / ((n : ℝ) + 1)) ^ k)).ofReal_comp
  unfold cd
  convert h using 1
  · funext y
    simp [Function.comp]
  · push_cast
    ring

lemma continuous_cd (k n : ℕ) : Continuous (cd k n) := by
  have hc : Continuous (iteratedDeriv k (bump : ℝ → ℝ)) :=
    ContDiff.continuous_iteratedDeriv' k (contDiff_bump_nat k)
  unfold cd
  exact Complex.continuous_ofReal.comp ((hc.comp (continuous_id.div_const _)).mul continuous_const)

lemma contDiff_cd (k n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cd k n) := by
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (iteratedDeriv k (bump : ℝ → ℝ)) := by
    have hb : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bump : ℝ → ℝ) := bump.contDiff
    rw [iteratedDeriv_eq_iterate]
    exact hb.iterate_deriv k
  unfold cd
  exact Complex.ofRealCLM.contDiff.comp ((hc.comp (contDiff_id.div_const _)).mul contDiff_const)

lemma iteratedDeriv_bump_eq_zero (k : ℕ) : ∀ y : ℝ, 2 < |y| → iteratedDeriv k (bump : ℝ → ℝ) y = 0 := by
  induction k with
  | zero =>
    intro y hy
    rw [iteratedDeriv_zero]
    apply bump.zero_of_le_dist
    rw [dist_zero_right, Real.norm_eq_abs]
    exact hy.le
  | succ k ih =>
    intro y hy
    rw [iteratedDeriv_succ]
    have hopen : IsOpen {x : ℝ | 2 < |x|} := isOpen_lt continuous_const continuous_abs
    have hev : iteratedDeriv k (bump : ℝ → ℝ) =ᶠ[𝓝 y] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (hopen.mem_nhds hy) fun x hx => ih x hx
    rw [hev.deriv_eq, deriv_const]

lemma cd_eq_zero {k n : ℕ} {u : ℝ} (hu : 3 * ((n : ℝ) + 1) < |u|) : cd k n u = 0 := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : 2 < |u / ((n : ℝ) + 1)| := by
    rw [abs_div, abs_of_pos hpos, lt_div_iff₀ hpos]
    linarith
  unfold cd
  rw [iteratedDeriv_bump_eq_zero k _ h2]
  simp

lemma hasCompactSupport_cd (k n : ℕ) : HasCompactSupport (cd k n) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(3 * ((n : ℝ) + 1))) (b := 3 * ((n : ℝ) + 1)))
    fun u hu => cd_eq_zero ?_
  rw [Set.mem_Icc, not_and_or] at hu
  rcases hu with h | h
  · have h' := not_le.mp h
    rw [abs_of_neg (by have : (0 : ℝ) ≤ (n : ℝ) := n.cast_nonneg; linarith)]
    linarith
  · have h' := not_le.mp h
    rw [abs_of_pos (by have : (0 : ℝ) ≤ (n : ℝ) := n.cast_nonneg; linarith)]
    linarith

lemma norm_cd_le (k n : ℕ) (u : ℝ) : ‖cd k n u‖ ≤ Bd k := by
  unfold cd
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow]
  have h1 : |1 / ((n : ℝ) + 1)| ≤ 1 := by
    rw [abs_of_pos (by positivity), div_le_one (by positivity)]
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have h2 : |1 / ((n : ℝ) + 1)| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg _) h1
  calc |iteratedDeriv k (bump : ℝ → ℝ) (u / ((n : ℝ) + 1))| * |1 / ((n : ℝ) + 1)| ^ k
      ≤ Bd k * 1 := mul_le_mul (abs_iteratedDeriv_bump_le k _) h2 (by positivity) (Bd_nonneg k)
    _ = Bd k := mul_one _


/-! ## C. The tests g_n, their derivatives, and t_n = g_n'' - g_n/4. -/

/-- K P(u) E(u) with the witness constants K = gaussK lam, b = gaussB lam. -/
def gq (c lam : ℝ) (P : ℂ[X]) (u : ℝ) : ℂ := gp (gaussK lam) c (gaussB lam) P u

def P1 (c lam : ℝ) : ℂ[X] := dop c (gaussB lam) X
def P2 (c lam : ℝ) : ℂ[X] := dop c (gaussB lam) (P1 c lam)
def P3 (c lam : ℝ) : ℂ[X] := dop c (gaussB lam) (P2 c lam)

lemma hasDerivAt_gq (c lam : ℝ) (P : ℂ[X]) (u : ℝ) :
    HasDerivAt (gq c lam P) (gq c lam (dop c (gaussB lam) P) u) u :=
  hasDerivAt_gp _ _ _ P u

def g0 (c lam : ℝ) (n : ℕ) (u : ℝ) : ℂ := gq c lam X u * cd 0 n u
def g1 (c lam : ℝ) (n : ℕ) (u : ℝ) : ℂ :=
  gq c lam (P1 c lam) u * cd 0 n u + gq c lam X u * cd 1 n u
def g2 (c lam : ℝ) (n : ℕ) (u : ℝ) : ℂ :=
  gq c lam (P2 c lam) u * cd 0 n u + 2 * (gq c lam (P1 c lam) u * cd 1 n u)
    + gq c lam X u * cd 2 n u
def g3 (c lam : ℝ) (n : ℕ) (u : ℝ) : ℂ :=
  gq c lam (P3 c lam) u * cd 0 n u + 3 * (gq c lam (P2 c lam) u * cd 1 n u)
    + 3 * (gq c lam (P1 c lam) u * cd 2 n u) + gq c lam X u * cd 3 n u

/-- The pole-free tests. -/
def ptest (c lam : ℝ) (n : ℕ) (u : ℝ) : ℂ := g2 c lam n u - (1 / 4 : ℂ) * g0 c lam n u
def ptest' (c lam : ℝ) (n : ℕ) (u : ℝ) : ℂ := g3 c lam n u - (1 / 4 : ℂ) * g1 c lam n u

lemma hasDerivAt_prod (c lam : ℝ) (P : ℂ[X]) (k n : ℕ) (u : ℝ) :
    HasDerivAt (fun x => gq c lam P x * cd k n x)
      (gq c lam (dop c (gaussB lam) P) u * cd k n u + gq c lam P u * cd (k + 1) n u) u :=
  (hasDerivAt_gq c lam P u).mul (hasDerivAt_cd k n u)

lemma hasDerivAt_g0 (c lam : ℝ) (n : ℕ) (u : ℝ) : HasDerivAt (g0 c lam n) (g1 c lam n u) u := by
  have h := hasDerivAt_prod c lam X 0 n u
  exact h

lemma hasDerivAt_g1 (c lam : ℝ) (n : ℕ) (u : ℝ) : HasDerivAt (g1 c lam n) (g2 c lam n u) u := by
  have h := (hasDerivAt_prod c lam (P1 c lam) 0 n u).add (hasDerivAt_prod c lam X 1 n u)
  refine h.congr_deriv ?_
  unfold g2 P2 P1
  ring

lemma hasDerivAt_g2 (c lam : ℝ) (n : ℕ) (u : ℝ) : HasDerivAt (g2 c lam n) (g3 c lam n u) u := by
  have h := ((hasDerivAt_prod c lam (P2 c lam) 0 n u).add
    ((hasDerivAt_prod c lam (P1 c lam) 1 n u).const_mul (2 : ℂ))).add
    (hasDerivAt_prod c lam X 2 n u)
  refine h.congr_deriv ?_
  unfold g3 P3 P2 P1
  ring

lemma hasDerivAt_ptest (c lam : ℝ) (n : ℕ) (u : ℝ) :
    HasDerivAt (ptest c lam n) (ptest' c lam n u) u :=
  (hasDerivAt_g2 c lam n u).sub ((hasDerivAt_g0 c lam n u).const_mul (1 / 4 : ℂ))

lemma continuous_gq (c lam : ℝ) (P : ℂ[X]) : Continuous (gq c lam P) := continuous_gp _ _ _ P

lemma continuous_g1 (c lam : ℝ) (n : ℕ) : Continuous (g1 c lam n) :=
  ((continuous_gq c lam (P1 c lam)).mul (continuous_cd 0 n)).add
    ((continuous_gq c lam X).mul (continuous_cd 1 n))
lemma continuous_g2 (c lam : ℝ) (n : ℕ) : Continuous (g2 c lam n) :=
  (((continuous_gq c lam (P2 c lam)).mul (continuous_cd 0 n)).add
    (continuous_const.mul ((continuous_gq c lam (P1 c lam)).mul (continuous_cd 1 n)))).add
    ((continuous_gq c lam X).mul (continuous_cd 2 n))
lemma continuous_g3 (c lam : ℝ) (n : ℕ) : Continuous (g3 c lam n) :=
  ((((continuous_gq c lam (P3 c lam)).mul (continuous_cd 0 n)).add
    (continuous_const.mul ((continuous_gq c lam (P2 c lam)).mul (continuous_cd 1 n)))).add
    (continuous_const.mul ((continuous_gq c lam (P1 c lam)).mul (continuous_cd 2 n)))).add
    ((continuous_gq c lam X).mul (continuous_cd 3 n))
lemma continuous_g0 (c lam : ℝ) (n : ℕ) : Continuous (g0 c lam n) :=
  (continuous_gq c lam X).mul (continuous_cd 0 n)
lemma continuous_ptest' (c lam : ℝ) (n : ℕ) : Continuous (ptest' c lam n) :=
  (continuous_g3 c lam n).sub (continuous_const.mul (continuous_g1 c lam n))

/-- A function vanishing for |u| > 3 (n + 1) has compact support. -/
lemma hcs_of_vanish {n : ℕ} {f : ℝ → ℂ} (hf : ∀ u, 3 * ((n : ℝ) + 1) < |u| → f u = 0) :
    HasCompactSupport f := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(3 * ((n : ℝ) + 1))) (b := 3 * ((n : ℝ) + 1)))
    fun u hu => hf u ?_
  rw [Set.mem_Icc, not_and_or] at hu
  rcases hu with h | h
  · have h' := not_le.mp h
    rw [abs_of_neg (by have : (0 : ℝ) ≤ (n : ℝ) := n.cast_nonneg; linarith)]
    linarith
  · have h' := not_le.mp h
    rw [abs_of_pos (by have : (0 : ℝ) ≤ (n : ℝ) := n.cast_nonneg; linarith)]
    linarith

lemma hasCompactSupport_g0 (c lam : ℝ) (n : ℕ) : HasCompactSupport (g0 c lam n) :=
  hcs_of_vanish (n := n) fun u hu => by simp [g0, cd_eq_zero hu]
lemma hasCompactSupport_g1 (c lam : ℝ) (n : ℕ) : HasCompactSupport (g1 c lam n) :=
  hcs_of_vanish (n := n) fun u hu => by simp [g1, cd_eq_zero hu]
lemma hasCompactSupport_g2 (c lam : ℝ) (n : ℕ) : HasCompactSupport (g2 c lam n) :=
  hcs_of_vanish (n := n) fun u hu => by simp [g2, cd_eq_zero hu]
lemma hasCompactSupport_ptest (c lam : ℝ) (n : ℕ) : HasCompactSupport (ptest c lam n) :=
  hcs_of_vanish (n := n) fun u hu => by simp [ptest, g2, g0, cd_eq_zero hu]

lemma contDiff_g0 (c lam : ℝ) (n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g0 c lam n) := by
  unfold g0 gq
  exact (contDiff_gp _ _ _ X).mul (contDiff_cd 0 n)

lemma contDiff_ptest (c lam : ℝ) (n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ptest c lam n) := by
  unfold ptest g2 g0 gq
  have a := contDiff_gp (gaussK lam) c (gaussB lam) (P2 c lam)
  have b := contDiff_gp (gaussK lam) c (gaussB lam) (P1 c lam)
  have d := contDiff_gp (gaussK lam) c (gaussB lam) X
  have e0 := contDiff_cd 0 n; have e1 := contDiff_cd 1 n; have e2 := contDiff_cd 2 n
  exact (((a.mul e0).add (contDiff_const.mul (b.mul e1))).add (d.mul e2)).sub
    (contDiff_const.mul (d.mul e0))

theorem isWeilTest_ptest (c lam : ℝ) (n : ℕ) : IsWeilTest (ptest c lam n) :=
  ⟨contDiff_ptest c lam n, hasCompactSupport_ptest c lam n⟩

/-- g_n is E6Bridge8's gaussTests. -/
lemma g0_eq_gaussTests (c lam : ℝ) (n : ℕ) : g0 c lam n = gaussTests c lam n := by
  funext u
  unfold g0 gq gp gE gaussTests gaussPhi
  rw [cd_zero, eval_X]

/-! ## D. The transform identity: paperFT t_n z = -(z^2 + 1/4) paperFT g_n z. -/

/-- One integration by parts, in transform form. -/
lemma paperFT_of_hasDerivAt {g g' : ℝ → ℂ} (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g')
    (hsupp : HasCompactSupport g) (z : ℂ) : paperFT g' z = -(I * z) * paperFT g z := by
  have h := I_mul_paperFT_eq hg hg' hsupp z
  unfold paperFT at h ⊢
  linear_combination h

lemma integrable_mul_cexp {f : ℝ → ℂ} (hf : Continuous f) (hs : HasCompactSupport f) (z : ℂ) :
    Integrable (fun u : ℝ => f u * cexp (I * z * u)) :=
  (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hs.mul_right

theorem paperFT_ptest (c lam : ℝ) (n : ℕ) (z : ℂ) :
    paperFT (ptest c lam n) z = -(z ^ 2 + 1 / 4) * paperFT (g0 c lam n) z := by
  have h1 := paperFT_of_hasDerivAt (hasDerivAt_g0 c lam n) (continuous_g1 c lam n)
    (hasCompactSupport_g0 c lam n) z
  have h2 := paperFT_of_hasDerivAt (hasDerivAt_g1 c lam n) (continuous_g2 c lam n)
    (hasCompactSupport_g1 c lam n) z
  have hlin : paperFT (ptest c lam n) z
      = paperFT (g2 c lam n) z - (1 / 4 : ℂ) * paperFT (g0 c lam n) z := by
    unfold paperFT ptest
    rw [← integral_const_mul, ← integral_sub
      (integrable_mul_cexp (continuous_g2 c lam n) (hasCompactSupport_g2 c lam n) z)
      ((integrable_mul_cexp (continuous_g0 c lam n) (hasCompactSupport_g0 c lam n) z).const_mul _)]
    congr 1
    funext u
    ring
  rw [hlin, h2, h1]
  linear_combination (paperFT (g0 c lam n) z) * (z ^ 2) * I_sq

/-- Exactly pole-free. -/
theorem ptest_poleFree (c lam : ℝ) (n : ℕ) :
    paperFT (ptest c lam n) (I / 2) = 0 ∧ paperFT (ptest c lam n) (-I / 2) = 0 := by
  constructor
  · rw [paperFT_ptest]
    have : (I / 2) ^ 2 + 1 / 4 = 0 := by linear_combination (1 / 4 : ℂ) * I_sq
    rw [this]; ring
  · rw [paperFT_ptest]
    have : (-I / 2) ^ 2 + 1 / 4 = 0 := by linear_combination (1 / 4 : ℂ) * I_sq
    rw [this]; ring

/-- The weight q(z) = (z^2 + 1/4)^2. -/
def qw (z : ℂ) : ℂ := (z ^ 2 + 1 / 4) ^ 2

lemma hermitianTransform_ptest (c lam : ℝ) (n : ℕ) (z : ℂ) :
    hermitianTransform (ptest c lam n) z = qw z * hermitianTransform (g0 c lam n) z := by
  unfold hermitianTransform qw
  rw [paperFT_ptest, paperFT_ptest]
  simp only [map_mul, map_neg, map_add, map_pow, Complex.conj_conj, map_div₀, map_one,
    map_ofNat]
  ring


/-! ## E. The truncation-uniform bound and the weighted approximation. -/

/-- The integrable shape exp (-b u^2 + |u|/2). -/
def eW (lam : ℝ) (u : ℝ) : ℝ := Real.exp (-gaussB lam * u ^ 2 + (1 / 2) * |u|)

lemma norm_prod_mul_cexp_le (c lam : ℝ) (P : ℂ[X]) (k n : ℕ) {z : ℂ} (hz : |z.im| ≤ 1 / 2) (u : ℝ) :
    ‖gq c lam P u * cd k n u * cexp (I * z * u)‖
      ≤ ‖gaussK lam‖ * Bd k * (pabs P u * eW lam u) := by
  rw [norm_mul, norm_mul]
  have h1 := norm_gp_le (gaussK lam) c (gaussB lam) P u
  have h2 := norm_cd_le k n u
  have h3 := norm_cexp_I_mul_le hz u
  have hK := norm_nonneg (gaussK lam)
  have hp := pabs_nonneg P u
  have hE := (Real.exp_pos (-gaussB lam * u ^ 2)).le
  have hB := Bd_nonneg k
  unfold gq
  calc ‖gp (gaussK lam) c (gaussB lam) P u‖ * ‖cd k n u‖ * ‖cexp (I * z * u)‖
      ≤ (‖gaussK lam‖ * pabs P u * Real.exp (-gaussB lam * u ^ 2)) * Bd k
          * Real.exp ((1 / 2) * |u|) := by gcongr
    _ = ‖gaussK lam‖ * Bd k * (pabs P u * eW lam u) := by
        unfold eW
        rw [Real.exp_add]
        ring

/-- shorthand for one majorant piece -/
def mp (c lam : ℝ) (P : ℂ[X]) (k : ℕ) (u : ℝ) : ℝ := ‖gaussK lam‖ * Bd k * (pabs P u * eW lam u)

lemma integrable_mp {c lam : ℝ} (hlam : 0 < lam) (P : ℂ[X]) (k : ℕ) : Integrable (mp c lam P k) := by
  have := (integrable_pabs_mul (gaussB_pos hlam) P).const_mul (‖gaussK lam‖ * Bd k)
  exact this

lemma mp_nonneg (c lam : ℝ) (P : ℂ[X]) (k : ℕ) (u : ℝ) : 0 ≤ mp c lam P k u := by
  unfold mp eW
  have := pabs_nonneg P u
  have := Bd_nonneg k
  positivity

def maj0 (c lam : ℝ) (u : ℝ) : ℝ :=
  mp c lam (P2 c lam) 0 u + 2 * mp c lam (P1 c lam) 1 u + mp c lam X 2 u + (1 / 4) * mp c lam X 0 u

def maj1 (c lam : ℝ) (u : ℝ) : ℝ :=
  mp c lam (P3 c lam) 0 u + 3 * mp c lam (P2 c lam) 1 u + 3 * mp c lam (P1 c lam) 2 u
    + mp c lam X 3 u + (1 / 4) * (mp c lam (P1 c lam) 0 u + mp c lam X 1 u)

lemma integrable_maj0 {c lam : ℝ} (hlam : 0 < lam) : Integrable (maj0 c lam) :=
  ((((integrable_mp hlam _ 0).add ((integrable_mp hlam _ 1).const_mul 2)).add
    (integrable_mp hlam _ 2)).add ((integrable_mp hlam _ 0).const_mul (1 / 4)))

lemma integrable_maj1 {c lam : ℝ} (hlam : 0 < lam) : Integrable (maj1 c lam) :=
  (((((integrable_mp hlam _ 0).add ((integrable_mp hlam _ 1).const_mul 3)).add
    ((integrable_mp hlam _ 2).const_mul 3)).add (integrable_mp hlam _ 3)).add
    (((integrable_mp hlam _ 0).add (integrable_mp hlam _ 1)).const_mul (1 / 4)))

lemma norm_ptest_mul_le (c lam : ℝ) (n : ℕ) {z : ℂ} (hz : |z.im| ≤ 1 / 2) (u : ℝ) :
    ‖ptest c lam n u * cexp (I * z * u)‖ ≤ maj0 c lam u := by
  set e := cexp (I * z * u)
  have hsplit : ptest c lam n u * e
      = gq c lam (P2 c lam) u * cd 0 n u * e + 2 * (gq c lam (P1 c lam) u * cd 1 n u * e)
        + gq c lam X u * cd 2 n u * e - (1 / 4 : ℂ) * (gq c lam X u * cd 0 n u * e) := by
    unfold ptest g2 g0; ring
  rw [hsplit]
  have a := norm_prod_mul_cexp_le c lam (P2 c lam) 0 n hz u
  have b := norm_prod_mul_cexp_le c lam (P1 c lam) 1 n hz u
  have d := norm_prod_mul_cexp_le c lam X 2 n hz u
  have f := norm_prod_mul_cexp_le c lam X 0 n hz u
  unfold maj0 mp
  calc _ ≤ ‖gq c lam (P2 c lam) u * cd 0 n u * e + 2 * (gq c lam (P1 c lam) u * cd 1 n u * e)
          + gq c lam X u * cd 2 n u * e‖ + ‖(1 / 4 : ℂ) * (gq c lam X u * cd 0 n u * e)‖ :=
        norm_sub_le _ _
    _ ≤ (‖gq c lam (P2 c lam) u * cd 0 n u * e‖ + ‖(2 : ℂ) * (gq c lam (P1 c lam) u * cd 1 n u * e)‖
          + ‖gq c lam X u * cd 2 n u * e‖) + ‖(1 / 4 : ℂ) * (gq c lam X u * cd 0 n u * e)‖ := by
        gcongr
        exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ = ‖gq c lam (P2 c lam) u * cd 0 n u * e‖ + 2 * ‖gq c lam (P1 c lam) u * cd 1 n u * e‖
          + ‖gq c lam X u * cd 2 n u * e‖ + (1 / 4) * ‖gq c lam X u * cd 0 n u * e‖ := by
        rw [norm_mul, norm_mul]; norm_num
    _ ≤ _ := by gcongr

lemma norm_ptest'_mul_le (c lam : ℝ) (n : ℕ) {z : ℂ} (hz : |z.im| ≤ 1 / 2) (u : ℝ) :
    ‖ptest' c lam n u * cexp (I * z * u)‖ ≤ maj1 c lam u := by
  set e := cexp (I * z * u)
  have hsplit : ptest' c lam n u * e
      = gq c lam (P3 c lam) u * cd 0 n u * e + 3 * (gq c lam (P2 c lam) u * cd 1 n u * e)
        + 3 * (gq c lam (P1 c lam) u * cd 2 n u * e) + gq c lam X u * cd 3 n u * e
        - (1 / 4 : ℂ) * (gq c lam (P1 c lam) u * cd 0 n u * e + gq c lam X u * cd 1 n u * e) := by
    unfold ptest' g3 g1; ring
  rw [hsplit]
  have a := norm_prod_mul_cexp_le c lam (P3 c lam) 0 n hz u
  have b := norm_prod_mul_cexp_le c lam (P2 c lam) 1 n hz u
  have d := norm_prod_mul_cexp_le c lam (P1 c lam) 2 n hz u
  have f := norm_prod_mul_cexp_le c lam X 3 n hz u
  have g := norm_prod_mul_cexp_le c lam (P1 c lam) 0 n hz u
  have h := norm_prod_mul_cexp_le c lam X 1 n hz u
  unfold maj1 mp
  set A1 := gq c lam (P3 c lam) u * cd 0 n u * e
  set A2 := gq c lam (P2 c lam) u * cd 1 n u * e
  set A3 := gq c lam (P1 c lam) u * cd 2 n u * e
  set A4 := gq c lam X u * cd 3 n u * e
  set A5 := gq c lam (P1 c lam) u * cd 0 n u * e
  set A6 := gq c lam X u * cd 1 n u * e
  have hn2 : ‖(3 : ℂ) * A2‖ = 3 * ‖A2‖ := by rw [norm_mul]; norm_num
  have hn3 : ‖(3 : ℂ) * A3‖ = 3 * ‖A3‖ := by rw [norm_mul]; norm_num
  have hn5 : ‖(1 / 4 : ℂ) * (A5 + A6)‖ ≤ (1 / 4) * (‖A5‖ + ‖A6‖) := by
    rw [norm_mul]; norm_num
    exact norm_add_le _ _
  calc ‖A1 + 3 * A2 + 3 * A3 + A4 - (1 / 4 : ℂ) * (A5 + A6)‖
      ≤ ‖A1‖ + ‖(3 : ℂ) * A2‖ + ‖(3 : ℂ) * A3‖ + ‖A4‖ + ‖(1 / 4 : ℂ) * (A5 + A6)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ _ := by rw [hn2, hn3]; linarith

lemma maj0_nonneg (c lam : ℝ) (u : ℝ) : 0 ≤ maj0 c lam u := by
  unfold maj0
  have := mp_nonneg c lam (P2 c lam) 0 u; have := mp_nonneg c lam (P1 c lam) 1 u
  have := mp_nonneg c lam X 2 u; have := mp_nonneg c lam X 0 u
  linarith

lemma maj1_nonneg (c lam : ℝ) (u : ℝ) : 0 ≤ maj1 c lam u := by
  unfold maj1
  have := mp_nonneg c lam (P3 c lam) 0 u; have := mp_nonneg c lam (P2 c lam) 1 u
  have := mp_nonneg c lam (P1 c lam) 2 u; have := mp_nonneg c lam X 3 u
  have := mp_nonneg c lam (P1 c lam) 0 u; have := mp_nonneg c lam X 1 u
  linarith

theorem exists_paperFT_ptest_bound {c lam : ℝ} (hlam : 0 < lam) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n (z : ℂ), |z.im| ≤ 1 / 2 →
      ‖paperFT (ptest c lam n) z‖ ≤ 2 * M / (1 + ‖z‖) := by
  set M0 := ∫ u : ℝ, maj0 c lam u with hM0
  set M1 := ∫ u : ℝ, maj1 c lam u with hM1
  have hM0nn : 0 ≤ M0 := integral_nonneg fun u => maj0_nonneg c lam u
  have hM1nn : 0 ≤ M1 := integral_nonneg fun u => maj1_nonneg c lam u
  refine ⟨max M0 M1, le_max_of_le_left hM0nn, fun n z hz => ?_⟩
  have h0 : ‖paperFT (ptest c lam n) z‖ ≤ M0 := by
    unfold paperFT
    exact norm_integral_le_of_norm_le (integrable_maj0 hlam)
      (Filter.Eventually.of_forall fun u => norm_ptest_mul_le c lam n hz u)
  have h1 : ‖z‖ * ‖paperFT (ptest c lam n) z‖ ≤ M1 := by
    have hid := I_mul_paperFT_eq (hasDerivAt_ptest c lam n) (continuous_ptest' c lam n)
      (hasCompactSupport_ptest c lam n) z
    have hnorm : ‖z‖ * ‖paperFT (ptest c lam n) z‖ = ‖I * z * paperFT (ptest c lam n) z‖ := by
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
    rw [hnorm, hid, norm_neg]
    exact norm_integral_le_of_norm_le (integrable_maj1 hlam)
      (Filter.Eventually.of_forall fun u => norm_ptest'_mul_le c lam n hz u)
  have hz0 := norm_nonneg z
  have hle0 : M0 ≤ max M0 M1 := le_max_left _ _
  have hle1 : M1 ≤ max M0 M1 := le_max_right _ _
  rw [le_div_iff₀ (by positivity)]
  rcases le_or_gt ‖z‖ 1 with hz1 | hz1
  · nlinarith [norm_nonneg (paperFT (ptest c lam n) z)]
  · nlinarith [norm_nonneg (paperFT (ptest c lam n) z)]

/-- The weighted Gaussian: q(z) G_{c,lam}(z). -/
def qG (c lam : ℝ) (z : ℂ) : ℂ := qw z * gaussTest c lam z

/-- **Weighted strip approximation by pole-free tests.** -/
theorem weighted_approx {c lam : ℝ} (hlam : 0 < lam) :
    (∀ n, IsWeilTest (ptest c lam n)) ∧
    (∀ n, paperFT (ptest c lam n) (I / 2) = 0 ∧ paperFT (ptest c lam n) (-I / 2) = 0) ∧
    (∃ C : ℝ, ∀ n (z : ℂ), |z.im| ≤ 1 / 2 →
      ‖hermitianTransform (ptest c lam n) z‖ ≤ C / (1 + Complex.normSq z)) ∧
    (∀ z : ℂ, |z.im| ≤ 1 / 2 →
      Tendsto (fun n => hermitianTransform (ptest c lam n) z) atTop (𝓝 (qG c lam z))) := by
  obtain ⟨M, hM, hbound⟩ := exists_paperFT_ptest_bound (c := c) hlam
  refine ⟨isWeilTest_ptest c lam, ptest_poleFree c lam, ⟨4 * M ^ 2, fun n z hz => ?_⟩,
    fun z hz => ?_⟩
  · have hzc : |(conj z).im| ≤ 1 / 2 := by rwa [Complex.conj_im, abs_neg]
    have h1 := hbound n z hz
    have h2 := hbound n (conj z) hzc
    rw [Complex.norm_conj] at h2
    rw [norm_hermitianTransform_eq]
    have hz0 := norm_nonneg z
    have hpos : 0 < 1 + ‖z‖ := by positivity
    calc ‖paperFT (ptest c lam n) z‖ * ‖paperFT (ptest c lam n) (conj z)‖
        ≤ (2 * M / (1 + ‖z‖)) * (2 * M / (1 + ‖z‖)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (div_nonneg (by linarith) hpos.le)
      _ = 4 * M ^ 2 / (1 + ‖z‖) ^ 2 := by field_simp; ring
      _ ≤ 4 * M ^ 2 / (1 + Complex.normSq z) := by
          have hns := Complex.normSq_nonneg z
          apply div_le_div_of_nonneg_left (by positivity) (by linarith)
          rw [Complex.normSq_eq_norm_sq]
          nlinarith
  · have hzc : |(conj z).im| ≤ 1 / 2 := by rwa [Complex.conj_im, abs_neg]
    have hfun : (fun n => hermitianTransform (ptest c lam n) z)
        = fun n => qw z * hermitianTransform (gaussTests c lam n) z := by
      funext n
      rw [hermitianTransform_ptest, g0_eq_gaussTests]
    rw [hfun]
    unfold qG
    refine tendsto_const_nhds.mul ?_
    rw [gaussTest_eq_half_mul_conj]
    unfold RvMBridge6.hermitianTransform
    exact (paperFT_gaussTests_tendsto hlam hz).mul
      ((Complex.continuous_conj.tendsto _).comp (paperFT_gaussTests_tendsto hlam hzc))

end RvMBridgePF
