/-
  ZhuOrtho -- orthonormality of the Legendre modes, uniform bounds on their transforms, and the
  pole vectors through the cosh/sinh Poisson integral (rvm_bridge island, 2026-09-23).

  Inputs for the in-kernel tail sums of Zhu eq. (13) (ZhuTail.lean):
    * `integral_legendreP_sq`: ∫_{-1}^1 P_n² = 2/(2n+1)  (Rodrigues, n-fold integration by parts,
      D^{2n}(X²-1)^n = (2n)!), hence `integral_legendreMode_sq`: ∫_{-L}^{L} T_n² = 1;
    * the uniform bounds |T̂_n(t)|, |∫ T_n sin(t·)| ≤ (1+2L)/2 and |p_n| ≤ cosh(L/2)(1+2L)/2 for
      EVERY mode (from ∫|T_n| ≤ (∫ T_n² + 2L)/2), used for the modes below the cut;
    * the pole-vector decay `poleVec_abs_le` / `poleVecOdd_abs_le`: |p_{2k}| ≤ 2 sqrt(L(2k+1/2))
      cosh(L/2) (L/2)^{2k}/(4k+1)!!, by the same integration by parts against cosh(yu) (the
      transform at the imaginary frequency i/2), for the modes above the cut.
  Nothing about zeros.  No `sorry`.  conjecture1_proved = False.
-/
import ZhuLegendre

open MeasureTheory intervalIntegral Polynomial
open scoped Nat

noncomputable section

namespace RvMBridgeZhu
open WeilWindow

/-! ### A. `D^{2n} (X²-1)^n = (2n)!`. -/

lemma monic_sq_sub_one : (Polynomial.X ^ 2 - 1 : Polynomial ℝ).Monic := by
  have := Polynomial.monic_X_pow_sub_C (1 : ℝ) (n := 2) (by norm_num)
  simpa using this

lemma natDegree_sq_sub_one_pow (n : ℕ) :
    ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ n).natDegree = 2 * n := by
  rw [monic_sq_sub_one.natDegree_pow]
  have : (Polynomial.X ^ 2 - 1 : Polynomial ℝ).natDegree = 2 := by
    have := Polynomial.natDegree_X_pow_sub_C (R := ℝ) (n := 2) (r := 1)
    simpa using this
  rw [this]; ring

lemma iterate_derivative_two_mul_sq_sub_one_pow (n : ℕ) :
    Polynomial.derivative^[2 * n] ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ n)
      = Polynomial.C (((2 * n).factorial : ℕ) : ℝ) := by
  ext m
  rw [Polynomial.coeff_iterate_derivative, Polynomial.coeff_C]
  split_ifs with hm
  · subst hm
    have h := Polynomial.coeff_natDegree (p := (Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ n)
    rw [natDegree_sq_sub_one_pow, (monic_sq_sub_one.pow n).leadingCoeff] at h
    rw [zero_add, Nat.descFactorial_self, h, nsmul_eq_mul, mul_one]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [natDegree_sq_sub_one_pow]; omega), smul_zero]

/-! ### B. `∫ D^{n-i} q · D^{n+i} q = (-1)^i ∫ (D^n q)²`. -/

lemma ibp_shift (n : ℕ) : ∀ i, i ≤ n →
    ∫ t in (-1 : ℝ)..1, Polynomial.eval t (Polynomial.derivative^[n - i] ((Polynomial.X ^ 2 - 1) ^ n))
        * Polynomial.eval t (Polynomial.derivative^[n + i] ((Polynomial.X ^ 2 - 1) ^ n))
      = (-1) ^ i * ∫ t in (-1 : ℝ)..1,
          Polynomial.eval t (Polynomial.derivative^[n] ((Polynomial.X ^ 2 - 1) ^ n))
            * Polynomial.eval t (Polynomial.derivative^[n] ((Polynomial.X ^ 2 - 1) ^ n)) := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have h := ibp_step (n := n) (j := n - (i + 1)) (by omega)
      (g := fun t => Polynomial.eval t (Polynomial.derivative^[n + i] ((Polynomial.X ^ 2 - 1) ^ n)))
      (g' := fun t => Polynomial.eval t (Polynomial.derivative^[n + i + 1] ((Polynomial.X ^ 2 - 1) ^ n)))
      (fun t => by rw [Function.iterate_succ_apply']; exact Polynomial.hasDerivAt _ t)
      (Polynomial.continuous _)
    rw [show n - (i + 1) + 1 = n - i by omega] at h
    rw [show n + (i + 1) = n + i + 1 by ring]
    have := ih (by omega)
    rw [h] at this
    rw [pow_succ (-1 : ℝ) i]
    linear_combination -this

/-! ### C. `∫_{-1}^1 P_n² = 2/(2n+1)` and `∫_{-L}^{L} T_n² = 1`. -/

lemma two_mul_factorial_mul (n : ℕ) :
    (((2 * n).factorial : ℕ) : ℝ) * (2 * (n : ℝ) + 1) = 2 ^ n * (n.factorial : ℝ) * ((2 * n + 1)‼ : ℕ) := by
  have h1 := Nat.factorial_eq_mul_doubleFactorial (2 * n)
  have h2 := Nat.factorial_succ (2 * n)
  have h3 := Nat.doubleFactorial_two_mul n
  have : (2 * n + 1) * (2 * n).factorial = (2 * n + 1)‼ * (2 ^ n * n.factorial) := by
    rw [← h3, ← h1, h2]
  have hc : (((2 * n + 1) * (2 * n).factorial : ℕ) : ℝ) = (((2 * n + 1)‼ * (2 ^ n * n.factorial) : ℕ) : ℝ) := by
    exact_mod_cast this
  push_cast at hc
  linear_combination hc

theorem integral_legendreP_sq (n : ℕ) :
    ∫ u in (-1 : ℝ)..1, (Polynomial.eval u (legendreP n)) ^ 2 = 2 / (2 * (n : ℝ) + 1) := by
  unfold legendreP
  set c : ℝ := 1 / (2 ^ n * (n.factorial : ℝ)) with hc
  have e1 : (fun u : ℝ => (Polynomial.eval u (Polynomial.C c
      * Polynomial.derivative^[n] ((Polynomial.X ^ 2 - 1) ^ n))) ^ 2)
      = fun u => c ^ 2 * (Polynomial.eval u (Polynomial.derivative^[n] ((Polynomial.X ^ 2 - 1) ^ n))
          * Polynomial.eval u (Polynomial.derivative^[n] ((Polynomial.X ^ 2 - 1) ^ n))) := by
    funext u; rw [Polynomial.eval_mul, Polynomial.eval_C]; ring
  rw [e1, intervalIntegral.integral_const_mul]
  have h := ibp_shift n n le_rfl
  have hL : ∫ t in (-1 : ℝ)..1, Polynomial.eval t (Polynomial.derivative^[n - n] ((Polynomial.X ^ 2 - 1) ^ n))
      * Polynomial.eval t (Polynomial.derivative^[n + n] ((Polynomial.X ^ 2 - 1) ^ n))
      = ∫ t in (-1 : ℝ)..1, Polynomial.eval t ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ n)
          * (((2 * n).factorial : ℕ) : ℝ) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [Nat.sub_self, show n + n = 2 * n by ring, iterate_derivative_two_mul_sq_sub_one_pow,
      Function.iterate_zero, id, Polynomial.eval_C]
  rw [hL, intervalIntegral.integral_mul_const] at h
  have hq : ∫ u in (-1 : ℝ)..1, Polynomial.eval u ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ n)
      = (-1) ^ n * ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext u
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]
    rw [show u ^ 2 - 1 = -1 * (1 - u ^ 2) by ring, mul_pow]
  rw [hq, integral_one_sub_sq_pow] at h
  have key : ∫ t in (-1 : ℝ)..1, Polynomial.eval t (Polynomial.derivative^[n] ((Polynomial.X ^ 2 - 1) ^ n))
      * Polynomial.eval t (Polynomial.derivative^[n] ((Polynomial.X ^ 2 - 1) ^ n))
      = (((2 * n).factorial : ℕ) : ℝ) * (2 ^ (n + 1) * (n.factorial : ℝ) / ((2 * n + 1)‼ : ℕ)) := by
    rcases neg_one_pow_eq_or ℝ n with hs | hs <;> rw [hs] at h <;> linarith
  rw [key, hc]
  have hf := two_mul_factorial_mul n
  have hpos : (0 : ℝ) < ((2 * n + 1)‼ : ℕ) := by exact_mod_cast Nat.doubleFactorial_pos _
  have hfpos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  rw [eq_div_iff (by positivity)]
  have e3 : (1 / (2 ^ n * (n.factorial : ℝ))) ^ 2 * ((((2 * n).factorial : ℕ) : ℝ)
      * (2 ^ (n + 1) * (n.factorial : ℝ) / ((2 * n + 1)‼ : ℕ))) * (2 * (n : ℝ) + 1)
      = (1 / (2 ^ n * (n.factorial : ℝ))) ^ 2 * (2 ^ (n + 1) * (n.factorial : ℝ) / ((2 * n + 1)‼ : ℕ))
        * ((((2 * n).factorial : ℕ) : ℝ) * (2 * (n : ℝ) + 1)) := by ring
  rw [e3, hf]
  field_simp
  ring

/-- The polynomial expression of `T_n` on `[-L, L]`. -/
def modePoly (L : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (((n : ℝ) + 1 / 2) / L) * (legendreP n).eval (x / L)

lemma legendreMode_eq_modePoly {L : ℝ} (hL : 0 < L) (n : ℕ) {x : ℝ} (hx : x ∈ Set.uIcc (-L) L) :
    legendreMode L n x = modePoly L n x := by
  rw [Set.uIcc_of_le (by linarith)] at hx
  simp only [legendreMode, modePoly]
  rw [if_pos (abs_le.mpr ⟨hx.1, hx.2⟩)]

lemma continuous_modePoly (L : ℝ) (n : ℕ) : Continuous (modePoly L n) := by
  unfold modePoly
  have := Polynomial.continuous (legendreP n)
  fun_prop

theorem integral_legendreMode_sq {L : ℝ} (hL : 0 < L) (n : ℕ) :
    ∫ x in (-L)..L, (legendreMode L n x) ^ 2 = 1 := by
  have e1 : ∫ x in (-L)..L, (legendreMode L n x) ^ 2
      = ∫ x in (-L)..L, (((n : ℝ) + 1 / 2) / L) * ((fun u => (Polynomial.eval u (legendreP n)) ^ 2) (x / L)) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [legendreMode_eq_modePoly hL n hx]
    simp only [modePoly]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have e2 := intervalIntegral.integral_comp_div (a := -L) (b := L)
    (fun u : ℝ => (Polynomial.eval u (legendreP n)) ^ 2) hL.ne'
  rw [e1, intervalIntegral.integral_const_mul, e2, neg_div, div_self hL.ne', integral_legendreP_sq,
    smul_eq_mul]
  field_simp

/-! ### D. Uniform bounds on the mode transforms and pole vectors. -/

lemma abs_le_half_sq_add_one (a : ℝ) : |a| ≤ (a ^ 2 + 1) / 2 := by
  nlinarith [sq_nonneg (|a| - 1), sq_abs a, abs_nonneg a]

theorem integral_abs_legendreMode_le {L : ℝ} (hL : 0 < L) (n : ℕ) :
    ∫ x in (-L)..L, |legendreMode L n x| ≤ (1 + 2 * L) / 2 := by
  have e1 : ∫ x in (-L)..L, |legendreMode L n x| = ∫ x in (-L)..L, |modePoly L n x| :=
    intervalIntegral.integral_congr fun x hx => by rw [legendreMode_eq_modePoly hL n hx]
  have e2 : ∫ x in (-L)..L, (legendreMode L n x) ^ 2 = ∫ x in (-L)..L, (modePoly L n x) ^ 2 :=
    intervalIntegral.integral_congr fun x hx => by rw [legendreMode_eq_modePoly hL n hx]
  have hsq := integral_legendreMode_sq hL n
  rw [e2] at hsq
  rw [e1]
  have hc := continuous_modePoly L n
  have hi2 : IntervalIntegrable (fun x => ((modePoly L n x) ^ 2 + 1) / 2) volume (-L) L :=
    (((hc.pow 2).add continuous_const).div_const 2).intervalIntegrable _ _
  have hi3 : IntervalIntegrable (fun x => (modePoly L n x) ^ 2) volume (-L) L :=
    (hc.pow 2).intervalIntegrable _ _
  calc ∫ x in (-L)..L, |modePoly L n x|
      ≤ ∫ x in (-L)..L, ((modePoly L n x) ^ 2 + 1) / 2 :=
        integral_mono_on (by linarith) (hc.abs.intervalIntegrable _ _) hi2
          (fun x _ => abs_le_half_sq_add_one _)
    _ = (1 + 2 * L) / 2 := by
        rw [intervalIntegral.integral_div, intervalIntegral.integral_add hi3
          (continuous_const.intervalIntegrable _ _), hsq, intervalIntegral.integral_const]
        simp
        ring

/-- The generic weighted bound: `|∫ T_n(x) w(x) dx| ≤ W (1+2L)/2` for `|w| ≤ W` on `[-L, L]`. -/
theorem abs_integral_legendreMode_mul_le {L : ℝ} (hL : 0 < L) (n : ℕ) {w : ℝ → ℝ} (hw : Continuous w)
    {W : ℝ} (hW : ∀ x ∈ Set.Icc (-L) L, |w x| ≤ W) :
    |∫ x in (-L)..L, legendreMode L n x * w x| ≤ W * ((1 + 2 * L) / 2) := by
  have e1 : ∫ x in (-L)..L, legendreMode L n x * w x = ∫ x in (-L)..L, modePoly L n x * w x :=
    intervalIntegral.integral_congr fun x hx => by rw [legendreMode_eq_modePoly hL n hx]
  have e2 : ∫ x in (-L)..L, |legendreMode L n x| = ∫ x in (-L)..L, |modePoly L n x| :=
    intervalIntegral.integral_congr fun x hx => by rw [legendreMode_eq_modePoly hL n hx]
  have hint := integral_abs_legendreMode_le hL n
  rw [e2] at hint
  have hc := continuous_modePoly L n
  have hW0 : 0 ≤ W := (abs_nonneg _).trans (hW (-L) ⟨le_rfl, by linarith⟩)
  rw [e1]
  calc |∫ x in (-L)..L, modePoly L n x * w x|
      ≤ ∫ x in (-L)..L, |modePoly L n x * w x| :=
        intervalIntegral.abs_integral_le_integral_abs (by linarith)
    _ ≤ ∫ x in (-L)..L, W * |modePoly L n x| := by
        refine integral_mono_on (by linarith) ((hc.mul hw).abs.intervalIntegrable _ _)
          ((hc.abs.const_mul W).intervalIntegrable _ _) (fun x hx => ?_)
        rw [abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hW x hx) (abs_nonneg _)
    _ = W * ∫ x in (-L)..L, |modePoly L n x| := intervalIntegral.integral_const_mul _ _
    _ ≤ W * ((1 + 2 * L) / 2) := mul_le_mul_of_nonneg_left hint hW0

theorem legendreModeFT_abs_le_uniform {L : ℝ} (hL : 0 < L) (n : ℕ) (t : ℝ) :
    |legendreModeFT L n t| ≤ (1 + 2 * L) / 2 := by
  have := abs_integral_legendreMode_mul_le hL n (w := fun x => Real.cos (t * x)) (by fun_prop) (W := 1)
    (fun x _ => Real.abs_cos_le_one _)
  simpa [legendreModeFT] using this

theorem legendreModeFTs_abs_le_uniform {L : ℝ} (hL : 0 < L) (n : ℕ) (t : ℝ) :
    |legendreModeFTs L n t| ≤ (1 + 2 * L) / 2 := by
  have := abs_integral_legendreMode_mul_le hL n (w := fun x => Real.sin (t * x)) (by fun_prop) (W := 1)
    (fun x _ => Real.abs_sin_le_one _)
  simpa [legendreModeFTs] using this

lemma abs_sinh_le_cosh (x : ℝ) : |Real.sinh x| ≤ Real.cosh x := by
  rw [abs_le]
  constructor
  · have := Real.sinh_lt_cosh (-x)
    rw [Real.sinh_neg, Real.cosh_neg] at this
    linarith
  · exact (Real.sinh_lt_cosh x).le

lemma cosh_half_le {L x : ℝ} (hx : x ∈ Set.Icc (-L) L) : Real.cosh (x / 2) ≤ Real.cosh (L / 2) := by
  rw [Real.cosh_le_cosh]
  have hL : 0 ≤ L := by linarith [hx.1, hx.2]
  rw [abs_of_nonneg (by linarith : 0 ≤ L / 2), abs_le]
  constructor <;> linarith [hx.1, hx.2]

theorem poleVec_abs_le_uniform {L : ℝ} (hL : 0 < L) (n : ℕ) :
    |poleVec L n| ≤ Real.cosh (L / 2) * ((1 + 2 * L) / 2) :=
  abs_integral_legendreMode_mul_le hL n (w := fun x => Real.cosh (x / 2)) (by fun_prop)
    (fun x hx => by rw [abs_of_pos (Real.cosh_pos _)]; exact cosh_half_le hx)

theorem poleVecOdd_abs_le_uniform {L : ℝ} (hL : 0 < L) (n : ℕ) :
    |poleVecOdd L n| ≤ Real.cosh (L / 2) * ((1 + 2 * L) / 2) :=
  abs_integral_legendreMode_mul_le hL n (w := fun x => Real.sinh (x / 2)) (by fun_prop)
    (fun x hx => (abs_sinh_le_cosh _).trans (cosh_half_le hx))

/-! ### E. The pole vectors by the cosh / sinh Poisson integral. -/

lemma ibp_two_steps_cosh {n j : ℕ} (hj : j + 2 ≤ n) (y : ℝ) :
    ∫ t in (-1 : ℝ)..1, Polynomial.eval t (Polynomial.derivative^[j + 2] ((Polynomial.X ^ 2 - 1) ^ n))
        * Real.cosh (y * t)
      = y ^ 2 * ∫ t in (-1 : ℝ)..1,
          Polynomial.eval t (Polynomial.derivative^[j] ((Polynomial.X ^ 2 - 1) ^ n)) * Real.cosh (y * t) := by
  have hcosh : ∀ t : ℝ, HasDerivAt (fun t => Real.cosh (y * t)) (y * Real.sinh (y * t)) t := by
    intro t
    refine (((hasDerivAt_id t).const_mul y).cosh).congr_deriv ?_
    simp only [id]; ring
  have hsinh : ∀ t : ℝ, HasDerivAt (fun t => Real.sinh (y * t)) (y * Real.cosh (y * t)) t := by
    intro t
    refine (((hasDerivAt_id t).const_mul y).sinh).congr_deriv ?_
    simp only [id]; ring
  have h1 := ibp_step (n := n) (j := j + 1) (by omega) hcosh (by fun_prop)
  have h2 := ibp_step (n := n) (j := j) (by omega) hsinh (by fun_prop)
  rw [show j + 1 + 1 = j + 2 by ring] at h1
  rw [h1]
  have e1 : ∫ t in (-1 : ℝ)..1, Polynomial.eval t (Polynomial.derivative^[j + 1] ((Polynomial.X ^ 2 - 1) ^ n))
      * (y * Real.sinh (y * t))
      = y * ∫ t in (-1 : ℝ)..1, Polynomial.eval t (Polynomial.derivative^[j + 1] ((Polynomial.X ^ 2 - 1) ^ n))
      * Real.sinh (y * t) := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext t; ring
  have e2 : ∫ t in (-1 : ℝ)..1, Polynomial.eval t (Polynomial.derivative^[j] ((Polynomial.X ^ 2 - 1) ^ n))
      * (y * Real.cosh (y * t))
      = y * ∫ t in (-1 : ℝ)..1, Polynomial.eval t (Polynomial.derivative^[j] ((Polynomial.X ^ 2 - 1) ^ n))
      * Real.cosh (y * t) := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext t; ring
  rw [e1, h2, e2]
  ring

lemma ibp_even_cosh (n : ℕ) (y : ℝ) :
    ∀ k, 2 * k ≤ n →
      ∫ t in (-1 : ℝ)..1, Polynomial.eval t (Polynomial.derivative^[2 * k] ((Polynomial.X ^ 2 - 1) ^ n))
          * Real.cosh (y * t)
        = (y ^ 2) ^ k * ∫ t in (-1 : ℝ)..1,
            Polynomial.eval t ((Polynomial.X ^ 2 - 1) ^ n) * Real.cosh (y * t) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, ibp_two_steps_cosh (by omega), ih (by omega), pow_succ]
    ring

theorem integral_legendreP_mul_cosh (k : ℕ) (y : ℝ) :
    ∫ u in (-1 : ℝ)..1, Polynomial.eval u (legendreP (2 * k)) * Real.cosh (y * u)
      = y ^ (2 * k) / (2 ^ (2 * k) * ((2 * k).factorial : ℝ))
        * ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ (2 * k) * Real.cosh (y * u) := by
  unfold legendreP
  have e : (fun u : ℝ => Polynomial.eval u (Polynomial.C (1 / (2 ^ (2 * k) * ((2 * k).factorial : ℝ)))
      * Polynomial.derivative^[2 * k] ((Polynomial.X ^ 2 - 1) ^ (2 * k))) * Real.cosh (y * u))
      = fun u => (1 / (2 ^ (2 * k) * ((2 * k).factorial : ℝ)))
        * (Polynomial.eval u (Polynomial.derivative^[2 * k] ((Polynomial.X ^ 2 - 1) ^ (2 * k)))
          * Real.cosh (y * u)) := by
    funext u; rw [Polynomial.eval_mul, Polynomial.eval_C]; ring
  rw [e, intervalIntegral.integral_const_mul, ibp_even_cosh (2 * k) y k le_rfl]
  have e2 : (fun t : ℝ => Polynomial.eval t ((Polynomial.X ^ 2 - 1) ^ (2 * k)) * Real.cosh (y * t))
      = fun t => (1 - t ^ 2) ^ (2 * k) * Real.cosh (y * t) := by
    funext t
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]
    rw [show t ^ 2 - 1 = -(1 - t ^ 2) by ring, Even.neg_pow ⟨k, by ring⟩]
  rw [e2, ← pow_mul]
  ring

theorem integral_legendreP_mul_sinh (k : ℕ) (y : ℝ) :
    ∫ u in (-1 : ℝ)..1, Polynomial.eval u (legendreP (2 * k + 1)) * Real.sinh (y * u)
      = y ^ (2 * k + 1) / (2 ^ (2 * k + 1) * ((2 * k + 1).factorial : ℝ))
        * ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ (2 * k + 1) * Real.cosh (y * u) := by
  unfold legendreP
  have hsinh : ∀ t : ℝ, HasDerivAt (fun t => Real.sinh (y * t)) (y * Real.cosh (y * t)) t := by
    intro t
    refine (((hasDerivAt_id t).const_mul y).sinh).congr_deriv ?_
    simp only [id]; ring
  have e : (fun u : ℝ => Polynomial.eval u (Polynomial.C (1 / (2 ^ (2 * k + 1) * ((2 * k + 1).factorial : ℝ)))
      * Polynomial.derivative^[2 * k + 1] ((Polynomial.X ^ 2 - 1) ^ (2 * k + 1))) * Real.sinh (y * u))
      = fun u => (1 / (2 ^ (2 * k + 1) * ((2 * k + 1).factorial : ℝ)))
        * (Polynomial.eval u (Polynomial.derivative^[2 * k + 1] ((Polynomial.X ^ 2 - 1) ^ (2 * k + 1)))
          * Real.sinh (y * u)) := by
    funext u; rw [Polynomial.eval_mul, Polynomial.eval_C]; ring
  rw [e, intervalIntegral.integral_const_mul, ibp_step (n := 2 * k + 1) (j := 2 * k) le_rfl hsinh (by fun_prop)]
  have e1 : ∫ t in (-1 : ℝ)..1, Polynomial.eval t (Polynomial.derivative^[2 * k] ((Polynomial.X ^ 2 - 1) ^ (2 * k + 1)))
      * (y * Real.cosh (y * t))
      = y * ∫ t in (-1 : ℝ)..1, Polynomial.eval t (Polynomial.derivative^[2 * k] ((Polynomial.X ^ 2 - 1) ^ (2 * k + 1)))
      * Real.cosh (y * t) := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext t; ring
  rw [e1, ibp_even_cosh (2 * k + 1) y k (by omega)]
  have e2 : (fun t : ℝ => Polynomial.eval t ((Polynomial.X ^ 2 - 1) ^ (2 * k + 1)) * Real.cosh (y * t))
      = fun t => -((1 - t ^ 2) ^ (2 * k + 1) * Real.cosh (y * t)) := by
    funext t
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]
    rw [show t ^ 2 - 1 = -(1 - t ^ 2) by ring, Odd.neg_pow ⟨k, by ring⟩]
    ring
  rw [e2, intervalIntegral.integral_neg, ← pow_mul]
  ring

lemma integral_one_sub_sq_pow_mul_cosh_nonneg (n : ℕ) (y : ℝ) :
    0 ≤ ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n * Real.cosh (y * u) := by
  refine intervalIntegral.integral_nonneg (by norm_num) fun u hu => ?_
  have h1 : 0 ≤ 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
  exact mul_nonneg (pow_nonneg h1 n) (Real.cosh_pos _).le

lemma integral_one_sub_sq_pow_mul_cosh_le (n : ℕ) (y : ℝ) :
    ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n * Real.cosh (y * u)
      ≤ Real.cosh y * (2 ^ (n + 1) * (n.factorial : ℝ) / ((2 * n + 1)‼ : ℕ)) := by
  rw [← integral_one_sub_sq_pow, ← intervalIntegral.integral_const_mul]
  refine integral_mono_on (by norm_num)
    ((by fun_prop : Continuous fun u : ℝ => (1 - u ^ 2) ^ n * Real.cosh (y * u)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun u : ℝ => Real.cosh y * (1 - u ^ 2) ^ n).intervalIntegrable _ _)
    (fun u hu => ?_)
  have h1 : 0 ≤ 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
  have hc : Real.cosh (y * u) ≤ Real.cosh y := by
    rw [Real.cosh_le_cosh, abs_mul]
    have : |u| ≤ 1 := abs_le.mpr ⟨hu.1, hu.2⟩
    exact mul_le_of_le_one_right (abs_nonneg _) this
  calc (1 - u ^ 2) ^ n * Real.cosh (y * u) ≤ (1 - u ^ 2) ^ n * Real.cosh y :=
        mul_le_mul_of_nonneg_left hc (pow_nonneg h1 n)
    _ = Real.cosh y * (1 - u ^ 2) ^ n := mul_comm _ _

/-- `p_{2k} = sqrt(L(2k+1/2)) · (L/2)^{2k}/(2^{2k}(2k)!) ∫ (1-u²)^{2k} cosh(Lu/2) du`. -/
theorem poleVec_eq {L : ℝ} (hL : 0 < L) (k : ℕ) :
    poleVec L (2 * k) = Real.sqrt (L * ((2 * k : ℕ) + 1 / 2))
      * ((L / 2) ^ (2 * k) / (2 ^ (2 * k) * ((2 * k).factorial : ℝ))
        * ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ (2 * k) * Real.cosh (L / 2 * u)) := by
  unfold poleVec
  have e1 : ∫ x in (-L)..L, legendreMode L (2 * k) x * Real.cosh (x / 2)
      = ∫ x in (-L)..L, Real.sqrt (((2 * k : ℕ) + 1 / 2) / L)
          * ((fun u : ℝ => Polynomial.eval u (legendreP (2 * k)) * Real.cosh (L / 2 * u)) (x / L)) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [legendreMode_eq_modePoly hL _ hx]
    simp only [modePoly]
    have : L / 2 * (x / L) = x / 2 := by field_simp
    rw [this]; ring
  have e2 := intervalIntegral.integral_comp_div (a := -L) (b := L)
    (fun u : ℝ => Polynomial.eval u (legendreP (2 * k)) * Real.cosh (L / 2 * u)) hL.ne'
  rw [e1, intervalIntegral.integral_const_mul, e2, neg_div, div_self hL.ne', integral_legendreP_mul_cosh,
    smul_eq_mul]
  have hsq := sqrt_div_mul_self hL (a := ((2 * k : ℕ) + 1 / 2)) (by positivity)
  rw [← hsq]; ring

theorem poleVec_abs_le {L : ℝ} (hL : 0 < L) (k : ℕ) :
    |poleVec L (2 * k)| ≤ 2 * Real.sqrt (L * ((2 * k : ℕ) + 1 / 2)) * Real.cosh (L / 2)
      * ((L / 2) ^ (2 * k) / ((2 * (2 * k) + 1)‼ : ℕ)) := by
  rw [poleVec_eq hL]
  have hI0 := integral_one_sub_sq_pow_mul_cosh_nonneg (2 * k) (L / 2)
  have hI := integral_one_sub_sq_pow_mul_cosh_le (2 * k) (L / 2)
  have hpref : 0 ≤ (L / 2) ^ (2 * k) / (2 ^ (2 * k) * ((2 * k).factorial : ℝ)) := by positivity
  rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hpref hI0))]
  have hpos : (0 : ℝ) < ((2 * (2 * k) + 1)‼ : ℕ) := by exact_mod_cast Nat.doubleFactorial_pos _
  have hfpos : (0 : ℝ) < ((2 * k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  calc Real.sqrt (L * ((2 * k : ℕ) + 1 / 2)) * ((L / 2) ^ (2 * k) / (2 ^ (2 * k) * ((2 * k).factorial : ℝ))
        * ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ (2 * k) * Real.cosh (L / 2 * u))
      ≤ Real.sqrt (L * ((2 * k : ℕ) + 1 / 2)) * ((L / 2) ^ (2 * k) / (2 ^ (2 * k) * ((2 * k).factorial : ℝ))
        * (Real.cosh (L / 2) * (2 ^ (2 * k + 1) * ((2 * k).factorial : ℝ) / ((2 * (2 * k) + 1)‼ : ℕ)))) := by
        gcongr
    _ = _ := by field_simp; ring

/-- `p^odd_{2k+1} = sqrt(L(2k+3/2)) · (L/2)^{2k+1}/(2^{2k+1}(2k+1)!) ∫ (1-u²)^{2k+1} cosh(Lu/2) du`. -/
theorem poleVecOdd_eq {L : ℝ} (hL : 0 < L) (k : ℕ) :
    poleVecOdd L (2 * k + 1) = Real.sqrt (L * ((2 * k + 1 : ℕ) + 1 / 2))
      * ((L / 2) ^ (2 * k + 1) / (2 ^ (2 * k + 1) * ((2 * k + 1).factorial : ℝ))
        * ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ (2 * k + 1) * Real.cosh (L / 2 * u)) := by
  unfold poleVecOdd
  have e1 : ∫ x in (-L)..L, legendreMode L (2 * k + 1) x * Real.sinh (x / 2)
      = ∫ x in (-L)..L, Real.sqrt (((2 * k + 1 : ℕ) + 1 / 2) / L)
          * ((fun u : ℝ => Polynomial.eval u (legendreP (2 * k + 1)) * Real.sinh (L / 2 * u)) (x / L)) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [legendreMode_eq_modePoly hL _ hx]
    simp only [modePoly]
    have : L / 2 * (x / L) = x / 2 := by field_simp
    rw [this]; ring
  have e2 := intervalIntegral.integral_comp_div (a := -L) (b := L)
    (fun u : ℝ => Polynomial.eval u (legendreP (2 * k + 1)) * Real.sinh (L / 2 * u)) hL.ne'
  rw [e1, intervalIntegral.integral_const_mul, e2, neg_div, div_self hL.ne', integral_legendreP_mul_sinh,
    smul_eq_mul]
  have hsq := sqrt_div_mul_self hL (a := ((2 * k + 1 : ℕ) + 1 / 2)) (by positivity)
  rw [← hsq]; ring

theorem poleVecOdd_abs_le {L : ℝ} (hL : 0 < L) (k : ℕ) :
    |poleVecOdd L (2 * k + 1)| ≤ 2 * Real.sqrt (L * ((2 * k + 1 : ℕ) + 1 / 2)) * Real.cosh (L / 2)
      * ((L / 2) ^ (2 * k + 1) / ((2 * (2 * k + 1) + 1)‼ : ℕ)) := by
  rw [poleVecOdd_eq hL]
  have hI0 := integral_one_sub_sq_pow_mul_cosh_nonneg (2 * k + 1) (L / 2)
  have hI := integral_one_sub_sq_pow_mul_cosh_le (2 * k + 1) (L / 2)
  have hpref : 0 ≤ (L / 2) ^ (2 * k + 1) / (2 ^ (2 * k + 1) * ((2 * k + 1).factorial : ℝ)) := by positivity
  rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hpref hI0))]
  have hpos : (0 : ℝ) < ((2 * (2 * k + 1) + 1)‼ : ℕ) := by exact_mod_cast Nat.doubleFactorial_pos _
  have hfpos : (0 : ℝ) < ((2 * k + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  calc Real.sqrt (L * ((2 * k + 1 : ℕ) + 1 / 2)) * ((L / 2) ^ (2 * k + 1) / (2 ^ (2 * k + 1) * ((2 * k + 1).factorial : ℝ))
        * ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ (2 * k + 1) * Real.cosh (L / 2 * u))
      ≤ Real.sqrt (L * ((2 * k + 1 : ℕ) + 1 / 2)) * ((L / 2) ^ (2 * k + 1) / (2 ^ (2 * k + 1) * ((2 * k + 1).factorial : ℝ))
        * (Real.cosh (L / 2) * (2 ^ (2 * k + 1 + 1) * ((2 * k + 1).factorial : ℝ) / ((2 * (2 * k + 1) + 1)‼ : ℕ)))) := by
        gcongr
    _ = _ := by field_simp; ring

end RvMBridgeZhu

end
