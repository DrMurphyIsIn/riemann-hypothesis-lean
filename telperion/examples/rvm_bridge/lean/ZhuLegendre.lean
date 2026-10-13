/-
  ZhuLegendre -- Zhu eqs. (6) and (12) (arXiv:2608.24827 v2), the Legendre / spherical-Bessel
  localization inputs, on the rvm_bridge island (2026-09-23).

  WHAT IS DEFINED (registry-mirrorable, namespace WeilWindow):
    * `legendreP n`        the Legendre polynomial, Rodrigues form P_n = (1/2^n n!) D^n (X^2-1)^n;
    * `sphericalBessel n x` the spherical Bessel function by the Poisson integral, cosine form
                            j_n(x) = x^n/(2^{n+1} n!) ∫_{-1}^{1} (1-u^2)^n cos(xu) du
                            (Mathlib has no spherical Bessel functions);
    * `legendreMode L n`   the orthonormal Legendre mode T_n(x) = sqrt((n+1/2)/L) P_n(x/L) on [-L, L];
    * `legendreModeFT L n t` its cosine transform ∫ T_n(x) cos(tx) dx (= the full transform for
                            even n);
    * `poleVec`, `combMatrix`, `reducedMat`: the pole vector p_n = <T_n, cosh(x/2)>, the C-matrix
      C_{nm} = (1/π) ∫_0^{T#} (Ψ_L - β*) T̂_n T̂_m, and Zhu's reduced matrix M = β* I + 2 p p^T + C
      on the even modes 2k;
    * `LegendreLocalization L T# N epsD epsB`: eq. (13)'s tail data -- Gershgorin deviation of the
      tail block <= epsD and both Schur sums of the leading-tail coupling <= epsB.

  WHAT IS PROVED:
    * eq. (12): |j_n(x)| <= x^n / (2n+1)!! for x >= 0  (`sphericalBessel_abs_le`), from the exact
      value ∫_{-1}^1 (1-u^2)^n du = 2^{n+1} n!/(2n+1)!! (`integral_one_sub_sq_pow`);
    * eq. (6): T̂_{2k}(t) = (-1)^k 2 sqrt(L (2k+1/2)) j_{2k}(tL)  (`legendreModeFT_eq`), by n-fold
      integration by parts against Rodrigues' formula (the boundary terms vanish because
      D^j (X^2-1)^n has a zero of order n-j at ±1);
    * the entry decay: |T̂_{2k}(t)| <= 2 sqrt(L(2k+1/2)) (tL)^{2k}/(4k+1)!! for 0 <= t
      (`legendreModeFT_abs_le`), which is what makes C super-exponentially localized past order
      e L T#/2.

  WHAT IS NOT PROVED HERE (recorded, not hidden): the tail sums epsD, epsB themselves (Zhu Section
  5.3 evaluates them numerically from these entry bounds, both < 1e-100), and the assembly of the
  reduced form R on the Legendre basis (Legendre completeness in L^2[-L, L], the matrix
  representation, the two-block bound (13)).  See the design doc.  No `sorry`.
  conjecture1_proved = False.
-/
import ZhuSymbol

open MeasureTheory intervalIntegral Polynomial
open scoped Nat

/-! ## A. Registry-facing definitions (namespace WeilWindow, mirrored verbatim into RHDefs). -/

namespace WeilWindow
open MeasureTheory Complex WeilExplicit WeilForm

/-- Zhu's comb mass `A_L = Σ_{log n < 2L} 2 Λ(n)/√n`.  A FINITE sum (`n < e^{2L}`), and the
    only information about the prime comb that the reduction uses; by Lemma 3.2 it is the exact
    supremum of the comb, so no smaller pointwise constant exists. -/
noncomputable def combMass (L : ℝ) : ℝ :=
  ∑' n : ℕ, if Real.log n < 2 * L then 2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n else 0

/-- Zhu's threshold `β* = log(T#/2π) - 1/T# - A_L`.  Theorem 1.1 requires `β* > 0`, which is
    exactly the requirement `T# > T₁ = 2π e^{A_L}` of the Theorem 1.4 barrier. -/
noncomputable def betaStar (L Tsharp : ℝ) : ℝ :=
  Real.log (Tsharp / (2 * Real.pi)) - 1 / Tsharp - combMass L

/-- The Legendre polynomial `P_n`, Rodrigues form `P_n = (1/(2^n n!)) D^n (X² - 1)^n`. -/
noncomputable def legendreP (n : ℕ) : Polynomial ℝ :=
  Polynomial.C (1 / (2 ^ n * (n.factorial : ℝ)))
    * (Polynomial.derivative^[n] ((Polynomial.X ^ 2 - 1) ^ n))

/-- The spherical Bessel function `j_n` by the Poisson integral (cosine form, the sine part
    vanishing by parity): `j_n(x) = x^n/(2^{n+1} n!) ∫_{-1}^{1} (1 - u²)^n cos(xu) du`. -/
noncomputable def sphericalBessel (n : ℕ) (x : ℝ) : ℝ :=
  x ^ n / (2 ^ (n + 1) * (n.factorial : ℝ))
    * ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n * Real.cos (x * u)

/-- Zhu's orthonormal Legendre mode `T_n(x) = P̄_n(x/L)/√L = sqrt((n+1/2)/L) P_n(x/L)` on
    `[-L, L]`, extended by zero. -/
noncomputable def legendreMode (L : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  if |x| ≤ L then Real.sqrt ((n + 1 / 2) / L) * (legendreP n).eval (x / L) else 0

/-- The cosine transform `∫ T_n(x) cos(tx) dx`; for even `n` this is the full transform
    `T̂_n(t) = ∫ T_n(x) e^{itx} dx` of eq. (6). -/
noncomputable def legendreModeFT (L : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ x in (-L)..L, legendreMode L n x * Real.cos (t * x)

/-- The pole vector `p_n = ∫ T_n(x) cosh(x/2) dx` (so `F(i/2) = Σ c_n p_n` for even `f = Σ c_n T_n`). -/
noncomputable def poleVec (L : ℝ) (n : ℕ) : ℝ :=
  ∫ x in (-L)..L, legendreMode L n x * Real.cosh (x / 2)

/-- Zhu's C-matrix, the operator with symbol `(Ψ_L - β*) χ_[0,T#]` in the Legendre basis:
    `C_{nm} = (1/π) ∫_0^{T#} (Ψ_L(t) - β*) T̂_n(t) T̂_m(t) dt`. -/
noncomputable def combMatrix (L Tsharp : ℝ) (n m : ℕ) : ℝ :=
  (1 / Real.pi) * ∫ t in (0 : ℝ)..Tsharp,
    (weilSymbol L t - betaStar L Tsharp) * (legendreModeFT L n t * legendreModeFT L m t)

/-- Zhu's reduced matrix `M_R = β* I + 2 p pᵀ + C` on the even modes `0, 2, 4, …`, indexed by
    `k ↦ 2k`. -/
noncomputable def reducedMat (L Tsharp : ℝ) (k j : ℕ) : ℝ :=
  (if k = j then betaStar L Tsharp else 0)
    + 2 * poleVec L (2 * k) * poleVec L (2 * j) + combMatrix L Tsharp (2 * k) (2 * j)

/-- Zhu eqs. (6), (12), (13), CONCRETE: the tail data of the block decomposition after `N` even
    modes.  (i) Gershgorin: every tail row `k ≥ N` of `M_R - β* I` has absolute row sum over the
    tail `≤ epsD` (so `λ_min(D) ≥ β* - epsD`); (ii) Schur: every leading column `j < N` has
    absolute tail-column sum `≤ epsB` and every tail row `k ≥ N` has absolute leading-row sum
    `≤ epsB` (so `‖B‖ ≤ epsB`).  Summability is required explicitly so the `tsum`s are honest.
    In the certified run both constants are below `1e-100` (Zhu Section 5.3). -/
def LegendreLocalization (L Tsharp : ℝ) (N : ℕ) (epsD epsB : ℝ) : Prop :=
  (∀ k, N ≤ k →
    Summable (fun j : ℕ => if N ≤ j then
      |reducedMat L Tsharp k j - (if k = j then betaStar L Tsharp else 0)| else 0) ∧
    ∑' j : ℕ, (if N ≤ j then
      |reducedMat L Tsharp k j - (if k = j then betaStar L Tsharp else 0)| else 0) ≤ epsD) ∧
  (∀ j, j < N →
    Summable (fun k : ℕ => if N ≤ k then |reducedMat L Tsharp k j| else 0) ∧
    ∑' k : ℕ, (if N ≤ k then |reducedMat L Tsharp k j| else 0) ≤ epsB) ∧
  (∀ k, N ≤ k → ∑ j ∈ Finset.range N, |reducedMat L Tsharp k j| ≤ epsB)

/-- The sine transform `∫ T_n(x) sin(tx) dx`; for odd `n` the full transform is `i` times it, so
    `|T̂_n(t)|² = (∫ T_n sin(tx))²`. -/
noncomputable def legendreModeFTs (L : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ x in (-L)..L, legendreMode L n x * Real.sin (t * x)

/-- The odd-sector pole vector `s_n = ∫ T_n(x) sinh(x/2) dx` (so `F(i/2) = -Σ c_n s_n` for odd
    `f = Σ c_n T_n`, and the pole term is `-2 (Σ c_n s_n)²`, Zhu Lemma 6.1). -/
noncomputable def poleVecOdd (L : ℝ) (n : ℕ) : ℝ :=
  ∫ x in (-L)..L, legendreMode L n x * Real.sinh (x / 2)

/-- The C-matrix on odd modes: `C_{nm} = (1/π) ∫_0^{T#} (Ψ_L(t) - β*) T̂_n(t) T̂_m(t) dt` with
    `|T̂_n| = |∫ T_n sin(t·)|`. -/
noncomputable def combMatrixOdd (L Tsharp : ℝ) (n m : ℕ) : ℝ :=
  (1 / Real.pi) * ∫ t in (0 : ℝ)..Tsharp,
    (weilSymbol L t - betaStar L Tsharp) * (legendreModeFTs L n t * legendreModeFTs L m t)

/-- Zhu's ODD-sector reduced matrix `β* I - 2 s sᵀ + C` on the odd modes `1, 3, 5, …`, indexed by
    `k ↦ 2k + 1` (Section 6: the pole sign is reversed). -/
noncomputable def reducedMatOdd (L Tsharp : ℝ) (k j : ℕ) : ℝ :=
  (if k = j then betaStar L Tsharp else 0)
    - 2 * poleVecOdd L (2 * k + 1) * poleVecOdd L (2 * j + 1)
    + combMatrixOdd L Tsharp (2 * k + 1) (2 * j + 1)

/-- The eq. (13) tail data of the ODD sector, the same shape as `LegendreLocalization` on
    `reducedMatOdd` (Zhu Section 6: "the tail and coupling bounds of Section 4 are unchanged"). -/
def LegendreLocalizationOdd (L Tsharp : ℝ) (N : ℕ) (epsD epsB : ℝ) : Prop :=
  (∀ k, N ≤ k →
    Summable (fun j : ℕ => if N ≤ j then
      |reducedMatOdd L Tsharp k j - (if k = j then betaStar L Tsharp else 0)| else 0) ∧
    ∑' j : ℕ, (if N ≤ j then
      |reducedMatOdd L Tsharp k j - (if k = j then betaStar L Tsharp else 0)| else 0) ≤ epsD) ∧
  (∀ j, j < N →
    Summable (fun k : ℕ => if N ≤ k then |reducedMatOdd L Tsharp k j| else 0) ∧
    ∑' k : ℕ, (if N ≤ k then |reducedMatOdd L Tsharp k j| else 0) ≤ epsB) ∧
  (∀ k, N ≤ k → ∑ j ∈ Finset.range N, |reducedMatOdd L Tsharp k j| ≤ epsB)

end WeilWindow

/-! ## B. The proofs. -/

noncomputable section

namespace RvMBridgeZhu
open WeilWindow

/-! ### B.1 The Wallis-type integral `∫_{-1}^1 (1-u²)^n du`. -/

/-- The recurrence `(2n+3) I_{n+1} = (2n+2) I_n`, by differentiating `u (1-u²)^{n+1}`. -/
lemma integral_one_sub_sq_pow_succ (n : ℕ) :
    (2 * (n : ℝ) + 3) * ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ (n + 1)
      = (2 * (n : ℝ) + 2) * ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n := by
  have hd : ∀ u : ℝ, HasDerivAt (fun u : ℝ => u * (1 - u ^ 2) ^ (n + 1))
      ((2 * (n : ℝ) + 3) * (1 - u ^ 2) ^ (n + 1) - (2 * (n : ℝ) + 2) * (1 - u ^ 2) ^ n) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => 1 - u ^ 2) (-(2 * u)) u :=
      ((hasDerivAt_pow 2 u).const_sub 1).congr_deriv (by norm_num)
    have h2 := h1.pow (n + 1)
    have h3 := (hasDerivAt_id u).mul h2
    refine h3.congr_deriv ?_
    simp only [id, Nat.add_sub_cancel, Pi.pow_apply]
    push_cast
    ring
  have hc1 : Continuous fun u : ℝ => (1 - u ^ 2) ^ (n + 1) := by fun_prop
  have hc0 : Continuous fun u : ℝ => (1 - u ^ 2) ^ n := by fun_prop
  have hint := integral_eq_sub_of_hasDerivAt (a := -1) (b := 1) (fun u _ => hd u)
    (((hc1.const_mul _).sub (hc0.const_mul _)).intervalIntegrable _ _)
  rw [integral_sub ((hc1.const_mul _).intervalIntegrable _ _) ((hc0.const_mul _).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hint
  norm_num at hint
  linarith

/-- `∫_{-1}^1 (1-u²)^n du = 2^{n+1} n! / (2n+1)!!`. -/
theorem integral_one_sub_sq_pow (n : ℕ) :
    ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n = 2 ^ (n + 1) * (n.factorial : ℝ) / ((2 * n + 1)‼ : ℕ) := by
  induction n with
  | zero => simp; norm_num
  | succ n ih =>
    have hrec := integral_one_sub_sq_pow_succ n
    have hdf : ((2 * (n + 1) + 1)‼ : ℕ) = (2 * n + 3) * (2 * n + 1)‼ := by
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, Nat.doubleFactorial_add_two]
    have hpos : (0 : ℝ) < ((2 * n + 1)‼ : ℕ) := by exact_mod_cast Nat.doubleFactorial_pos _
    have h3 : (0 : ℝ) < 2 * (n : ℝ) + 3 := by positivity
    rw [ih] at hrec
    rw [hdf, Nat.factorial_succ]
    push_cast
    field_simp
    push_cast at hrec
    field_simp at hrec
    linear_combination hrec

/-! ### B.2 Eq. (12): the elementary bound `|j_n(x)| ≤ x^n / (2n+1)!!`. -/

theorem sphericalBessel_abs_le (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    |sphericalBessel n x| ≤ x ^ n / ((2 * n + 1)‼ : ℕ) := by
  unfold sphericalBessel
  have hpref : 0 ≤ x ^ n / (2 ^ (n + 1) * (n.factorial : ℝ)) := by positivity
  rw [abs_mul, abs_of_nonneg hpref]
  have hI : |∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n * Real.cos (x * u)|
      ≤ ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n := by
    refine (intervalIntegral.abs_integral_le_integral_abs (by norm_num)).trans ?_
    refine integral_mono_on (by norm_num)
      ((by fun_prop : Continuous fun u : ℝ => |(1 - u ^ 2) ^ n * Real.cos (x * u)|).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun u : ℝ => (1 - u ^ 2) ^ n).intervalIntegrable _ _)
      (fun u hu => ?_)
    have h1 : 0 ≤ 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
    rw [abs_mul, abs_of_nonneg (pow_nonneg h1 n)]
    have := Real.abs_cos_le_one (x * u)
    calc (1 - u ^ 2) ^ n * |Real.cos (x * u)| ≤ (1 - u ^ 2) ^ n * 1 :=
          mul_le_mul_of_nonneg_left this (pow_nonneg h1 n)
      _ = (1 - u ^ 2) ^ n := mul_one _
  rw [integral_one_sub_sq_pow] at hI
  have hpos : (0 : ℝ) < ((2 * n + 1)‼ : ℕ) := by exact_mod_cast Nat.doubleFactorial_pos _
  calc x ^ n / (2 ^ (n + 1) * (n.factorial : ℝ)) * |∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n * Real.cos (x * u)|
      ≤ x ^ n / (2 ^ (n + 1) * (n.factorial : ℝ)) * (2 ^ (n + 1) * (n.factorial : ℝ) / ((2 * n + 1)‼ : ℕ)) :=
        mul_le_mul_of_nonneg_left hI hpref
    _ = x ^ n / ((2 * n + 1)‼ : ℕ) := by
        field_simp

/-! ### B.3 Rodrigues: `D^j (X²-1)^n` has a zero of order `n - j` at `±1`. -/

/-- `D^j (X²-1)^n = (X²-1)^{n-j} · r` for some polynomial `r`, `j ≤ n`. -/
lemma iterate_derivative_sq_sub_one_pow (n : ℕ) :
    ∀ j, j ≤ n → ∃ r : Polynomial ℝ,
      Polynomial.derivative^[j] ((Polynomial.X ^ 2 - 1) ^ n) = (Polynomial.X ^ 2 - 1) ^ (n - j) * r := by
  intro j
  induction j with
  | zero => intro _; exact ⟨1, by simp⟩
  | succ j ih =>
    intro hj
    obtain ⟨r, hr⟩ := ih (by omega)
    have hnj : n - j = (n - (j + 1)) + 1 := by omega
    refine ⟨Polynomial.C ((n - j : ℕ) : ℝ) * Polynomial.derivative (Polynomial.X ^ 2 - 1) * r
      + (Polynomial.X ^ 2 - 1) * Polynomial.derivative r, ?_⟩
    rw [Function.iterate_succ_apply', hr, Polynomial.derivative_mul, Polynomial.derivative_pow, hnj,
      Nat.add_sub_cancel]
    ring

/-- The boundary values vanish: `eval (±1) (D^j (X²-1)^n) = 0` for `j < n`. -/
lemma eval_iterate_derivative_sq_sub_one_pow {n j : ℕ} (hj : j < n) (x : ℝ) (hx : x ^ 2 = 1) :
    Polynomial.eval x (Polynomial.derivative^[j] ((Polynomial.X ^ 2 - 1) ^ n)) = 0 := by
  obtain ⟨r, hr⟩ := iterate_derivative_sq_sub_one_pow n j hj.le
  rw [hr, Polynomial.eval_mul, Polynomial.eval_pow]
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, hx,
    sub_self]
  rw [zero_pow (by omega)]
  ring

/-! ### B.4 One integration by parts against `D^{j+1} (X²-1)^n`, `j + 1 ≤ n`. -/

lemma ibp_step {n j : ℕ} (hj : j + 1 ≤ n) {g g' : ℝ → ℝ} (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg' : Continuous g') :
    ∫ t in (-1 : ℝ)..1, Polynomial.eval t (Polynomial.derivative^[j + 1] ((Polynomial.X ^ 2 - 1) ^ n)) * g t
      = - ∫ t in (-1 : ℝ)..1, Polynomial.eval t (Polynomial.derivative^[j] ((Polynomial.X ^ 2 - 1) ^ n)) * g' t := by
  set q : Polynomial ℝ := (Polynomial.X ^ 2 - 1) ^ n with hq
  have hu : ∀ t ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt (fun t => Polynomial.eval t (Polynomial.derivative^[j] q))
      (Polynomial.eval t (Polynomial.derivative^[j + 1] q)) t := by
    intro t _
    rw [Function.iterate_succ_apply']
    exact Polynomial.hasDerivAt _ t
  have hv : ∀ t ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt g (g' t) t := fun t _ => hg t
  have hcg : Continuous g := continuous_iff_continuousAt.mpr fun t => (hg t).continuousAt
  have key := integral_deriv_mul_eq_sub hu hv
    ((Polynomial.continuous _).intervalIntegrable _ _) (hg'.intervalIntegrable _ _)
  have hb1 : Polynomial.eval (1 : ℝ) (Polynomial.derivative^[j] q) = 0 :=
    eval_iterate_derivative_sq_sub_one_pow (by omega) 1 (by norm_num)
  have hb2 : Polynomial.eval (-1 : ℝ) (Polynomial.derivative^[j] q) = 0 :=
    eval_iterate_derivative_sq_sub_one_pow (by omega) (-1) (by norm_num)
  have hi1 : IntervalIntegrable (fun x => Polynomial.eval x (Polynomial.derivative^[j + 1] q) * g x)
      volume (-1) 1 := ((Polynomial.continuous _).mul hcg).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x => Polynomial.eval x (Polynomial.derivative^[j] q) * g' x)
      volume (-1) 1 := ((Polynomial.continuous _).mul hg').intervalIntegrable _ _
  rw [hb1, hb2, integral_add hi1 hi2] at key
  linarith

/-- Two steps: `∫ D^{j+2} q · cos(x·) = -x² ∫ D^j q · cos(x·)`, `j + 2 ≤ n`. -/
lemma ibp_two_steps {n j : ℕ} (hj : j + 2 ≤ n) (x : ℝ) :
    ∫ t in (-1 : ℝ)..1, Polynomial.eval t (Polynomial.derivative^[j + 2] ((Polynomial.X ^ 2 - 1) ^ n))
        * Real.cos (x * t)
      = -(x ^ 2) * ∫ t in (-1 : ℝ)..1,
          Polynomial.eval t (Polynomial.derivative^[j] ((Polynomial.X ^ 2 - 1) ^ n)) * Real.cos (x * t) := by
  have hcos : ∀ t : ℝ, HasDerivAt (fun t => Real.cos (x * t)) (-x * Real.sin (x * t)) t := by
    intro t
    refine (((hasDerivAt_id t).const_mul x).cos).congr_deriv ?_
    simp only [id]
    ring
  have hsin : ∀ t : ℝ, HasDerivAt (fun t => Real.sin (x * t)) (x * Real.cos (x * t)) t := by
    intro t
    refine (((hasDerivAt_id t).const_mul x).sin).congr_deriv ?_
    simp only [id]
    ring
  have h1 := ibp_step (n := n) (j := j + 1) (by omega) hcos (by fun_prop)
  have h2 := ibp_step (n := n) (j := j) (by omega) hsin (by fun_prop)
  rw [show j + 1 + 1 = j + 2 by ring] at h1
  rw [h1]
  have e1 : ∫ t in (-1 : ℝ)..1, Polynomial.eval t (Polynomial.derivative^[j + 1] ((Polynomial.X ^ 2 - 1) ^ n))
      * (-x * Real.sin (x * t))
      = -x * ∫ t in (-1 : ℝ)..1, Polynomial.eval t (Polynomial.derivative^[j + 1] ((Polynomial.X ^ 2 - 1) ^ n))
      * Real.sin (x * t) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    ring
  have e2 : ∫ t in (-1 : ℝ)..1, Polynomial.eval t (Polynomial.derivative^[j] ((Polynomial.X ^ 2 - 1) ^ n))
      * (x * Real.cos (x * t))
      = x * ∫ t in (-1 : ℝ)..1, Polynomial.eval t (Polynomial.derivative^[j] ((Polynomial.X ^ 2 - 1) ^ n))
      * Real.cos (x * t) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    ring
  rw [e1, h2, e2]
  ring

/-- `∫ D^{2k} q · cos(x·) = (-x²)^k ∫ q · cos(x·)`, `2k ≤ n`. -/
lemma ibp_even (n : ℕ) (x : ℝ) :
    ∀ k, 2 * k ≤ n →
      ∫ t in (-1 : ℝ)..1, Polynomial.eval t (Polynomial.derivative^[2 * k] ((Polynomial.X ^ 2 - 1) ^ n))
          * Real.cos (x * t)
        = (-(x ^ 2)) ^ k * ∫ t in (-1 : ℝ)..1,
            Polynomial.eval t ((Polynomial.X ^ 2 - 1) ^ n) * Real.cos (x * t) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, ibp_two_steps (by omega), ih (by omega), pow_succ]
    ring

/-! ### B.5 Eq. (6), core: `∫_{-1}^1 P_{2k}(u) cos(xu) du = (-1)^k · 2 · j_{2k}(x)`. -/

theorem integral_legendreP_mul_cos (k : ℕ) (x : ℝ) :
    ∫ u in (-1 : ℝ)..1, Polynomial.eval u (legendreP (2 * k)) * Real.cos (x * u)
      = (-1) ^ k * 2 * sphericalBessel (2 * k) x := by
  unfold legendreP sphericalBessel
  have e : (fun u : ℝ => Polynomial.eval u (Polynomial.C (1 / (2 ^ (2 * k) * ((2 * k).factorial : ℝ)))
      * Polynomial.derivative^[2 * k] ((Polynomial.X ^ 2 - 1) ^ (2 * k))) * Real.cos (x * u))
      = fun u => (1 / (2 ^ (2 * k) * ((2 * k).factorial : ℝ)))
        * (Polynomial.eval u (Polynomial.derivative^[2 * k] ((Polynomial.X ^ 2 - 1) ^ (2 * k)))
          * Real.cos (x * u)) := by
    funext u
    rw [Polynomial.eval_mul, Polynomial.eval_C]
    ring
  rw [e, intervalIntegral.integral_const_mul, ibp_even (2 * k) x k le_rfl]
  have e2 : (fun t : ℝ => Polynomial.eval t ((Polynomial.X ^ 2 - 1) ^ (2 * k)) * Real.cos (x * t))
      = fun t => (1 - t ^ 2) ^ (2 * k) * Real.cos (x * t) := by
    funext t
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]
    rw [show t ^ 2 - 1 = -(1 - t ^ 2) by ring, Even.neg_pow ⟨k, by ring⟩]
  rw [e2]
  have e3 : (-(x ^ 2)) ^ k = (-1) ^ k * x ^ (2 * k) := by
    rw [neg_eq_neg_one_mul, mul_pow, pow_mul]
  rw [e3]
  field_simp
  ring

/-! ### B.6 Eq. (6): `T̂_{2k}(t) = (-1)^k · 2 sqrt(L (2k + 1/2)) · j_{2k}(tL)`. -/

lemma sqrt_div_mul_self {L a : ℝ} (hL : 0 < L) (ha : 0 ≤ a) :
    Real.sqrt (a / L) * L = Real.sqrt (L * a) := by
  have hL2 : Real.sqrt (L ^ 2) = L := Real.sqrt_sq hL.le
  rw [← hL2, ← Real.sqrt_mul (by positivity), Real.sqrt_sq hL.le]
  congr 1
  field_simp

theorem legendreModeFT_eq {L : ℝ} (hL : 0 < L) (k : ℕ) (t : ℝ) :
    legendreModeFT L (2 * k) t
      = (-1) ^ k * 2 * Real.sqrt (L * ((2 * k : ℕ) + 1 / 2)) * sphericalBessel (2 * k) (t * L) := by
  unfold legendreModeFT
  have e1 : ∫ x in (-L)..L, legendreMode L (2 * k) x * Real.cos (t * x)
      = ∫ x in (-L)..L, Real.sqrt (((2 * k : ℕ) + 1 / 2) / L)
          * ((fun u : ℝ => Polynomial.eval u (legendreP (2 * k)) * Real.cos (t * L * u)) (x / L)) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by linarith)] at hx
    simp only [legendreMode]
    rw [if_pos (abs_le.mpr ⟨hx.1, hx.2⟩)]
    have : t * L * (x / L) = t * x := by field_simp
    rw [this]
    ring
  have e2 := intervalIntegral.integral_comp_div (a := -L) (b := L)
    (fun u : ℝ => Polynomial.eval u (legendreP (2 * k)) * Real.cos (t * L * u)) hL.ne'
  rw [e1, intervalIntegral.integral_const_mul, e2, neg_div, div_self hL.ne',
    integral_legendreP_mul_cos, smul_eq_mul]
  have hsq := sqrt_div_mul_self hL (a := ((2 * k : ℕ) + 1 / 2)) (by positivity)
  calc Real.sqrt (((2 * k : ℕ) + 1 / 2) / L) * (L * ((-1) ^ k * 2 * sphericalBessel (2 * k) (t * L)))
      = (Real.sqrt (((2 * k : ℕ) + 1 / 2) / L) * L) * ((-1) ^ k * 2 * sphericalBessel (2 * k) (t * L)) := by
        ring
    _ = _ := by rw [hsq]; ring

/-! ### B.7 The entry decay: `|T̂_{2k}(t)| ≤ 2 sqrt(L(2k+1/2)) (tL)^{2k} / (4k+1)!!`, `0 ≤ t`. -/

theorem legendreModeFT_abs_le {L : ℝ} (hL : 0 < L) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    |legendreModeFT L (2 * k) t|
      ≤ 2 * Real.sqrt (L * ((2 * k : ℕ) + 1 / 2)) * ((t * L) ^ (2 * k) / ((2 * (2 * k) + 1)‼ : ℕ)) := by
  rw [legendreModeFT_eq hL, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (sphericalBessel_abs_le _ (by positivity)) (by positivity)

/-! ### B.8 The ODD modes: `∫_{-1}^1 P_{2k+1}(u) sin(xu) du = (-1)^k · 2 · j_{2k+1}(x)`. -/

theorem integral_legendreP_mul_sin (k : ℕ) (x : ℝ) :
    ∫ u in (-1 : ℝ)..1, Polynomial.eval u (legendreP (2 * k + 1)) * Real.sin (x * u)
      = (-1) ^ k * 2 * sphericalBessel (2 * k + 1) x := by
  unfold legendreP sphericalBessel
  have hsin : ∀ t : ℝ, HasDerivAt (fun t => Real.sin (x * t)) (x * Real.cos (x * t)) t := by
    intro t
    refine (((hasDerivAt_id t).const_mul x).sin).congr_deriv ?_
    simp only [id]
    ring
  have e : (fun u : ℝ => Polynomial.eval u (Polynomial.C (1 / (2 ^ (2 * k + 1) * ((2 * k + 1).factorial : ℝ)))
      * Polynomial.derivative^[2 * k + 1] ((Polynomial.X ^ 2 - 1) ^ (2 * k + 1))) * Real.sin (x * u))
      = fun u => (1 / (2 ^ (2 * k + 1) * ((2 * k + 1).factorial : ℝ)))
        * (Polynomial.eval u (Polynomial.derivative^[2 * k + 1] ((Polynomial.X ^ 2 - 1) ^ (2 * k + 1)))
          * Real.sin (x * u)) := by
    funext u
    rw [Polynomial.eval_mul, Polynomial.eval_C]
    ring
  rw [e, intervalIntegral.integral_const_mul, ibp_step (n := 2 * k + 1) (j := 2 * k) le_rfl hsin (by fun_prop)]
  have e1 : ∫ t in (-1 : ℝ)..1, Polynomial.eval t (Polynomial.derivative^[2 * k] ((Polynomial.X ^ 2 - 1) ^ (2 * k + 1)))
      * (x * Real.cos (x * t))
      = x * ∫ t in (-1 : ℝ)..1, Polynomial.eval t (Polynomial.derivative^[2 * k] ((Polynomial.X ^ 2 - 1) ^ (2 * k + 1)))
      * Real.cos (x * t) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    ring
  rw [e1, ibp_even (2 * k + 1) x k (by omega)]
  have e2 : (fun t : ℝ => Polynomial.eval t ((Polynomial.X ^ 2 - 1) ^ (2 * k + 1)) * Real.cos (x * t))
      = fun t => -((1 - t ^ 2) ^ (2 * k + 1) * Real.cos (x * t)) := by
    funext t
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]
    rw [show t ^ 2 - 1 = -(1 - t ^ 2) by ring, Odd.neg_pow ⟨k, by ring⟩]
    ring
  rw [e2, intervalIntegral.integral_neg]
  have e3 : (-(x ^ 2)) ^ k = (-1) ^ k * x ^ (2 * k) := by
    rw [neg_eq_neg_one_mul, mul_pow, pow_mul]
  rw [e3]
  field_simp
  ring

theorem legendreModeFTs_eq {L : ℝ} (hL : 0 < L) (k : ℕ) (t : ℝ) :
    legendreModeFTs L (2 * k + 1) t
      = (-1) ^ k * 2 * Real.sqrt (L * ((2 * k + 1 : ℕ) + 1 / 2)) * sphericalBessel (2 * k + 1) (t * L) := by
  unfold legendreModeFTs
  have e1 : ∫ x in (-L)..L, legendreMode L (2 * k + 1) x * Real.sin (t * x)
      = ∫ x in (-L)..L, Real.sqrt (((2 * k + 1 : ℕ) + 1 / 2) / L)
          * ((fun u : ℝ => Polynomial.eval u (legendreP (2 * k + 1)) * Real.sin (t * L * u)) (x / L)) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by linarith)] at hx
    simp only [legendreMode]
    rw [if_pos (abs_le.mpr ⟨hx.1, hx.2⟩)]
    have : t * L * (x / L) = t * x := by field_simp
    rw [this]
    ring
  have e2 := intervalIntegral.integral_comp_div (a := -L) (b := L)
    (fun u : ℝ => Polynomial.eval u (legendreP (2 * k + 1)) * Real.sin (t * L * u)) hL.ne'
  rw [e1, intervalIntegral.integral_const_mul, e2, neg_div, div_self hL.ne',
    integral_legendreP_mul_sin, smul_eq_mul]
  have hsq := sqrt_div_mul_self hL (a := ((2 * k + 1 : ℕ) + 1 / 2)) (by positivity)
  calc Real.sqrt (((2 * k + 1 : ℕ) + 1 / 2) / L) * (L * ((-1) ^ k * 2 * sphericalBessel (2 * k + 1) (t * L)))
      = (Real.sqrt (((2 * k + 1 : ℕ) + 1 / 2) / L) * L) * ((-1) ^ k * 2 * sphericalBessel (2 * k + 1) (t * L)) := by
        ring
    _ = _ := by rw [hsq]; ring

theorem legendreModeFTs_abs_le {L : ℝ} (hL : 0 < L) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    |legendreModeFTs L (2 * k + 1) t|
      ≤ 2 * Real.sqrt (L * ((2 * k + 1 : ℕ) + 1 / 2))
        * ((t * L) ^ (2 * k + 1) / ((2 * (2 * k + 1) + 1)‼ : ℕ)) := by
  rw [legendreModeFTs_eq hL, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (sphericalBessel_abs_le _ (by positivity)) (by positivity)

end RvMBridgeZhu

end
