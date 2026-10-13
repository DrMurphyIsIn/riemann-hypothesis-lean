/-
  KWin_Taylor -- parity-generic Taylor remainders and the finite-interval transform calculus of
  the KWin certificate (rvm_bridge island, 2026-09-24).

  For par = 0 (even sector) / par = 1 (odd sector):
    phiF par = cos / sin,   poleF par x = cosh(x/2) / sinh(x/2),
    tayl par M y  = sum_{m<M} (-1)^m y^(2m+par) / (2m+par)!,
    ptayl par M y = sum_{m<M} y^(2m+par) / (2m+par)!.
  PROVED: |phiF par y - tayl par M y| <= 2 |y|^(2M+par)/(2M+par)! for |y| <= (2M+par+1)/2
  (Mathlib's Complex.exp_bound' at i y, real / imaginary parts), the same for poleF (Real.exp_bound
  at +-x/2), and their integrated forms on [-l, l]:
    |Tr f t - sum_{m<M} (-1)^m (t l)^(2m+par)/(2m+par)! mo f (2m+par)| <= 2 (t l)^(2M+par)/(2M+par)! A1 f,
  where Tr f t = int_{-l}^{l} f(x) phiF(t x), mo f n = int_{-l}^{l} f(x) (x/l)^n, A1 f = int |f|;
  Cauchy-Schwarz A1(f)^2 <= 2 l int f^2; continuity of t -> Tr f t.  Pure real analysis; nothing
  about zeros.  conjecture1_proved = False.  No `sorry`.
-/
import Mathlib

open Finset MeasureTheory intervalIntegral

noncomputable section

namespace KWin

/-! ## A. Definitions. -/

def phiF (par : ℕ) (y : ℝ) : ℝ := if par = 0 then Real.cos y else Real.sin y
def poleF (par : ℕ) (x : ℝ) : ℝ := if par = 0 then Real.cosh (x / 2) else Real.sinh (x / 2)
def tayl (par M : ℕ) (y : ℝ) : ℝ :=
  ∑ m ∈ range M, (-1) ^ m * y ^ (2 * m + par) / ((2 * m + par).factorial : ℝ)
def ptayl (par M : ℕ) (y : ℝ) : ℝ := ∑ m ∈ range M, y ^ (2 * m + par) / ((2 * m + par).factorial : ℝ)

/-- `int_{-l}^{l} |f|`. -/
def A1 (l : ℝ) (f : ℝ → ℝ) : ℝ := ∫ x in (-l)..l, |f x|
/-- `int_{-l}^{l} f(x) (x/l)^n dx`. -/
def mo (l : ℝ) (f : ℝ → ℝ) (n : ℕ) : ℝ := ∫ x in (-l)..l, f x * (x / l) ^ n
/-- The sector transform `int_{-l}^{l} f(x) phiF(t x) dx` (cosine / sine transform). -/
def Tr (l : ℝ) (par : ℕ) (f : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x in (-l)..l, f x * phiF par (t * x)
/-- The sector pole functional `int_{-l}^{l} f(x) poleF(x) dx`. -/
def Pl (l : ℝ) (par : ℕ) (f : ℝ → ℝ) : ℝ := ∫ x in (-l)..l, f x * poleF par x
/-- `int_{-l}^{l} f g`. -/
def ip (l : ℝ) (f g : ℝ → ℝ) : ℝ := ∫ x in (-l)..l, f x * g x

lemma continuous_phiF (par : ℕ) : Continuous (phiF par) := by
  by_cases h : par = 0
  · have e : phiF par = Real.cos := by funext y; simp [phiF, h]
    rw [e]; exact Real.continuous_cos
  · have e : phiF par = Real.sin := by funext y; simp [phiF, h]
    rw [e]; exact Real.continuous_sin

lemma continuous_poleF (par : ℕ) : Continuous (poleF par) := by
  by_cases h : par = 0
  · have e : poleF par = fun x => Real.cosh (x / 2) := by funext y; simp [poleF, h]
    rw [e]; fun_prop
  · have e : poleF par = fun x => Real.sinh (x / 2) := by funext y; simp [poleF, h]
    rw [e]; fun_prop

lemma continuous_tayl (par M : ℕ) : Continuous (tayl par M) := by
  unfold tayl; fun_prop

lemma continuous_ptayl (par M : ℕ) : Continuous (ptayl par M) := by
  unfold ptayl; fun_prop

lemma abs_phiF_le (par : ℕ) (y : ℝ) : |phiF par y| ≤ 1 := by
  by_cases h : par = 0
  · simp only [phiF, h, if_true]; exact Real.abs_cos_le_one y
  · simp only [phiF, h, if_false]; exact Real.abs_sin_le_one y

lemma phiF_neg (par : ℕ) (hpar : par = 0 ∨ par = 1) (y : ℝ) :
    phiF par (-y) = (if par = 0 then 1 else -1) * phiF par y := by
  rcases hpar with h | h <;> subst h <;> simp [phiF]

/-! ## B. Finite-sum bookkeeping. -/

lemma sum_range_two_mul {β : Type*} [AddCommMonoid β] (f : ℕ → β) (M : ℕ) :
    ∑ k ∈ range (2 * M), f k = ∑ m ∈ range M, (f (2 * m) + f (2 * m + 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    abel

lemma expI_sum_even (y : ℝ) (M : ℕ) :
    ∑ k ∈ range (2 * M), ((y : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)
      = ((tayl 0 M y : ℝ) : ℂ) + ((tayl 1 M y : ℝ) : ℂ) * Complex.I := by
  rw [sum_range_two_mul]
  unfold tayl
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h1 : ((y : ℂ) * Complex.I) ^ (2 * m) = (-1) ^ m * (y : ℂ) ^ (2 * m) := by
    rw [mul_pow, pow_mul Complex.I, Complex.I_sq]; ring
  have h2 : ((y : ℂ) * Complex.I) ^ (2 * m + 1) = (-1) ^ m * (y : ℂ) ^ (2 * m + 1) * Complex.I := by
    rw [pow_succ, h1]; ring
  simp only [add_zero]
  rw [h1, h2]
  ring

lemma expI_sum_odd (y : ℝ) (M : ℕ) :
    ∑ k ∈ range (2 * M + 1), ((y : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)
      = ((tayl 0 (M + 1) y : ℝ) : ℂ) + ((tayl 1 M y : ℝ) : ℂ) * Complex.I := by
  rw [Finset.sum_range_succ, expI_sum_even]
  have h1 : ((y : ℂ) * Complex.I) ^ (2 * M) = (-1) ^ M * (y : ℂ) ^ (2 * M) := by
    rw [mul_pow, pow_mul Complex.I, Complex.I_sq]; ring
  rw [h1]
  unfold tayl
  rw [Finset.sum_range_succ]
  push_cast
  simp only [add_zero]
  ring

lemma exp_sum_add_neg_even (y : ℝ) (M : ℕ) :
    ∑ k ∈ range (2 * M), y ^ k / (k.factorial : ℝ) + ∑ k ∈ range (2 * M), (-y) ^ k / (k.factorial : ℝ)
      = 2 * ptayl 0 M y := by
  rw [← Finset.sum_add_distrib, sum_range_two_mul]
  unfold ptayl
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e1 : (-y) ^ (2 * m) = y ^ (2 * m) := by rw [pow_mul, neg_sq, ← pow_mul]
  have e2 : (-y) ^ (2 * m + 1) = -y ^ (2 * m + 1) := by rw [pow_succ, e1]; ring
  simp only [add_zero]
  rw [e1, e2]
  ring

lemma exp_sum_sub_neg_odd (y : ℝ) (M : ℕ) :
    ∑ k ∈ range (2 * M + 1), y ^ k / (k.factorial : ℝ)
      - ∑ k ∈ range (2 * M + 1), (-y) ^ k / (k.factorial : ℝ) = 2 * ptayl 1 M y := by
  rw [← Finset.sum_sub_distrib, Finset.sum_range_succ, sum_range_two_mul]
  have e0 : (-y) ^ (2 * M) = y ^ (2 * M) := by rw [pow_mul, neg_sq, ← pow_mul]
  rw [e0, sub_self, add_zero]
  unfold ptayl
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e1 : (-y) ^ (2 * m) = y ^ (2 * m) := by rw [pow_mul, neg_sq, ← pow_mul]
  have e2 : (-y) ^ (2 * m + 1) = -y ^ (2 * m + 1) := by rw [pow_succ, e1]; ring
  rw [e1, e2]
  ring

/-! ## C. Pointwise Taylor remainders. -/

lemma cos_sub_tayl_le {y : ℝ} {M : ℕ} (hy : |y| ≤ (2 * M + 1) / 2) :
    |Real.cos y - tayl 0 M y| ≤ 2 * |y| ^ (2 * M) / ((2 * M).factorial : ℝ) := by
  have hx : ‖(y : ℂ) * Complex.I‖ / ((2 * M).succ : ℝ) ≤ 1 / 2 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      div_le_iff₀ (by positivity)]
    push_cast
    linarith
  have h := Complex.exp_bound' hx
  rw [expI_sum_even] at h
  have e : Complex.exp ((y : ℂ) * Complex.I) - (((tayl 0 M y : ℝ) : ℂ) + ((tayl 1 M y : ℝ) : ℂ) * Complex.I)
      = ((Real.cos y - tayl 0 M y : ℝ) : ℂ) + ((Real.sin y - tayl 1 M y : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  rw [e] at h
  have hre := Complex.abs_re_le_norm (((Real.cos y - tayl 0 M y : ℝ) : ℂ)
    + ((Real.sin y - tayl 1 M y : ℝ) : ℂ) * Complex.I)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] at hre
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at h
  calc |Real.cos y - tayl 0 M y| ≤ _ := hre
    _ ≤ _ := h
    _ = 2 * |y| ^ (2 * M) / ((2 * M).factorial : ℝ) := by ring

lemma sin_sub_tayl_le {y : ℝ} {M : ℕ} (hy : |y| ≤ (2 * M + 1 + 1) / 2) :
    |Real.sin y - tayl 1 M y| ≤ 2 * |y| ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ) := by
  have hx : ‖(y : ℂ) * Complex.I‖ / ((2 * M + 1).succ : ℝ) ≤ 1 / 2 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      div_le_iff₀ (by positivity)]
    push_cast
    linarith
  have h := Complex.exp_bound' hx
  rw [expI_sum_odd] at h
  have e : Complex.exp ((y : ℂ) * Complex.I)
      - (((tayl 0 (M + 1) y : ℝ) : ℂ) + ((tayl 1 M y : ℝ) : ℂ) * Complex.I)
      = ((Real.cos y - tayl 0 (M + 1) y : ℝ) : ℂ) + ((Real.sin y - tayl 1 M y : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  rw [e] at h
  have him := Complex.abs_im_le_norm (((Real.cos y - tayl 0 (M + 1) y : ℝ) : ℂ)
    + ((Real.sin y - tayl 1 M y : ℝ) : ℂ) * Complex.I)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.ofReal_re,
    Complex.I_im, mul_zero, mul_one, zero_add, add_zero] at him
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at h
  calc |Real.sin y - tayl 1 M y| ≤ _ := him
    _ ≤ _ := h
    _ = 2 * |y| ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ) := by ring

/-- The sector Taylor remainder. -/
theorem phiF_sub_tayl_le {par M : ℕ} (hpar : par = 0 ∨ par = 1) {y : ℝ}
    (hy : |y| ≤ (2 * M + par + 1) / 2) :
    |phiF par y - tayl par M y| ≤ 2 * |y| ^ (2 * M + par) / ((2 * M + par).factorial : ℝ) := by
  rcases hpar with h | h <;> subst h
  · simp only [phiF, if_true, add_zero] at hy ⊢
    push_cast at hy
    exact cos_sub_tayl_le (by simpa using hy)
  · simp only [phiF, one_ne_zero, if_false] at hy ⊢
    push_cast at hy
    exact sin_sub_tayl_le (by linarith)

lemma real_exp_bound2 {y : ℝ} (hy : |y| ≤ 1) {n : ℕ} (hn : 0 < n) :
    |Real.exp y - ∑ m ∈ range n, y ^ m / (m.factorial : ℝ)| ≤ 2 * |y| ^ n / (n.factorial : ℝ) := by
  have h := Real.exp_bound hy hn
  refine h.trans ?_
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hp : 0 ≤ |y| ^ n := by positivity
  rw [show (2 : ℝ) * |y| ^ n / (n.factorial : ℝ) = |y| ^ n * (2 / (n.factorial : ℝ)) by ring]
  apply mul_le_mul_of_nonneg_left _ hp
  push_cast
  rw [div_le_div_iff₀ (by positivity) hf]
  nlinarith

/-- The pole Taylor remainder (`|x/2| <= 1`, at least one term). -/
theorem poleF_sub_ptayl_le {par M : ℕ} (hpar : par = 0 ∨ par = 1) (hM : 0 < 2 * M + par) {x : ℝ}
    (hx : |x / 2| ≤ 1) :
    |poleF par x - ptayl par M (x / 2)| ≤ 2 * |x / 2| ^ (2 * M + par) / ((2 * M + par).factorial : ℝ) := by
  have hx' : |-(x / 2)| ≤ 1 := by rwa [abs_neg]
  have h1 := real_exp_bound2 hx hM
  have h2 := real_exp_bound2 hx' hM
  rw [abs_neg] at h2
  rcases hpar with h | h <;> subst h
  · simp only [add_zero] at h1 h2 hM ⊢
    have hs := exp_sum_add_neg_even (x / 2) M
    simp only [poleF, if_true]
    rw [Real.cosh_eq]
    have e : (Real.exp (x / 2) + Real.exp (-(x / 2))) / 2 - ptayl 0 M (x / 2)
        = ((Real.exp (x / 2) - ∑ m ∈ range (2 * M), (x / 2) ^ m / (m.factorial : ℝ))
          + (Real.exp (-(x / 2)) - ∑ m ∈ range (2 * M), (-(x / 2)) ^ m / (m.factorial : ℝ))) / 2 := by
      linarith
    rw [e, abs_div, abs_two]
    have := abs_add_le (Real.exp (x / 2) - ∑ m ∈ range (2 * M), (x / 2) ^ m / (m.factorial : ℝ))
      (Real.exp (-(x / 2)) - ∑ m ∈ range (2 * M), (-(x / 2)) ^ m / (m.factorial : ℝ))
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    linarith
  · have hs := exp_sum_sub_neg_odd (x / 2) M
    simp only [poleF, one_ne_zero, if_false]
    rw [Real.sinh_eq]
    have e : (Real.exp (x / 2) - Real.exp (-(x / 2))) / 2 - ptayl 1 M (x / 2)
        = ((Real.exp (x / 2) - ∑ m ∈ range (2 * M + 1), (x / 2) ^ m / (m.factorial : ℝ))
          - (Real.exp (-(x / 2)) - ∑ m ∈ range (2 * M + 1), (-(x / 2)) ^ m / (m.factorial : ℝ))) / 2 := by
      linarith
    rw [e, abs_div, abs_two]
    have := abs_sub (Real.exp (x / 2) - ∑ m ∈ range (2 * M + 1), (x / 2) ^ m / (m.factorial : ℝ))
      (Real.exp (-(x / 2)) - ∑ m ∈ range (2 * M + 1), (-(x / 2)) ^ m / (m.factorial : ℝ))
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    linarith

/-! ## D. Integral calculus on [-l, l]. -/

lemma intervalIntegrable_of_cont {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ) :
    IntervalIntegrable f volume a b := hf.intervalIntegrable a b

/-- `|int f g| <= B int |f|` when `|g| <= B` on `[-l, l]`. -/
lemma abs_int_mul_le {l : ℝ} (hl : 0 ≤ l) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {B : ℝ} (hB : ∀ x ∈ Set.Icc (-l) l, |g x| ≤ B) :
    |∫ x in (-l)..l, f x * g x| ≤ B * A1 l f := by
  have hab : -l ≤ l := by linarith
  refine (intervalIntegral.abs_integral_le_integral_abs hab).trans ?_
  have hmono : ∫ x in (-l)..l, |f x * g x| ≤ ∫ x in (-l)..l, |f x| * B := by
    apply intervalIntegral.integral_mono_on hab
    · exact (hf.mul hg).abs.intervalIntegrable _ _
    · exact (hf.abs.mul continuous_const).intervalIntegrable _ _
    · intro x hx
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hB x hx) (abs_nonneg _)
  refine hmono.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_mul_const]
  unfold A1
  ring

lemma A1_nonneg {l : ℝ} (hl : 0 ≤ l) (f : ℝ → ℝ) : 0 ≤ A1 l f :=
  intervalIntegral.integral_nonneg (by linarith) fun x _ => abs_nonneg _

/-- Cauchy-Schwarz on `[-l, l]`: `(int |f|)^2 <= 2 l int f^2`. -/
theorem A1_sq_le {l : ℝ} (hl : 0 < l) {f : ℝ → ℝ} (hf : Continuous f) :
    A1 l f ^ 2 ≤ 2 * l * ∫ x in (-l)..l, f x ^ 2 := by
  set m := A1 l f / (2 * l) with hm
  have hab : -l ≤ l := by linarith
  have h0 : 0 ≤ ∫ x in (-l)..l, (|f x| - m) ^ 2 :=
    intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg _
  have e : (fun x => (|f x| - m) ^ 2) = fun x => f x ^ 2 - (2 * m) * |f x| + m ^ 2 := by
    funext x; rw [sub_sq, sq_abs]; ring
  have hI1 : IntervalIntegrable (fun x => f x ^ 2) volume (-l) l := (hf.pow 2).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun x => (2 * m) * |f x|) volume (-l) l :=
    (continuous_const.mul hf.abs).intervalIntegrable _ _
  rw [e, intervalIntegral.integral_add (hI1.sub hI2) intervalIntegrable_const,
    intervalIntegral.integral_sub hI1 hI2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at h0
  simp only [smul_eq_mul, sub_neg_eq_add] at h0
  have hA : A1 l f = ∫ x in (-l)..l, |f x| := rfl
  rw [← hA] at h0
  have hl2 : (l + l) = 2 * l := by ring
  rw [hl2] at h0
  have hmm : 2 * m * A1 l f - m ^ 2 * (2 * l) = A1 l f ^ 2 / (2 * l) := by
    rw [hm]; field_simp; ring
  have : A1 l f ^ 2 / (2 * l) ≤ ∫ x in (-l)..l, f x ^ 2 := by linarith
  rwa [div_le_iff₀ (by positivity), mul_comm] at this

/-! ## E. The transforms: truncation, crude bounds, continuity. -/

lemma pow_mul_div_pow {l : ℝ} (hl : l ≠ 0) (t x : ℝ) (n : ℕ) :
    (t * x) ^ n = (t * l) ^ n * (x / l) ^ n := by
  rw [← mul_pow]; congr 1; field_simp

/-- The truncated transform, as an integral. -/
lemma int_mul_tayl {l : ℝ} (hl : 0 < l) {f : ℝ → ℝ} (hf : Continuous f) (par M : ℕ) (t : ℝ) :
    ∫ x in (-l)..l, f x * tayl par M (t * x)
      = ∑ m ∈ range M, (-1) ^ m * (t * l) ^ (2 * m + par) / ((2 * m + par).factorial : ℝ)
          * mo l f (2 * m + par) := by
  unfold tayl mo
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    rw [pow_mul_div_pow hl.ne']
    ring
  · intro m _
    exact (hf.mul (by fun_prop)).intervalIntegrable _ _

lemma int_mul_ptayl {l : ℝ} (hl : 0 < l) {f : ℝ → ℝ} (hf : Continuous f) (par M : ℕ) :
    ∫ x in (-l)..l, f x * ptayl par M (x / 2)
      = ∑ m ∈ range M, (l / 2) ^ (2 * m + par) / ((2 * m + par).factorial : ℝ) * mo l f (2 * m + par) := by
  unfold ptayl mo
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    have : (x / 2) ^ (2 * m + par) = (l / 2) ^ (2 * m + par) * (x / l) ^ (2 * m + par) := by
      rw [← mul_pow]; congr 1; field_simp
    rw [this]
    ring
  · intro m _
    exact (hf.mul (by fun_prop)).intervalIntegrable _ _

/-- **Transform truncation.**  For `0 <= t`, `t l <= (2M+par+1)/2`. -/
theorem Tr_sub_le {l : ℝ} (hl : 0 < l) {par M : ℕ} (hpar : par = 0 ∨ par = 1) {f : ℝ → ℝ}
    (hf : Continuous f) {t : ℝ} (ht : 0 ≤ t) (htl : t * l ≤ (2 * M + par + 1) / 2) :
    |Tr l par f t - ∑ m ∈ range M, (-1) ^ m * (t * l) ^ (2 * m + par) / ((2 * m + par).factorial : ℝ)
        * mo l f (2 * m + par)|
      ≤ 2 * (t * l) ^ (2 * M + par) / ((2 * M + par).factorial : ℝ) * A1 l f := by
  have hI1 : IntervalIntegrable (fun x => f x * phiF par (t * x)) volume (-l) l :=
    (hf.mul ((continuous_phiF par).comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun x => f x * tayl par M (t * x)) volume (-l) l :=
    (hf.mul ((continuous_tayl par M).comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  rw [← int_mul_tayl hl hf, Tr, ← intervalIntegral.integral_sub hI1 hI2]
  have e : (fun x => f x * phiF par (t * x) - f x * tayl par M (t * x))
      = fun x => f x * (phiF par (t * x) - tayl par M (t * x)) := by funext x; ring
  rw [e]
  apply abs_int_mul_le hl.le hf
  · exact ((continuous_phiF par).comp (continuous_const.mul continuous_id)).sub
      ((continuous_tayl par M).comp (continuous_const.mul continuous_id))
  · intro x hx
    have hxl : |x| ≤ l := abs_le.mpr ⟨hx.1, hx.2⟩
    have htx : |t * x| ≤ t * l := by
      rw [abs_mul, abs_of_nonneg ht]; exact mul_le_mul_of_nonneg_left hxl ht
    refine (phiF_sub_tayl_le hpar (htx.trans htl)).trans ?_
    have hfac : (0 : ℝ) < ((2 * M + par).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [div_le_div_iff_of_pos_right hfac]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) htx _) (by norm_num)

/-- **Pole truncation.**  For `l/2 <= 1`. -/
theorem Pl_sub_le {l : ℝ} (hl : 0 < l) (hl2 : l / 2 ≤ 1) {par M : ℕ} (hpar : par = 0 ∨ par = 1)
    (hM : 0 < 2 * M + par) {f : ℝ → ℝ} (hf : Continuous f) :
    |Pl l par f - ∑ m ∈ range M, (l / 2) ^ (2 * m + par) / ((2 * m + par).factorial : ℝ)
        * mo l f (2 * m + par)|
      ≤ 2 * (l / 2) ^ (2 * M + par) / ((2 * M + par).factorial : ℝ) * A1 l f := by
  have hI1 : IntervalIntegrable (fun x => f x * poleF par x) volume (-l) l :=
    (hf.mul (continuous_poleF par)).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun x => f x * ptayl par M (x / 2)) volume (-l) l :=
    (hf.mul ((continuous_ptayl par M).comp (continuous_id.div_const 2))).intervalIntegrable _ _
  rw [← int_mul_ptayl hl hf, Pl, ← intervalIntegral.integral_sub hI1 hI2]
  have e : (fun x => f x * poleF par x - f x * ptayl par M (x / 2))
      = fun x => f x * (poleF par x - ptayl par M (x / 2)) := by funext x; ring
  rw [e]
  apply abs_int_mul_le hl.le hf
  · exact (continuous_poleF par).sub ((continuous_ptayl par M).comp (continuous_id.div_const 2))
  · intro x hx
    have hxl : |x / 2| ≤ l / 2 := by
      rw [abs_div, abs_two]
      exact div_le_div_of_nonneg_right (abs_le.mpr ⟨hx.1, hx.2⟩) (by norm_num)
    refine (poleF_sub_ptayl_le hpar hM (hxl.trans hl2)).trans ?_
    have hfac : (0 : ℝ) < ((2 * M + par).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [div_le_div_iff_of_pos_right hfac]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hxl _) (by norm_num)

theorem abs_Tr_le {l : ℝ} (hl : 0 < l) (par : ℕ) {f : ℝ → ℝ} (hf : Continuous f) (t : ℝ) :
    |Tr l par f t| ≤ A1 l f := by
  have := abs_int_mul_le hl.le hf ((continuous_phiF par).comp (continuous_const.mul continuous_id))
    (B := 1) fun x _ => abs_phiF_le par (t * x)
  simpa [Tr] using this

theorem abs_Pl_le {l : ℝ} (hl : 0 < l) (par : ℕ) {f : ℝ → ℝ} (hf : Continuous f) :
    |Pl l par f| ≤ Real.cosh (l / 2) * A1 l f := by
  apply abs_int_mul_le hl.le hf (continuous_poleF par)
  intro x hx
  have hc : Real.cosh (x / 2) ≤ Real.cosh (l / 2) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg (by linarith : 0 ≤ l / 2), abs_div, abs_two]
    exact div_le_div_of_nonneg_right (abs_le.mpr ⟨hx.1, hx.2⟩) (by norm_num)
  by_cases h : par = 0
  · simp only [poleF, h, if_true]
    rw [abs_of_pos (Real.cosh_pos _)]
    exact hc
  · simp only [poleF, h, if_false]
    refine le_trans ?_ hc
    rw [abs_le]
    constructor
    · have := Real.sinh_lt_cosh (-(x / 2))
      rw [Real.sinh_neg, Real.cosh_neg] at this
      linarith
    · exact (Real.sinh_lt_cosh _).le

theorem continuous_Tr (l : ℝ) (par : ℕ) {f : ℝ → ℝ} (hf : Continuous f) : Continuous (Tr l par f) := by
  unfold Tr
  have hc : Continuous (fun p : ℝ × ℝ => f p.2 * phiF par (p.1 * p.2)) :=
    (hf.comp continuous_snd).mul ((continuous_phiF par).comp (continuous_fst.mul continuous_snd))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc (-l) l

end KWin

end
