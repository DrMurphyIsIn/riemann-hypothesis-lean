/-
  ArchS10_Exact -- stage S10 of the archimedean conceptual blueprint (2026-10-11), part 1:
  the data-independent algebra behind the certified kernel χ.

  1. `CC f f' t` is CC's C_n(ρ) of (99) at ρ = e^t, written for an arbitrary pair (f, f') in place
     of (ξ_n^an, (ξ_n^an)'), so that `ArchS8.ProlateData.Cn D n t = CC (D.phi n) (deriv (D.phi n)) t`
     (`Cn_eq_CC`, by `rfl`).  It is quadratic: `CC (c f) (c f') = c² CC f f'` (`CC_smul`).
  2. `CC_psi` (the exact polynomial integral).  For an even polynomial ψ = Σ_k B_k x^{2k}
     (S9's `psi J B n`),
        CC ψ ψ' t = Σ_l hh_l (e^{(2l+1/2)t} - e^{-(2l+1/2)t}),
        hh_l = Σ_k 4kl B_k B_l/(2k+2l+1) - ψ(1)·2l·B_l.
     The double integral of CC (99) collapses to a finite sinh series because the two boundary
     terms of (99) cancel the "lower-limit" half of the polynomial integral after a k ↔ l swap.
  3. `abs_exp_sub_taylor_le`: |e^x - Σ_{m<N} x^m/m!| ≤ 2|x|^N/N! for |x| ≤ (N+1)/2
     (Mathlib's `Complex.exp_bound'`).
  4. `abs_CC_sub_le`, `abs_CC_le`: perturbation bounds for CC on t ∈ [0, log 2] from bounds of
     f, f' on [1/2, 2] (the only arguments CC uses there).
  No sorry, no axiom.  conjecture1_proved = False.  Nothing here is RH progress.
-/
import ArchS8_ProlateData
import ArchS9_Frame

open MeasureTheory Set Finset
open scoped Interval

noncomputable section

namespace ArchS10

/-- CC (99), `C(ρ)` at `ρ = e^t`, for an arbitrary function `f` with derivative stand-in `f'`:
`ρ^{1/2}∫_{ρ⁻¹}^1 x f'(x) ρx f'(ρx) dx + ρ^{-3/2} f'(ρ⁻¹) f(1) - ρ^{3/2} f(1) f'(ρ)`. -/
def CC (f f' : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (t / 2) * (∫ x in (Real.exp (-t))..1,
      (x * f' x) * (Real.exp t * x * f' (Real.exp t * x)))
    + Real.exp (-(3 / 2) * t) * f' (Real.exp (-t)) * f 1
    - Real.exp ((3 / 2) * t) * f 1 * f' (Real.exp t)

theorem Cn_eq_CC (D : ArchS8.ProlateDataNat) (n : ℕ) (t : ℝ) :
    D.Cn n t = CC (D.phi n) (deriv (D.phi n)) t := rfl

theorem CC_smul (c : ℝ) (f f' : ℝ → ℝ) (t : ℝ) :
    CC (fun x => c * f x) (fun x => c * f' x) t = c ^ 2 * CC f f' t := by
  unfold CC
  have : (∫ x in (Real.exp (-t))..1,
        (x * (c * f' x)) * (Real.exp t * x * (c * f' (Real.exp t * x))))
      = c ^ 2 * ∫ x in (Real.exp (-t))..1, (x * f' x) * (Real.exp t * x * f' (Real.exp t * x)) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => by ring
  rw [this]; ring

/-- `e^{b t} - e^{-b t}` with `b = 2l + 1/2`. -/
def ex (l : ℕ) (t : ℝ) : ℝ :=
  Real.exp ((2 * l + 1 / 2) * t) - Real.exp (-((2 * l + 1 / 2) * t))

/-- The exact coefficient `hh_l` of `CC ψ ψ'` (see the module header). -/
def hhR (J : ℕ) (B : ℕ → ℕ → ℝ) (n l : ℕ) : ℝ :=
  (∑ k ∈ range J, 4 * (k : ℝ) * l * B n k * B n l / (2 * k + 2 * l + 1))
    - (∑ k ∈ range J, B n k) * (2 * l) * B n l

section Poly

variable (J : ℕ) (B : ℕ → ℕ → ℝ) (n : ℕ)

lemma x_psid (x : ℝ) :
    x * ArchS9.psid J B n x = ∑ k ∈ range J, B n k * (2 * k) * x ^ (2 * k) := by
  unfold ArchS9.psid
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases k with _ | k
  · simp
  · have : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    rw [this, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ]
    ring

lemma psi_one : ArchS9.psi J B n 1 = ∑ k ∈ range J, B n k := by
  simp [ArchS9.psi]

lemma bdry_lo (t : ℝ) :
    Real.exp (-(3 / 2) * t) * ArchS9.psid J B n (Real.exp (-t))
      = ∑ l ∈ range J, B n l * (2 * l) * Real.exp (-((2 * l + 1 / 2) * t)) := by
  unfold ArchS9.psid
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rcases l with _ | l
  · simp
  · rw [← Real.exp_nat_mul]
    have h : Real.exp (-(3 / 2) * t) * Real.exp (((2 * (l + 1) - 1 : ℕ) : ℝ) * -t)
        = Real.exp (-((2 * ((l + 1 : ℕ) : ℝ) + 1 / 2) * t)) := by
      rw [← Real.exp_add]; congr 1
      have : ((2 * (l + 1) - 1 : ℕ) : ℝ) = 2 * l + 1 := by
        rw [show 2 * (l + 1) - 1 = 2 * l + 1 by omega]; push_cast; ring
      rw [this]; push_cast; ring
    calc Real.exp (-(3 / 2) * t) * (B n (l + 1) * (2 * ((l + 1 : ℕ) : ℝ))
          * Real.exp (((2 * (l + 1) - 1 : ℕ) : ℝ) * -t))
        = B n (l + 1) * (2 * ((l + 1 : ℕ) : ℝ))
          * (Real.exp (-(3 / 2) * t) * Real.exp (((2 * (l + 1) - 1 : ℕ) : ℝ) * -t)) := by ring
      _ = _ := by rw [h]

lemma bdry_hi (t : ℝ) :
    Real.exp ((3 / 2) * t) * ArchS9.psid J B n (Real.exp t)
      = ∑ l ∈ range J, B n l * (2 * l) * Real.exp ((2 * l + 1 / 2) * t) := by
  unfold ArchS9.psid
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rcases l with _ | l
  · simp
  · rw [← Real.exp_nat_mul]
    have h : Real.exp ((3 / 2) * t) * Real.exp (((2 * (l + 1) - 1 : ℕ) : ℝ) * t)
        = Real.exp ((2 * ((l + 1 : ℕ) : ℝ) + 1 / 2) * t) := by
      rw [← Real.exp_add]; congr 1
      have : ((2 * (l + 1) - 1 : ℕ) : ℝ) = 2 * l + 1 := by
        rw [show 2 * (l + 1) - 1 = 2 * l + 1 by omega]; push_cast; ring
      rw [this]; push_cast; ring
    calc Real.exp ((3 / 2) * t) * (B n (l + 1) * (2 * ((l + 1 : ℕ) : ℝ))
          * Real.exp (((2 * (l + 1) - 1 : ℕ) : ℝ) * t))
        = B n (l + 1) * (2 * ((l + 1 : ℕ) : ℝ))
          * (Real.exp ((3 / 2) * t) * Real.exp (((2 * (l + 1) - 1 : ℕ) : ℝ) * t)) := by ring
      _ = _ := by rw [h]

lemma term_id (k l : ℕ) (t : ℝ) :
    Real.exp (t / 2) * (Real.exp t ^ (2 * l)
        * ((1 : ℝ) ^ (2 * k + 2 * l + 1) - Real.exp (-t) ^ (2 * k + 2 * l + 1)))
      = Real.exp ((2 * l + 1 / 2) * t) - Real.exp (-((2 * k + 1 / 2) * t)) := by
  rw [one_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul, mul_sub, mul_one, mul_sub,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  · congr 1; push_cast; ring
  · congr 1; push_cast; ring

lemma integral_part (t : ℝ) :
    Real.exp (t / 2) * (∫ x in (Real.exp (-t))..1,
        (x * ArchS9.psid J B n x) * (Real.exp t * x * ArchS9.psid J B n (Real.exp t * x)))
      = ∑ k ∈ range J, ∑ l ∈ range J, B n k * (2 * k) * (B n l * (2 * l))
          / (2 * k + 2 * l + 1) * (Real.exp ((2 * l + 1 / 2) * t)
            - Real.exp (-((2 * k + 1 / 2) * t))) := by
  have hint : ∀ x, (x * ArchS9.psid J B n x) * (Real.exp t * x * ArchS9.psid J B n (Real.exp t * x))
      = ∑ k ∈ range J, ∑ l ∈ range J,
          (B n k * (2 * k) * (B n l * (2 * l)) * Real.exp t ^ (2 * l)) * x ^ (2 * k + 2 * l) := by
    intro x
    rw [x_psid, x_psid, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_pow, pow_add]; ring
  simp_rw [hint]
  rw [intervalIntegral.integral_finsetSum (fun k _ => ?_)]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_finsetSum (fun l _ => ?_)]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [intervalIntegral.integral_const_mul, integral_pow, ← term_id k l t]
      push_cast
      field_simp
    · exact (continuous_const.mul (continuous_pow _)).intervalIntegrable _ _
  · exact (continuous_finsetSum _ fun l _ =>
      continuous_const.mul (continuous_pow _)).intervalIntegrable _ _

/-- **The exact polynomial integral**: CC (99) for S9's even polynomial ψ is a finite sinh series. -/
theorem CC_psi (t : ℝ) :
    CC (ArchS9.psi J B n) (ArchS9.psid J B n) t = ∑ l ∈ range J, hhR J B n l * ex l t := by
  set P : ℕ → ℝ := fun l => Real.exp ((2 * l + 1 / 2) * t) with hP
  set N : ℕ → ℝ := fun l => Real.exp (-((2 * l + 1 / 2) * t)) with hN
  set c : ℕ → ℝ := fun k => B n k * (2 * k) with hc
  set q : ℕ → ℕ → ℝ := fun k l => c k * c l / (2 * k + 2 * l + 1) with hq
  have hsym : ∀ k l, q k l = q l k := fun k l => by simp only [hq]; ring_nf
  have h1 := integral_part J B n t
  have h2 := bdry_lo J B n t
  have h3 := bdry_hi J B n t
  have e1 : Real.exp (-(3 / 2) * t) * ArchS9.psid J B n (Real.exp (-t)) * ArchS9.psi J B n 1
      = ArchS9.psi J B n 1 * (Real.exp (-(3 / 2) * t) * ArchS9.psid J B n (Real.exp (-t))) := by ring
  have e2 : Real.exp ((3 / 2) * t) * ArchS9.psi J B n 1 * ArchS9.psid J B n (Real.exp t)
      = ArchS9.psi J B n 1 * (Real.exp ((3 / 2) * t) * ArchS9.psid J B n (Real.exp t)) := by ring
  unfold CC
  rw [h1, e1, e2, h2, h3, psi_one]
  set S1 := ∑ k ∈ range J, B n k
  -- the double sum, symmetrised
  have hdouble : ∑ k ∈ range J, ∑ l ∈ range J, B n k * (2 * k) * (B n l * (2 * l))
        / (2 * k + 2 * l + 1) * (P l - N k)
      = ∑ l ∈ range J, (∑ k ∈ range J, q k l) * (P l - N l) := by
    have a1 : ∑ k ∈ range J, ∑ l ∈ range J, B n k * (2 * k) * (B n l * (2 * l))
          / (2 * k + 2 * l + 1) * (P l - N k)
        = ∑ k ∈ range J, ∑ l ∈ range J, q k l * P l - ∑ k ∈ range J, ∑ l ∈ range J, q k l * N k := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [hq, hc]; ring
    have a2 : ∑ k ∈ range J, ∑ l ∈ range J, q k l * P l = ∑ l ∈ range J, (∑ k ∈ range J, q k l) * P l := by
      rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun l _ => by rw [Finset.sum_mul]
    have a3 : ∑ k ∈ range J, ∑ l ∈ range J, q k l * N k = ∑ k ∈ range J, (∑ l ∈ range J, q l k) * N k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun l _ => by rw [hsym]
    rw [a1, a2, a3, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [show (∑ k ∈ range J, ∑ l ∈ range J, B n k * (2 * k) * (B n l * (2 * l))
        / (2 * k + 2 * l + 1) * (Real.exp ((2 * l + 1 / 2) * t) - Real.exp (-((2 * k + 1 / 2) * t))))
      = ∑ k ∈ range J, ∑ l ∈ range J, B n k * (2 * k) * (B n l * (2 * l))
        / (2 * k + 2 * l + 1) * (P l - N k) from rfl, hdouble]
  unfold hhR ex
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hql : ∑ k ∈ range J, q k l = ∑ k ∈ range J, 4 * (k : ℝ) * l * B n k * B n l / (2 * k + 2 * l + 1) :=
    Finset.sum_congr rfl fun k _ => by simp only [hq, hc]; ring
  rw [hql]
  simp only [hP, hN]
  ring

end Poly

/-! ## Exponential Taylor bound and the size of `ex`. -/

/-- `|e^x - Σ_{m<N} x^m/m!| ≤ 2|x|^N/N!` as soon as `|x| ≤ (N+1)/2`. -/
theorem abs_exp_sub_taylor_le {x : ℝ} {N : ℕ} (hx : |x| ≤ ((N : ℝ) + 1) / 2) :
    |Real.exp x - ∑ m ∈ range N, x ^ m / (m.factorial : ℝ)| ≤ |x| ^ N / (N.factorial : ℝ) * 2 := by
  have hx' : ‖(x : ℂ)‖ / (N.succ : ℝ) ≤ 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ (by positivity)]
    push_cast; linarith
  have h := Complex.exp_bound' hx'
  have e : Complex.exp (x : ℂ) - ∑ m ∈ range N, (x : ℂ) ^ m / (m.factorial : ℂ)
      = ((Real.exp x - ∑ m ∈ range N, x ^ m / (m.factorial : ℝ) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [e, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

lemma exp_mul_le_two_pow {b t : ℝ} (l : ℕ) (hb : b ≤ 2 * l + 1) (ht0 : 0 ≤ t)
    (ht : t ≤ Real.log 2) : Real.exp (b * t) ≤ 2 ^ (2 * l + 1) := by
  have h1 : b * t ≤ ((2 * l + 1 : ℕ) : ℝ) * Real.log 2 := by
    push_cast
    exact mul_le_mul hb ht ht0 (by positivity)
  calc Real.exp (b * t) ≤ Real.exp (((2 * l + 1 : ℕ) : ℝ) * Real.log 2) := Real.exp_le_exp.2 h1
    _ = 2 ^ (2 * l + 1) := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

/-- `|e^{b t} - e^{-b t}| ≤ 2^{2l+1} + 1` on `[0, log 2]`. -/
theorem abs_ex_le (l : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ Real.log 2) :
    |ex l t| ≤ 2 ^ (2 * l + 1) + 1 := by
  unfold ex
  have h1 := exp_mul_le_two_pow (b := 2 * l + 1 / 2) l (by linarith) ht0 ht
  have h2 : Real.exp (-((2 * l + 1 / 2) * t)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by have : 0 ≤ (2 * (l : ℝ) + 1 / 2) * t := by positivity
                              linarith)
  have h3 := Real.exp_pos ((2 * l + 1 / 2) * t)
  have h4 := Real.exp_pos (-((2 * l + 1 / 2) * t))
  rw [abs_le]; constructor <;> linarith

/-! ## Perturbation bounds for `CC` on `[0, log 2]`. -/

lemma exp_le_two {t : ℝ} (ht : t ≤ Real.log 2) : Real.exp t ≤ 2 := by
  calc Real.exp t ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 ht
    _ = 2 := Real.exp_log (by norm_num)

lemma half_le_exp_neg {t : ℝ} (ht : t ≤ Real.log 2) : 1 / 2 ≤ Real.exp (-t) := by
  rw [Real.exp_neg]
  have := exp_le_two ht
  have h0 := Real.exp_pos t
  rw [le_inv_comm₀ (by norm_num) h0]; linarith

lemma exp_half_le_two {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ Real.log 2) : Real.exp (t / 2) ≤ 2 :=
  (Real.exp_le_exp.2 (by linarith)).trans (exp_le_two ht)

lemma exp_three_half_le_four {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ Real.log 2) :
    Real.exp ((3 / 2) * t) ≤ 4 := by
  have h : Real.exp ((3 / 2) * t) ≤ Real.exp (2 * t) := Real.exp_le_exp.2 (by linarith)
  have h2 : Real.exp (2 * t) = Real.exp t ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h2] at h
  have := exp_le_two ht
  have h0 := Real.exp_pos t
  nlinarith

lemma exp_neg_three_half_le_one {t : ℝ} (ht0 : 0 ≤ t) : Real.exp (-(3 / 2) * t) ≤ 1 :=
  Real.exp_le_one_iff.2 (by nlinarith)

/-- `|ab - cd| ≤ |a - c|(|d| + |b - d|) + |c| |b - d|`, with bounds plugged in. -/
lemma abs_mul_sub_mul_le {a b c d ea eb Gc Gd : ℝ} (ha : |a - c| ≤ ea) (hb : |b - d| ≤ eb)
    (hc : |c| ≤ Gc) (hd : |d| ≤ Gd) : |a * b - c * d| ≤ ea * (Gd + eb) + Gc * eb := by
  have e : a * b - c * d = (a - c) * b + c * (b - d) := by ring
  have hb' : |b| ≤ Gd + eb := by
    have := abs_sub_abs_le_abs_sub b d; linarith
  have hea : 0 ≤ ea := (abs_nonneg _).trans ha
  have hGc : 0 ≤ Gc := (abs_nonneg _).trans hc
  rw [e]
  calc |(a - c) * b + c * (b - d)| ≤ |a - c| * |b| + |c| * |b - d| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ ea * (Gd + eb) + Gc * eb := by gcongr

/-- **Perturbation of CC** on `t ∈ [0, log 2]`: only values on `[1/2, 2]` enter. -/
theorem abs_CC_sub_le {f f' g g' : ℝ → ℝ} {e0 e1 G0 G1 t : ℝ}
    (hf : Continuous f') (hg : Continuous g')
    (h0 : ∀ x ∈ Icc (1 / 2 : ℝ) 2, |f x - g x| ≤ e0)
    (h1 : ∀ x ∈ Icc (1 / 2 : ℝ) 2, |f' x - g' x| ≤ e1)
    (hG0 : ∀ x ∈ Icc (1 / 2 : ℝ) 2, |g x| ≤ G0) (hG1 : ∀ x ∈ Icc (1 / 2 : ℝ) 2, |g' x| ≤ G1)
    (ht0 : 0 ≤ t) (ht : t ≤ Real.log 2) :
    |CC f f' t - CC g g' t|
      ≤ 4 * (e1 * (G1 + e1) + G1 * e1) + (e1 * (G0 + e0) + G1 * e0)
        + 4 * (e0 * (G1 + e1) + G0 * e1) := by
  have hρ := exp_le_two ht
  have hρ1 : 1 ≤ Real.exp t := Real.one_le_exp_iff.2 ht0
  have hi := half_le_exp_neg ht
  have hi1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hm1 : (1 : ℝ) ∈ Icc (1 / 2 : ℝ) 2 := ⟨by norm_num, by norm_num⟩
  have hmρ : Real.exp t ∈ Icc (1 / 2 : ℝ) 2 := ⟨by linarith, hρ⟩
  have hmi : Real.exp (-t) ∈ Icc (1 / 2 : ℝ) 2 := ⟨hi, by linarith⟩
  have he0 : 0 ≤ e0 := (abs_nonneg _).trans (h0 1 hm1)
  have he1 : 0 ≤ e1 := (abs_nonneg _).trans (h1 1 hm1)
  have hG0' : 0 ≤ G0 := (abs_nonneg _).trans (hG0 1 hm1)
  have hG1' : 0 ≤ G1 := (abs_nonneg _).trans (hG1 1 hm1)
  set P11 := e1 * (G1 + e1) + G1 * e1
  have hP11 : 0 ≤ P11 := by positivity
  -- the integral part
  have hI : |(∫ x in (Real.exp (-t))..1, (x * f' x) * (Real.exp t * x * f' (Real.exp t * x)))
      - ∫ x in (Real.exp (-t))..1, (x * g' x) * (Real.exp t * x * g' (Real.exp t * x))| ≤ 2 * P11 := by
    rw [← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := Real.exp (-t)) (b := 1)
      (C := 2 * P11) (f := fun x => (x * f' x) * (Real.exp t * x * f' (Real.exp t * x))
        - (x * g' x) * (Real.exp t * x * g' (Real.exp t * x))) (fun x hx => ?_)
    · rw [Real.norm_eq_abs] at hb
      refine hb.trans ?_
      rw [abs_of_nonneg (by linarith)]
      nlinarith
    · rw [Set.uIoc_of_le hi1] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx1.le
      have hmx : x ∈ Icc (1 / 2 : ℝ) 2 := ⟨by linarith, by linarith⟩
      have hρx1 : 1 ≤ Real.exp t * x := by
        have : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
        nlinarith
      have hρx2 : Real.exp t * x ≤ 2 := by nlinarith
      have hmρx : Real.exp t * x ∈ Icc (1 / 2 : ℝ) 2 := ⟨by linarith, hρx2⟩
      have hp := abs_mul_sub_mul_le (h1 x hmx) (h1 _ hmρx) (hG1 x hmx) (hG1 _ hmρx)
      have e : (x * f' x) * (Real.exp t * x * f' (Real.exp t * x))
            - (x * g' x) * (Real.exp t * x * g' (Real.exp t * x))
          = (x * (Real.exp t * x)) * (f' x * f' (Real.exp t * x) - g' x * g' (Real.exp t * x)) := by
        ring
      rw [Real.norm_eq_abs, e, abs_mul, abs_of_pos (by positivity)]
      have hxx : x * (Real.exp t * x) ≤ 2 := by nlinarith
      exact mul_le_mul hxx hp (abs_nonneg _) (by norm_num)
  -- the boundary parts
  have hB1 := abs_mul_sub_mul_le (h1 _ hmi) (h0 1 hm1) (hG1 _ hmi) (hG0 1 hm1)
  have hB2 := abs_mul_sub_mul_le (h0 1 hm1) (h1 _ hmρ) (hG0 1 hm1) (hG1 _ hmρ)
  have hc1 := exp_half_le_two ht0 ht
  have hc2 := exp_neg_three_half_le_one ht0
  have hc3 := exp_three_half_le_four ht0 ht
  have e : CC f f' t - CC g g' t
      = Real.exp (t / 2) * ((∫ x in (Real.exp (-t))..1, (x * f' x) * (Real.exp t * x * f' (Real.exp t * x)))
          - ∫ x in (Real.exp (-t))..1, (x * g' x) * (Real.exp t * x * g' (Real.exp t * x)))
        + Real.exp (-(3 / 2) * t) * (f' (Real.exp (-t)) * f 1 - g' (Real.exp (-t)) * g 1)
        - Real.exp ((3 / 2) * t) * (f 1 * f' (Real.exp t) - g 1 * g' (Real.exp t)) := by
    unfold CC; ring
  rw [e]
  have p1 := Real.exp_pos (t / 2)
  have p2 := Real.exp_pos (-(3 / 2) * t)
  have p3 := Real.exp_pos ((3 / 2) * t)
  calc _ ≤ |Real.exp (t / 2) * ((∫ x in (Real.exp (-t))..1, (x * f' x) * (Real.exp t * x * f' (Real.exp t * x)))
          - ∫ x in (Real.exp (-t))..1, (x * g' x) * (Real.exp t * x * g' (Real.exp t * x)))|
        + |Real.exp (-(3 / 2) * t) * (f' (Real.exp (-t)) * f 1 - g' (Real.exp (-t)) * g 1)|
        + |Real.exp ((3 / 2) * t) * (f 1 * f' (Real.exp t) - g 1 * g' (Real.exp t))| := by
        refine (abs_sub _ _).trans ?_
        gcongr; exact abs_add_le _ _
    _ ≤ 2 * (2 * P11) + 1 * (e1 * (G0 + e0) + G1 * e0) + 4 * (e0 * (G1 + e1) + G0 * e1) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos p1, abs_of_pos p2, abs_of_pos p3]
        gcongr
    _ = _ := by ring

/-- Size of `CC g g'` from bounds on `[1/2, 2]`. -/
theorem abs_CC_le {g g' : ℝ → ℝ} {G0 G1 t : ℝ} (hg : Continuous g')
    (hG0 : ∀ x ∈ Icc (1 / 2 : ℝ) 2, |g x| ≤ G0) (hG1 : ∀ x ∈ Icc (1 / 2 : ℝ) 2, |g' x| ≤ G1)
    (ht0 : 0 ≤ t) (ht : t ≤ Real.log 2) :
    |CC g g' t| ≤ 4 * G1 ^ 2 + 5 * G0 * G1 := by
  have hz : CC (fun _ => 0) (fun _ => 0) t = 0 := by simp [CC]
  have e : CC g g' t = CC g g' t - CC (fun _ => 0) (fun _ => 0) t := by rw [hz, sub_zero]
  have h2 := abs_CC_sub_le (f := g) (f' := g') (g := fun _ => 0) (g' := fun _ => 0) (e0 := G0)
    (e1 := G1) (G0 := 0) (G1 := 0) hg continuous_const
    (fun x hx => by simpa using hG0 x hx) (fun x hx => by simpa using hG1 x hx)
    (fun x _ => by simp) (fun x _ => by simp) ht0 ht
  rw [← e] at h2
  refine h2.trans (le_of_eq ?_)
  ring

end ArchS10
