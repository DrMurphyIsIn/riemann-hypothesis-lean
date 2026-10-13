/-
  KWin_Minorant -- the proved piecewise-polynomial minorant w <= Psi of the Weil symbol on
  [0, 20] (rvm_bridge island, 2026-09-24).

  conjecture1_proved = False.  (Finite-window Weil positivity is not RH; PR #604: the 1.3e-3
  full-class margin is zero content; not Connes-Consani, whose theorem is pole-free.)

  STATEMENT (`wpoly_le_Psi`): for each of the 7 pieces [brk i, brk (i+1)] of [0, 20] and every t
  in it,  wpoly i t = sum_p wpCoef i p t^p <= Psi t = Re psi(1/4 + it/2) - log pi,  where the
  coefficients wpCoef are the exact rationals computed by KWin_Data (and evaluated by the kernel
  inside the head certificate).  No pointwise digamma value is ever enclosed numerically.

  ROUTE.
    1. The island's series floor `psiR_ge_series` with N = 400 terms (the Lorentzian form:
       psiR r >= -gamma + H_N - sum_{j<=N} Lz(j + 1/4, r) + serG(N) - serG(N + M)).
    2. Lorentzians j < 18: the GEOMETRIC Taylor bound `lor_taylor` about the piece centre c
       (1/(b - i r) = (1/z) sum_{k<=d} q^k + q^(d+1)/(z (1 - q)), z = b - i c, q = i (r-c)/z), with
       the coefficients `kap` floor-rounded at 10^-30 and the rounding paid by 10^-30 sum h^k.
    3. Lorentzians 18 <= j <= 400: the global alternating bound 1/(1+y) <= sum_{k<=10} (-y)^k,
       summed with termwise ceilings / floors (`gAlt`).
    4. serG(N) >= (1/4)/(N+5/4) + (1/2)(y - y^2) (two log floors), serG(N+M) <= the island's
       serG_bounds upper, gamma <= gammaUp (KWin_Constants), log pi <= 1.1447298859.
    5. The kernel-side coefficients are the shift-to-power expansion of steps 2-4
       (`wpoly_eq`: binomial theorem).
  No `sorry`.
-/
import KWin_Constants
import KWin_Cert

open Real Finset

noncomputable section

namespace KWin
open RvMBridge11 RvMBridge30

/-- The Lorentzian `x / (x^2 + (r/2)^2)` of the vertical-line digamma series. -/
def Lz (x r : ℝ) : ℝ := x / (x ^ 2 + (r / 2) ^ 2)

/-- The minorant polynomial on piece `i`. -/
def wpoly (i : ℕ) (t : ℝ) : ℝ := ∑ p ∈ range (Dmax + 1), (((wpList i).getD p 0 : ℚ) : ℝ) * t ^ p

/-! ## A. The series floor in Lorentzian form. -/

theorem psi_series_Lz (r : ℝ) (N M : ℕ) :
    -Real.eulerMascheroniConstant + (∑ n ∈ range N, (1 : ℝ) / ((n : ℝ) + 1))
      - (∑ j ∈ range (N + 1), Lz ((j : ℝ) + 1 / 4) r)
      + (serG (r / 2) N - serG (r / 2) ((N : ℝ) + M)) ≤ psiR r := by
  have h := psiR_ge_series r N M
  have e1 : (∑ j ∈ range (N + 1), Lz ((j : ℝ) + 1 / 4) r)
      = (∑ n ∈ range N, Lz ((n : ℝ) + 1 + 1 / 4) r) + Lz (1 / 4) r := by
    rw [Finset.sum_range_succ']
    push_cast
    simp only [zero_add]
  have e2 : ∑ n ∈ range N, serF (r / 2) n
      = ∑ n ∈ range N, (1 : ℝ) / ((n : ℝ) + 1) - ∑ n ∈ range N, Lz ((n : ℝ) + 1 + 1 / 4) r := by
    rw [← Finset.sum_sub_distrib]
    rfl
  have e3 : (1 / 4 : ℝ) / ((1 / 4) ^ 2 + (r / 2) ^ 2) = Lz (1 / 4) r := rfl
  rw [e2, e3] at h
  rw [e1]
  linarith

/-! ## B. The geometric Taylor bound for one Lorentzian. -/

/-- `2b/(b^2 + r^2) <= sum_{k<=d} 2 Re(I^k/(b - cI)^(k+1)) (r-c)^k + 2 rho^(d+1)/((1-rho) s)`,
`rho = h/s`, whenever `s <= |b - cI|`, `|r - c| <= h < s`. -/
theorem lor_taylor {b c r h s : ℝ} (hb : 0 < b) (hs : 0 < s) (hsz : s ^ 2 ≤ b ^ 2 + c ^ 2)
    (hh0 : 0 ≤ h) (hhs : h < s) (hu : |r - c| ≤ h) (d : ℕ) :
    2 * b / (b ^ 2 + r ^ 2)
      ≤ ∑ k ∈ range (d + 1), 2 * (Complex.I ^ k / ((b : ℂ) - (c : ℂ) * Complex.I) ^ (k + 1)).re
          * (r - c) ^ k
        + 2 * (h / s) ^ (d + 1) / ((1 - h / s) * s) := by
  set z : ℂ := (b : ℂ) - (c : ℂ) * Complex.I with hz
  set u : ℝ := r - c with hu_def
  have hz0 : z ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp [hz] at this
    linarith
  have hzsq : ‖z‖ ^ 2 = b ^ 2 + c ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [hz]; ring
  have hzs : s ≤ ‖z‖ := by
    rw [← pow_le_pow_iff_left₀ hs.le (norm_nonneg z) (by norm_num : (2 : ℕ) ≠ 0), hzsq]
    exact hsz
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hs hzs
  set q : ℂ := (u : ℂ) * Complex.I / z with hq
  have hqn : ‖q‖ = |u| / ‖z‖ := by
    rw [hq, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hρ0 : 0 ≤ h / s := div_nonneg hh0 hs.le
  have hρ1 : h / s < 1 := (div_lt_one hs).mpr hhs
  have hqle : ‖q‖ ≤ h / s := by
    rw [hqn]
    calc |u| / ‖z‖ ≤ h / ‖z‖ := div_le_div_of_nonneg_right hu hzpos.le
      _ ≤ h / s := div_le_div_of_nonneg_left hh0 hs hzs
  have hq1 : ‖q‖ < 1 := lt_of_le_of_lt hqle hρ1
  have h1q : (1 : ℂ) - q ≠ 0 := by
    intro h0
    have : q = 1 := by linear_combination -h0
    rw [this, norm_one] at hq1
    exact lt_irrefl _ hq1
  -- b - rI = z (1 - q)
  have hfac : (b : ℂ) - (r : ℂ) * Complex.I = z * (1 - q) := by
    rw [hq, mul_sub, mul_one, mul_div_cancel₀ _ hz0, hz, hu_def]
    push_cast
    ring
  -- the geometric identity
  have hgeo : (1 : ℂ) / (1 - q) = (∑ k ∈ range (d + 1), q ^ k) + q ^ (d + 1) / (1 - q) := by
    have := geom_sum_mul_neg q (d + 1)
    field_simp
    linear_combination -this
  have hinv : (1 : ℂ) / ((b : ℂ) - (r : ℂ) * Complex.I)
      = (∑ k ∈ range (d + 1), (Complex.I ^ k / z ^ (k + 1)) * (u : ℂ) ^ k)
        + q ^ (d + 1) / (z * (1 - q)) := by
    have e1 : (1 : ℂ) / (z * (1 - q)) = (1 / z) * (1 / (1 - q)) := by
      rw [one_div_mul_one_div]
    rw [hfac, e1, hgeo, mul_add, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [hq, div_pow, mul_pow]
      field_simp
      ring
    · field_simp
  -- real parts
  have hre : ((1 : ℂ) / ((b : ℂ) - (r : ℂ) * Complex.I)).re = b / (b ^ 2 + r ^ 2) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    simp
    ring
  have hsumre : (∑ k ∈ range (d + 1), (Complex.I ^ k / z ^ (k + 1)) * (u : ℂ) ^ k).re
      = ∑ k ∈ range (d + 1), (Complex.I ^ k / z ^ (k + 1)).re * u ^ k := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Complex.ofReal_pow, Complex.re_mul_ofReal]
  -- the tail
  have htail : (q ^ (d + 1) / (z * (1 - q))).re ≤ (h / s) ^ (d + 1) / ((1 - h / s) * s) := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_div, norm_mul, norm_pow]
    have h1q' : 1 - h / s ≤ ‖1 - q‖ := by
      have := norm_sub_norm_le (1 : ℂ) q
      rw [norm_one] at this
      linarith
    have hden : (1 - h / s) * s ≤ ‖z‖ * ‖1 - q‖ := by
      rw [mul_comm]
      exact mul_le_mul hzs h1q' (by linarith) (norm_nonneg _)
    have hdpos : 0 < (1 - h / s) * s := mul_pos (by linarith) hs
    calc ‖q‖ ^ (d + 1) / (‖z‖ * ‖1 - q‖) ≤ (h / s) ^ (d + 1) / (‖z‖ * ‖1 - q‖) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hqle _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ (h / s) ^ (d + 1) / ((1 - h / s) * s) :=
          div_le_div_of_nonneg_left (pow_nonneg hρ0 _) hdpos hden
  have hmain : b / (b ^ 2 + r ^ 2)
      = ∑ k ∈ range (d + 1), (Complex.I ^ k / z ^ (k + 1)).re * u ^ k
        + (q ^ (d + 1) / (z * (1 - q))).re := by
    rw [← hre, hinv, Complex.add_re, hsumre]
  have e2 : 2 * b / (b ^ 2 + r ^ 2) = 2 * (b / (b ^ 2 + r ^ 2)) := by ring
  rw [e2, hmain, mul_add, Finset.mul_sum]
  have e3 : ∀ k ∈ range (d + 1), 2 * ((Complex.I ^ k / z ^ (k + 1)).re * u ^ k)
      = 2 * (Complex.I ^ k / z ^ (k + 1)).re * u ^ k := fun k _ => by ring
  rw [Finset.sum_congr rfl e3]
  have e4 : 2 * (h / s) ^ (d + 1) / ((1 - h / s) * s) = 2 * ((h / s) ^ (d + 1) / ((1 - h / s) * s)) := by
    ring
  rw [e4]
  linarith

/-! ## C. One exact Lorentzian with rounded rational coefficients. -/

lemma smax_pos {b c : ℚ} (hb : 0 < b) : 0 < smax b c := by
  unfold smax
  exact lt_of_lt_of_le hb (le_trans (le_max_left b c) (le_max_left _ _))

lemma smax_sq_le {b c : ℚ} (hb : 0 ≤ b) (hc : 0 ≤ c) : smax b c ^ 2 ≤ b ^ 2 + c ^ 2 := by
  unfold smax
  rcases le_total (max b c) (7 / 10 * (b + c)) with h | h
  · rw [max_eq_right h]; nlinarith [sq_nonneg (b - c), mul_nonneg hb hc]
  · rw [max_eq_left h]
    rcases le_total b c with h2 | h2
    · rw [max_eq_right h2]; nlinarith
    · rw [max_eq_left h2]; nlinarith

theorem Lz_le_kapR {b c h : ℚ} (hb : 0 < b) (hc : 0 ≤ c) (hh0 : 0 ≤ h) (hhs : h < smax b c)
    {r : ℝ} (hu : |r - (c : ℝ)| ≤ (h : ℝ)) (d : ℕ) :
    Lz ((b : ℝ) / 2) r ≤ ∑ k ∈ range (d + 1), ((kapR b c k : ℚ) : ℝ) * (r - c) ^ k
      + ((remB b c h d : ℚ) : ℝ) + (((∑ k ∈ range (d + 1), h ^ k) / 10 ^ Rk : ℚ) : ℝ) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hL : Lz ((b : ℝ) / 2) r = 2 * (b : ℝ) / ((b : ℝ) ^ 2 + r ^ 2) := by
    unfold Lz
    field_simp
  have hs := smax_pos (c := c) hb
  have hsq := smax_sq_le hb.le hc
  have hT := lor_taylor (b := (b : ℝ)) (c := (c : ℝ)) (r := r) (h := (h : ℝ))
    (s := ((smax b c : ℚ) : ℝ)) hbR (by exact_mod_cast hs) (by exact_mod_cast hsq)
    (by exact_mod_cast hh0) (by exact_mod_cast hhs) hu d
  have hk : ∀ k, 2 * (Complex.I ^ k / (((b : ℝ) : ℂ) - (((c : ℝ)) : ℂ) * Complex.I) ^ (k + 1)).re
      = ((kap b c k : ℚ) : ℝ) := by
    intro k
    rw [kap_eq hb k]
    push_cast
    rfl
  simp only [hk] at hT
  have hrem : 2 * ((h : ℝ) / ((smax b c : ℚ) : ℝ)) ^ (d + 1)
      / ((1 - (h : ℝ) / ((smax b c : ℚ) : ℝ)) * ((smax b c : ℚ) : ℝ)) = ((remB b c h d : ℚ) : ℝ) := by
    unfold remB
    push_cast
    ring
  rw [hrem] at hT
  have hround : ∀ k ∈ range (d + 1), ((kap b c k : ℚ) : ℝ) * (r - c) ^ k
      ≤ ((kapR b c k : ℚ) : ℝ) * (r - c) ^ k + (h : ℝ) ^ k / 10 ^ Rk := by
    intro k _
    have h1 : ((kapR b c k : ℚ) : ℝ) ≤ ((kap b c k : ℚ) : ℝ) := by exact_mod_cast floorR_le _ _
    have h2 : ((kap b c k : ℚ) : ℝ) - ((kapR b c k : ℚ) : ℝ) ≤ 1 / 10 ^ Rk := by
      have := sub_floorR_le (kap b c k) Rk
      have h' : (((kap b c k - kapR b c k : ℚ)) : ℝ) ≤ ((1 / 10 ^ Rk : ℚ) : ℝ) := by exact_mod_cast this
      push_cast at h'
      exact h'
    have h3 : |(r - c) ^ k| ≤ (h : ℝ) ^ k := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hu k
    have h4 : (((kap b c k : ℚ) : ℝ) - ((kapR b c k : ℚ) : ℝ)) * (r - c) ^ k
        ≤ (((kap b c k : ℚ) : ℝ) - ((kapR b c k : ℚ) : ℝ)) * |(r - c) ^ k| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
    have h5 : (((kap b c k : ℚ) : ℝ) - ((kapR b c k : ℚ) : ℝ)) * |(r - c) ^ k|
        ≤ (1 / 10 ^ Rk) * (h : ℝ) ^ k :=
      mul_le_mul h2 h3 (abs_nonneg _) (by positivity)
    have e : (1 / 10 ^ Rk : ℝ) * (h : ℝ) ^ k = (h : ℝ) ^ k / 10 ^ Rk := by ring
    linarith
  have hsum := Finset.sum_le_sum hround
  rw [Finset.sum_add_distrib] at hsum
  have e5 : (((∑ k ∈ range (d + 1), h ^ k) / 10 ^ Rk : ℚ) : ℝ)
      = ∑ k ∈ range (d + 1), (h : ℝ) ^ k / 10 ^ Rk := by
    push_cast
    rw [Finset.sum_div]
  rw [hL, e5]
  linarith

/-! ## D. The alternating tail. -/

lemma inv_one_add_le_alt {y : ℝ} (hy : 0 ≤ y) (K : ℕ) :
    1 / (1 + y) ≤ ∑ k ∈ range (2 * K + 1), (-y) ^ k := by
  have h := geom_sum_mul_neg (-y) (2 * K + 1)
  have hodd : (-y) ^ (2 * K + 1) = -(y ^ (2 * K + 1)) := by
    rw [pow_succ, pow_mul, neg_sq, ← pow_mul]; ring
  rw [sub_neg_eq_add, hodd, sub_neg_eq_add] at h
  rw [div_le_iff₀ (by linarith)]
  nlinarith [pow_nonneg hy (2 * K + 1)]

lemma Lz_le_alt (j : ℕ) (r : ℝ) (K : ℕ) :
    Lz ((j : ℝ) + 1 / 4) r
      ≤ ∑ k ∈ range (2 * K + 1), r ^ (2 * k) * ((-1) ^ k * (4 ^ (k + 1) / (4 * (j : ℝ) + 1) ^ (2 * k + 1))) := by
  have e4 : (4 * (j : ℝ) + 1) = 4 * ((j : ℝ) + 1 / 4) := by ring
  rw [e4]
  have hx : (0 : ℝ) < (j : ℝ) + 1 / 4 := by positivity
  generalize hX : (j : ℝ) + 1 / 4 = X at hx ⊢
  have hy : 0 ≤ (r ^ 2 / 4) / X ^ 2 := by positivity
  have hLz : Lz X r = (1 / X) * (1 / (1 + (r ^ 2 / 4) / X ^ 2)) := by
    unfold Lz
    field_simp
    ring
  rw [hLz]
  have h1 := inv_one_add_le_alt hy K
  refine (mul_le_mul_of_nonneg_left h1 (by positivity)).trans (le_of_eq ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [neg_pow, div_pow, div_pow, ← pow_mul, ← pow_mul, mul_pow]
  field_simp
  ring

lemma nat_div_ceil_ge (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b ≤ (((a + b - 1) / b : ℕ) : ℝ) := by
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) hb
  have h3 : a ≤ b * ((a + b - 1) / b) := by omega
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hbR]
  have : (a : ℝ) ≤ (b : ℝ) * (((a + b - 1) / b : ℕ) : ℝ) := by exact_mod_cast h3
  linarith

lemma gAlt_ge (k : ℕ) :
    (-1) ^ k * ∑ j ∈ Ico nS (Nser + 1), (4 : ℝ) ^ (k + 1) / (4 * (j : ℝ) + 1) ^ (2 * k + 1)
      ≤ ((gAlt k : ℚ) : ℝ) := by
  have hR : (0 : ℝ) < 10 ^ (30 + 3 * k) := by positivity
  have hterm : ∀ j : ℕ, (4 : ℝ) ^ (k + 1) / (4 * (j : ℝ) + 1) ^ (2 * k + 1)
      = ((4 ^ (k + 1) * 10 ^ (30 + 3 * k) : ℕ) : ℝ) / (((4 * j + 1) ^ (2 * k + 1) : ℕ) : ℝ)
        / 10 ^ (30 + 3 * k) := by
    intro j
    push_cast
    field_simp
  unfold gAlt
  split_ifs with hk
  · have hev : (-1 : ℝ) ^ k = 1 := by
      rw [← Nat.div_add_mod k 2, hk, add_zero, pow_mul]; norm_num
    rw [hev, one_mul]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [hterm j]
    apply div_le_div_of_nonneg_right _ hR.le
    have hpos : 0 < (4 * j + 1) ^ (2 * k + 1) := by positivity
    have := nat_div_ceil_ge (4 ^ (k + 1) * 10 ^ (30 + 3 * k)) ((4 * j + 1) ^ (2 * k + 1)) hpos
    push_cast at this ⊢
    exact this
  · have hodd : (-1 : ℝ) ^ k = -1 := by
      have hk1 : k % 2 = 1 := by omega
      rw [← Nat.div_add_mod k 2, hk1, pow_add, pow_mul]; norm_num
    rw [hodd, neg_one_mul]
    push_cast
    rw [neg_div, neg_le_neg_iff, Finset.sum_div]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [hterm j]
    apply div_le_div_of_nonneg_right _ hR.le
    exact Nat.cast_div_le

theorem sum_Lz_large_le (r : ℝ) :
    ∑ j ∈ Ico nS (Nser + 1), Lz ((j : ℝ) + 1 / 4) r
      ≤ ∑ k ∈ range (2 * Kalt + 1), r ^ (2 * k) * ((gAlt k : ℚ) : ℝ) := by
  calc ∑ j ∈ Ico nS (Nser + 1), Lz ((j : ℝ) + 1 / 4) r
      ≤ ∑ j ∈ Ico nS (Nser + 1), ∑ k ∈ range (2 * Kalt + 1),
          r ^ (2 * k) * ((-1) ^ k * (4 ^ (k + 1) / (4 * (j : ℝ) + 1) ^ (2 * k + 1))) :=
        Finset.sum_le_sum fun j _ => Lz_le_alt j r Kalt
    _ = ∑ k ∈ range (2 * Kalt + 1), r ^ (2 * k)
          * ((-1) ^ k * ∑ j ∈ Ico nS (Nser + 1), (4 : ℝ) ^ (k + 1) / (4 * (j : ℝ) + 1) ^ (2 * k + 1)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ ∑ k ∈ range (2 * Kalt + 1), r ^ (2 * k) * ((gAlt k : ℚ) : ℝ) := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact mul_le_mul_of_nonneg_left (gAlt_ge k) (by rw [pow_mul]; exact pow_nonneg (sq_nonneg r) k)

/-! ## E. The integral tail of the series. -/

lemma serG_N_ge (N : ℕ) (r : ℝ) :
    (1 / 4) / ((N : ℝ) + 5 / 4) + r ^ 2 / (8 * ((N : ℝ) + 5 / 4) ^ 2)
      - r ^ 4 / (32 * ((N : ℝ) + 5 / 4) ^ 4) ≤ serG (r / 2) N := by
  have hX : (0 : ℝ) < (N : ℝ) + 1 + 1 / 4 := by positivity
  have hx1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set w : ℝ := (r / 2) ^ 2 / ((N : ℝ) + 1 + 1 / 4) ^ 2 with hw_def
  have hw : 0 ≤ w := by positivity
  have e : serG (r / 2) N
      = Real.log (((N : ℝ) + 1 + 1 / 4) / ((N : ℝ) + 1)) + (1 / 2) * Real.log (1 + w) := by
    unfold serG
    rw [Real.log_div hX.ne' hx1.ne']
    have h2 : ((N : ℝ) + 1 + 1 / 4) ^ 2 + (r / 2) ^ 2 = ((N : ℝ) + 1 + 1 / 4) ^ 2 * (1 + w) := by
      rw [hw_def]; field_simp
    rw [h2, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  have h1 : 1 - ((N : ℝ) + 1) / ((N : ℝ) + 1 + 1 / 4)
      ≤ Real.log (((N : ℝ) + 1 + 1 / 4) / ((N : ℝ) + 1)) := by
    have := Real.one_sub_inv_le_log_of_pos (x := ((N : ℝ) + 1 + 1 / 4) / ((N : ℝ) + 1)) (by positivity)
    rwa [inv_div] at this
  have h2 : w - w ^ 2 ≤ Real.log (1 + w) := by
    have := Real.one_sub_inv_le_log_of_pos (x := 1 + w) (by positivity)
    have h3 : w - w ^ 2 ≤ 1 - (1 + w)⁻¹ := by
      rw [← sub_nonneg]
      have e2 : 1 - (1 + w)⁻¹ - (w - w ^ 2) = w ^ 3 / (1 + w) := by
        field_simp
        ring
      rw [e2]
      positivity
    linarith
  have e3 : 1 - ((N : ℝ) + 1) / ((N : ℝ) + 1 + 1 / 4) = (1 / 4) / ((N : ℝ) + 5 / 4) := by
    field_simp
    ring
  have e4 : w = r ^ 2 / (4 * ((N : ℝ) + 5 / 4) ^ 2) := by
    rw [hw_def]; field_simp; ring
  rw [e]
  rw [e3] at h1
  have e5 : (1 / 2) * (w - w ^ 2)
      = r ^ 2 / (8 * ((N : ℝ) + 5 / 4) ^ 2) - r ^ 4 / (32 * ((N : ℝ) + 5 / 4) ^ 4) := by
    rw [e4]
    field_simp
    ring
  linarith [h1, h2, e5]

lemma serG_NM_le (N M : ℕ) (r : ℝ) :
    serG (r / 2) ((N : ℝ) + M)
      ≤ (1 / 2) * ((((N : ℝ) + M + 5 / 4) ^ 2 - ((N : ℝ) + M + 1) ^ 2) / ((N : ℝ) + M + 1) ^ 2)
        + r ^ 2 / (8 * ((N : ℝ) + M + 1) ^ 2) := by
  have h := (serG_bounds (r / 2) (x := (N : ℝ) + M) (by positivity)).2
  have hx1 : (0 : ℝ) < (N : ℝ) + M + 1 := by positivity
  refine h.trans (le_of_eq ?_)
  field_simp
  ring

/-! ## F. Assembly. -/

/-- The global part of the lower bound (constants, integral tail, large Lorentzians). -/
def globPoly (r : ℝ) : ℝ :=
  ((C0 : ℚ) : ℝ) + ((C1 : ℚ) : ℝ) * r ^ 2 + ((C2 : ℚ) : ℝ) * r ^ 4
    - ∑ k ∈ range (2 * Kalt + 1), r ^ (2 * k) * ((gAlt k : ℚ) : ℝ)

lemma HNr_le_Q : HNr ≤ ∑ n ∈ range Nser, (1 : ℚ) / ((n : ℚ) + 1) := by
  unfold HNr
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun n _ => ?_
  have h1 : (((10 ^ 30 / (n + 1) : ℕ) : ℚ)) ≤ ((10 ^ 30 : ℕ) : ℚ) / ((n + 1 : ℕ) : ℚ) := Nat.cast_div_le
  have hA : (0 : ℚ) < 10 ^ 30 := by positivity
  rw [div_le_iff₀ hA]
  calc (((10 ^ 30 / (n + 1) : ℕ) : ℚ)) ≤ ((10 ^ 30 : ℕ) : ℚ) / ((n + 1 : ℕ) : ℚ) := h1
    _ = 1 / ((n : ℚ) + 1) * 10 ^ 30 := by push_cast; ring

lemma HNr_le : ((HNr : ℚ) : ℝ) ≤ ∑ n ∈ range Nser, (1 : ℝ) / ((n : ℝ) + 1) := by
  have := (Rat.cast_le (K := ℝ)).mpr HNr_le_Q
  push_cast at this
  exact this

/-- **The global series floor**: `Psi r >= globPoly r - sum_{j<18} Lz(j + 1/4, r)` for all `r`. -/
theorem Psi_ge_glob (r : ℝ) :
    globPoly r - ∑ j ∈ range nS, Lz ((j : ℝ) + 1 / 4) r ≤ Psi r := by
  have hs := psi_series_Lz r Nser Mser
  have hsplit : ∑ j ∈ range (Nser + 1), Lz ((j : ℝ) + 1 / 4) r
      = ∑ j ∈ range nS, Lz ((j : ℝ) + 1 / 4) r + ∑ j ∈ Ico nS (Nser + 1), Lz ((j : ℝ) + 1 / 4) r := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      Finset.sum_Ico_consecutive _ (Nat.zero_le nS) (by unfold nS Nser; norm_num)]
  have hlarge := sum_Lz_large_le r
  have hG1 := serG_N_ge Nser r
  have hG2 := serG_NM_le Nser Mser r
  have hH := HNr_le
  have hg := gamma_le
  have hp := log_pi_le
  unfold Psi globPoly
  have hC0 : ((C0 : ℚ) : ℝ) = -((gammaUpQ : ℚ) : ℝ) - ((logPiUpQ : ℚ) : ℝ) + ((HNr : ℚ) : ℝ)
      + (1 / 4) / ((Nser : ℝ) + 5 / 4)
      - (1 / 2) * ((((Nser : ℝ) + Mser + 5 / 4) ^ 2 - ((Nser : ℝ) + Mser + 1) ^ 2)
        / ((Nser : ℝ) + Mser + 1) ^ 2) := by
    unfold C0 NQ MQ
    push_cast
    ring
  have hC1 : ((C1 : ℚ) : ℝ) = 1 / (8 * ((Nser : ℝ) + 5 / 4) ^ 2) - 1 / (8 * ((Nser : ℝ) + Mser + 1) ^ 2) := by
    unfold C1 NQ MQ
    push_cast
    ring
  have hC2 : ((C2 : ℚ) : ℝ) = -1 / (32 * ((Nser : ℝ) + 5 / 4) ^ 4) := by
    unfold C2 NQ
    push_cast
    ring
  rw [hC0, hC1, hC2]
  rw [hsplit] at hs
  have e1 : r ^ 2 / (8 * ((Nser : ℝ) + 5 / 4) ^ 2) = 1 / (8 * ((Nser : ℝ) + 5 / 4) ^ 2) * r ^ 2 := by ring
  have e2 : r ^ 4 / (32 * ((Nser : ℝ) + 5 / 4) ^ 4) = -(-1 / (32 * ((Nser : ℝ) + 5 / 4) ^ 4) * r ^ 4) := by
    ring
  have e3 : r ^ 2 / (8 * ((Nser : ℝ) + Mser + 1) ^ 2) = 1 / (8 * ((Nser : ℝ) + Mser + 1) ^ 2) * r ^ 2 := by
    ring
  rw [e1, e2] at hG1
  rw [e3] at hG2
  linarith

/-- The global polynomial dominates its rounded kernel coefficients. -/
theorem globC_poly_le (r : ℝ) :
    ∑ p ∈ range (Dmax + 1), ((globC p : ℚ) : ℝ) * r ^ p ≤ globPoly r := by
  have hle : ∀ p ∈ range (Dmax + 1), ((globC p : ℚ) : ℝ) * r ^ p ≤ ((globRaw p : ℚ) : ℝ) * r ^ p := by
    intro p _
    rcases Nat.even_or_odd p with ⟨m, hm⟩ | hodd
    · have hr : 0 ≤ r ^ p := by rw [hm, ← two_mul, pow_mul]; positivity
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast floorR_le _ _) hr
    · have h0 : globRaw p = 0 := by
        unfold globRaw
        have h1 : p % 2 = 1 := Nat.odd_iff.mp hodd
        have hp0 : p ≠ 0 := by omega
        have hp2 : p ≠ 2 := by omega
        have hp4 : p ≠ 4 := by omega
        simp [hp0, hp2, hp4, h1]
      have hc : globC p = 0 := by
        unfold globC; rw [h0]; simp [floorR]
      rw [hc, h0]
  refine (Finset.sum_le_sum hle).trans (le_of_eq ?_)
  unfold globPoly globRaw
  simp only [Dmax, Kalt, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  push_cast
  ring

/-! ## G. The shift-to-power identity. -/

lemma sum_ite_le_range {β : Type*} [AddCommMonoid β] (f : ℕ → β) {d D : ℕ} (h : d ≤ D) :
    ∑ k ∈ range (D + 1), (if k ≤ d then f k else 0) = ∑ k ∈ range (d + 1), f k := by
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem wpoly_eq {i : ℕ} (r : ℝ) :
    wpoly i r = ∑ p ∈ range (Dmax + 1), ((globC p : ℚ) : ℝ) * r ^ p
      - ∑ k ∈ range (Dmax + 1), ((uCoef i k : ℚ) : ℝ) * (r - pcen i) ^ k - ((rhoR i : ℚ) : ℝ) := by
  unfold wpoly
  have hw : ∀ p ∈ range (Dmax + 1), (((wpList i).getD p 0 : ℚ) : ℝ) * r ^ p
      = ((globC p : ℚ) : ℝ) * r ^ p
        - ∑ k ∈ range (Dmax + 1), (if p ≤ k then ((uCoef i k : ℚ) : ℝ) * (k.choose p : ℝ)
            * (-(pcen i : ℝ)) ^ (k - p) * r ^ p else 0)
        - (if p = 0 then ((rhoR i : ℚ) : ℝ) else 0) := by
    intro p hp
    have hp' := Finset.mem_range.mp hp
    unfold wpList
    rw [getD_map_range _ _ hp']
    unfold wpCoef
    rw [globList, getD_map_range _ _ hp']
    push_cast
    rw [sub_mul, sub_mul, Finset.sum_mul]
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      split_ifs
      · rw [uList, getD_map_range _ _ (Finset.mem_range.mp hk)]
        push_cast
        ring
      · simp
    · split_ifs with h0 <;> simp [h0]
  rw [Finset.sum_congr rfl hw, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  congr 1
  · congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ Dmax := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have e : ∑ p ∈ range (Dmax + 1), (if p ≤ k then ((uCoef i k : ℚ) : ℝ) * (k.choose p : ℝ)
          * (-(pcen i : ℝ)) ^ (k - p) * r ^ p else 0)
        = ∑ p ∈ range (k + 1), ((uCoef i k : ℚ) : ℝ) * (k.choose p : ℝ) * (-(pcen i : ℝ)) ^ (k - p)
          * r ^ p := sum_ite_le_range _ hk'
    rw [e, sub_eq_add_neg r, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  · rw [Finset.sum_ite_eq' (range (Dmax + 1)) 0 (fun _ => ((rhoR i : ℚ) : ℝ))]
    simp [Dmax]

/-! ## H. The minorant on each piece. -/

lemma brk_nonneg (i : ℕ) : 0 ≤ brk i := by
  unfold brk
  split <;> norm_num

lemma brk_le_succ {i : ℕ} (hi : i < nPc) : brk i ≤ brk (i + 1) := by
  unfold nPc at hi
  interval_cases i <;> norm_num [brk]

theorem sum_Lz_small_le {i : ℕ} (hi : i < nPc) {r : ℝ} (hu : |r - (pcen i : ℝ)| ≤ (phw i : ℝ)) :
    ∑ j ∈ range nS, Lz ((j : ℝ) + 1 / 4) r
      ≤ ∑ k ∈ range (Dmax + 1), ((uCoef i k : ℚ) : ℝ) * (r - pcen i) ^ k + ((rhoR i : ℚ) : ℝ) := by
  have hc : 0 ≤ pcen i := by
    unfold pcen; have := brk_nonneg i; have := brk_nonneg (i + 1); linarith
  have hh : 0 ≤ phw i := by unfold phw; have := brk_le_succ hi; linarith
  have hj : ∀ j ∈ range nS, Lz ((j : ℝ) + 1 / 4) r
      ≤ ∑ k ∈ range (Dmax + 1), (if k ≤ deg i j then ((kapR (bS j) (pcen i) k : ℚ) : ℝ) else 0)
            * (r - pcen i) ^ k
        + (((remB (bS j) (pcen i) (phw i) (deg i j)
          + (∑ k ∈ range (deg i j + 1), phw i ^ k) / 10 ^ Rk : ℚ)) : ℝ) := by
    intro j hjm
    have hjS := Finset.mem_range.mp hjm
    obtain ⟨hlt, hdeg⟩ := pieceCheck_sound piece_ok hi hjS
    have hb : (0 : ℚ) < bS j := by unfold bS; positivity
    have hL := Lz_le_kapR hb hc hh hlt hu (deg i j)
    have hx : ((bS j : ℚ) : ℝ) / 2 = (j : ℝ) + 1 / 4 := by unfold bS; push_cast; ring
    rw [hx] at hL
    have e : ∑ k ∈ range (Dmax + 1), (if k ≤ deg i j then ((kapR (bS j) (pcen i) k : ℚ) : ℝ) else 0)
          * (r - pcen i) ^ k
        = ∑ k ∈ range (deg i j + 1), ((kapR (bS j) (pcen i) k : ℚ) : ℝ) * (r - pcen i) ^ k := by
      rw [← sum_ite_le_range _ hdeg]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs <;> simp
    rw [e]
    push_cast at hL ⊢
    linarith
  refine (Finset.sum_le_sum hj).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  have hu1 : ∀ k ∈ range (Dmax + 1), ∑ j ∈ range nS, (if k ≤ deg i j then
      ((kapR (bS j) (pcen i) k : ℚ) : ℝ) else 0) * (r - pcen i) ^ k
      = ((uCoef i k : ℚ) : ℝ) * (r - pcen i) ^ k := by
    intro k _
    unfold uCoef
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hu1]
  have hrho : ∑ j ∈ range nS, (((remB (bS j) (pcen i) (phw i) (deg i j)
        + (∑ k ∈ range (deg i j + 1), phw i ^ k) / 10 ^ Rk : ℚ)) : ℝ) ≤ ((rhoR i : ℚ) : ℝ) := by
    have h1 := le_ceilR (rhoRaw i) Rk
    have h2 : ((rhoRaw i : ℚ) : ℝ) ≤ ((rhoR i : ℚ) : ℝ) := by exact_mod_cast h1
    refine le_trans (le_of_eq ?_) h2
    unfold rhoRaw
    push_cast
    rfl
  linarith

/-- **The minorant**: on piece `i`, `wpoly i t <= Psi t`. -/
theorem wpoly_le_Psi {i : ℕ} (hi : i < nPc) {t : ℝ} (ha : ((brk i : ℚ) : ℝ) ≤ t)
    (hb : t ≤ ((brk (i + 1) : ℚ) : ℝ)) : wpoly i t ≤ Psi t := by
  have hu : |t - (pcen i : ℝ)| ≤ (phw i : ℝ) := by
    unfold pcen phw
    push_cast
    rw [abs_le]
    constructor <;> linarith
  rw [wpoly_eq]
  have h1 := globC_poly_le t
  have h2 := sum_Lz_small_le hi hu
  have h3 := Psi_ge_glob t
  linarith

end KWin

end
