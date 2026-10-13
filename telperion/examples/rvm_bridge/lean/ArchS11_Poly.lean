/-
  ArchS11_Poly -- polynomials on [0, 1] given by rational coefficient lists, and the exact identities
  behind the S11 certificate (stage S11 of the archimedean programme, rvm_bridge island, 2026-10-11).

  PROVED HERE (no `sorry`):
    * `integral_pv_mul_pv`   ∫_0^1 pv p · pv q = mom p q;
    * `integral_abs_pow_mul_pow` (the central formula) for s ∈ [0, 1]:
          ∫_0^1 |s - t|^i t^m dt = Σ_d Fc i m d · s^d     (binomial expansion on [0, s] and [s, 1]);
    * `pv_hatT`              pv (hatT E P) s = ∫_0^1 pv E (|s - t|) · pv P t dt;
    * `integral_integral_abs_pow`, `KKh_eq`
          ∫_0^1 ∫_0^1 |s - t|^n = 2/((n+1)(n+2)),   ∫∫ (pv E |s - t| + c0)^2 = KKh E c0;
    * `pv_lc`                pv of a checked linear combination.
  The data-dependent hypothesis is only `binOK = true` (Pascal's triangle, ArchS11_CertPsi).
  conjecture1_proved = False.
-/
import ArchS11_Data

open Finset MeasureTheory intervalIntegral Set

noncomputable section

namespace ArchS11

open ArchS11.Data

/-! ## A. Coefficient lists. -/

/-- Evaluation of a coefficient list. -/
def pv (p : List ℚ) (x : ℝ) : ℝ := ∑ k ∈ range p.length, (p.getD k 0 : ℝ) * x ^ k

theorem pv_eq_range {p : List ℚ} {D : ℕ} (h : p.length ≤ D) (x : ℝ) :
    pv p x = ∑ k ∈ range D, (p.getD k 0 : ℝ) * x ^ k := by
  unfold pv
  refine Finset.sum_subset (fun k hk => by simp at hk ⊢; omega) ?_
  intro k _ hk
  rw [Finset.mem_range, not_lt] at hk
  rw [List.getD_eq_default _ _ hk]
  simp

theorem continuous_pv (p : List ℚ) : Continuous (pv p) := by
  unfold pv
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_pow k)

theorem getD_map_range {α : Type*} (f : ℕ → α) {n i : ℕ} (d : α) (h : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

theorem lc_length (cs : List ℚ) (ps : List (List ℚ)) (D : ℕ) : (lc cs ps D).length = D := by
  simp [lc]

theorem pv_lc {cs : List ℚ} {ps : List (List ℚ)} {D : ℕ}
    (hlen : ∀ s < cs.length, (ps.getD s []).length ≤ D) (x : ℝ) :
    pv (lc cs ps D) x = ∑ s ∈ range cs.length, (cs.getD s 0 : ℝ) * pv (ps.getD s []) x := by
  rw [pv, lc_length]
  rw [Finset.sum_congr rfl fun k hk => by
    rw [show (lc cs ps D).getD k 0 = _ from getD_map_range _ 0 (Finset.mem_range.1 hk)]]
  push_cast
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [pv_eq_range (hlen s (Finset.mem_range.1 hs)), Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem pv_unitL (m : ℕ) (x : ℝ) : pv (unitL m) x = x ^ m := by
  rw [pv_eq_range (D := m + 1) (by simp [unitL]) x, Finset.sum_range_succ,
    Finset.sum_eq_zero fun k hk => ?_]
  · simp [unitL]
  · have hk' : k < m := Finset.mem_range.1 hk
    rw [unitL, List.getD_append _ _ _ _ (by simpa using hk'), List.getD_eq_getElem?_getD]
    simp [hk']

theorem pv_one (x : ℝ) : pv [1] x = 1 := by simp [pv]

/-! ## B. Moments. -/

theorem intervalIntegrable_pow_mul (c : ℝ) (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => c * x ^ n) volume a b :=
  (continuous_const.mul (continuous_pow n)).intervalIntegrable _ _

/-- `∫_0^1 pv p · pv q = mom p q`. -/
theorem integral_pv_mul_pv (p q : List ℚ) :
    ∫ x in (0 : ℝ)..1, pv p x * pv q x = (mom p q : ℝ) := by
  have h : ∀ x : ℝ, pv p x * pv q x = ∑ i ∈ range p.length, ∑ j ∈ range q.length,
      ((p.getD i 0 : ℝ) * (q.getD j 0 : ℝ)) * x ^ (i + j) := by
    intro x
    unfold pv
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [h]
  rw [intervalIntegral.integral_finsetSum (f := fun i x => ∑ j ∈ range q.length,
      ((p.getD i 0 : ℝ) * (q.getD j 0 : ℝ)) * x ^ (i + j)) fun i _ =>
    (continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_pow _)).intervalIntegrable _ _]
  unfold mom
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum (f := fun j x => ((p.getD i 0 : ℝ) * (q.getD j 0 : ℝ)) *
      x ^ (i + j)) fun j _ => intervalIntegrable_pow_mul _ _ _ _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  field_simp
  ring

/-! ## C. Pascal's triangle and signs. -/

theorem binOK_sound (hb : binOK = true) : ∀ n ≤ 46, ∀ k, binN n k = n.choose k := by
  simp only [binOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hb
  obtain ⟨hrow, hrec⟩ := hb
  have hzero : ∀ n ≤ 46, ∀ k, n < k → binN n k = 0 := by
    intro n hn k hk
    unfold binN
    exact List.getD_eq_default _ _ (by rw [(hrow n (by omega)).1]; omega)
  intro n
  induction n with
  | zero =>
    intro _ k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using (hrow 0 (by omega)).2
    · rw [hzero 0 (by omega) k hk, Nat.choose_eq_zero_of_lt hk]
  | succ n ih =>
    intro hn k
    rcases k with _ | k
    · simpa using (hrow (n + 1) (by omega)).2
    · by_cases hk : k ≤ n
      · rw [hrec n (by omega) k (by omega), ih (by omega), ih (by omega), Nat.choose_succ_succ']
      · rw [hzero (n + 1) hn (k + 1) (by omega), Nat.choose_eq_zero_of_lt (by omega)]

theorem binom_eq (hb : binOK = true) {n : ℕ} (hn : n ≤ 46) (k : ℕ) :
    (binom n k : ℝ) = (n.choose k : ℝ) := by
  unfold binom
  rw [binOK_sound hb n hn k]
  push_cast
  rfl

theorem sg_eq (k : ℕ) : (sg k : ℝ) = (-1) ^ k := by
  unfold sg
  rcases Nat.even_or_odd k with h | h
  · rw [if_pos (Nat.even_iff.1 h), h.neg_one_pow]
    simp
  · rw [if_neg (by rw [Nat.odd_iff] at h; omega), h.neg_one_pow]
    simp

/-! ## D. The central formula. -/

/-- `(s - t)^i` expanded in powers of `t`. -/
theorem sub_pow_expand (s t : ℝ) (i : ℕ) :
    (s - t) ^ i = ∑ k ∈ range (i + 1), (i.choose k : ℝ) * (-1) ^ k * s ^ (i - k) * t ^ k := by
  rw [show s - t = -t + s by ring, add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [neg_pow]
  ring

/-- `(t - s)^i` expanded in powers of `t`. -/
theorem sub_pow_expand' (s t : ℝ) (i : ℕ) :
    (t - s) ^ i = ∑ k ∈ range (i + 1), (i.choose k : ℝ) * (-1) ^ (i - k) * s ^ (i - k) * t ^ k := by
  rw [show t - s = t + -s by ring, add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [neg_pow]
  ring

theorem integral_poly_piece (c : ℕ → ℝ) (n : ℕ) (m : ℕ) (a b : ℝ) :
    ∫ t in a..b, (∑ k ∈ range n, c k * t ^ k) * t ^ m
      = ∑ k ∈ range n, c k * ((b ^ (k + m + 1) - a ^ (k + m + 1)) / (k + m + 1)) := by
  have h : ∀ t : ℝ, (∑ k ∈ range n, c k * t ^ k) * t ^ m = ∑ k ∈ range n, c k * t ^ (k + m) := by
    intro t
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [h]
  rw [intervalIntegral.integral_finsetSum (f := fun k t => c k * t ^ (k + m))
    fun k _ => intervalIntegrable_pow_mul _ _ _ _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  ring_nf

/-- **The central formula.**  For `s ∈ [0, 1]`, `∫_0^1 |s - t|^i t^m dt = Σ_d Fc i m d · s^d`. -/
theorem integral_abs_pow_mul_pow (hb : binOK = true) {i m : ℕ} (hi : i ≤ 46) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {D : ℕ} (hD : i + m + 2 ≤ D) :
    ∫ t in (0 : ℝ)..1, |s - t| ^ i * t ^ m = ∑ d ∈ range D, (Fc i m d : ℝ) * s ^ d := by
  have hcont : Continuous fun t : ℝ => |s - t| ^ i * t ^ m := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := s) (hcont.intervalIntegrable _ _)
    (hcont.intervalIntegrable _ _)]
  have h1 : ∫ t in (0 : ℝ)..s, |s - t| ^ i * t ^ m
      = ∫ t in (0 : ℝ)..s, (∑ k ∈ range (i + 1), (i.choose k : ℝ) * (-1) ^ k * s ^ (i - k) * t ^ k)
          * t ^ m := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hs0] at ht
    rw [abs_of_nonneg (by linarith [ht.2]), sub_pow_expand]
  have h2 : ∫ t in s..(1 : ℝ), |s - t| ^ i * t ^ m
      = ∫ t in s..(1 : ℝ), (∑ k ∈ range (i + 1),
          (i.choose k : ℝ) * (-1) ^ (i - k) * s ^ (i - k) * t ^ k) * t ^ m := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hs1] at ht
    rw [abs_sub_comm, abs_of_nonneg (by linarith [ht.1]), sub_pow_expand']
  rw [h1, h2, integral_poly_piece, integral_poly_piece, ← Finset.sum_add_distrib]
  -- the right-hand side
  have hA : ∑ d ∈ range D, (if d = i + m + 1 then (Acoef i m : ℝ) else 0) * s ^ d
      = (Acoef i m : ℝ) * s ^ (i + m + 1) := by
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq' (range D) (i + m + 1), if_pos (Finset.mem_range.2 (by omega))]
  have hB : ∑ d ∈ range D, (if d ≤ i then (Bcoef i m (i - d) : ℝ) else 0) * s ^ d
      = ∑ k ∈ range (i + 1), (Bcoef i m k : ℝ) * s ^ (i - k) := by
    simp_rw [ite_mul, zero_mul]
    rw [← Finset.sum_filter, show (range D).filter (· ≤ i) = range (i + 1) by
      ext d; simp only [Finset.mem_filter, Finset.mem_range]; omega]
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    rw [show i + 1 - 1 - k = i - k by omega, show i - (i - k) = k by omega]
  have hRHS : ∑ d ∈ range D, (Fc i m d : ℝ) * s ^ d
      = (Acoef i m : ℝ) * s ^ (i + m + 1) + ∑ k ∈ range (i + 1), (Bcoef i m k : ℝ) * s ^ (i - k) := by
    rw [← hA, ← hB, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    unfold Fc
    push_cast
    split_ifs <;> push_cast <;> ring
  rw [hRHS]
  unfold Acoef Bcoef
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  rw [binom_eq hb hi, sg_eq, sg_eq]
  have e1 : s ^ (i - k) * s ^ (k + m + 1) = s ^ (i + m + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [← e1, show ((m : ℝ) + k + 1) = (k : ℝ) + m + 1 by ring, one_pow,
    zero_pow (by omega : k + m + 1 ≠ 0)]
  ring

/-! ## E. The operator on coefficient lists. -/

theorem hatT_length (E P : List ℚ) : (hatT E P).length = E.length + P.length := by simp [hatT]

theorem hatT_getD (E P : List ℚ) {d : ℕ} (hd : d < E.length + P.length) :
    (hatT E P).getD d 0 = ∑ i ∈ range E.length, ∑ m ∈ range P.length,
      E.getD i 0 * P.getD m 0 * Fc i m d := by
  rw [hatT, getD_map_range _ 0 (by simpa using hd)]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hE
  · rw [hE]; simp
  · refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with hP
    · rw [hP]; simp
    · rfl

/-- **The kernel applied to a polynomial**: `pv (hatT E P) s = ∫_0^1 pv E (|s - t|) pv P t dt`. -/
theorem pv_hatT (hb : binOK = true) {E P : List ℚ} (hE : E.length ≤ 47) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) :
    pv (hatT E P) s = ∫ t in (0 : ℝ)..1, pv E |s - t| * pv P t := by
  have hR : ∀ t : ℝ, pv E |s - t| * pv P t = ∑ i ∈ range E.length, ∑ m ∈ range P.length,
      ((E.getD i 0 : ℝ) * (P.getD m 0 : ℝ)) * (|s - t| ^ i * t ^ m) := by
    intro t
    unfold pv
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring
  simp_rw [hR]
  rw [intervalIntegral.integral_finsetSum (f := fun i t => ∑ m ∈ range P.length,
      ((E.getD i 0 : ℝ) * (P.getD m 0 : ℝ)) * (|s - t| ^ i * t ^ m)) fun i _ =>
    (continuous_finsetSum _ fun m _ => continuous_const.mul (by fun_prop)).intervalIntegrable _ _]
  have hL : pv (hatT E P) s = ∑ i ∈ range E.length, ∑ m ∈ range P.length,
      ((E.getD i 0 : ℝ) * (P.getD m 0 : ℝ)) *
        ∑ d ∈ range (E.length + P.length), (Fc i m d : ℝ) * s ^ d := by
    unfold pv
    rw [hatT_length]
    rw [Finset.sum_congr rfl fun d hd => by rw [hatT_getD E P (Finset.mem_range.1 hd)]]
    push_cast
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun d _ => by ring
  rw [hL]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [intervalIntegral.integral_finsetSum (f := fun m t => ((E.getD i 0 : ℝ) * (P.getD m 0 : ℝ)) *
      (|s - t| ^ i * t ^ m)) fun m _ => (continuous_const.mul (by fun_prop)).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [intervalIntegral.integral_const_mul, integral_abs_pow_mul_pow hb (by
    have := Finset.mem_range.1 hi; omega) hs0 hs1 (D := E.length + P.length) (by
    have := Finset.mem_range.1 hi; have := Finset.mem_range.1 hm; omega)]

/-! ## F. The squared kernel. -/

theorem integral_abs_pow (n : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∫ t in (0 : ℝ)..1, |s - t| ^ n = (s ^ (n + 1) + (1 - s) ^ (n + 1)) / (n + 1) := by
  have hcont : Continuous fun t : ℝ => |s - t| ^ n := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := s) (hcont.intervalIntegrable _ _)
    (hcont.intervalIntegrable _ _)]
  have h1 : ∫ t in (0 : ℝ)..s, |s - t| ^ n = ∫ t in (0 : ℝ)..s, (s - t) ^ n := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hs0] at ht
    rw [abs_of_nonneg (by linarith [ht.2])]
  have h2 : ∫ t in s..(1 : ℝ), |s - t| ^ n = ∫ t in s..(1 : ℝ), (t - s) ^ n := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hs1] at ht
    rw [abs_sub_comm, abs_of_nonneg (by linarith [ht.1])]
  rw [h1, h2, intervalIntegral.integral_comp_sub_left (fun t => t ^ n),
    intervalIntegral.integral_comp_sub_right (fun t => t ^ n), integral_pow, integral_pow]
  simp only [sub_self, sub_zero]
  rw [zero_pow (by omega)]
  ring

/-- The closed form of the inner integral, as a function of `s`. -/
def gpow (n : ℕ) (s : ℝ) : ℝ := (s ^ (n + 1) + (1 - s) ^ (n + 1)) / (n + 1)

theorem continuous_gpow (n : ℕ) : Continuous (gpow n) := by unfold gpow; fun_prop

theorem integral_gpow (n : ℕ) : ∫ s in (0 : ℝ)..1, gpow n s = (Jc n : ℝ) := by
  unfold gpow
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (f := fun x : ℝ => x ^ (n + 1))
    (g := fun x : ℝ => (1 - x) ^ (n + 1)) ((continuous_pow _).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun x : ℝ => (1 - x) ^ (n + 1)).intervalIntegrable _ _),
    integral_pow, intervalIntegral.integral_comp_sub_left (fun s => s ^ (n + 1)), integral_pow]
  unfold Jc
  push_cast
  simp only [sub_self, sub_zero, one_pow, zero_pow (Nat.succ_ne_zero _)]
  field_simp
  ring

theorem integral_integral_abs_pow (n : ℕ) :
    ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, |s - t| ^ n = (Jc n : ℝ) := by
  rw [← integral_gpow n]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs
  exact integral_abs_pow n hs.1 hs.2

theorem integral_sum_abs {ι : Type*} (s : ℝ) (S : Finset ι) (c : ι → ℝ) (n : ι → ℕ) :
    ∫ t in (0 : ℝ)..1, ∑ i ∈ S, c i * |s - t| ^ n i
      = ∑ i ∈ S, c i * ∫ t in (0 : ℝ)..1, |s - t| ^ n i := by
  rw [intervalIntegral.integral_finsetSum (f := fun i t => c i * |s - t| ^ n i)
    fun i _ => (continuous_const.mul (by fun_prop)).intervalIntegrable _ _]
  exact Finset.sum_congr rfl fun i _ => intervalIntegral.integral_const_mul _ _

theorem continuous_sum_abs {ι : Type*} (s : ℝ) (S : Finset ι) (c : ι → ℝ) (n : ι → ℕ) :
    Continuous fun t : ℝ => ∑ i ∈ S, c i * |s - t| ^ n i :=
  continuous_finsetSum _ fun i _ => continuous_const.mul (by fun_prop)

theorem integral_sum_gpow {ι : Type*} (S : Finset ι) (c : ι → ℝ) (n : ι → ℕ) :
    ∫ s in (0 : ℝ)..1, ∑ i ∈ S, c i * gpow (n i) s = ∑ i ∈ S, c i * (Jc (n i) : ℝ) := by
  rw [intervalIntegral.integral_finsetSum (f := fun i s => c i * gpow (n i) s)
    fun i _ => (continuous_const.mul (continuous_gpow _)).intervalIntegrable _ _]
  exact Finset.sum_congr rfl fun i _ => by rw [intervalIntegral.integral_const_mul, integral_gpow]

theorem continuous_sum_gpow {ι : Type*} (S : Finset ι) (c : ι → ℝ) (n : ι → ℕ) :
    Continuous fun s : ℝ => ∑ i ∈ S, c i * gpow (n i) s :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (continuous_gpow _)

theorem pv_sq_expand (E : List ℚ) (c0 : ℚ) (w : ℝ) :
    (pv E w + c0) ^ 2 = (∑ p ∈ range E.length ×ˢ range E.length,
        ((E.getD p.1 0 : ℝ) * (E.getD p.2 0 : ℝ)) * w ^ (p.1 + p.2))
      + (∑ i ∈ range E.length, (2 * c0 * (E.getD i 0 : ℝ)) * w ^ i) + (c0 : ℝ) * c0 := by
  unfold pv
  rw [Finset.sum_product, add_sq, sq, Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_mul]
  have : ∑ i ∈ range E.length, ∑ j ∈ range E.length,
      (E.getD i 0 : ℝ) * w ^ i * ((E.getD j 0 : ℝ) * w ^ j)
      = ∑ i ∈ range E.length, ∑ j ∈ range E.length, ((E.getD i 0 : ℝ) * (E.getD j 0 : ℝ)) * w ^ (i + j) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [this]
  congr 1
  · congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  · ring

/-- `∫_0^1 ∫_0^1 (pv E |s - t| + c0)^2 = KKh E c0`. -/
theorem KKh_eq (E : List ℚ) (c0 : ℚ) :
    ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, (pv E |s - t| + c0) ^ 2 = (KKh E c0 : ℝ) := by
  set S2 := range E.length ×ˢ range E.length
  set c2 : ℕ × ℕ → ℝ := fun p => (E.getD p.1 0 : ℝ) * (E.getD p.2 0 : ℝ)
  set c1 : ℕ → ℝ := fun i => 2 * c0 * (E.getD i 0 : ℝ)
  have hinner : ∀ s ∈ Set.uIcc (0 : ℝ) 1, ∫ t in (0 : ℝ)..1, (pv E |s - t| + c0) ^ 2
      = (∑ p ∈ S2, c2 p * gpow (p.1 + p.2) s) + (∑ i ∈ range E.length, c1 i * gpow i s)
        + (c0 : ℝ) * c0 := by
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    simp_rw [pv_sq_expand]
    rw [intervalIntegral.integral_add (f := fun t => (∑ p ∈ S2, c2 p * |s - t| ^ (p.1 + p.2))
        + ∑ i ∈ range E.length, c1 i * |s - t| ^ i) (g := fun _ => (c0 : ℝ) * c0)
      (((continuous_sum_abs s S2 c2 _).add (continuous_sum_abs s _ c1 _)).intervalIntegrable _ _)
      intervalIntegrable_const,
      intervalIntegral.integral_add ((continuous_sum_abs s S2 c2 _).intervalIntegrable _ _)
        ((continuous_sum_abs s _ c1 _).intervalIntegrable _ _),
      integral_sum_abs, integral_sum_abs, intervalIntegral.integral_const]
    simp only [sub_zero, one_smul]
    congr 2
    · exact Finset.sum_congr rfl fun p _ => by rw [integral_abs_pow _ hs.1 hs.2, gpow]
    · exact Finset.sum_congr rfl fun i _ => by rw [integral_abs_pow _ hs.1 hs.2, gpow]
  rw [intervalIntegral.integral_congr hinner,
    intervalIntegral.integral_add (f := fun s => (∑ p ∈ S2, c2 p * gpow (p.1 + p.2) s)
        + ∑ i ∈ range E.length, c1 i * gpow i s) (g := fun _ => (c0 : ℝ) * c0)
      (((continuous_sum_gpow S2 c2 _).add (continuous_sum_gpow _ c1 _)).intervalIntegrable _ _)
      intervalIntegrable_const,
    intervalIntegral.integral_add ((continuous_sum_gpow S2 c2 _).intervalIntegrable _ _)
      ((continuous_sum_gpow _ c1 _).intervalIntegrable _ _),
    integral_sum_gpow, integral_sum_gpow, intervalIntegral.integral_const]
  simp only [sub_zero, one_smul]
  unfold KKh
  push_cast
  rw [Finset.sum_product, Finset.mul_sum]
  simp only [c2, c1]
  ring_nf

end ArchS11
