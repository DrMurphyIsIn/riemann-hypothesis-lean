/-
  KWin2_Minorant -- the proved piecewise-polynomial minorant of the Weil symbol WITH the prime comb,
  parametric in the window (rvm_bridge island, 2026-09-24).

  conjecture1_proved = False.  (Finite-window Weil positivity is not RH; not Connes-Consani, whose
  theorem is for the pole-free class; cf. PR #604.)

  STATEMENTS.
    * `wpoly_le_Psi`: for every piece i of the KPar P and every t in it,
          wpoly P i t <= Psi t = Re psi(1/4 + it/2) - log pi,
      KWin's construction (KWin_Minorant) with nS, Kalt, Nser, Mser, Dmax, the pieces and the gamma /
      log pi constants as parameters: the island's series floor `psiR_ge_series`, the exact
      Lorentzians by the geometric Taylor bound `KWin.Lz_le_kapR`, the rest by the alternating bound.
    * `comb_le_combPoly`: for 0 <= t <= T and any real a, c with |a - a0| <= da, |c - c0| <= dc,
          c cos(t a) <= combPoly P t,
      from |cos x - cos y| <= |x - y|, the Taylor bound `KWin.cos_sub_tayl_le` of cos at t a0, and
      coefficients rounded up (t >= 0).  The instance file feeds a = log 2, c = 2 Lambda(2)/sqrt 2.
    * `sym_minorant`: wpoly P i t - combPoly P t <= Psi t - c cos(t a) on every piece.
  No `sorry`.
-/
import KWin2_Data
import KWin_Minorant
import KWin_Taylor

open Real Finset

noncomputable section

namespace KWin2
open KWin RvMBridge11 RvMBridge30

variable (P : KPar)

/-! ## A. Reindexing even powers. -/

lemma sum_even_reindex {β : Type*} [AddCommMonoid β] (f : ℕ → β) {K D : ℕ} (h : 2 * K ≤ D + 2) :
    ∑ p ∈ range (D + 1), (if p % 2 = 0 ∧ p / 2 < K then f p else 0) = ∑ m ∈ range K, f (2 * m) := by
  rw [← Finset.sum_filter]
  have hs : (range (D + 1)).filter (fun p => p % 2 = 0 ∧ p / 2 < K)
      = (range K).image (fun m => 2 * m) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨_, h1, h2⟩
      exact ⟨p / 2, h2, by omega⟩
    · rintro ⟨m, hm, rfl⟩
      refine ⟨by omega, by omega, by omega⟩
  rw [hs, Finset.sum_image (fun a _ b _ hab => by omega)]

/-! ## B. The alternating tail. -/

lemma gAlt_ge (k : ℕ) :
    (-1) ^ k * ∑ j ∈ Ico P.nS (P.Nser + 1), (4 : ℝ) ^ (k + 1) / (4 * (j : ℝ) + 1) ^ (2 * k + 1)
      ≤ ((gAlt P k : ℚ) : ℝ) := by
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
    ∑ j ∈ Ico P.nS (P.Nser + 1), Lz ((j : ℝ) + 1 / 4) r
      ≤ ∑ k ∈ range (2 * P.Kalt + 1), r ^ (2 * k) * ((gAlt P k : ℚ) : ℝ) := by
  calc ∑ j ∈ Ico P.nS (P.Nser + 1), Lz ((j : ℝ) + 1 / 4) r
      ≤ ∑ j ∈ Ico P.nS (P.Nser + 1), ∑ k ∈ range (2 * P.Kalt + 1),
          r ^ (2 * k) * ((-1) ^ k * (4 ^ (k + 1) / (4 * (j : ℝ) + 1) ^ (2 * k + 1))) :=
        Finset.sum_le_sum fun j _ => Lz_le_alt j r P.Kalt
    _ = ∑ k ∈ range (2 * P.Kalt + 1), r ^ (2 * k)
          * ((-1) ^ k * ∑ j ∈ Ico P.nS (P.Nser + 1), (4 : ℝ) ^ (k + 1) / (4 * (j : ℝ) + 1) ^ (2 * k + 1)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ ∑ k ∈ range (2 * P.Kalt + 1), r ^ (2 * k) * ((gAlt P k : ℚ) : ℝ) := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact mul_le_mul_of_nonneg_left (gAlt_ge P k) (by rw [pow_mul]; exact pow_nonneg (sq_nonneg r) k)

/-! ## C. The global series floor. -/

/-- The global part of the lower bound (constants, integral tail, large Lorentzians). -/
def globPoly (r : ℝ) : ℝ :=
  ((C0 P : ℚ) : ℝ) + ((C1 P : ℚ) : ℝ) * r ^ 2 + ((C2 P : ℚ) : ℝ) * r ^ 4
    - ∑ k ∈ range (2 * P.Kalt + 1), r ^ (2 * k) * ((gAlt P k : ℚ) : ℝ)

lemma HNr_le_Q : HNr P ≤ ∑ n ∈ range P.Nser, (1 : ℚ) / ((n : ℚ) + 1) := by
  unfold HNr
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun n _ => ?_
  have h1 : (((10 ^ 30 / (n + 1) : ℕ) : ℚ)) ≤ ((10 ^ 30 : ℕ) : ℚ) / ((n + 1 : ℕ) : ℚ) := Nat.cast_div_le
  have hA : (0 : ℚ) < 10 ^ 30 := by positivity
  rw [div_le_iff₀ hA]
  calc (((10 ^ 30 / (n + 1) : ℕ) : ℚ)) ≤ ((10 ^ 30 : ℕ) : ℚ) / ((n + 1 : ℕ) : ℚ) := h1
    _ = 1 / ((n : ℚ) + 1) * 10 ^ 30 := by push_cast; ring

lemma HNr_le : ((HNr P : ℚ) : ℝ) ≤ ∑ n ∈ range P.Nser, (1 : ℝ) / ((n : ℝ) + 1) := by
  have := (Rat.cast_le (K := ℝ)).mpr (HNr_le_Q P)
  push_cast at this
  exact this

/-- **The global series floor**: `Psi r >= globPoly r - sum_{j < nS} Lz(j + 1/4, r)` for all `r`. -/
theorem Psi_ge_glob (hγ : Real.eulerMascheroniConstant ≤ ((P.gamUp : ℚ) : ℝ))
    (hlp : Real.log Real.pi ≤ ((P.logPiUp : ℚ) : ℝ)) (hnS : P.nS ≤ P.Nser + 1) (r : ℝ) :
    globPoly P r - ∑ j ∈ range P.nS, Lz ((j : ℝ) + 1 / 4) r ≤ Psi r := by
  have hs := psi_series_Lz r P.Nser P.Mser
  have hsplit : ∑ j ∈ range (P.Nser + 1), Lz ((j : ℝ) + 1 / 4) r
      = ∑ j ∈ range P.nS, Lz ((j : ℝ) + 1 / 4) r
        + ∑ j ∈ Ico P.nS (P.Nser + 1), Lz ((j : ℝ) + 1 / 4) r := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      Finset.sum_Ico_consecutive _ (Nat.zero_le P.nS) hnS]
  have hlarge := sum_Lz_large_le P r
  have hG1 := serG_N_ge P.Nser r
  have hG2 := serG_NM_le P.Nser P.Mser r
  have hH := HNr_le P
  unfold Psi globPoly
  have hC0 : ((C0 P : ℚ) : ℝ) = -((P.gamUp : ℚ) : ℝ) - ((P.logPiUp : ℚ) : ℝ) + ((HNr P : ℚ) : ℝ)
      + (1 / 4) / ((P.Nser : ℝ) + 5 / 4)
      - (1 / 2) * ((((P.Nser : ℝ) + P.Mser + 5 / 4) ^ 2 - ((P.Nser : ℝ) + P.Mser + 1) ^ 2)
        / ((P.Nser : ℝ) + P.Mser + 1) ^ 2) := by
    unfold C0
    push_cast
    ring
  have hC1 : ((C1 P : ℚ) : ℝ) = 1 / (8 * ((P.Nser : ℝ) + 5 / 4) ^ 2)
      - 1 / (8 * ((P.Nser : ℝ) + P.Mser + 1) ^ 2) := by
    unfold C1
    push_cast
    ring
  have hC2 : ((C2 P : ℚ) : ℝ) = -1 / (32 * ((P.Nser : ℝ) + 5 / 4) ^ 4) := by
    unfold C2
    push_cast
    ring
  rw [hC0, hC1, hC2]
  rw [hsplit] at hs
  have e1 : r ^ 2 / (8 * ((P.Nser : ℝ) + 5 / 4) ^ 2) = 1 / (8 * ((P.Nser : ℝ) + 5 / 4) ^ 2) * r ^ 2 := by
    ring
  have e2 : r ^ 4 / (32 * ((P.Nser : ℝ) + 5 / 4) ^ 4)
      = -(-1 / (32 * ((P.Nser : ℝ) + 5 / 4) ^ 4) * r ^ 4) := by
    ring
  have e3 : r ^ 2 / (8 * ((P.Nser : ℝ) + P.Mser + 1) ^ 2)
      = 1 / (8 * ((P.Nser : ℝ) + P.Mser + 1) ^ 2) * r ^ 2 := by
    ring
  rw [e1, e2] at hG1
  rw [e3] at hG2
  linarith

/-- The global polynomial dominates its rounded kernel coefficients. -/
theorem globC_poly_le (hD4 : 4 ≤ P.Dmax) (hDK : 4 * P.Kalt ≤ P.Dmax) (r : ℝ) :
    ∑ p ∈ range (P.Dmax + 1), ((globC P p : ℚ) : ℝ) * r ^ p ≤ globPoly P r := by
  have hle : ∀ p ∈ range (P.Dmax + 1),
      ((globC P p : ℚ) : ℝ) * r ^ p ≤ ((globRaw P p : ℚ) : ℝ) * r ^ p := by
    intro p _
    rcases Nat.even_or_odd p with ⟨m, hm⟩ | hodd
    · have hr : 0 ≤ r ^ p := by rw [hm, ← two_mul, pow_mul]; positivity
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast floorR_le _ _) hr
    · have h0 : globRaw P p = 0 := by
        unfold globRaw
        have h1 : p % 2 = 1 := Nat.odd_iff.mp hodd
        have hp0 : p ≠ 0 := by omega
        have hp2 : p ≠ 2 := by omega
        have hp4 : p ≠ 4 := by omega
        simp [hp0, hp2, hp4, h1]
      have hc : globC P p = 0 := by
        unfold globC; rw [h0]; simp [floorR]
      rw [hc, h0]
  refine (Finset.sum_le_sum hle).trans (le_of_eq ?_)
  -- the base part and the alternating part
  have hpt : ∀ p, ((globRaw P p : ℚ) : ℝ) * r ^ p
      = ((if p = 0 then ((C0 P : ℚ) : ℝ) else 0) + (if p = 2 then ((C1 P : ℚ) : ℝ) * r ^ 2 else 0)
          + (if p = 4 then ((C2 P : ℚ) : ℝ) * r ^ 4 else 0))
        - (if p % 2 = 0 ∧ p / 2 < 2 * P.Kalt + 1 then ((gAlt P (p / 2) : ℚ) : ℝ) * r ^ p else 0) := by
    intro p
    unfold globRaw
    by_cases h0 : p = 0
    · subst h0; simp
    by_cases h2 : p = 2
    · subst h2; simp; split_ifs <;> push_cast <;> ring
    by_cases h4 : p = 4
    · subst h4; simp; split_ifs <;> push_cast <;> ring
    simp only [h0, h2, h4, if_false, add_zero, zero_sub, Rat.cast_neg]
    split_ifs <;> push_cast <;> ring
  simp_rw [hpt]
  rw [Finset.sum_sub_distrib, sum_even_reindex _ (by omega : 2 * (2 * P.Kalt + 1) ≤ P.Dmax + 2)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
    Finset.sum_ite_eq']
  have m0 : 0 ∈ range (P.Dmax + 1) := Finset.mem_range.mpr (by omega)
  have m2 : 2 ∈ range (P.Dmax + 1) := Finset.mem_range.mpr (by omega)
  have m4 : 4 ∈ range (P.Dmax + 1) := Finset.mem_range.mpr (by omega)
  rw [if_pos m0, if_pos m2, if_pos m4]
  unfold globPoly
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]
  ring

/-! ## D. The shift-to-power identity. -/

lemma sum_ite_le_range' {β : Type*} [AddCommMonoid β] (f : ℕ → β) {d D : ℕ} (h : d ≤ D) :
    ∑ k ∈ range (D + 1), (if k ≤ d then f k else 0) = ∑ k ∈ range (d + 1), f k := by
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem wpoly_eq {i : ℕ} (r : ℝ) :
    wpoly P i r = ∑ p ∈ range (P.Dmax + 1), ((globC P p : ℚ) : ℝ) * r ^ p
      - ∑ k ∈ range (P.Dmax + 1), ((uCoef P i k : ℚ) : ℝ) * (r - pcen P i) ^ k - ((rhoR P i : ℚ) : ℝ) := by
  unfold wpoly
  have hw : ∀ p ∈ range (P.Dmax + 1), (((wpList P i).getD p 0 : ℚ) : ℝ) * r ^ p
      = ((globC P p : ℚ) : ℝ) * r ^ p
        - ∑ k ∈ range (P.Dmax + 1), (if p ≤ k then ((uCoef P i k : ℚ) : ℝ) * (k.choose p : ℝ)
            * (-(pcen P i : ℝ)) ^ (k - p) * r ^ p else 0)
        - (if p = 0 then ((rhoR P i : ℚ) : ℝ) else 0) := by
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
    have hk' : k ≤ P.Dmax := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have e : ∑ p ∈ range (P.Dmax + 1), (if p ≤ k then ((uCoef P i k : ℚ) : ℝ) * (k.choose p : ℝ)
          * (-(pcen P i : ℝ)) ^ (k - p) * r ^ p else 0)
        = ∑ p ∈ range (k + 1), ((uCoef P i k : ℚ) : ℝ) * (k.choose p : ℝ) * (-(pcen P i : ℝ)) ^ (k - p)
          * r ^ p := sum_ite_le_range' _ hk'
    rw [e, sub_eq_add_neg r, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  · rw [Finset.sum_ite_eq' (range (P.Dmax + 1)) 0 (fun _ => ((rhoR P i : ℚ) : ℝ))]
    simp

/-! ## E. The minorant on each piece. -/

lemma brk_le_succ (hb : brkCheck P = true) {i : ℕ} (hi : i < nPc P) : brk P i ≤ brk P (i + 1) :=
  (brkCheck_sound P hb).2.2 i hi

lemma brk_nonneg (hb : brkCheck P = true) {i : ℕ} (hi : i ≤ nPc P) : 0 ≤ brk P i := by
  induction i with
  | zero => rw [(brkCheck_sound P hb).1]
  | succ n ih => exact (ih (by omega)).trans (brk_le_succ P hb (by omega))

theorem sum_Lz_small_le (hb : brkCheck P = true) (hpc : pieceCheck P = true) {i : ℕ} (hi : i < nPc P)
    {r : ℝ} (hu : |r - (pcen P i : ℝ)| ≤ (phw P i : ℝ)) :
    ∑ j ∈ range P.nS, Lz ((j : ℝ) + 1 / 4) r
      ≤ ∑ k ∈ range (P.Dmax + 1), ((uCoef P i k : ℚ) : ℝ) * (r - pcen P i) ^ k + ((rhoR P i : ℚ) : ℝ) := by
  have hc : 0 ≤ pcen P i := by
    unfold pcen
    have := brk_nonneg P hb (i := i) (by omega)
    have := brk_nonneg P hb (i := i + 1) (by omega)
    linarith
  have hh : 0 ≤ phw P i := by unfold phw; have := brk_le_succ P hb hi; linarith
  have hj : ∀ j ∈ range P.nS, Lz ((j : ℝ) + 1 / 4) r
      ≤ ∑ k ∈ range (P.Dmax + 1), (if k ≤ deg P i j then ((kapR (bS j) (pcen P i) k : ℚ) : ℝ) else 0)
            * (r - pcen P i) ^ k
        + (((remB (bS j) (pcen P i) (phw P i) (deg P i j)
          + (∑ k ∈ range (deg P i j + 1), phw P i ^ k) / 10 ^ Rk : ℚ)) : ℝ) := by
    intro j hjm
    have hjS := Finset.mem_range.mp hjm
    obtain ⟨hlt, hdeg⟩ := pieceCheck_sound P hpc hi hjS
    have hb' : (0 : ℚ) < bS j := by unfold bS; positivity
    have hL := Lz_le_kapR hb' hc hh hlt hu (deg P i j)
    have hx : ((bS j : ℚ) : ℝ) / 2 = (j : ℝ) + 1 / 4 := by unfold bS; push_cast; ring
    rw [hx] at hL
    have e : ∑ k ∈ range (P.Dmax + 1), (if k ≤ deg P i j then ((kapR (bS j) (pcen P i) k : ℚ) : ℝ) else 0)
          * (r - pcen P i) ^ k
        = ∑ k ∈ range (deg P i j + 1), ((kapR (bS j) (pcen P i) k : ℚ) : ℝ) * (r - pcen P i) ^ k := by
      rw [← sum_ite_le_range' _ hdeg]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs <;> simp
    rw [e]
    push_cast at hL ⊢
    linarith
  refine (Finset.sum_le_sum hj).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  have hu1 : ∀ k ∈ range (P.Dmax + 1), ∑ j ∈ range P.nS, (if k ≤ deg P i j then
      ((kapR (bS j) (pcen P i) k : ℚ) : ℝ) else 0) * (r - pcen P i) ^ k
      = ((uCoef P i k : ℚ) : ℝ) * (r - pcen P i) ^ k := by
    intro k _
    unfold uCoef
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hu1]
  have hrho : ∑ j ∈ range P.nS, (((remB (bS j) (pcen P i) (phw P i) (deg P i j)
        + (∑ k ∈ range (deg P i j + 1), phw P i ^ k) / 10 ^ Rk : ℚ)) : ℝ) ≤ ((rhoR P i : ℚ) : ℝ) := by
    have h1 := le_ceilR (rhoRaw P i) Rk
    have h2 : ((rhoRaw P i : ℚ) : ℝ) ≤ ((rhoR P i : ℚ) : ℝ) := by exact_mod_cast h1
    refine le_trans (le_of_eq ?_) h2
    unfold rhoRaw
    push_cast
    rfl
  linarith

/-- **The Psi_0 minorant**: on piece `i`, `wpoly P i t <= Psi t`. -/
theorem wpoly_le_Psi (hb : brkCheck P = true) (hpc : pieceCheck P = true) (hm : minCheck P = true)
    (hγ : Real.eulerMascheroniConstant ≤ ((P.gamUp : ℚ) : ℝ))
    (hlp : Real.log Real.pi ≤ ((P.logPiUp : ℚ) : ℝ)) {i : ℕ} (hi : i < nPc P) {t : ℝ}
    (ha : ((brk P i : ℚ) : ℝ) ≤ t) (hb' : t ≤ ((brk P (i + 1) : ℚ) : ℝ)) : wpoly P i t ≤ Psi t := by
  obtain ⟨hnS, hDK, hD4⟩ := minCheck_sound P hm
  have hu : |t - (pcen P i : ℝ)| ≤ (phw P i : ℝ) := by
    unfold pcen phw
    push_cast
    rw [abs_le]
    constructor <;> linarith
  rw [wpoly_eq]
  have h1 := globC_poly_le P hD4 hDK t
  have h2 := sum_Lz_small_le P hb hpc hi hu
  have h3 := Psi_ge_glob P hγ hlp hnS t
  linarith

/-! ## F. The comb upper polynomial. -/

/-- **The comb bound**: `c cos(t a) <= combPoly P t` on `[0, T]`. -/
theorem comb_le_combPoly (hcc : combCheck P = true) {a c : ℝ} (ha : |a - (P.a0 : ℝ)| ≤ (P.da : ℝ))
    (hc : |c - (P.c0 : ℝ)| ≤ (P.dc : ℝ)) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ (P.T : ℝ)) :
    c * Real.cos (t * a) ≤ combPoly P t := by
  obtain ⟨hc0, ha0, hda, hdc, hMc, hK⟩ := combCheck_sound P hcc
  have hc0R : (0 : ℝ) ≤ (P.c0 : ℝ) := by exact_mod_cast hc0
  have ha0R : (0 : ℝ) ≤ (P.a0 : ℝ) := by exact_mod_cast ha0
  have hdaR : (0 : ℝ) ≤ (P.da : ℝ) := by exact_mod_cast hda
  -- step 1: move to (a0, c0)
  have h1 : c * Real.cos (t * a)
      ≤ (P.c0 : ℝ) * Real.cos (t * P.a0) + (P.dc : ℝ) + (P.c0 : ℝ) * t * (P.da : ℝ) := by
    have hcos := Real.abs_cos_sub_cos_le (t * a) (t * P.a0)
    have e1 : |t * a - t * (P.a0 : ℝ)| = t * |a - (P.a0 : ℝ)| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg ht0]
    rw [e1] at hcos
    have hc1 : |Real.cos (t * a)| ≤ 1 := Real.abs_cos_le_one _
    have e2 : c * Real.cos (t * a) = (P.c0 : ℝ) * Real.cos (t * P.a0) + (c - P.c0) * Real.cos (t * a)
        + (P.c0 : ℝ) * (Real.cos (t * a) - Real.cos (t * P.a0)) := by ring
    rw [e2]
    have h2 : (c - P.c0) * Real.cos (t * a) ≤ (P.dc : ℝ) := by
      calc (c - P.c0) * Real.cos (t * a) ≤ |(c - P.c0) * Real.cos (t * a)| := le_abs_self _
        _ = |c - P.c0| * |Real.cos (t * a)| := abs_mul _ _
        _ ≤ (P.dc : ℝ) * 1 := mul_le_mul hc hc1 (abs_nonneg _) (by exact_mod_cast hdc)
        _ = (P.dc : ℝ) := mul_one _
    have h4 : |Real.cos (t * a) - Real.cos (t * P.a0)| ≤ t * (P.da : ℝ) :=
      hcos.trans (mul_le_mul_of_nonneg_left ha ht0)
    have h3 : (P.c0 : ℝ) * (Real.cos (t * a) - Real.cos (t * P.a0)) ≤ (P.c0 : ℝ) * t * (P.da : ℝ) := by
      have := le_abs_self (Real.cos (t * a) - Real.cos (t * P.a0))
      have := mul_le_mul_of_nonneg_left (this.trans h4) hc0R
      linarith
    linarith
  -- step 2: the Taylor bound of cos at t a0
  have hy0 : 0 ≤ t * (P.a0 : ℝ) := mul_nonneg ht0 ha0R
  have hyT : t * (P.a0 : ℝ) ≤ (P.a0 : ℝ) * (P.T : ℝ) := by nlinarith
  have hMcR : (P.a0 : ℝ) * (P.T : ℝ) ≤ (2 * P.Mc + 1) / 2 := by
    have := (Rat.cast_le (K := ℝ)).mpr hMc
    push_cast at this
    exact this
  have hy : |t * (P.a0 : ℝ)| ≤ (2 * P.Mc + 1) / 2 := by
    rw [abs_of_nonneg hy0]; linarith
  have htay := cos_sub_tayl_le hy
  have hpowle : |t * (P.a0 : ℝ)| ^ (2 * P.Mc) ≤ ((P.a0 : ℝ) * (P.T : ℝ)) ^ (2 * P.Mc) := by
    rw [abs_of_nonneg hy0]
    exact pow_le_pow_left₀ hy0 hyT _
  have hfac : (0 : ℝ) < ((2 * P.Mc).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hrem : Real.cos (t * P.a0) ≤ tayl 0 P.Mc (t * P.a0)
      + 2 * ((P.a0 : ℝ) * (P.T : ℝ)) ^ (2 * P.Mc) / ((2 * P.Mc).factorial : ℝ) := by
    have := (abs_le.mp htay).2
    have h5 : 2 * |t * (P.a0 : ℝ)| ^ (2 * P.Mc) / ((2 * P.Mc).factorial : ℝ)
        ≤ 2 * ((P.a0 : ℝ) * (P.T : ℝ)) ^ (2 * P.Mc) / ((2 * P.Mc).factorial : ℝ) := by
      rw [div_le_div_iff_of_pos_right hfac]
      linarith
    linarith
  -- step 3: the rounded coefficients
  have hKR : (P.c0 : ℝ) * (2 * ((P.a0 : ℝ) * (P.T : ℝ)) ^ (2 * P.Mc) / ((2 * P.Mc).factorial : ℝ))
      + (P.dc : ℝ) + (P.c0 : ℝ) * (P.T : ℝ) * (P.da : ℝ) ≤ (P.combK : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr hK
    push_cast at this
    exact this
  have htaylsum : (P.c0 : ℝ) * tayl 0 P.Mc (t * P.a0)
      ≤ ∑ m ∈ range P.Mc, ((ceilR (P.c0 * (-1) ^ m * P.a0 ^ (2 * m) / ((2 * m).factorial : ℚ))
          (P.Rc + 2 * (2 * m)) : ℚ) : ℝ) * t ^ (2 * m) := by
    unfold tayl
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m _ => ?_
    have hr := le_ceilR (P.c0 * (-1) ^ m * P.a0 ^ (2 * m) / ((2 * m).factorial : ℚ)) (P.Rc + 2 * (2 * m))
    have hr' : ((P.c0 * (-1) ^ m * P.a0 ^ (2 * m) / ((2 * m).factorial : ℚ) : ℚ) : ℝ)
        ≤ ((ceilR (P.c0 * (-1) ^ m * P.a0 ^ (2 * m) / ((2 * m).factorial : ℚ)) (P.Rc + 2 * (2 * m)) : ℚ) : ℝ) := by
      exact_mod_cast hr
    have ht2 : 0 ≤ t ^ (2 * m) := by rw [pow_mul]; positivity
    have e : (P.c0 : ℝ) * ((-1) ^ m * (t * P.a0) ^ (2 * m + 0) / ((2 * m + 0).factorial : ℝ))
        = ((P.c0 * (-1) ^ m * P.a0 ^ (2 * m) / ((2 * m).factorial : ℚ) : ℚ) : ℝ) * t ^ (2 * m) := by
      push_cast
      rw [add_zero, mul_pow]
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hr' ht2
  have hpoly : combPoly P t = ∑ m ∈ range P.Mc, ((ceilR (P.c0 * (-1) ^ m * P.a0 ^ (2 * m)
      / ((2 * m).factorial : ℚ)) (P.Rc + 2 * (2 * m)) : ℚ) : ℝ) * t ^ (2 * m) + (P.combK : ℝ) := by
    unfold combPoly
    have hpt : ∀ p ∈ range (2 * P.Mc + 1), (((combList P).getD p 0 : ℚ) : ℝ) * t ^ p
        = (if p % 2 = 0 ∧ p / 2 < P.Mc then ((ceilR (P.c0 * (-1) ^ (p / 2) * P.a0 ^ p
            / (p.factorial : ℚ)) (P.Rc + 2 * p) : ℚ) : ℝ) * t ^ p else 0)
          + (if p = 0 then (P.combK : ℝ) else 0) := by
      intro p hp
      unfold combList
      rw [getD_map_range _ _ (Finset.mem_range.mp hp)]
      unfold combC
      by_cases h0 : p = 0
      · subst h0; simp; split_ifs <;> simp
      · simp only [h0, if_false, add_zero]
        split_ifs <;> simp
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib,
      sum_even_reindex _ (by omega : 2 * P.Mc ≤ 2 * P.Mc + 2), Finset.sum_ite_eq']
    rw [if_pos (Finset.mem_range.mpr (by omega))]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Nat.mul_div_cancel_left m (by norm_num : 0 < 2)]
  rw [hpoly]
  have h6 : (P.c0 : ℝ) * Real.cos (t * P.a0) ≤ (P.c0 : ℝ) * tayl 0 P.Mc (t * P.a0)
      + (P.c0 : ℝ) * (2 * ((P.a0 : ℝ) * (P.T : ℝ)) ^ (2 * P.Mc) / ((2 * P.Mc).factorial : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hrem hc0R
    linarith
  have h7 : (P.c0 : ℝ) * t * (P.da : ℝ) ≤ (P.c0 : ℝ) * (P.T : ℝ) * (P.da : ℝ) := by
    have := mul_le_mul_of_nonneg_left htT hc0R
    nlinarith
  linarith

/-- **The symbol minorant on a piece**: `wpoly - combPoly <= Psi - c cos(t a)`. -/
theorem sym_minorant (hb : brkCheck P = true) (hpc : pieceCheck P = true) (hm : minCheck P = true)
    (hcc : combCheck P = true)
    (hγ : Real.eulerMascheroniConstant ≤ ((P.gamUp : ℚ) : ℝ))
    (hlp : Real.log Real.pi ≤ ((P.logPiUp : ℚ) : ℝ)) {a c : ℝ} (ha : |a - (P.a0 : ℝ)| ≤ (P.da : ℝ))
    (hc : |c - (P.c0 : ℝ)| ≤ (P.dc : ℝ)) {i : ℕ} (hi : i < nPc P) {t : ℝ}
    (hti : ((brk P i : ℚ) : ℝ) ≤ t) (hti' : t ≤ ((brk P (i + 1) : ℚ) : ℝ)) :
    wpoly P i t - combPoly P t ≤ Psi t - c * Real.cos (t * a) := by
  have h1 := wpoly_le_Psi P hb hpc hm hγ hlp hi hti hti'
  have ht0 : 0 ≤ t := le_trans (by exact_mod_cast brk_nonneg P hb (i := i) (by omega)) hti
  have htT : t ≤ (P.T : ℝ) := by
    have hmono : ∀ k, i + 1 + k ≤ nPc P → brk P (i + 1) ≤ brk P (i + 1 + k) := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ n ih =>
        intro hk
        exact (ih (by omega)).trans (by
          rw [show i + 1 + (n + 1) = (i + 1 + n) + 1 by ring]
          exact brk_le_succ P hb (by omega))
    have h2 := hmono (nPc P - (i + 1)) (by omega)
    rw [show i + 1 + (nPc P - (i + 1)) = nPc P by omega, (brkCheck_sound P hb).2.1] at h2
    have h3 : ((brk P (i + 1) : ℚ) : ℝ) ≤ (P.T : ℝ) := by exact_mod_cast h2
    linarith
  have h2 := comb_le_combPoly P hcc ha hc ht0 htT
  linarith

end KWin2

end
