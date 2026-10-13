/-
  E6Bridge23 -- the LOCAL-COUNT SUM (obligation LocalCountSum of E6Bridge22), 2026-09-21.

  TARGET.  RvMBridge22.LocalCountSum :
      ∃ C, ∀ a : ℝ, Sum'_rho m(rho)/(1 + (Im rho - a)^2) ≤ C (1 + log (2 + |a|)).

  THE ARGUMENT (the textbook Sum_rho 1/(1 + (t - gamma)^2) = O(log t) from the local zero count).
  Every finite partial sum over a Finset u of zeros is regrouped by the integer k := ceil(Im rho - a),
  so that the fiber k lies in the unit window (a + k - 1, a + k], where Zeta23's local count
  (Zeta23.RvM.zeta_local_zero_count : Ncount t (t+1) ≤ A0 log(|t| + 3)) bounds the multiplicity
  sum, while on the fiber 1/(1 + (Im rho - a)^2) ≤ 4/(1 + k^2).  Hence
      Sum_{rho in u} lcTerm a rho ≤ Sum_{k in Z} 4/(1 + k^2) * A0 log(|a| + |k| + 4)
                                 ≤ 4 A0 (log(2 + |a|) S1 + S2),
  S1 = Sum_k 1/(1 + k^2), S2 = Sum_k log(|k| + 4)/(1 + k^2) (summable: the tail majorant 6 |k|^{-3/2}
  from log y ≤ 2 sqrt y).  Real.tsum_le_of_sum_le turns the uniform finite-sum bound into the tsum
  bound with C := 4 A0 (S1 + S2).

  DELIVERED.  local_count_sum : RvMBridge22.LocalCountSum, kernel-clean; hence (with E6Bridge22)
  the growth of the entire extension and the derivative partial fraction of xi'/xi rest on
  StripDerivBound alone: xiLogDerivDerivEq_of_strip.  Nothing here bears on RH.
  conjecture1_proved = False.
-/
import E6Bridge22

open Zeta23 Complex Filter Topology
open scoped BigOperators

noncomputable section

namespace RvMBridge23
open RvMBridge22

/-! ## A. The fiber weight: on ceil(x) = k, 1/(1 + x^2) ≤ 4/(1 + k^2). -/

lemma one_add_sq_le_of_ceil {x : ℝ} {k : ℤ} (hk : ⌈x⌉ = k) :
    1 + (k : ℝ) ^ 2 ≤ 4 * (1 + x ^ 2) := by
  have h1 : x ≤ (k : ℝ) := by rw [← hk]; exact Int.le_ceil x
  have h2 : (k : ℝ) < x + 1 := by rw [← hk]; exact Int.ceil_lt_add_one x
  rcases le_or_gt (1 : ℤ) k with hk1 | hk0
  · have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hx0 : 0 ≤ (k : ℝ) - 1 := by linarith
    have hxx : ((k : ℝ) - 1) * ((k : ℝ) - 1) ≤ x * x :=
      mul_le_mul (by linarith) (by linarith) hx0 (by linarith)
    nlinarith [sq_nonneg (3 * (k : ℝ) - 4)]
  · have hk0' : (k : ℝ) ≤ 0 := by
      have : k ≤ 0 := by omega
      exact_mod_cast this
    have hxx : (-(k : ℝ)) * (-(k : ℝ)) ≤ (-x) * (-x) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    nlinarith

lemma lcTerm_le_fiber_weight (a : ℝ) {ρ : ℂ} {k : ℤ} (hk : ⌈ρ.im - a⌉ = k) :
    lcTerm a ρ ≤ (WeilExplicit.zeroMult ρ : ℝ) * (4 / (1 + (k : ℝ) ^ 2)) := by
  unfold lcTerm
  rw [div_eq_mul_one_div]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have h := one_add_sq_le_of_ceil hk
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-! ## B. The fiber lies in a unit window; its multiplicity sum is a local count. -/

lemma lcTerm_eq_zero_of_not_nontrivial {a : ℝ} {ρ : ℂ} (h : ¬ IsNontrivialZero ρ) : lcTerm a ρ = 0 := by
  unfold lcTerm
  rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial h]
  simp

lemma zeroMult_cast_eq {ρ : ℂ} (h : IsNontrivialZero ρ) :
    (WeilExplicit.zeroMult ρ : ℝ) = (Zeta23.zeroMult ρ : ℝ) := by
  rw [RvMBridge4.zeroMult_eq_mult h]
  rfl

/-- The multiplicity sum over any finite set of nontrivial zeros with ceil(Im rho - a) = k is at
most the local count of the window (a + k - 1, a + k]. -/
lemma sum_zeroMult_fiber_le (a : ℝ) (k : ℤ) (u : Finset ℂ)
    (hu : ∀ ρ ∈ u, IsNontrivialZero ρ ∧ ⌈ρ.im - a⌉ = k) :
    ∑ ρ ∈ u, (WeilExplicit.zeroMult ρ : ℝ) ≤ (Ncount (a + k - 1) (a + k) : ℝ) := by
  have hfin := Zeta23.zerosIn_finite (a + k - 1) (a + k)
  have hsub : u ⊆ hfin.toFinset := by
    intro ρ hρ
    obtain ⟨hnt, hk⟩ := hu ρ hρ
    rw [Set.Finite.mem_toFinset]
    refine ⟨hnt, ?_, ?_⟩
    · have := Int.ceil_lt_add_one (ρ.im - a)
      rw [hk] at this
      linarith
    · have := Int.le_ceil (ρ.im - a)
      rw [hk] at this
      linarith
  calc ∑ ρ ∈ u, (WeilExplicit.zeroMult ρ : ℝ) = ∑ ρ ∈ u, (Zeta23.zeroMult ρ : ℝ) :=
        Finset.sum_congr rfl fun ρ hρ => zeroMult_cast_eq (hu ρ hρ).1
    _ ≤ ∑ ρ ∈ hfin.toFinset, (Zeta23.zeroMult ρ : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _
    _ = (Ncount (a + k - 1) (a + k) : ℝ) := by
        unfold Ncount
        rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Nat.cast_sum]

/-! ## C. The weighted count series over Z and its two summable pieces. -/

/-- S1's term: 1/(1 + k^2). -/
def wt (k : ℤ) : ℝ := 1 / (1 + (k : ℝ) ^ 2)

/-- S2's term: log(|k| + 4)/(1 + k^2). -/
def wlog (k : ℤ) : ℝ := Real.log (|(k : ℝ)| + 4) / (1 + (k : ℝ) ^ 2)

lemma wt_nonneg (k : ℤ) : 0 ≤ wt k := by unfold wt; positivity

lemma wlog_nonneg (k : ℤ) : 0 ≤ wlog k := by
  unfold wlog
  apply div_nonneg _ (by positivity)
  exact Real.log_nonneg (by linarith [abs_nonneg (k : ℝ)])

lemma summable_wt : Summable wt := by
  refine Summable.of_norm_bounded_eventually (g := fun k : ℤ => 1 / (k : ℝ) ^ 2)
    (Real.summable_one_div_int_pow.mpr one_lt_two) ?_
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with k hk
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  rw [Real.norm_of_nonneg (wt_nonneg k)]
  unfold wt
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith [sq_nonneg (k : ℝ)])

/-- log(y + 4) ≤ 6 sqrt y for y ≥ 1 (from log t ≤ t - 1 at t = sqrt(y + 4) and y + 4 ≤ 9 y). -/
lemma log_add_four_le {y : ℝ} (hy : 1 ≤ y) : Real.log (y + 4) ≤ 6 * Real.sqrt y := by
  have h1 : Real.log (y + 4) = 2 * Real.log (Real.sqrt (y + 4)) := by
    rw [Real.log_sqrt (by linarith)]; ring
  have h2 : Real.log (Real.sqrt (y + 4)) ≤ Real.sqrt (y + 4) - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith))
  have h3 : Real.sqrt (y + 4) ≤ 3 * Real.sqrt y := by
    rw [show (3 : ℝ) * Real.sqrt y = Real.sqrt (3 ^ 2 * y) by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  linarith

/-- The tail majorant: log(y + 4)/(1 + y^2) ≤ 6 y^{-3/2} for y ≥ 1. -/
lemma log_div_le_rpow {y : ℝ} (hy : 1 ≤ y) :
    Real.log (y + 4) / (1 + y ^ 2) ≤ 6 * y ^ (-(3 / 2 : ℝ)) := by
  have hy0 : 0 < y := by linarith
  have hrpow : y ^ (-(3 / 2 : ℝ)) = 1 / (y * Real.sqrt y) := by
    rw [Real.rpow_neg hy0.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hy0,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
    exact (one_div _).symm
  rw [hrpow, mul_one_div]
  have hsq : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
  have hs0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hlog := log_add_four_le hy
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hprod : Real.log (y + 4) * (y * Real.sqrt y) ≤ 6 * Real.sqrt y * (y * Real.sqrt y) :=
    mul_le_mul_of_nonneg_right hlog (by positivity)
  nlinarith

lemma summable_wlog : Summable wlog := by
  refine Summable.of_norm_bounded_eventually (g := fun k : ℤ => 6 * |(k : ℝ)| ^ (-(3 / 2 : ℝ)))
    ((Real.summable_abs_int_rpow (by norm_num)).mul_left 6) ?_
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with k hk
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    have := Int.one_le_abs hk
    rw [← Int.cast_abs]
    exact_mod_cast this
  rw [Real.norm_of_nonneg (wlog_nonneg k)]
  unfold wlog
  have := log_div_le_rpow hk1
  rwa [sq_abs] at this

/-! ## D. The uniform finite-sum bound and the assembly. -/

/-- The weighted count series' term at centre a: 4/(1 + k^2) * A0 log(|a| + |k| + 4). -/
def wcount (A₀ a : ℝ) (k : ℤ) : ℝ := 4 / (1 + (k : ℝ) ^ 2) * (A₀ * Real.log (|a| + |(k : ℝ)| + 4))

lemma wcount_le (A₀ a : ℝ) (hA₀ : 0 ≤ A₀) (k : ℤ) :
    wcount A₀ a k ≤ 4 * A₀ * (Real.log (2 + |a|) * wt k + wlog k) := by
  unfold wcount wt wlog
  have hsplit : Real.log (|a| + |(k : ℝ)| + 4) ≤ Real.log (2 + |a|) + Real.log (|(k : ℝ)| + 4) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    refine Real.log_le_log (by positivity) ?_
    nlinarith [abs_nonneg a, abs_nonneg (k : ℝ)]
  have h4 : 0 ≤ 4 / (1 + (k : ℝ) ^ 2) := by positivity
  calc 4 / (1 + (k : ℝ) ^ 2) * (A₀ * Real.log (|a| + |(k : ℝ)| + 4))
      ≤ 4 / (1 + (k : ℝ) ^ 2) * (A₀ * (Real.log (2 + |a|) + Real.log (|(k : ℝ)| + 4))) := by
        gcongr
    _ = 4 * A₀ * (Real.log (2 + |a|) * (1 / (1 + (k : ℝ) ^ 2))
          + Real.log (|(k : ℝ)| + 4) / (1 + (k : ℝ) ^ 2)) := by ring

lemma wcount_nonneg (A₀ a : ℝ) (hA₀ : 0 ≤ A₀) (k : ℤ) : 0 ≤ wcount A₀ a k := by
  unfold wcount
  have : 0 ≤ Real.log (|a| + |(k : ℝ)| + 4) :=
    Real.log_nonneg (by linarith [abs_nonneg a, abs_nonneg (k : ℝ)])
  positivity

lemma summable_wbound (A₀ a : ℝ) :
    Summable (fun k : ℤ => 4 * A₀ * (Real.log (2 + |a|) * wt k + wlog k)) :=
  ((summable_wt.mul_left _).add summable_wlog).mul_left _

lemma summable_wcount (A₀ a : ℝ) (hA₀ : 0 ≤ A₀) : Summable (wcount A₀ a) :=
  (summable_wbound A₀ a).of_nonneg_of_le (wcount_nonneg A₀ a hA₀) (wcount_le A₀ a hA₀)

/-- **The uniform finite-sum bound.**  For every Finset u of points and every centre a,
Sum_{rho in u} lcTerm a rho ≤ Sum'_{k : Z} wcount A0 a k. -/
theorem sum_lcTerm_le (A₀ : ℝ) (hA₀ : 0 ≤ A₀)
    (hloc : ∀ t : ℝ, (Ncount t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (a : ℝ) (u : Finset ℂ) :
    ∑ ρ ∈ u, lcTerm a ρ ≤ ∑' k : ℤ, wcount A₀ a k := by
  classical
  set u' : Finset ℂ := u.filter (fun ρ => IsNontrivialZero ρ) with hu'
  have hfilt : ∑ ρ ∈ u, lcTerm a ρ = ∑ ρ ∈ u', lcTerm a ρ := by
    rw [hu', Finset.sum_filter_of_ne]
    intro ρ _ hne
    by_contra h
    exact hne (lcTerm_eq_zero_of_not_nontrivial h)
  set g : ℂ → ℤ := fun ρ => ⌈ρ.im - a⌉ with hg
  set t : Finset ℤ := u'.image g with ht
  have hmaps : ∀ ρ ∈ u', g ρ ∈ t := fun ρ hρ => Finset.mem_image_of_mem g hρ
  rw [hfilt, ← Finset.sum_fiberwise_of_maps_to hmaps]
  -- each fiber
  have hfiber : ∀ k ∈ t, ∑ ρ ∈ u' with g ρ = k, lcTerm a ρ ≤ wcount A₀ a k := by
    intro k _
    have hmem : ∀ ρ ∈ u'.filter (fun ρ => g ρ = k), IsNontrivialZero ρ ∧ ⌈ρ.im - a⌉ = k := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      exact ⟨(Finset.mem_filter.mp hρ.1).2, hρ.2⟩
    calc ∑ ρ ∈ u' with g ρ = k, lcTerm a ρ
        ≤ ∑ ρ ∈ u' with g ρ = k, (WeilExplicit.zeroMult ρ : ℝ) * (4 / (1 + (k : ℝ) ^ 2)) :=
          Finset.sum_le_sum fun ρ hρ => lcTerm_le_fiber_weight a (hmem ρ hρ).2
      _ = (4 / (1 + (k : ℝ) ^ 2)) * ∑ ρ ∈ u' with g ρ = k, (WeilExplicit.zeroMult ρ : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun ρ _ => by ring
      _ ≤ (4 / (1 + (k : ℝ) ^ 2)) * (Ncount (a + k - 1) (a + k) : ℝ) :=
          mul_le_mul_of_nonneg_left (sum_zeroMult_fiber_le a k _ hmem) (by positivity)
      _ ≤ (4 / (1 + (k : ℝ) ^ 2)) * (A₀ * Real.log (|a + k - 1| + 3)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have := hloc (a + k - 1)
          rwa [show a + k - 1 + 1 = a + k by ring] at this
      _ ≤ wcount A₀ a k := by
          unfold wcount
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hA₀) (by positivity)
          refine Real.log_le_log (by positivity) ?_
          have h1 : |a + k - 1| ≤ |a| + |(k : ℝ)| + 1 := by
            refine abs_le.mpr ⟨?_, ?_⟩
            · linarith [neg_abs_le a, neg_abs_le (k : ℝ)]
            · linarith [le_abs_self a, le_abs_self (k : ℝ)]
          linarith
  calc ∑ k ∈ t, ∑ ρ ∈ u' with g ρ = k, lcTerm a ρ ≤ ∑ k ∈ t, wcount A₀ a k :=
        Finset.sum_le_sum hfiber
    _ ≤ ∑' k : ℤ, wcount A₀ a k :=
        (summable_wcount A₀ a hA₀).sum_le_tsum t fun k _ => wcount_nonneg A₀ a hA₀ k

/-- The two absolute constants. -/
def S1 : ℝ := ∑' k : ℤ, wt k
def S2 : ℝ := ∑' k : ℤ, wlog k

lemma S1_nonneg : 0 ≤ S1 := tsum_nonneg wt_nonneg
lemma S2_nonneg : 0 ≤ S2 := tsum_nonneg wlog_nonneg

lemma tsum_wcount_le (A₀ a : ℝ) (hA₀ : 0 ≤ A₀) :
    ∑' k : ℤ, wcount A₀ a k ≤ 4 * A₀ * (Real.log (2 + |a|) * S1 + S2) := by
  unfold S1 S2
  refine ((summable_wcount A₀ a hA₀).tsum_le_tsum (wcount_le A₀ a hA₀) (summable_wbound A₀ a)).trans ?_
  rw [tsum_mul_left, Summable.tsum_add (summable_wt.mul_left _) summable_wlog, tsum_mul_left]

/-- **LocalCountSum, discharged.** -/
theorem local_count_sum : RvMBridge22.LocalCountSum := by
  obtain ⟨A₀, hA₀1, hloc⟩ := Zeta23.RvM.zeta_local_zero_count
  have hA₀ : 0 ≤ A₀ := by linarith
  refine ⟨4 * A₀ * (S1 + S2), fun a => ?_⟩
  have hL : 0 ≤ Real.log (2 + |a|) := Real.log_nonneg (by linarith [abs_nonneg a])
  have hS1 := S1_nonneg
  have hS2 := S2_nonneg
  calc ∑' ρ : ℂ, lcTerm a ρ ≤ ∑' k : ℤ, wcount A₀ a k :=
        Real.tsum_le_of_sum_le (fun ρ => lcTerm_nonneg a ρ) (sum_lcTerm_le A₀ hA₀ hloc a)
    _ ≤ 4 * A₀ * (Real.log (2 + |a|) * S1 + S2) := tsum_wcount_le A₀ a hA₀
    _ ≤ 4 * A₀ * (S1 + S2) * (1 + Real.log (2 + |a|)) := by nlinarith [mul_nonneg hL hS2, mul_nonneg hA₀ (mul_nonneg hL hS2), mul_nonneg hA₀ hS1]

/-! ## E. Consequences on E6Bridge22's assembly: everything now rests on StripDerivBound. -/

theorem xiDiffExtGrowthRight_of_strip (h2 : RvMBridge22.StripDerivBound) :
    RvMBridge20.XiDiffExtGrowthRight :=
  RvMBridge22.xiDiffExtGrowthRight_of_two local_count_sum h2

theorem xiLogDerivDerivEq_of_strip (h2 : RvMBridge22.StripDerivBound) :
    RvMBridge18.XiLogDerivDerivEq :=
  RvMBridge22.xiLogDerivDerivEq_of_two local_count_sum h2

end RvMBridge23
