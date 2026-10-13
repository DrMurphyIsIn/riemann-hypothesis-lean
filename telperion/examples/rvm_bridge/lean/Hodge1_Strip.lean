/-
  Hodge1_Strip -- HODGE-1 Phase 1, steps (a) and (b) of the one-prime reduction (2026-10-12,
  HODGE-1 plan, "Phase 1"; structure notes, Candidate 2a/2b; both unpublished).

  On the window 2L <= log 3 the prime side of the autocorrelation f = g * g~ of a test g with
  tsupport g ⊆ [-L, L] is the n = 2 term alone, and that term is controlled by the L^2 mass of g
  on two strips:

    (b) primeSide_autocorr_eq_two:   primeSide f = (log 2 / sqrt 2) (f(log 2) + f(-log 2))
        (Λ(2) = log 2; n = 0, 1 carry Λ = 0; n >= 3 has log n >= log 3 >= 2L, outside the
        support of f, with the boundary point killed by continuity, as in E6Bridge31 Stage 0).

    (a) re_autocorr_pair_le_stripEnergy:  for L < log 2,
          Re (f(log 2) + f(-log 2)) <= ∫_S |g|^2,   S = [-L, L - log 2] ∪ [log 2 - L, L].
        f(b) = ∫ g(v) conj g(v - b) dv.  The integrand vanishes unless v and v - b both lie in
        [-L, L]; for b = log 2 that forces v ∈ [log 2 - L, L] and v - b ∈ [-L, L - log 2], and
        there |g(v)| |g(v - b)| <= (|g(v)|^2 + |g(v - b)|^2) / 2.  Translating the second term
        back, |f(log 2)| <= (∫_right |g|^2 + ∫_left |g|^2) / 2, and symmetrically for b = -log 2.
        L < log 2 makes the strips disjoint (L - log 2 < 0 < log 2 - L), so the two strip
        integrals add up to ∫_S.  No conjugate symmetry f(-x) = conj f(x) is needed: each of the
        two values is bounded by its own modulus.

  Nothing here involves the zeros; no RH progress is claimed.  conjecture1_proved = False.
-/
import E6Bridge31

open Zeta23 Complex MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Hodge1
open WeilExplicit

/-! ## A. The two strips. -/

/-- S = [-L, L - log 2] ∪ [log 2 - L, L]: where g and its shift by ±log 2 can overlap. -/
def stripSet (L : ℝ) : Set ℝ :=
  Set.Icc (-L) (L - Real.log 2) ∪ Set.Icc (Real.log 2 - L) L

lemma measurableSet_stripSet (L : ℝ) : MeasurableSet (stripSet L) :=
  measurableSet_Icc.union measurableSet_Icc

lemma disjoint_strips {L : ℝ} (hL : L < Real.log 2) :
    Disjoint (Set.Icc (-L) (L - Real.log 2)) (Set.Icc (Real.log 2 - L) L) := by
  refine Set.disjoint_left.mpr fun x hx hy => ?_
  rw [Set.mem_Icc] at hx hy
  linarith [hx.2, hy.1]

/-- On the window 2L <= log 3 the strips are disjoint: log 3 < log 4 = 2 log 2. -/
lemma lt_log_two_of_le_log_three {L : ℝ} (hL : 2 * L ≤ Real.log 3) : L < Real.log 2 := by
  have h34 : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  linarith

/-! ## B. The shift bound. -/

/-- Pointwise: |g(v)| |g(v - b)| <= (1_A |g|^2 (v) + 1_B |g|^2 (v - b)) / 2 whenever every v with
v, v - b ∈ [-L, L] has v ∈ A and v - b ∈ B. -/
lemma norm_mul_norm_shift_le {g : ℝ → ℂ} {L b : ℝ} {A B : Set ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L)
    (hAB : ∀ v, v ∈ Set.Icc (-L) L → v - b ∈ Set.Icc (-L) L → v ∈ A ∧ v - b ∈ B) (v : ℝ) :
    ‖g v‖ * ‖g (v - b)‖
      ≤ (1 / 2) * (A.indicator (fun u => ‖g u‖ ^ 2) v + B.indicator (fun u => ‖g u‖ ^ 2) (v - b)) := by
  have hnn : 0 ≤ A.indicator (fun u => ‖g u‖ ^ 2) v + B.indicator (fun u => ‖g u‖ ^ 2) (v - b) :=
    add_nonneg (Set.indicator_nonneg (fun u _ => by positivity) v)
      (Set.indicator_nonneg (fun u _ => by positivity) (v - b))
  by_cases h1 : g v = 0
  · rw [h1, norm_zero, zero_mul]
    positivity
  by_cases h2 : g (v - b) = 0
  · rw [h2, norm_zero, mul_zero]
    positivity
  have hv : v ∈ Set.Icc (-L) L := hsupp (subset_tsupport g (Function.mem_support.mpr h1))
  have hvb : v - b ∈ Set.Icc (-L) L := hsupp (subset_tsupport g (Function.mem_support.mpr h2))
  obtain ⟨hA, hB⟩ := hAB v hv hvb
  rw [Set.indicator_of_mem hA, Set.indicator_of_mem hB]
  nlinarith [sq_nonneg (‖g v‖ - ‖g (v - b)‖)]

/-- |f(b)| <= (∫_A |g|^2 + ∫_B |g|^2) / 2 under the same overlap condition. -/
lemma norm_autocorr_le {g : ℝ → ℂ} (hg : IsWeilTest g) {L b : ℝ} {A B : Set ℝ}
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hsupp : tsupport g ⊆ Set.Icc (-L) L)
    (hAB : ∀ v, v ∈ Set.Icc (-L) L → v - b ∈ Set.Icc (-L) L → v ∈ A ∧ v - b ∈ B) :
    ‖autocorr g b‖ ≤ (1 / 2) * ((∫ u in A, ‖g u‖ ^ 2) + ∫ u in B, ‖g u‖ ^ 2) := by
  have hI := RvMBridge31.integrable_normSq hg
  have hIA : Integrable (A.indicator fun u => ‖g u‖ ^ 2) := hI.indicator hAm
  have hIB : Integrable (fun v => B.indicator (fun u => ‖g u‖ ^ 2) (v - b)) :=
    (hI.indicator hBm).comp_sub_right b
  calc ‖autocorr g b‖
      ≤ ∫ v : ℝ, ‖g v * (starRingEnd ℂ) (g (v - b))‖ := norm_integral_le_integral_norm _
    _ = ∫ v : ℝ, ‖g v‖ * ‖g (v - b)‖ := by
        congr 1
        funext v
        rw [norm_mul, Complex.norm_conj]
    _ ≤ ∫ v : ℝ, (1 / 2) * (A.indicator (fun u => ‖g u‖ ^ 2) v
          + B.indicator (fun u => ‖g u‖ ^ 2) (v - b)) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => by positivity)
          ((hIA.add hIB).const_mul _)
          (Filter.Eventually.of_forall fun v => norm_mul_norm_shift_le hsupp hAB v)
    _ = (1 / 2) * ((∫ u in A, ‖g u‖ ^ 2) + ∫ u in B, ‖g u‖ ^ 2) := by
        rw [integral_const_mul, integral_add hIA hIB, integral_indicator hAm,
          integral_sub_right_eq_self (fun v => B.indicator (fun u => ‖g u‖ ^ 2) v) b,
          integral_indicator hBm]

/-! ## C. Step (a): the strip lemma. -/

/-- The L^2 mass of g on the two strips. -/
def stripEnergy (g : ℝ → ℂ) (L : ℝ) : ℝ := ∫ u in stripSet L, ‖g u‖ ^ 2

/-- (a) THE STRIP LEMMA: for L < log 2, Re (f(log 2) + f(-log 2)) <= ∫_S |g|^2, f = autocorr g. -/
theorem re_autocorr_pair_le_stripEnergy {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) (hL : L < Real.log 2) :
    (autocorr g (Real.log 2) + autocorr g (-Real.log 2)).re ≤ stripEnergy g L := by
  set a := Real.log 2
  set Lft := Set.Icc (-L) (L - a)
  set Rgt := Set.Icc (a - L) L
  have hp : ‖autocorr g a‖ ≤ (1 / 2) * ((∫ u in Rgt, ‖g u‖ ^ 2) + ∫ u in Lft, ‖g u‖ ^ 2) :=
    norm_autocorr_le hg measurableSet_Icc measurableSet_Icc hsupp fun v hv hvb => by
      simp only [Lft, Rgt, Set.mem_Icc] at hv hvb ⊢
      constructor <;> constructor <;> linarith
  have hm : ‖autocorr g (-a)‖ ≤ (1 / 2) * ((∫ u in Lft, ‖g u‖ ^ 2) + ∫ u in Rgt, ‖g u‖ ^ 2) :=
    norm_autocorr_le hg measurableSet_Icc measurableSet_Icc hsupp fun v hv hvb => by
      simp only [Lft, Rgt, Set.mem_Icc] at hv hvb ⊢
      constructor <;> constructor <;> linarith
  have hI := RvMBridge31.integrable_normSq hg
  have hS : stripEnergy g L = (∫ u in Lft, ‖g u‖ ^ 2) + ∫ u in Rgt, ‖g u‖ ^ 2 :=
    setIntegral_union (disjoint_strips hL) measurableSet_Icc hI.integrableOn hI.integrableOn
  rw [hS, Complex.add_re]
  linarith [Complex.re_le_norm (autocorr g a), Complex.re_le_norm (autocorr g (-a))]

/-! ## D. Step (b): on the window 2L <= log 3 the prime side is the n = 2 term. -/

/-- (b) For 2L <= log 3: primeSide (autocorr g) = (log 2 / sqrt 2) (f(log 2) + f(-log 2)). -/
theorem primeSide_autocorr_eq_two {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) (hL : 2 * L ≤ Real.log 3) :
    primeSide (autocorr g)
      = ((Real.log 2 / Real.sqrt 2 : ℝ) : ℂ)
          * (autocorr g (Real.log 2) + autocorr g (-Real.log 2)) := by
  have hf : Continuous (autocorr g) := (RvMBridge5.isWeilTest_autocorr hg).1.continuous
  have hts := RvMBridge31.tsupport_autocorr_subset hsupp
  unfold primeSide
  rw [tsum_eq_single 2]
  · rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    push_cast
    rfl
  · intro n hn2
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · simp
      · simp [ArithmeticFunction.vonMangoldt_apply_one]
    · have hn3 : 3 ≤ n := by omega
      have hlog : Real.log 3 ≤ Real.log n :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hn3)
      rw [RvMBridge31.eq_zero_of_tsupport_subset_Icc_right hf hts (by linarith),
        RvMBridge31.eq_zero_of_tsupport_subset_Icc_left hf hts (by linarith)]
      simp

end Hodge1
