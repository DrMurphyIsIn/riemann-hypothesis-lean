/-
  KWin2_Round -- a ROUNDED positive-semidefiniteness certificate for the exact head matrices
  (rvm_bridge island, 2026-09-24).

  conjecture1_proved = False.  Pure linear algebra over ℚ / ℝ; nothing about zeros.

  WHY.  The exact head matrix of a window past L = 9/20 has entries of ~1200 digits, and KWin's
  exact LDL^T (KWin.psdCert) lets the Schur complements grow to tens of thousands of digits; that is
  what dominates the kernel time.  `psdCertR A n R` instead floors every entry at 10^-R and shifts
  the diagonal down by n 10^-R, then runs the SAME exact LDL^T checker on these short rationals.

  PROVED HERE (`headPSD_of_psdCertR`): psdCertR A n R = true implies
      0 <= sum_{j,k < n} x_j x_k A_jk   for every real x,
  because the rounding defect E = A - floor(A) has 0 <= E_jk < 10^-R, so
  |x^T E x| <= 10^-R (sum |x_j|)^2 <= n 10^-R sum x_j^2 (Cauchy-Schwarz), which the diagonal shift
  pays for.  `HeadPSD A n` is the semantic statement consumed by KWin2_Head / KWin2_Tail; both the
  exact certificate (`headPSD_of_psdCert`) and the rounded one (`headPSD_of_psdCertR`) produce it.
  No `sorry`.
-/
import KWin2_Data

open Finset

namespace KWin2
open KWin

/-- The semantic PSD statement of an `n x n` matrix given as a list of rows. -/
def HeadPSD (A : List (List ℚ)) (n : ℕ) : Prop :=
  ∀ x : ℕ → ℝ, 0 ≤ ∑ j ∈ range n, ∑ k ∈ range n, x j * x k * ((mget A j k : ℚ) : ℝ)

theorem headPSD_of_psdCert {A : List (List ℚ)} {n : ℕ} (h : psdCert A n = true) : HeadPSD A n :=
  fun x => psdCert_sound h x

/-- Floor every entry at `10^-R` and shift the diagonal down by `n 10^-R`. -/
def roundShift (A : List (List ℚ)) (n R : ℕ) : List (List ℚ) :=
  (List.range n).map (fun j => (List.range n).map (fun k =>
    floorR (mget A j k) R - (if j = k then (n : ℚ) / 10 ^ R else 0)))

/-- The rounded certificate: KWin's exact LDL^T checker on the rounded, shifted matrix. -/
def psdCertR (A : List (List ℚ)) (n R : ℕ) : Bool := psdCert (roundShift A n R) n

lemma sum_abs_sq_le (n : ℕ) (x : ℕ → ℝ) :
    (∑ j ∈ range n, |x j|) ^ 2 ≤ (n : ℝ) * ∑ j ∈ range n, x j ^ 2 := by
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq (range n) (fun _ => (1 : ℝ)) (fun j => |x j|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, sq_abs]
    at h2
  exact h2

theorem headPSD_of_psdCertR {A : List (List ℚ)} {n R : ℕ} (h : psdCertR A n R = true) :
    HeadPSD A n := by
  intro x
  have hB := psdCert_sound h x
  have hBe : ∀ j ∈ range n, ∀ k ∈ range n, ((mget (roundShift A n R) j k : ℚ) : ℝ)
      = ((floorR (mget A j k) R : ℚ) : ℝ) - (if j = k then (n : ℝ) / 10 ^ R else 0) := by
    intro j hj k hk
    unfold roundShift
    rw [mget_map_range _ (Finset.mem_range.mp hj) (Finset.mem_range.mp hk)]
    push_cast
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => by rw [hBe j hj k hk]] at hB
  -- the defect
  set e : ℕ → ℕ → ℝ := fun j k => ((mget A j k : ℚ) : ℝ) - ((floorR (mget A j k) R : ℚ) : ℝ) with he
  have he0 : ∀ j k, 0 ≤ e j k := fun j k => by
    rw [he]; simp only
    have := floorR_le (mget A j k) R
    have h' : ((floorR (mget A j k) R : ℚ) : ℝ) ≤ ((mget A j k : ℚ) : ℝ) := by exact_mod_cast this
    linarith
  have he1 : ∀ j k, e j k ≤ 1 / 10 ^ R := fun j k => by
    rw [he]; simp only
    have := sub_floorR_le (mget A j k) R
    have h' : (((mget A j k - floorR (mget A j k) R : ℚ)) : ℝ) ≤ ((1 / 10 ^ R : ℚ) : ℝ) := by
      exact_mod_cast this
    push_cast at h'
    linarith
  have hsplit : ∑ j ∈ range n, ∑ k ∈ range n, x j * x k * ((mget A j k : ℚ) : ℝ)
      = ∑ j ∈ range n, ∑ k ∈ range n, x j * x k
          * (((floorR (mget A j k) R : ℚ) : ℝ) - (if j = k then (n : ℝ) / 10 ^ R else 0))
        + (n : ℝ) / 10 ^ R * ∑ j ∈ range n, x j ^ 2
        + ∑ j ∈ range n, ∑ k ∈ range n, x j * x k * e j k := by
    have hdiag : ∑ j ∈ range n, ∑ k ∈ range n, x j * x k * (if j = k then (n : ℝ) / 10 ^ R else 0)
        = (n : ℝ) / 10 ^ R * ∑ j ∈ range n, x j ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.sum_eq_single j]
      · simp; ring
      · intro k _ hkj; simp [Ne.symm hkj]
      · intro hj'; exact absurd hj hj'
    rw [← hdiag, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [he]; simp only
    ring
  have hE : -((n : ℝ) / 10 ^ R * ∑ j ∈ range n, x j ^ 2)
      ≤ ∑ j ∈ range n, ∑ k ∈ range n, x j * x k * e j k := by
    have h1 : ∀ j ∈ range n, ∀ k ∈ range n, -(|x j| * |x k| * (1 / 10 ^ R)) ≤ x j * x k * e j k := by
      intro j _ k _
      have hab : |x j * x k * e j k| ≤ |x j| * |x k| * (1 / 10 ^ R) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (he0 j k)]
        exact mul_le_mul_of_nonneg_left (he1 j k) (by positivity)
      exact (neg_le_neg hab).trans (neg_abs_le _)
    have h2 := Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => h1 j hj k hk
    have h3 : ∑ j ∈ range n, ∑ k ∈ range n, -(|x j| * |x k| * (1 / 10 ^ R))
        = -((1 / 10 ^ R) * (∑ j ∈ range n, |x j|) ^ 2) := by
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [h3] at h2
    have h4 := sum_abs_sq_le n x
    have h5 : (1 / 10 ^ R : ℝ) * (∑ j ∈ range n, |x j|) ^ 2
        ≤ (n : ℝ) / 10 ^ R * ∑ j ∈ range n, x j ^ 2 := by
      have hp : (0 : ℝ) ≤ 1 / 10 ^ R := by positivity
      calc (1 / 10 ^ R : ℝ) * (∑ j ∈ range n, |x j|) ^ 2
          ≤ (1 / 10 ^ R) * ((n : ℝ) * ∑ j ∈ range n, x j ^ 2) := mul_le_mul_of_nonneg_left h4 hp
        _ = (n : ℝ) / 10 ^ R * ∑ j ∈ range n, x j ^ 2 := by ring
    linarith
  rw [hsplit]
  linarith

end KWin2
