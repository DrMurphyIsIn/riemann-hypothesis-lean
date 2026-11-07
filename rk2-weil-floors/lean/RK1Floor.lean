import Mathlib

/-!
# RK-1: kernel lemmas for interval-box certificates of Weil-form heads

Two generic facts about real matrices G known only through an outward-rounded integer box
|G i j - M i j / S| ≤ w / S (the box is an Arb enclosure of the head, carried as a hypothesis):

* `floor_of_rowsum`: a Cholesky-residual / Gershgorin row-sum check on integers gives a uniform
  lower bound ((c - ρ)/S) Σ x² ≤ xᵀ G x for EVERY G in the box (a quantitative positive floor);
* `neg_of_box`: an integer vector v with vᵀMv + w (Σ|v|)² < 0 gives vᵀ G v < 0 for every G in
  the box (a certified negative Rayleigh quotient: the head is not positive semidefinite).

Instances discharge the integer hypotheses with `decide +kernel`.  Finite linear algebra only;
nothing here says anything about zeta.  conjecture1_proved = False.
-/

namespace RK1

open Finset

/-- Dot product of integer lists (stops at the shorter list). -/
def dotL : List ℤ → List ℤ → ℤ
  | [], _ => 0
  | _ :: _, [] => 0
  | a :: as, b :: bs => a * b + dotL as bs

theorem dotL_comm : ∀ a b : List ℤ, dotL a b = dotL b a
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by simp only [dotL, mul_comm a b, dotL_comm as bs]

theorem dotL_eq_sum : ∀ (m : ℕ) (a b : List ℤ), a.length ≤ m →
    dotL a b = ∑ k : Fin m, a.getD k 0 * b.getD k 0
  | 0, [], b, _ => by simp [dotL]
  | 0, _ :: _, _, h => by simp at h
  | m + 1, [], b, _ => by simp [dotL]
  | m + 1, _ :: _, [], _ => by simp [dotL]
  | m + 1, x :: a, y :: b, h => by
      rw [Fin.sum_univ_succ]
      simp only [dotL, Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ]
      rw [dotL_eq_sum m a b (by simp at h; omega)]

/-- A Gram form Σᵢⱼ xᵢ (Σₖ aᵢₖ aⱼₖ) xⱼ is a sum of squares. -/
theorem gram_nonneg {m : ℕ} (a : Fin m → Fin m → ℝ) (x : Fin m → ℝ) :
    0 ≤ ∑ i, ∑ j, x i * (∑ k, a i k * a j k) * x j := by
  have h : ∑ i, ∑ j, x i * (∑ k, a i k * a j k) * x j
      = ∑ k, (∑ i, x i * a i k) * (∑ j, x j * a j k) := by
    calc ∑ i, ∑ j, x i * (∑ k, a i k * a j k) * x j
        = ∑ i, ∑ j, ∑ k, (x i * a i k) * (x j * a j k) := by
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
          rw [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun k _ => by ring)
      _ = ∑ i, ∑ k, ∑ j, (x i * a i k) * (x j * a j k) := by
          exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = ∑ k, ∑ i, ∑ j, (x i * a i k) * (x j * a j k) := Finset.sum_comm
      _ = ∑ k, (∑ i, x i * a i k) * (∑ j, x j * a j k) := by
          exact Finset.sum_congr rfl (fun k _ => (Finset.sum_mul_sum _ _ _ _).symm)
  rw [h]
  exact Finset.sum_nonneg (fun k _ => mul_self_nonneg _)

set_option maxHeartbeats 2000000 in
/-- **Floor on an interval box.**  If the integer residual of the rounded Cholesky factor has row
sums Σⱼ |Mᵢⱼ - c δᵢⱼ - (LLᵀ)ᵢⱼ| + m w ≤ ρ, then every real G within w/S of M/S satisfies
((c - ρ)/S) Σ xᵢ² ≤ xᵀ G x. -/
theorem floor_of_rowsum {m : ℕ} (G : Fin m → Fin m → ℝ) (Mz : Fin m → Fin m → ℤ)
    (Lr : Fin m → List ℤ) (hlen : ∀ i, (Lr i).length ≤ m)
    (c w ρ : ℤ) (S : ℝ) (hS : 0 < S) (hw : 0 ≤ w)
    (hbox : ∀ i j, |G i j - (Mz i j : ℝ) / S| ≤ (w : ℝ) / S)
    (hsym : ∀ i j, Mz i j = Mz j i)
    (hrow : ∀ i, ∑ j, |Mz i j - (if i = j then c else 0) - dotL (Lr i) (Lr j)| + (m : ℤ) * w ≤ ρ) :
    ∀ x : Fin m → ℝ, ((c - ρ : ℤ) : ℝ) / S * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, x i * G i j * x j := by
  intro x
  -- integer pieces
  set d : Fin m → Fin m → ℤ := fun i j => if i = j then c else 0 with hd
  set P : Fin m → Fin m → ℤ := fun i j => dotL (Lr i) (Lr j) with hP
  set e : Fin m → Fin m → ℤ := fun i j => |Mz i j - d i j - P i j| + w with he
  have he_nn : ∀ i j, (0 : ℝ) ≤ (e i j : ℝ) := fun i j => by
    have : (0 : ℤ) ≤ e i j := add_nonneg (abs_nonneg _) hw
    exact_mod_cast this
  have he_sym : ∀ i j, e i j = e j i := by
    intro i j
    simp only [he, hd, hP, hsym i j, dotL_comm (Lr i) (Lr j), eq_comm (a := i)]
  have hrowe : ∀ i, ∑ j, (e i j : ℝ) ≤ (ρ : ℝ) := by
    intro i
    have h1 : ∑ j, e i j = ∑ j, |Mz i j - (if i = j then c else 0) - dotL (Lr i) (Lr j)|
        + (m : ℤ) * w := by
      simp only [he, hd, hP, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have h2 : ∑ j, e i j ≤ ρ := by rw [h1]; exact hrow i
    exact_mod_cast h2
  have hcole : ∀ j, ∑ i, (e i j : ℝ) ≤ (ρ : ℝ) := by
    intro j
    have : ∑ i, (e i j : ℝ) = ∑ i, (e j i : ℝ) :=
      Finset.sum_congr rfl (fun i _ => by rw [he_sym i j])
    rw [this]; exact hrowe j
  -- the residual E = G - (d + P)/S is entrywise below e/S
  have hE : ∀ i j, |G i j - ((d i j : ℝ) + (P i j : ℝ)) / S| ≤ (e i j : ℝ) / S := by
    intro i j
    have hsplit : G i j - ((d i j : ℝ) + (P i j : ℝ)) / S
        = (G i j - (Mz i j : ℝ) / S) + ((Mz i j - d i j - P i j : ℤ) : ℝ) / S := by
      push_cast; ring
    rw [hsplit]
    calc |(G i j - (Mz i j : ℝ) / S) + ((Mz i j - d i j - P i j : ℤ) : ℝ) / S|
        ≤ |G i j - (Mz i j : ℝ) / S| + |((Mz i j - d i j - P i j : ℤ) : ℝ) / S| := abs_add_le _ _
      _ ≤ (w : ℝ) / S + ((|Mz i j - d i j - P i j| : ℤ) : ℝ) / S := by
          gcongr
          · exact hbox i j
          · rw [abs_div, abs_of_pos hS, Int.cast_abs]
      _ = (e i j : ℝ) / S := by simp only [he]; push_cast; ring
  -- decomposition of the form
  set E : Fin m → Fin m → ℝ := fun i j => G i j - ((d i j : ℝ) + (P i j : ℝ)) / S with hEdef
  have hdecomp : ∑ i, ∑ j, x i * G i j * x j
      = (c : ℝ) / S * ∑ i, x i ^ 2
        + (1 / S) * ∑ i, ∑ j, x i * (∑ k : Fin m, ((Lr i).getD k 0 : ℝ) * ((Lr j).getD k 0 : ℝ)) * x j
        + ∑ i, ∑ j, x i * E i j * x j := by
    have hPsum : ∀ i j, (P i j : ℝ) = ∑ k : Fin m, ((Lr i).getD k 0 : ℝ) * ((Lr j).getD k 0 : ℝ) := by
      intro i j
      simp only [hP]
      rw [dotL_eq_sum m (Lr i) (Lr j) (hlen i)]
      push_cast; rfl
    have hdiag : ∑ i, ∑ j, x i * ((d i j : ℝ) / S) * x j = (c : ℝ) / S * ∑ i, x i ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_eq_single i]
      · simp only [hd, ite_true]; ring
      · intro j _ hji
        simp [hd, Ne.symm hji]
      · intro h; exact absurd (Finset.mem_univ i) h
    calc ∑ i, ∑ j, x i * G i j * x j
        = ∑ i, ∑ j, (x i * ((d i j : ℝ) / S) * x j
            + (1 / S) * (x i * (P i j : ℝ) * x j) + x i * E i j * x j) := by
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
          simp only [hEdef]; ring
      _ = ∑ i, ∑ j, x i * ((d i j : ℝ) / S) * x j
            + (1 / S) * ∑ i, ∑ j, x i * (P i j : ℝ) * x j + ∑ i, ∑ j, x i * E i j * x j := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ = _ := by
          have hPpart : ∑ i, ∑ j, x i * (P i j : ℝ) * x j
              = ∑ i, ∑ j, x i * (∑ k : Fin m, ((Lr i).getD k 0 : ℝ) * ((Lr j).getD k 0 : ℝ)) * x j :=
            Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [hPsum i j]))
          rw [hdiag, hPpart]
  -- the Gram part is non-negative
  have hgram := gram_nonneg (fun (i k : Fin m) => ((Lr i).getD k 0 : ℝ)) x
  -- the residual part is at least -(ρ/S) Σ x²
  have hres : -((ρ : ℝ) / S * ∑ i, x i ^ 2) ≤ ∑ i, ∑ j, x i * E i j * x j := by
    have hterm : ∀ i j, -((x i ^ 2 * (e i j : ℝ) + x j ^ 2 * (e i j : ℝ)) / (2 * S))
        ≤ x i * E i j * x j := by
      intro i j
      have hEij : |E i j| ≤ (e i j : ℝ) / S := hE i j
      have hab : |x i| * |x j| ≤ (x i ^ 2 + x j ^ 2) / 2 := by
        nlinarith [sq_nonneg (|x i| - |x j|), sq_abs (x i), sq_abs (x j)]
      have h1 : |x i * E i j * x j| ≤ (x i ^ 2 + x j ^ 2) / 2 * ((e i j : ℝ) / S) := by
        rw [abs_mul, abs_mul]
        have hes : 0 ≤ (e i j : ℝ) / S := div_nonneg (he_nn i j) hS.le
        calc |x i| * |E i j| * |x j| = (|x i| * |x j|) * |E i j| := by ring
          _ ≤ (x i ^ 2 + x j ^ 2) / 2 * ((e i j : ℝ) / S) :=
              mul_le_mul hab hEij (abs_nonneg _) (by positivity)
      have h2 : (x i ^ 2 + x j ^ 2) / 2 * ((e i j : ℝ) / S)
          = (x i ^ 2 * (e i j : ℝ) + x j ^ 2 * (e i j : ℝ)) / (2 * S) := by
        field_simp
      rw [← h2]
      exact neg_le_of_abs_le h1
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) =>
      Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hterm i j))
    refine le_trans ?_ hsum
    have hA : ∑ i, ∑ j, x i ^ 2 * (e i j : ℝ) ≤ (ρ : ℝ) * ∑ i, x i ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [← Finset.mul_sum]
      nlinarith [hrowe i, sq_nonneg (x i)]
    have hB : ∑ i, ∑ j, x j ^ 2 * (e i j : ℝ) ≤ (ρ : ℝ) * ∑ i, x i ^ 2 := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_le_sum (fun j _ => ?_)
      rw [← Finset.mul_sum]
      nlinarith [hcole j, sq_nonneg (x j)]
    have hsplit : ∑ i, ∑ j, -((x i ^ 2 * (e i j : ℝ) + x j ^ 2 * (e i j : ℝ)) / (2 * S))
        = -((∑ i, ∑ j, x i ^ 2 * (e i j : ℝ) + ∑ i, ∑ j, x j ^ 2 * (e i j : ℝ)) / (2 * S)) := by
      simp only [Finset.sum_neg_distrib, ← Finset.sum_div, Finset.sum_add_distrib]
    rw [hsplit, neg_le_neg_iff, div_le_iff₀ (by positivity)]
    have hr : ((ρ : ℝ) / S * ∑ i, x i ^ 2) * (2 * S) = 2 * ((ρ : ℝ) * ∑ i, x i ^ 2) := by
      field_simp
    rw [hr]
    linarith [hA, hB]
  -- assemble
  rw [hdecomp]
  have hgS : 0 ≤ (1 / S) * ∑ i, ∑ j, x i * (∑ k : Fin m, ((Lr i).getD k 0 : ℝ) * ((Lr j).getD k 0 : ℝ)) * x j :=
    mul_nonneg (by positivity) hgram
  have hcast : ((c - ρ : ℤ) : ℝ) / S * ∑ i, x i ^ 2
      = (c : ℝ) / S * ∑ i, x i ^ 2 - (ρ : ℝ) / S * ∑ i, x i ^ 2 := by push_cast; ring
  rw [hcast]
  linarith

/-- **Certified negative direction on an interval box.**  If vᵀ M v + w (Σ|vᵢ|)² < 0 in integers,
every real G within w/S of M/S has vᵀ G v < 0, hence is not positive semidefinite. -/
theorem neg_of_box {m : ℕ} (G : Fin m → Fin m → ℝ) (Mz : Fin m → Fin m → ℤ) (v : Fin m → ℤ)
    (w : ℤ) (S : ℝ) (hS : 0 < S)
    (hbox : ∀ i j, |G i j - (Mz i j : ℝ) / S| ≤ (w : ℝ) / S)
    (hneg : ∑ i, ∑ j, v i * Mz i j * v j + w * (∑ i, |v i|) ^ 2 < 0) :
    ∑ i, ∑ j, (v i : ℝ) * G i j * (v j : ℝ) < 0 := by
  have hterm : ∀ i j, (v i : ℝ) * G i j * (v j : ℝ)
      ≤ (v i : ℝ) * ((Mz i j : ℝ) / S) * (v j : ℝ) + |(v i : ℝ)| * |(v j : ℝ)| * ((w : ℝ) / S) := by
    intro i j
    have h1 : (v i : ℝ) * G i j * (v j : ℝ) - (v i : ℝ) * ((Mz i j : ℝ) / S) * (v j : ℝ)
        = (v i : ℝ) * (G i j - (Mz i j : ℝ) / S) * (v j : ℝ) := by ring
    have h2 : (v i : ℝ) * (G i j - (Mz i j : ℝ) / S) * (v j : ℝ)
        ≤ |(v i : ℝ)| * |(v j : ℝ)| * ((w : ℝ) / S) := by
      have := le_abs_self ((v i : ℝ) * (G i j - (Mz i j : ℝ) / S) * (v j : ℝ))
      refine le_trans this ?_
      rw [abs_mul, abs_mul]
      calc |(v i : ℝ)| * |G i j - (Mz i j : ℝ) / S| * |(v j : ℝ)|
          = |(v i : ℝ)| * |(v j : ℝ)| * |G i j - (Mz i j : ℝ) / S| := by ring
        _ ≤ |(v i : ℝ)| * |(v j : ℝ)| * ((w : ℝ) / S) :=
            mul_le_mul_of_nonneg_left (hbox i j) (by positivity)
    linarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hterm i j))
  refine lt_of_le_of_lt hsum ?_
  have hR : ∑ i, ∑ j, ((v i : ℝ) * ((Mz i j : ℝ) / S) * (v j : ℝ)
        + |(v i : ℝ)| * |(v j : ℝ)| * ((w : ℝ) / S))
      = (((∑ i, ∑ j, v i * Mz i j * v j + w * (∑ i, |v i|) ^ 2 : ℤ)) : ℝ) / S := by
    push_cast
    rw [sq, Finset.sum_mul_sum]
    simp only [Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum, add_div]
    congr 1
    · refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_)); ring
    · refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_)); ring
  rw [hR]
  have hnegR : (((∑ i, ∑ j, v i * Mz i j * v j + w * (∑ i, |v i|) ^ 2 : ℤ)) : ℝ) < 0 := by
    exact_mod_cast hneg
  exact div_neg_of_neg_of_pos hnegR hS

end RK1
