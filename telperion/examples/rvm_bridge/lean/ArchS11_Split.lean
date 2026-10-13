/-
  ArchS11_Split -- assembly lemmas for the split S11 certificate checks (rvm_bridge island).
  Each certificate Boolean is a conjunction of per-row checks; these lemmas rebuild it from per-row
  `decide +kernel` theorems kept in small modules (bounded peak memory per module).
  conjecture1_proved = False.  No `sorry`.
-/
import ArchS11_Data

open Finset

namespace ArchS11.Data

theorem rows8 {f : ℕ → Bool} (h0 : f 0 = true) (h1 : f 1 = true) (h2 : f 2 = true) (h3 : f 3 = true)
    (h4 : f 4 = true) (h5 : f 5 = true) (h6 : f 6 = true) (h7 : f 7 = true) :
    ∀ j < NG, f j = true := by
  intro j hj
  have : j < 8 := hj
  interval_cases j <;> assumption

theorem rows8' {U : List (List ℚ)} {u : List ℚ}
    (h0 : mom (U.getD 0 []) (U.getD 0 []) = u.getD 0 0) (h1 : mom (U.getD 1 []) (U.getD 1 []) = u.getD 1 0)
    (h2 : mom (U.getD 2 []) (U.getD 2 []) = u.getD 2 0) (h3 : mom (U.getD 3 []) (U.getD 3 []) = u.getD 3 0)
    (h4 : mom (U.getD 4 []) (U.getD 4 []) = u.getD 4 0) (h5 : mom (U.getD 5 []) (U.getD 5 []) = u.getD 5 0)
    (h6 : mom (U.getD 6 []) (U.getD 6 []) = u.getD 6 0) (h7 : mom (U.getD 7 []) (U.getD 7 []) = u.getD 7 0) :
    ∀ j < NG, mom (U.getD j []) (U.getD j []) = u.getD j 0 := by
  intro j hj
  have : j < 8 := hj
  interval_cases j <;> assumption

theorem all_range_NG {f : ℕ → Bool} (h : ∀ j < NG, f j = true) : (List.range NG).all f = true := by
  rw [List.all_eq_true]
  intro j hj
  exact h j (List.mem_range.1 hj)

theorem psiOK_of {E : List ℚ} {Psi : List (List ℚ)} (hl : decide (Psi.length = NG) = true)
    (h : ∀ j < NG, psiRow E Psi j = true) : psiOK E Psi = true := by
  unfold psiOK
  rw [hl, all_range_NG h]
  rfl

theorem uOK_of {Psi : List (List ℚ)} {c0 : ℚ} {U : List (List ℚ)} (hl : decide (U.length = NG) = true)
    (h : ∀ j < NG, uRow Psi c0 U j = true) : uOK Psi c0 U = true := by
  unfold uOK
  rw [hl, all_range_NG h]
  rfl

theorem rhoOK_of {U B rho : List (List ℚ)} (hl : decide (rho.length = NG) = true)
    (h : ∀ j < NG, rhoRow U B rho j = true) : rhoOK U B rho = true := by
  unfold rhoOK
  rw [hl, all_range_NG h]
  rfl

theorem dOK_of {rho : List (List ℚ)} {al dh : List ℚ} (h : ∀ j < NG, dRow rho al dh j = true) :
    dOK rho al dh = true := all_range_NG h

theorem qmatOK_of {U Q : List (List ℚ)} {dh : List ℚ} {lam t : ℚ}
    (h : ∀ j < NG, qRow U Q dh lam t j = true) : qmatOK U Q dh lam t = true := all_range_NG h

theorem tailOK_of {E : List ℚ} {c0 : ℚ} {U : List (List ℚ)} {lam t q : ℚ}
    (h1 : decide (0 < t) = true) (h2 : decide (0 ≤ q) = true) (h3 : decide (q + 1 / t ≤ lam) = true)
    (h4 : q2val E c0 U ≤ q * q) : tailOK E c0 U lam t q = true := by
  unfold tailOK
  rw [h1, h2, h3, decide_eq_true h4]
  rfl

theorem and6 {a b c d e f : Bool} (ha : a = true) (hb : b = true) (hc : c = true) (hd : d = true)
    (he : e = true) (hf : f = true) : (a && b && c && d && e && f) = true := by
  rw [ha, hb, hc, hd, he, hf]
  rfl

/-- The Legendre Gram matrix is diagonal (kernel check, small). -/
theorem ortho_ok' : ∀ j < NG, ∀ l < NG, j ≠ l → mom (Phi j) (Phi l) = 0 := by
  have h : orthoOK = true := by decide +kernel
  unfold orthoOK at h
  rw [List.all_eq_true] at h
  intro j hj l hl hjl
  have h2 := h j (List.mem_range.2 hj)
  rw [List.all_eq_true] at h2
  have h3 := h2 l (List.mem_range.2 hl)
  rw [if_neg hjl] at h3
  exact of_decide_eq_true h3

/-- The tail value through the diagonal moments `uu_j = mom U_j U_j` (the Gram of Φ is diagonal). -/
theorem q2val_eq {E : List ℚ} {c0 : ℚ} {U : List (List ℚ)} {uu : List ℚ}
    (hortho : ∀ j < NG, ∀ l < NG, j ≠ l → mom (Phi j) (Phi l) = 0)
    (huu : ∀ j < NG, mom (U.getD j []) (U.getD j []) = uu.getD j 0) :
    q2val E c0 U = KKh E c0 - 2 * (∑ j ∈ range NG, wq j * uu.getD j 0)
      + ∑ j ∈ range NG, wq j * wq j * mom (Phi j) (Phi j) * uu.getD j 0 := by
  unfold q2val
  congr 1
  · congr 2
    exact Finset.sum_congr rfl fun j hj => by rw [huu j (Finset.mem_range.1 hj)]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    rw [Finset.sum_eq_single j]
    · split_ifs with h
      · rw [h]; ring
      · rw [huu j hj']
    · intro l hl hlj
      rw [if_pos (hortho j hj' l (Finset.mem_range.1 hl) (Ne.symm hlj))]
    · intro h; exact absurd hj h

end ArchS11.Data
