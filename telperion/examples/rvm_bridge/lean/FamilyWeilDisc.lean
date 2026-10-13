/-
  FamilyWeilDisc -- fundamental discriminants and Kronecker symbols, kernel-decidable
  (Stage 0 of the quadratic-family programme, 2026-09-25).

  * IsFundDisc d: d /= 1 and (d = 1 mod 4 squarefree, or d = 4m with m = 2, 3 mod 4 squarefree).
    Defined through a BOUNDED squarefree check (SqfreeChk, a structurally decidable Prop on N),
    so `decide` reduces it in the kernel; isFundDisc_iff restates it with Mathlib's Squarefree.
    The DECISION of the parallel session: d = 1 (zeta^2, double pole) is excluded.
  * kron2 d: the Kronecker symbol (d/2) (0 for d even, +1 for d = +-1 mod 8, -1 for d = +-3
    mod 8) = Mathlib's ZMod.χ₈ d (kron2_eq_χ₈); kron3, kron5: explicit residue tables, equal to
    Mathlib's jacobiSym d 3 / d 5 (kronSym_three, kronSym_five); kronSym d p: the symbol at a
    prime p (kron2 at 2, jacobiSym d p at odd p).
  * Tri: the three-element value type of a symbol, with toInt/ofInt.

  Pure arithmetic; nothing about the Weil form.  conjecture1_proved = False.
-/
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

namespace FamilyWeil

/-! ## A. A kernel-decidable squarefree check. -/

/-- `m /= 0` and no `k` with `2 <= k < m` has `k^2 | m`.  Structurally decidable. -/
def SqfreeChk (m : ℕ) : Prop := m ≠ 0 ∧ ∀ k, k < m → 2 ≤ k → m % (k * k) ≠ 0

instance : DecidablePred SqfreeChk := fun m => by
  unfold SqfreeChk
  infer_instance

/-- The bounded check is Mathlib's `Squarefree` on `ℕ`. -/
theorem sqfreeChk_iff (m : ℕ) : SqfreeChk m ↔ Squarefree m := by
  constructor
  · rintro ⟨hm, h⟩ x hx
    rw [Nat.isUnit_iff]
    by_contra hx1
    rcases Nat.lt_or_ge x 2 with hlt | hge
    · interval_cases x
      · exact hm (by simpa using hx)
      · exact hx1 rfl
    · have h1 : x * x ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hx
      have hxm : x < m := by nlinarith
      exact h x hxm hge (Nat.mod_eq_zero_of_dvd hx)
  · intro hs
    refine ⟨hs.ne_zero, fun k hk hk2 hmod => ?_⟩
    have hdvd : k * k ∣ m := Nat.dvd_of_mod_eq_zero hmod
    have := Nat.isUnit_iff.mp (hs k hdvd)
    omega

/-! ## B. Fundamental discriminants. -/

/-- Fundamental discriminant: `d /= 1` and either `d = 1 (mod 4)` squarefree, or `d = 4m` with
`m = 2, 3 (mod 4)` squarefree.  (`d = 0` is excluded by the squarefree clauses.) -/
def IsFundDisc (d : ℤ) : Prop :=
  d ≠ 1 ∧ ((d % 4 = 1 ∧ SqfreeChk d.natAbs)
    ∨ (d % 4 = 0 ∧ ((d / 4) % 4 = 2 ∨ (d / 4) % 4 = 3) ∧ SqfreeChk (d / 4).natAbs))

instance : DecidablePred IsFundDisc := fun d => by
  unfold IsFundDisc
  infer_instance

/-- The definition restated with Mathlib's `Squarefree` on `ℤ`. -/
theorem isFundDisc_iff (d : ℤ) :
    IsFundDisc d ↔ d ≠ 1 ∧ ((d % 4 = 1 ∧ Squarefree d)
      ∨ (d % 4 = 0 ∧ ((d / 4) % 4 = 2 ∨ (d / 4) % 4 = 3) ∧ Squarefree (d / 4))) := by
  simp only [IsFundDisc, sqfreeChk_iff, Int.squarefree_natAbs]

theorem IsFundDisc.ne_zero {d : ℤ} (h : IsFundDisc d) : d ≠ 0 := by
  rcases h with ⟨_, ⟨h2, _⟩ | ⟨_, _, ⟨h4, _⟩⟩⟩ <;> omega

theorem IsFundDisc.natAbs_pos {d : ℤ} (h : IsFundDisc d) : 0 < d.natAbs :=
  Int.natAbs_pos.mpr h.ne_zero

/-- Sanity: the first few. -/
example : IsFundDisc (-3) ∧ IsFundDisc (-4) ∧ IsFundDisc 5 ∧ IsFundDisc 8 ∧ IsFundDisc (-7)
    ∧ ¬ IsFundDisc 1 ∧ ¬ IsFundDisc 0 ∧ ¬ IsFundDisc 4 ∧ ¬ IsFundDisc 9 ∧ ¬ IsFundDisc (-9)
    ∧ IsFundDisc 12 ∧ ¬ IsFundDisc 16 := by decide

/-! ## C. Kronecker symbols. -/

/-- `(d/2)`: `0` for `d` even, `+1` for `d = +-1 (mod 8)`, `-1` for `d = +-3 (mod 8)`. -/
def kron2 (d : ℤ) : ℤ := if d % 2 = 0 then 0 else if d % 8 = 1 ∨ d % 8 = 7 then 1 else -1

/-- `(d/3)` by residues. -/
def kron3 (d : ℤ) : ℤ := if d % 3 = 0 then 0 else if d % 3 = 1 then 1 else -1

/-- `(d/5)` by residues (`1, 4` are the squares mod `5`). -/
def kron5 (d : ℤ) : ℤ := if d % 5 = 0 then 0 else if d % 5 = 1 ∨ d % 5 = 4 then 1 else -1

/-- The Kronecker symbol `(d/p)` at a prime `p`: `kron2` at `2`, the Jacobi (= Legendre)
symbol at odd `p`. -/
def kronSym (d : ℤ) (p : ℕ) : ℤ := if p = 2 then kron2 d else jacobiSym d p

theorem kron2_eq_χ₈ (d : ℤ) : kron2 d = ZMod.χ₈ d := by
  rw [ZMod.χ₈_int_eq_if_mod_eight]
  rfl

@[simp] theorem kronSym_two (d : ℤ) : kronSym d 2 = kron2 d := by simp [kronSym]

theorem kronSym_three (d : ℤ) : kronSym d 3 = kron3 d := by
  unfold kronSym kron3
  rw [if_neg (by norm_num), jacobiSym.mod_left]
  simp only [Nat.cast_ofNat]
  have h : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by omega
  rcases h with h | h | h <;> rw [h] <;> norm_num

theorem kronSym_five (d : ℤ) : kronSym d 5 = kron5 d := by
  unfold kronSym kron5
  rw [if_neg (by norm_num), jacobiSym.mod_left]
  simp only [Nat.cast_ofNat]
  have h : d % 5 = 0 ∨ d % 5 = 1 ∨ d % 5 = 2 ∨ d % 5 = 3 ∨ d % 5 = 4 := by omega
  rcases h with h | h | h | h | h <;> rw [h] <;> norm_num

theorem kron2_mem (d : ℤ) : kron2 d = -1 ∨ kron2 d = 0 ∨ kron2 d = 1 := by
  unfold kron2; split_ifs <;> simp

theorem kron3_mem (d : ℤ) : kron3 d = -1 ∨ kron3 d = 0 ∨ kron3 d = 1 := by
  unfold kron3; split_ifs <;> simp

theorem kron5_mem (d : ℤ) : kron5 d = -1 ∨ kron5 d = 0 ∨ kron5 d = 1 := by
  unfold kron5; split_ifs <;> simp

/-! ## D. The value type of a symbol. -/

/-- The three values of a Kronecker symbol: `m = -1`, `z = 0`, `p = +1`. -/
inductive Tri
  | m | z | p
  deriving DecidableEq, Repr

def Tri.toInt : Tri → ℤ
  | .m => -1
  | .z => 0
  | .p => 1

def Tri.ofInt (x : ℤ) : Tri := if x = -1 then .m else if x = 0 then .z else .p

theorem Tri.toInt_ofInt {x : ℤ} (hx : x = -1 ∨ x = 0 ∨ x = 1) : (Tri.ofInt x).toInt = x := by
  rcases hx with rfl | rfl | rfl <;> rfl

/-- The universe of `Tri`, as a list (for `decide`). -/
def triList : List Tri := [.m, .z, .p]

theorem mem_triList (t : Tri) : t ∈ triList := by cases t <;> simp [triList]

/-- `d` with sign `neg` and absolute value `m`. -/
def signed (neg : Bool) (m : ℕ) : ℤ := if neg then -(m : ℤ) else m

theorem signed_natAbs (d : ℤ) : signed (decide (d < 0)) d.natAbs = d := by
  unfold signed
  by_cases h : d < 0
  · simp only [h, decide_true, if_true]
    omega
  · simp only [h, decide_false, Bool.false_eq_true, if_false]
    omega

end FamilyWeil
