/-
  FamilyWeilTable -- the d_min tables (Stage 0 of the quadratic-family programme, 2026-09-25).

  CUTOFFS.  The cells are cut at an INTEGER N (pattern = (chi_d(p))_{p < N}): N = 4 gives the
  primes {2, 3} (18 cells), N = 7 the primes {2, 3, 5} (54 cells).  The window statements carry a
  REAL cutoff X (WindowPosX X d: tests supported in [-L, L] with 2L <= log X) and hold for ANY
  0 < X <= N: family4_of_* for X <= 4 (atoms n in {2, 3}; at X = 4 the atom 4 sits on the support
  edge and drops), family7_of_* for X <= 7 (atoms n < 7), in particular X = 6.5, the Stage 1/2
  cutoff of the scoping memo, whose units (2L <= log 6.5) plug into family7_of_dmins at X = 6.5.
  For X in (5, 7] the table7 cells are exactly the cells of the primes below X.  The integer
  corollaries family4_of_dmins_nat / family7_of_dmins_nat are the case X = N.

  Every (pattern, sign) cell is given its minimal fundamental discriminant d_min with a
  KERNEL-CHECKED proof (`decide +kernel`, Nat/Int arithmetic only) that
    (i)   d_min is a fundamental discriminant,
    (ii)  d_min has the pattern and the sign,
    (iii) no fundamental discriminant of the same sign with smaller |d| has the pattern.
  Both tables are TOTAL (no empty cell: every pattern is realised, CRT), which the same `decide`
  certifies (the `none` branch of the entry check is `False`); the reduction of FamilyWeilQuad
  covers the empty branch anyway.

  Cross-checked (2026-09-25) against the parallel session's independent table (dmin_table.json,
  72 records, searched to |d| <= 1e6) and the scoping memo's min_disc.log: no disagreement.
  DECISION carried: d = 1 (zeta^2) is excluded, so the (+, all +1) cell has d_min = 73 at N = 4
  and 241 at N = 7.

  Family statements: family4_of_dmins / family7_of_dmins -- "for every fundamental d, W(X)"
  follows from the conjunction of W(X) at the 18 (resp. 54) values of d_min, for any real
  0 < X <= 4 (resp. <= 7).  W(X) here is "Re weilFormQ d >= 0 on the window", a statement about the
  frequency-side DEFINITION weilFormQ (see FamilyWeilQuad's disclosure); no explicit formula for
  zeta_K is proved.  Stage 0 proves NO positivity unit.  conjecture1_proved = False.
-/
import FamilyWeilQuad

open Zeta23 Complex MeasureTheory

namespace FamilyWeil
open WeilExplicit

/-! ## A. The cells cut at N = 4: primes {2, 3}, 9 patterns x 2 signs = 18 cells (real cutoffs X <= 4). -/

/-- A pattern on the primes `2, 3` as a function on `ℕ`. -/
def patFun2 (ε : Tri × Tri) : ℕ → ℤ :=
  fun p => if p = 2 then ε.1.toInt else if p = 3 then ε.2.toInt else 0

/-- Cell membership at `N = 4`, in decidable form (cheap conjuncts first). -/
def InCell4 (ε : Tri × Tri) (neg : Bool) (d : ℤ) : Prop :=
  decide (d < 0) = neg ∧ kron2 d = ε.1.toInt ∧ kron3 d = ε.2.toInt ∧ IsFundDisc d

instance (ε : Tri × Tri) (neg : Bool) (d : ℤ) : Decidable (InCell4 ε neg d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem inCell4_iff (ε : Tri × Tri) (neg : Bool) (d : ℤ) :
    InCell 4 (patFun2 ε) neg d ↔ InCell4 ε neg d := by
  constructor
  · rintro ⟨hf, hs, hp⟩
    refine ⟨hs, ?_, ?_, hf⟩
    · have := hp 2 Nat.prime_two (by norm_num)
      simpa [patFun2] using this
    · have := hp 3 Nat.prime_three (by norm_num)
      simpa [patFun2, kronSym_three] using this
  · rintro ⟨hs, h2, h3, hf⟩
    refine ⟨hf, hs, fun p hp hpN => ?_⟩
    interval_cases p
    · exact absurd hp Nat.not_prime_zero
    · exact absurd hp Nat.not_prime_one
    · simpa [patFun2] using h2
    · simpa [patFun2, kronSym_three] using h3

/-- Minimality in decidable form: no smaller `|d|` of the same sign lies in the cell. -/
def IsCellMin4B (ε : Tri × Tri) (neg : Bool) (d : ℤ) : Prop :=
  InCell4 ε neg d ∧ ∀ m, m < d.natAbs → ¬ InCell4 ε neg (signed neg m)

instance (ε : Tri × Tri) (neg : Bool) (d : ℤ) : Decidable (IsCellMin4B ε neg d) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem isCellMin_of_B4 {ε : Tri × Tri} {neg : Bool} {d : ℤ} (h : IsCellMin4B ε neg d) :
    IsCellMin 4 (patFun2 ε) neg d := by
  refine ⟨(inCell4_iff ε neg d).mpr h.1, fun d' hd' => ?_⟩
  by_contra hlt
  push Not at hlt
  have hd'B := (inCell4_iff ε neg d').mp hd'
  have hsign : decide (d' < 0) = neg := hd'B.1
  have hs' : signed neg d'.natAbs = d' := by
    rw [← hsign]
    exact signed_natAbs d'
  have := h.2 d'.natAbs hlt
  rw [hs'] at this
  exact this hd'B

/-- THE TABLE at `N = 4`: cell `((eps_2, eps_3), sign) -> d_min`. -/
def table4 : Tri × Tri → Bool → Option ℤ
  | (.m, .m), false => some 5
  | (.m, .m), true => some (-19)
  | (.m, .z), false => some 21
  | (.m, .z), true => some (-3)
  | (.m, .p), false => some 13
  | (.m, .p), true => some (-11)
  | (.z, .m), false => some 8
  | (.z, .m), true => some (-4)
  | (.z, .z), false => some 12
  | (.z, .z), true => some (-24)
  | (.z, .p), false => some 28
  | (.z, .p), true => some (-8)
  | (.p, .m), false => some 17
  | (.p, .m), true => some (-7)
  | (.p, .z), false => some 33
  | (.p, .z), true => some (-15)
  | (.p, .p), false => some 73
  | (.p, .p), true => some (-23)

/-- The entry check: `some d` must be the minimal member; `none` is rejected (the table is total). -/
def EntryChk4 (ε : Tri × Tri) (neg : Bool) : Option ℤ → Prop
  | some d => IsCellMin4B ε neg d
  | none => False

instance (ε : Tri × Tri) (neg : Bool) : DecidablePred (EntryChk4 ε neg)
  | some d => inferInstanceAs (Decidable (IsCellMin4B ε neg d))
  | none => inferInstanceAs (Decidable False)

/-- KERNEL CHECK of the 18 cells: (i) fundamental, (ii) pattern and sign, (iii) minimal. -/
theorem table4_check : ∀ a ∈ triList, ∀ b ∈ triList, ∀ neg ∈ [false, true],
    EntryChk4 (a, b) neg (table4 (a, b) neg) := by
  decide +kernel

/-- Every `N = 4` entry is a correct table entry in the sense of `CellEntry`. -/
theorem table4_spec (ε : Tri × Tri) (neg : Bool) : CellEntry 4 (patFun2 ε) neg (table4 ε neg) := by
  obtain ⟨a, b⟩ := ε
  have h := table4_check a (mem_triList a) b (mem_triList b) neg (by cases neg <;> simp)
  cases ht : table4 (a, b) neg with
  | none => rw [ht] at h; exact h.elim
  | some d => rw [ht] at h; exact isCellMin_of_B4 h

/-- THE REDUCTION for the cells cut at `N = 4`, at any real cutoff `0 < X <= 4`: window positivity at
every table value gives it for every fundamental discriminant. -/
theorem family4_of_table {X : ℝ} (hX0 : 0 < X) (hXN : X ≤ 4)
    (hpos : ∀ (ε : Tri × Tri) (neg : Bool) (d : ℤ), table4 ε neg = some d → WindowPosX X d) :
    ∀ d, IsFundDisc d → WindowPosX X d := by
  intro d hd
  have hcell : InCell 4 (patFun2 (Tri.ofInt (kron2 d), Tri.ofInt (kron3 d))) (decide (d < 0)) d := by
    rw [inCell4_iff]
    exact ⟨rfl, (Tri.toInt_ofInt (kron2_mem d)).symm, (Tri.toInt_ofInt (kron3_mem d)).symm, hd⟩
  exact reduction_of_entry (by norm_num) hX0 (by exact_mod_cast hXN) (table4_spec _ _) (hpos _ _) d hcell

/-- The 18 values of `d_min` at `N = 4`, in the order of the cells
`(eps_2, eps_3) in {-1, 0, 1}^2` (lexicographic), sign `+` then `-`. -/
def dmins4 : List ℤ := [5, (-19), 21, (-3), 13, (-11), 8, (-4), 12, (-24), 28, (-8), 17, (-7), 33, (-15), 73, (-23)]

theorem table4_mem : ∀ a ∈ triList, ∀ b ∈ triList, ∀ neg ∈ [false, true],
    ∀ d ∈ table4 (a, b) neg, d ∈ dmins4 := by
  decide +kernel

/-- The family statement at any real cutoff `0 < X <= 4` from the conjunction over the 18 cells' `d_min`. -/
theorem family4_of_dmins {X : ℝ} (hX0 : 0 < X) (hXN : X ≤ 4)
    (hpos : ∀ d ∈ dmins4, WindowPosX X d) :
    ∀ d, IsFundDisc d → WindowPosX X d :=
  family4_of_table hX0 hXN fun ε neg d hd =>
    hpos d (table4_mem ε.1 (mem_triList _) ε.2 (mem_triList _) neg (by cases neg <;> simp) d
      (Option.mem_def.mpr hd))

/-- The integer-cutoff corollary at `X = 4`. -/
theorem family4_of_dmins_nat (hpos : ∀ d ∈ dmins4, WindowPos 4 d) :
    ∀ d, IsFundDisc d → WindowPos 4 d :=
  family4_of_dmins (by norm_num) (by norm_num) hpos

/-- The family statement at any real cutoff `0 < X <= 4` from the explicit conjunction over the
18 cells' `d_min`. -/
theorem family4_of_cells {X : ℝ} (hX0 : 0 < X) (hXN : X ≤ 4) (h : WindowPosX X 5 ∧ WindowPosX X (-19) ∧ WindowPosX X 21 ∧ WindowPosX X (-3) ∧ WindowPosX X 13 ∧ WindowPosX X (-11) ∧ WindowPosX X 8 ∧ WindowPosX X (-4) ∧ WindowPosX X 12 ∧ WindowPosX X (-24) ∧ WindowPosX X 28 ∧ WindowPosX X (-8) ∧ WindowPosX X 17 ∧ WindowPosX X (-7) ∧ WindowPosX X 33 ∧ WindowPosX X (-15) ∧ WindowPosX X 73 ∧ WindowPosX X (-23)) :
    ∀ d, IsFundDisc d → WindowPosX X d := by
  refine family4_of_dmins hX0 hXN ?_
  simp only [dmins4, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
    and_true]
  exact h

/-! ## B. The cells cut at N = 7: primes {2, 3, 5}, 27 patterns x 2 signs = 54 cells (real cutoffs X <= 7, e.g. 6.5). -/

/-- A pattern on the primes `2, 3, 5` as a function on `ℕ`. -/
def patFun3 (ε : Tri × Tri × Tri) : ℕ → ℤ :=
  fun p => if p = 2 then ε.1.toInt else if p = 3 then ε.2.1.toInt
    else if p = 5 then ε.2.2.toInt else 0

/-- Cell membership at `N = 7`, in decidable form. -/
def InCell7 (ε : Tri × Tri × Tri) (neg : Bool) (d : ℤ) : Prop :=
  decide (d < 0) = neg ∧ kron2 d = ε.1.toInt ∧ kron3 d = ε.2.1.toInt ∧ kron5 d = ε.2.2.toInt
    ∧ IsFundDisc d

instance (ε : Tri × Tri × Tri) (neg : Bool) (d : ℤ) : Decidable (InCell7 ε neg d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

theorem inCell7_iff (ε : Tri × Tri × Tri) (neg : Bool) (d : ℤ) :
    InCell 7 (patFun3 ε) neg d ↔ InCell7 ε neg d := by
  constructor
  · rintro ⟨hf, hs, hp⟩
    refine ⟨hs, ?_, ?_, ?_, hf⟩
    · have := hp 2 Nat.prime_two (by norm_num)
      simpa [patFun3] using this
    · have := hp 3 Nat.prime_three (by norm_num)
      simpa [patFun3, kronSym_three] using this
    · have := hp 5 Nat.prime_five (by norm_num)
      simpa [patFun3, kronSym_five] using this
  · rintro ⟨hs, h2, h3, h5, hf⟩
    refine ⟨hf, hs, fun p hp hpN => ?_⟩
    interval_cases p
    · exact absurd hp Nat.not_prime_zero
    · exact absurd hp Nat.not_prime_one
    · simpa [patFun3] using h2
    · simpa [patFun3, kronSym_three] using h3
    · exact absurd hp (by norm_num)
    · simpa [patFun3, kronSym_five] using h5
    · exact absurd hp (by norm_num)

def IsCellMin7B (ε : Tri × Tri × Tri) (neg : Bool) (d : ℤ) : Prop :=
  InCell7 ε neg d ∧ ∀ m, m < d.natAbs → ¬ InCell7 ε neg (signed neg m)

instance (ε : Tri × Tri × Tri) (neg : Bool) (d : ℤ) : Decidable (IsCellMin7B ε neg d) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem isCellMin_of_B7 {ε : Tri × Tri × Tri} {neg : Bool} {d : ℤ} (h : IsCellMin7B ε neg d) :
    IsCellMin 7 (patFun3 ε) neg d := by
  refine ⟨(inCell7_iff ε neg d).mpr h.1, fun d' hd' => ?_⟩
  by_contra hlt
  push Not at hlt
  have hd'B := (inCell7_iff ε neg d').mp hd'
  have hsign : decide (d' < 0) = neg := hd'B.1
  have hs' : signed neg d'.natAbs = d' := by
    rw [← hsign]
    exact signed_natAbs d'
  have := h.2 d'.natAbs hlt
  rw [hs'] at this
  exact this hd'B

/-- THE TABLE at `N = 7` (primes `{2, 3, 5}`): cell `((eps_2, eps_3, eps_5), sign) -> d_min`. -/
def table7 : Tri × Tri × Tri → Bool → Option ℤ
  | (.m, .m, .m), false => some 53
  | (.m, .m, .m), true => some (-43)
  | (.m, .m, .z), false => some 5
  | (.m, .m, .z), true => some (-115)
  | (.m, .m, .p), false => some 29
  | (.m, .m, .p), true => some (-19)
  | (.m, .z, .m), false => some 93
  | (.m, .z, .m), true => some (-3)
  | (.m, .z, .z), false => some 165
  | (.m, .z, .z), true => some (-195)
  | (.m, .z, .p), false => some 21
  | (.m, .z, .p), true => some (-51)
  | (.m, .p, .m), false => some 13
  | (.m, .p, .m), true => some (-83)
  | (.m, .p, .z), false => some 85
  | (.m, .p, .z), true => some (-35)
  | (.m, .p, .p), false => some 61
  | (.m, .p, .p), true => some (-11)
  | (.z, .m, .m), false => some 8
  | (.z, .m, .m), true => some (-52)
  | (.z, .m, .z), false => some 140
  | (.z, .m, .z), true => some (-40)
  | (.z, .m, .p), false => some 44
  | (.z, .m, .p), true => some (-4)
  | (.z, .z, .m), false => some 12
  | (.z, .z, .m), true => some (-132)
  | (.z, .z, .z), false => some 60
  | (.z, .z, .z), true => some (-120)
  | (.z, .z, .p), false => some 24
  | (.z, .z, .p), true => some (-24)
  | (.z, .p, .m), false => some 28
  | (.z, .p, .m), true => some (-8)
  | (.z, .p, .z), false => some 40
  | (.z, .p, .z), true => some (-20)
  | (.z, .p, .p), false => some 76
  | (.z, .p, .p), true => some (-56)
  | (.p, .m, .m), false => some 17
  | (.p, .m, .m), true => some (-7)
  | (.p, .m, .z), false => some 65
  | (.p, .m, .z), true => some (-55)
  | (.p, .m, .p), false => some 41
  | (.p, .m, .p), true => some (-31)
  | (.p, .z, .m), false => some 33
  | (.p, .z, .m), true => some (-87)
  | (.p, .z, .z), false => some 105
  | (.p, .z, .z), true => some (-15)
  | (.p, .z, .p), false => some 129
  | (.p, .z, .p), true => some (-39)
  | (.p, .p, .m), false => some 73
  | (.p, .p, .m), true => some (-23)
  | (.p, .p, .z), false => some 145
  | (.p, .p, .z), true => some (-95)
  | (.p, .p, .p), false => some 241
  | (.p, .p, .p), true => some (-71)

def EntryChk7 (ε : Tri × Tri × Tri) (neg : Bool) : Option ℤ → Prop
  | some d => IsCellMin7B ε neg d
  | none => False

instance (ε : Tri × Tri × Tri) (neg : Bool) : DecidablePred (EntryChk7 ε neg)
  | some d => inferInstanceAs (Decidable (IsCellMin7B ε neg d))
  | none => inferInstanceAs (Decidable False)

/-- KERNEL CHECK of the 54 cells: (i) fundamental, (ii) pattern and sign, (iii) minimal. -/
theorem table7_check : ∀ a ∈ triList, ∀ b ∈ triList, ∀ c ∈ triList, ∀ neg ∈ [false, true],
    EntryChk7 (a, b, c) neg (table7 (a, b, c) neg) := by
  decide +kernel

theorem table7_spec (ε : Tri × Tri × Tri) (neg : Bool) :
    CellEntry 7 (patFun3 ε) neg (table7 ε neg) := by
  obtain ⟨a, b, c⟩ := ε
  have h := table7_check a (mem_triList a) b (mem_triList b) c (mem_triList c) neg
    (by cases neg <;> simp)
  cases ht : table7 (a, b, c) neg with
  | none => rw [ht] at h; exact h.elim
  | some d => rw [ht] at h; exact isCellMin_of_B7 h

/-- THE REDUCTION for the cells cut at `N = 7`, at any real cutoff `0 < X <= 7` (e.g. `6.5`). -/
theorem family7_of_table {X : ℝ} (hX0 : 0 < X) (hXN : X ≤ 7)
    (hpos : ∀ (ε : Tri × Tri × Tri) (neg : Bool) (d : ℤ), table7 ε neg = some d → WindowPosX X d) :
    ∀ d, IsFundDisc d → WindowPosX X d := by
  intro d hd
  have hcell : InCell 7 (patFun3 (Tri.ofInt (kron2 d), Tri.ofInt (kron3 d), Tri.ofInt (kron5 d)))
      (decide (d < 0)) d := by
    rw [inCell7_iff]
    exact ⟨rfl, (Tri.toInt_ofInt (kron2_mem d)).symm, (Tri.toInt_ofInt (kron3_mem d)).symm,
      (Tri.toInt_ofInt (kron5_mem d)).symm, hd⟩
  exact reduction_of_entry (by norm_num) hX0 (by exact_mod_cast hXN) (table7_spec _ _) (hpos _ _) d hcell

/-- The 54 values of `d_min` at `N = 7`, in the order of the cells
`(eps_2, eps_3, eps_5) in {-1, 0, 1}^3` (lexicographic), sign `+` then `-`. -/
def dmins7 : List ℤ := [53, (-43), 5, (-115), 29, (-19), 93, (-3), 165, (-195), 21, (-51), 13, (-83), 85, (-35), 61, (-11), 8, (-52), 140, (-40), 44, (-4), 12, (-132), 60, (-120), 24, (-24), 28, (-8), 40, (-20), 76, (-56), 17, (-7), 65, (-55), 41, (-31), 33, (-87), 105, (-15), 129, (-39), 73, (-23), 145, (-95), 241, (-71)]

theorem table7_mem : ∀ a ∈ triList, ∀ b ∈ triList, ∀ c ∈ triList, ∀ neg ∈ [false, true],
    ∀ d ∈ table7 (a, b, c) neg, d ∈ dmins7 := by
  decide +kernel

/-- The family statement at any real cutoff `0 < X <= 7` (e.g. `X = 6.5`) from the conjunction over
the 54 cells' `d_min`. -/
theorem family7_of_dmins {X : ℝ} (hX0 : 0 < X) (hXN : X ≤ 7)
    (hpos : ∀ d ∈ dmins7, WindowPosX X d) :
    ∀ d, IsFundDisc d → WindowPosX X d :=
  family7_of_table hX0 hXN fun ε neg d hd =>
    hpos d (table7_mem ε.1 (mem_triList _) ε.2.1 (mem_triList _) ε.2.2 (mem_triList _) neg
      (by cases neg <;> simp) d (Option.mem_def.mpr hd))

/-- The integer-cutoff corollary at `X = 7`. -/
theorem family7_of_dmins_nat (hpos : ∀ d ∈ dmins7, WindowPos 7 d) :
    ∀ d, IsFundDisc d → WindowPos 7 d :=
  family7_of_dmins (by norm_num) (by norm_num) hpos

/-- The family statement at any real cutoff `0 < X <= 7` from the explicit conjunction over the
54 cells' `d_min`. -/
theorem family7_of_cells {X : ℝ} (hX0 : 0 < X) (hXN : X ≤ 7) (h : WindowPosX X 53 ∧ WindowPosX X (-43) ∧ WindowPosX X 5 ∧ WindowPosX X (-115) ∧ WindowPosX X 29 ∧ WindowPosX X (-19) ∧ WindowPosX X 93 ∧ WindowPosX X (-3) ∧ WindowPosX X 165 ∧ WindowPosX X (-195) ∧ WindowPosX X 21 ∧ WindowPosX X (-51) ∧ WindowPosX X 13 ∧ WindowPosX X (-83) ∧ WindowPosX X 85 ∧ WindowPosX X (-35) ∧ WindowPosX X 61 ∧ WindowPosX X (-11) ∧ WindowPosX X 8 ∧ WindowPosX X (-52) ∧ WindowPosX X 140 ∧ WindowPosX X (-40) ∧ WindowPosX X 44 ∧ WindowPosX X (-4) ∧ WindowPosX X 12 ∧ WindowPosX X (-132) ∧ WindowPosX X 60 ∧ WindowPosX X (-120) ∧ WindowPosX X 24 ∧ WindowPosX X (-24) ∧ WindowPosX X 28 ∧ WindowPosX X (-8) ∧ WindowPosX X 40 ∧ WindowPosX X (-20) ∧ WindowPosX X 76 ∧ WindowPosX X (-56) ∧ WindowPosX X 17 ∧ WindowPosX X (-7) ∧ WindowPosX X 65 ∧ WindowPosX X (-55) ∧ WindowPosX X 41 ∧ WindowPosX X (-31) ∧ WindowPosX X 33 ∧ WindowPosX X (-87) ∧ WindowPosX X 105 ∧ WindowPosX X (-15) ∧ WindowPosX X 129 ∧ WindowPosX X (-39) ∧ WindowPosX X 73 ∧ WindowPosX X (-23) ∧ WindowPosX X 145 ∧ WindowPosX X (-95) ∧ WindowPosX X 241 ∧ WindowPosX X (-71)) :
    ∀ d, IsFundDisc d → WindowPosX X d := by
  refine family7_of_dmins hX0 hXN ?_
  simp only [dmins7, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
    and_true]
  exact h

end FamilyWeil
