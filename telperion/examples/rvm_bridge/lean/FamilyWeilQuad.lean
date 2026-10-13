/-
  FamilyWeilQuad -- the quadratic-field instance of the parametric Weil form, its log|d|
  monotonicity, and the d_min reduction (Stage 0 of the quadratic-family programme, 2026-09-25).

  For a fundamental discriminant d the member is zeta_K, K = Q(sqrt d):
    weights   weightQ d (p^k) = log p (1 + chi_d(p)^k)            (weightQ_prime_pow),
    shifts    [0, mu_d], mu_d = 0 for d > 0, 1 for d < 0  (Gamma_R(s) Gamma_R(s + mu_d)),
    conductor logq = log |d|,
    weilFormQ d = weilFormF (quadData d).

  The cell of d at cutoff N: its sign and its pattern (chi_d(p))_{p < N} (InCell N eps neg d).
  The cell form cellForm N eps neg = weilFormF (cellData N eps neg) has the weights cut at n < N,
  the shifts of the sign, and conductor term 0; it depends on d ONLY through (eps, neg).

  MONOTONICITY (weilFormQ_autocorr_eq, re_weilFormQ_mono): for g a Weil test supported in
  [-L, L] with 2L <= log N,
      weilFormQ d (autocorr g) = cellForm N (chi_d) (sign d) (autocorr g) + (autocorr g 0) log|d|,
  autocorr g 0 = ||g||^2 >= 0, hence for d, d' in the same cell with |d'| <= |d|
      Re weilFormQ d' (autocorr g) <= Re weilFormQ d (autocorr g).

  REDUCTION (cell_reduction, reduction_of_entry): window positivity WindowPosX X d at a REAL cutoff
  X with 0 < X <= N (tests supported in [-L, L] with 2L <= log X) of the minimal member d_min of a
  cell at the integer cutoff N implies it for every member; a table entry is either `some d_min`
  (with IsCellMin) or `none` (with a proof the cell is empty), and the reduction covers both
  branches.  WindowPos N d is the corollary at X = N (cell_reduction_nat).

  DISCLOSURE.  weilFormQ d is a DEFINITION on the frequency side: the parametric form at the data
  (weightQ d, [0, mu_d], log|d|).  No explicit formula tying it to the zeros of zeta_K is proved
  on this island (Mathlib has no Hadamard product / explicit formula for Dirichlet L-functions),
  and the t-side writing of the archimedean term is not proved either.  "WindowPosX X d" means
  "Re of this functional >= 0 on the window"; its identification with Weil positivity for zeta_K
  rests on the zeta anchor weilFormF_zeta (the same functional IS the island's zeta form at the
  zeta data) plus the hand derivation of the second gamma factor Gamma_R(s + mu_d) and of the
  weights c_d(p^k) = log p (1 + chi_d(p)^k) (the coefficients of -zeta_K'/zeta_K).

  Nothing about positivity is proved.  conjecture1_proved = False.
-/
import FamilyWeilForm
import FamilyWeilDisc

open Zeta23 Complex MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace FamilyWeil
open WeilExplicit

/-! ## A. The weights of zeta_K and their dependence on the pattern. -/

/-- `weightQ d n = Lambda(n) (1 + chi_d(p)^k)` for `n = p^k` (`0` off prime powers). -/
def weightQ (d : ℤ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n
    * (1 + ((kronSym d n.minFac : ℤ) : ℝ) ^ (n.factorization n.minFac))

/-- The memo's formula `c_d(p^k) = log p (1 + chi_d(p)^k)`. -/
theorem weightQ_prime_pow {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k ≠ 0) (d : ℤ) :
    weightQ d (p ^ k) = Real.log p * (1 + ((kronSym d p : ℤ) : ℝ) ^ k) := by
  unfold weightQ
  rw [ArithmeticFunction.vonMangoldt_apply_pow hk, ArithmeticFunction.vonMangoldt_apply_prime hp,
    hp.pow_minFac hk, hp.factorization_pow, Finsupp.single_eq_same]

/-- The weights cut at `n < N`, as a function of an abstract pattern `eps`. -/
def cellWeight (N : ℕ) (ε : ℕ → ℤ) (n : ℕ) : ℝ :=
  if n < N then
    ArithmeticFunction.vonMangoldt n * (1 + ((ε n.minFac : ℤ) : ℝ) ^ (n.factorization n.minFac))
  else 0

lemma weightQ_eq_cellWeight (d : ℤ) {N n : ℕ} (hn : n < N) :
    weightQ d n = cellWeight N (kronSym d) n := by
  simp [weightQ, cellWeight, hn]

/-- The cut weights depend on the pattern only at the primes below `N`. -/
theorem cellWeight_congr {N : ℕ} {ε ε' : ℕ → ℤ}
    (h : ∀ p, p.Prime → p < N → ε p = ε' p) : cellWeight N ε = cellWeight N ε' := by
  funext n
  unfold cellWeight
  split_ifs with hn
  · by_cases hpp : IsPrimePow n
    · have hn1 : n ≠ 1 := fun h1 => by
        subst h1
        exact not_isPrimePow_one hpp
      have hmin : n.minFac.Prime := Nat.minFac_prime hn1
      have hle : n.minFac ≤ n := Nat.minFac_le hpp.pos
      rw [h _ hmin (lt_of_le_of_lt hle hn)]
    · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
      simp
  · rfl

/-! ## B. The quadratic instance and the cell forms. -/

/-- The second gamma shift from the sign: `mu = 1` for `d < 0`, `0` for `d > 0`. -/
def muOf (neg : Bool) : ℝ := if neg then 1 else 0

/-- The data of `zeta_K`, `K = Q(sqrt d)`: weights `weightQ d`, factors `Gamma_R(s) Gamma_R(s + mu_d)`,
conductor `|d|`. -/
def quadData (d : ℤ) : FormData :=
  { c := weightQ d, shifts := [0, muOf (decide (d < 0))], logq := Real.log (d.natAbs : ℝ) }

/-- The Weil form of `zeta_K`. -/
def weilFormQ (d : ℤ) (g : ℝ → ℂ) : ℂ := weilFormF (quadData d) g

/-- The archimedean symbol of a quadratic member: `psiR + psi_{mu_d}`. -/
lemma symbolArch_quad (d : ℤ) (r : ℝ) :
    symbolArch (quadData d) r = RvMBridge11.psiR r + psiShift (muOf (decide (d < 0))) r := by
  simp [symbolArch, quadData, psiShift_zero]

/-- The cell data: cut weights of the pattern, the shifts of the sign, no conductor term. -/
def cellData (N : ℕ) (ε : ℕ → ℤ) (neg : Bool) : FormData :=
  { c := cellWeight N ε, shifts := [0, muOf neg], logq := 0 }

/-- The cell form: depends on `d` only through `(eps, neg)`. -/
def cellForm (N : ℕ) (ε : ℕ → ℤ) (neg : Bool) (g : ℝ → ℂ) : ℂ := weilFormF (cellData N ε neg) g

theorem cellForm_congr {N : ℕ} {ε ε' : ℕ → ℤ} (h : ∀ p, p.Prime → p < N → ε p = ε' p)
    (neg : Bool) : cellForm N ε neg = cellForm N ε' neg := by
  unfold cellForm cellData
  rw [cellWeight_congr h]

/-! ## C. Monotonicity in `log |d|`. -/

/-- THE SPLIT: on the window, `weilFormQ d = cellForm + f(0) log|d|`. -/
theorem weilFormQ_autocorr_eq (d : ℤ) {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) {N : ℕ} (hN : 1 ≤ N) (hL : 2 * L ≤ Real.log N) :
    weilFormQ d (autocorr g)
      = cellForm N (kronSym d) (decide (d < 0)) (autocorr g)
        + autocorr g 0 * (Real.log (d.natAbs : ℝ) : ℂ) := by
  unfold weilFormQ
  rw [weilFormF_eq_zero_logq_add]
  have hq : (quadData d).logq = Real.log (d.natAbs : ℝ) := rfl
  rw [hq]
  congr 1
  unfold cellForm weilFormF
  have harch : archSideF (withLogq (quadData d) 0) (autocorr g)
      = archSideF (cellData N (kronSym d) (decide (d < 0))) (autocorr g) :=
    archSideF_congr rfl rfl _
  have hprime : primeSideF (withLogq (quadData d) 0) (autocorr g)
      = primeSideF (cellData N (kronSym d) (decide (d < 0))) (autocorr g) :=
    primeSideF_congr_window (fun n hn => weightQ_eq_cellWeight d hn) hg hsupp hN hL
  rw [harch, hprime]

/-- The real-part form: `Re weilFormQ d = Re cellForm + ||g||^2 log|d|`. -/
theorem re_weilFormQ_autocorr_eq (d : ℤ) {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) {N : ℕ} (hN : 1 ≤ N) (hL : 2 * L ≤ Real.log N) :
    (weilFormQ d (autocorr g)).re
      = (cellForm N (kronSym d) (decide (d < 0)) (autocorr g)).re
        + RvMBridge31.mass g * Real.log (d.natAbs : ℝ) := by
  rw [weilFormQ_autocorr_eq d hg hsupp hN hL, Complex.add_re, RvMBridge31.autocorr_zero,
    ← Complex.ofReal_mul, Complex.ofReal_re]

/-- The cell of `d` at cutoff `N`: fundamental, of sign `neg`, with pattern `eps` on the
primes below `N`. -/
def InCell (N : ℕ) (ε : ℕ → ℤ) (neg : Bool) (d : ℤ) : Prop :=
  IsFundDisc d ∧ decide (d < 0) = neg ∧ ∀ p, p.Prime → p < N → kronSym d p = ε p

/-- Two members of a cell have the same cell form. -/
theorem cellForm_eq_of_inCell {N : ℕ} {ε : ℕ → ℤ} {neg : Bool} {d d' : ℤ}
    (hd : InCell N ε neg d) (hd' : InCell N ε neg d') :
    cellForm N (kronSym d) (decide (d < 0)) = cellForm N (kronSym d') (decide (d' < 0)) := by
  rw [hd.2.1, hd'.2.1]
  exact cellForm_congr (fun p hp hpN => by rw [hd.2.2 p hp hpN, hd'.2.2 p hp hpN]) neg

/-- MONOTONICITY IN `log |d|` within a cell. -/
theorem re_weilFormQ_mono {N : ℕ} {ε : ℕ → ℤ} {neg : Bool} {d d' : ℤ}
    (hd : InCell N ε neg d) (hd' : InCell N ε neg d') (habs : d'.natAbs ≤ d.natAbs)
    {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ} (hsupp : tsupport g ⊆ Set.Icc (-L) L) (hN : 1 ≤ N)
    (hL : 2 * L ≤ Real.log N) :
    (weilFormQ d' (autocorr g)).re ≤ (weilFormQ d (autocorr g)).re := by
  rw [re_weilFormQ_autocorr_eq d hg hsupp hN hL, re_weilFormQ_autocorr_eq d' hg hsupp hN hL,
    cellForm_eq_of_inCell hd hd']
  have hlog : Real.log (d'.natAbs : ℝ) ≤ Real.log (d.natAbs : ℝ) :=
    Real.log_le_log (Nat.cast_pos.mpr hd'.1.natAbs_pos) (by exact_mod_cast habs)
  have hm := RvMBridge31.mass_nonneg g
  nlinarith

/-! ## D. Window positivity and the reduction to the minimal member. -/

/-- `W(X)` for `chi_d` at a REAL cutoff `X`: the (frequency-side) Weil form of `zeta_K` has
nonnegative real part on every autocorrelation of a Weil test supported in `[-L, L]` with
`2L <= log X`.  This is a statement about the DEFINITION `weilFormQ`; see the module docstring. -/
def WindowPosX (X : ℝ) (d : ℤ) : Prop :=
  ∀ (g : ℝ → ℂ) (L : ℝ), IsWeilTest g → tsupport g ⊆ Set.Icc (-L) L → 2 * L ≤ Real.log X →
    0 ≤ (weilFormQ d (autocorr g)).re

/-- `W(N)` at an integer cutoff: `WindowPosX N`. -/
def WindowPos (N : ℕ) (d : ℤ) : Prop := WindowPosX (N : ℝ) d

theorem windowPos_iff (N : ℕ) (d : ℤ) : WindowPos N d ↔ WindowPosX (N : ℝ) d := Iff.rfl

/-- A smaller cutoff admits fewer tests: `WindowPosX` is antitone in `X` on `(0, ∞)`. -/
theorem WindowPosX.mono {X Y : ℝ} (hX : 0 < X) (hXY : X ≤ Y) {d : ℤ} (h : WindowPosX Y d) :
    WindowPosX X d := fun g L hg hsupp hL =>
  h g L hg hsupp (le_trans hL (Real.log_le_log hX hXY))

/-- `d` is the member of its cell of least `|d|`. -/
def IsCellMin (N : ℕ) (ε : ℕ → ℤ) (neg : Bool) (d : ℤ) : Prop :=
  InCell N ε neg d ∧ ∀ d', InCell N ε neg d' → d.natAbs ≤ d'.natAbs

/-- THE CELL REDUCTION at a real cutoff `0 < X <= N`: window positivity at the minimal member of
the cell (cut at `N`) gives it on the whole cell.  (`2L <= log X <= log N` keeps the finite prime
side over `n < N` and the cell decomposition.) -/
theorem cell_reduction {N : ℕ} (hN : 1 ≤ N) {X : ℝ} (hX0 : 0 < X) (hXN : X ≤ N)
    {ε : ℕ → ℤ} {neg : Bool} {dmin : ℤ}
    (hmin : IsCellMin N ε neg dmin) (hpos : WindowPosX X dmin) :
    ∀ d, InCell N ε neg d → WindowPosX X d := by
  intro d hd g L hg hsupp hL
  have hLN : 2 * L ≤ Real.log N := le_trans hL (Real.log_le_log hX0 hXN)
  have h1 := hpos g L hg hsupp hL
  have h2 := re_weilFormQ_mono hd hmin.1 (hmin.2 d hd) hg hsupp hN hLN
  linarith

/-- The integer-cutoff corollary at `X = N`. -/
theorem cell_reduction_nat {N : ℕ} (hN : 1 ≤ N) {ε : ℕ → ℤ} {neg : Bool} {dmin : ℤ}
    (hmin : IsCellMin N ε neg dmin) (hpos : WindowPos N dmin) :
    ∀ d, InCell N ε neg d → WindowPos N d :=
  cell_reduction hN (by exact_mod_cast hN) le_rfl hmin hpos

/-- A table entry: `some d` with `d` the minimal member, or `none` with a proof of emptiness. -/
def CellEntry (N : ℕ) (ε : ℕ → ℤ) (neg : Bool) : Option ℤ → Prop
  | some d => IsCellMin N ε neg d
  | none => ∀ d, ¬ InCell N ε neg d

/-- The reduction through a table entry, both branches, at a real cutoff `0 < X <= N`. -/
theorem reduction_of_entry {N : ℕ} (hN : 1 ≤ N) {X : ℝ} (hX0 : 0 < X) (hXN : X ≤ N)
    {ε : ℕ → ℤ} {neg : Bool} {e : Option ℤ}
    (he : CellEntry N ε neg e) (hpos : ∀ d, e = some d → WindowPosX X d) :
    ∀ d, InCell N ε neg d → WindowPosX X d := by
  cases e with
  | none => exact fun d hd => absurd hd (he d)
  | some dmin => exact cell_reduction hN hX0 hXN he (hpos dmin rfl)

end FamilyWeil
