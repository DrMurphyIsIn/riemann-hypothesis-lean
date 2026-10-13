/-
  Hodge1_KPen -- the exact-rational data layer of the HODGE-1 archimedean strip certificate
  (2026-10-12, Phase 1b-A; design notes, unpublished, sections 2 and 4).

  conjecture1_proved = False.  Nothing here involves the zeros or the primes: the symbol is the
  archimedean Psi = Re psi(1/4 + it/2) - log pi, with no comb.

  WHAT CHANGES AGAINST KWin2_Data.  An `HPar` is a `KWin2.KPar` (comb switched off: c0 = dc = combK = 0)
  plus three numbers:
    * pc   : the PENALTY coefficient of the pole functional, replacing KWin2's 2 eps.  On the
             two-condition pole-free class the pole functional of every parity piece vanishes, so
             any pc >= 0 may be added for free; pc = 1000 restores the margin of the hyperplane;
    * s0   : the inner edge of the strip block S' = {s0 <= |x| <= l}  (s0 <= log 2 - l);
    * w2up : a rational upper bound for w2 = log 2 / sqrt 2.
  The head matrix gains the strip block -pi_hi w2up (Pim + eta leakQ), with
    * Pim_jk = 2 int_{s0}^{l} (x/l)^(2j+2k+2par) dx  (closed form; the strip Gram of the head monomials);
    * leakQ = Pim - Pim D - (Pim D)^T + D^T G D,  the Gram form of the LEAKAGE  || 1_S' h - p ||^2
      where p = sum_k (D a)_k (x/l)^(2k+par) is any head polynomial; D is an untrusted rational matrix
      (the generator hodge1_gen.py takes D = G^{-1} Pim rounded at 10^-25; any D is sound).
  The tail constants become kapTP = pc Cp dPT + S0/3 I1T and dTP = beta0 - 2 l S0/3 I2T - w2up (1 + 1/eta)
  (the tail pole term pc (Pl r)^2 >= 0 is dropped; the strip costs w2up (1 + 1/eta) of the tail).
  Every Boolean checker is evaluated by the kernel (`decide +kernel`) in the instance files.  No `sorry`.
-/
import KWin2_Round

open Finset

namespace Hodge1
open KWin KWin2

/-- The parameters of one HODGE-1 strip certificate. -/
structure HPar where
  /-- the KWin2 window data (symbol minorant, head truncations, tail floor `lamFloor`) -/
  K : KPar
  /-- the penalty coefficient of the pole functional -/
  pc : ℚ
  /-- the inner edge of the strip block -/
  s0 : ℚ
  /-- the strip weight, `>= log 2 / sqrt 2` -/
  w2up : ℚ

variable (H : HPar)

/-- The strip Gram matrix: `2 int_{s0}^{l} (x/l)^(2j+2k+2par) dx = 2l/(n+1) (1 - (s0/l)^(n+1))`. -/
def Pim (par j k : ℕ) : ℚ :=
  2 * H.K.ell / (2 * j + 2 * k + 2 * par + 1) * (1 - (H.s0 / H.K.ell) ^ (2 * j + 2 * k + 2 * par + 1))

/-- `(Pim D)_jk`. -/
def PDmat (par N : ℕ) (D : List (List ℚ)) : List (List ℚ) :=
  (List.range N).map (fun j => (List.range N).map (fun k =>
    ∑ i ∈ range N, Pim H par j i * mget D i k))

/-- `(G D)_ik`. -/
def GDmat (par N : ℕ) (D : List (List ℚ)) : List (List ℚ) :=
  (List.range N).map (fun i => (List.range N).map (fun k =>
    ∑ i' ∈ range N, Gm H.K par i i' * mget D i' k))

/-- `(D^T G D)_jk`. -/
def DGDmat (par N : ℕ) (D : List (List ℚ)) : List (List ℚ) :=
  (List.range N).map (fun j => (List.range N).map (fun k =>
    ∑ i ∈ range N, mget D i j * mget (GDmat H par N D) i k))

/-- The leakage Gram form `Pim - Pim D - (Pim D)^T + D^T G D`. -/
def leakQ (par N : ℕ) (D : List (List ℚ)) (j k : ℕ) : ℚ :=
  Pim H par j k - mget (PDmat H par N D) j k - mget (PDmat H par N D) k j + mget (DGDmat H par N D) j k

/-- The pi-scaled head matrix of `pc Pl^2 + beta0 int + (1/pi) int_0^T (Psi - beta0) Tr^2
- w2up (Pi' + eta leak) - lam int`, with the head errors charged on the diagonal. -/
def headEntryP (par N : ℕ) (lam eta : ℚ) (D : List (List ℚ)) (j k : ℕ) : ℚ :=
  piLoQ * H.pc * pv H.K par j * pv H.K par k + diagc H.K lam * Gm H.K par j k
  + ∑ m ∈ range H.K.Mt, Bm H.K par m j * ((WBmat H.K par N).getD m []).getD k 0
  - piHiQ * H.w2up * (Pim H par j k + eta * leakQ H par N D j k)

def headMatP (par N : ℕ) (lam eta : ℚ) (D : List (List ℚ)) : List (List ℚ) :=
  (List.range N).map (fun j => (List.range N).map (headEntryP H par N lam eta D j))

/-- The head truncation error with the penalty coefficient `pc` in place of `2`. -/
def EheadP (par : ℕ) : ℚ :=
  H.pc * piHiQ * (2 * (H.K.ell / 2) ^ (2 * H.K.Mp + par) / ((2 * H.K.Mp + par).factorial : ℚ))
      * (2 * H.K.Cp + 2 * (H.K.ell / 2) ^ (2 * H.K.Mp + par) / ((2 * H.K.Mp + par).factorial : ℚ))
  + H.K.S0 * (2 * (2 * H.K.ell ^ (2 * H.K.Mt + par) * H.K.T ^ (2 * H.K.Mt + par + 1)
        / ((2 * H.K.Mt + par + 1) * ((2 * H.K.Mt + par).factorial : ℚ)))
      + 4 * H.K.ell ^ (2 * (2 * H.K.Mt + par)) * H.K.T ^ (2 * (2 * H.K.Mt + par) + 1)
        / ((2 * (2 * H.K.Mt + par) + 1) * ((2 * H.K.Mt + par).factorial : ℚ) ^ 2))

/-- Coupling constant `|RbP(h, r)| <= kapTP A1(h) A1(r)`. -/
def kapTP (par N : ℕ) : ℚ := H.pc * H.K.Cp * dPT H.K par N + H.K.S0 / 3 * I1T H.K par N

/-- Tail floor of the strip form: `RbP(r, r) - w2up (1 + 1/eta) int r^2 >= dTP int r^2`. -/
def dTP (par N : ℕ) (eta : ℚ) : ℚ :=
  H.K.beta0 - 2 * H.K.ell * (H.K.S0 / 3 * I2T H.K par N) - H.w2up * (1 + 1 / eta)

def tailCondP (par N : ℕ) (lam eta : ℚ) : Bool :=
  decide (H.K.lamFloor ≤ lam) && decide (H.K.lamFloor ≤ dTP H par N eta) &&
  decide (4 * kapTP H par N ^ 2 * H.K.ell ^ 2 ≤ (lam - H.K.lamFloor) * (dTP H par N eta - H.K.lamFloor)) &&
  decide (EheadP H par ≤ H.K.Econst) && decide (lam < H.K.beta0) &&
  decide (H.K.T * H.K.ell ≤ ((2 * N + par + 1 : ℕ) : ℚ) / 2) &&
  decide (H.K.T * H.K.ell ≤ ((2 * H.K.Mt + par + 1 : ℕ) : ℚ) / 2) && decide (1 ≤ N) &&
  decide (0 ≤ H.pc) && decide (0 < eta) && decide (0 ≤ H.w2up) && decide (0 ≤ H.s0) &&
  decide (H.s0 ≤ H.K.ell)

theorem tailCondP_sound {par N : ℕ} {lam eta : ℚ} (h : tailCondP H par N lam eta = true) :
    H.K.lamFloor ≤ lam ∧ H.K.lamFloor ≤ dTP H par N eta
      ∧ 4 * kapTP H par N ^ 2 * H.K.ell ^ 2 ≤ (lam - H.K.lamFloor) * (dTP H par N eta - H.K.lamFloor)
      ∧ EheadP H par ≤ H.K.Econst ∧ lam < H.K.beta0
      ∧ H.K.T * H.K.ell ≤ ((2 * N + par + 1 : ℕ) : ℚ) / 2
      ∧ H.K.T * H.K.ell ≤ ((2 * H.K.Mt + par + 1 : ℕ) : ℚ) / 2 ∧ 1 ≤ N
      ∧ 0 ≤ H.pc ∧ 0 < eta ∧ 0 ≤ H.w2up ∧ 0 ≤ H.s0 ∧ H.s0 ≤ H.K.ell := by
  unfold tailCondP at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

end Hodge1
