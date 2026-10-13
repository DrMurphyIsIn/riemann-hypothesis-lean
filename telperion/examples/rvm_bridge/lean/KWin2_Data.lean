/-
  KWin2_Data -- the PARAMETRIC exact-rational data layer of the window certificate past the
  prime-free boundary (rvm_bridge island, 2026-09-24).

  conjecture1_proved = False.  A finite-window Weil positivity statement is NOT RH.  Nothing here is
  Connes-Consani (their theorem is for the pole-free class; the certificate keeps the pole terms,
  i.e. it is the goal node's full class).  Cf. PR #604: a finite-window margin is a statement about
  a finite window; at these windows it samples the zeros and proves nothing about them.

  WHAT CHANGES AGAINST KWin_Data.  KWin certified the prime-free edge 2L = log 2 with every
  parameter hard-wired (l = 26/75, T = 20, beta0 = 1.107, the seven pieces of [0, 20], ...).  Past
  2L = log 2 the PRIME COMB enters the Weil symbol,
      Psi_L(t) = Re psi(1/4 + it/2) - log pi - sum_{log n < 2L} (2 Lambda(n)/sqrt n) cos(t log n),
  and the certificate needs a larger frequency cut T (the comb lowers betaStar by its mass).  Here
  every parameter is a field of `KPar`, so one set of soundness proofs (KWin2_Head / KWin2_Tail)
  serves every window; a window is one `KPar` value plus its kernel evaluations.
    * the symbol minorant of Psi_0 = Re psi - log pi on the pieces of [0, T] (series floor with
      `Nser` terms, `nS` exact Lorentzians by geometric Taylor bounds, the rest by the alternating
      bound of order 2 Kalt), exactly KWin's construction with the constants as parameters;
    * the COMB is kept pointwise on [0, T]: an upper polynomial for c cos(t a) (c = 2 Lambda(2)/sqrt 2,
      a = log 2), from the Taylor polynomial of cos at t a0 (a0, c0 rational with |a - a0| <= da,
      |c - c0| <= dc proved in the instance file), coefficients rounded UP (t >= 0), the remainder,
      dc and c0 T da absorbed in the constant `combK` (checked by `combCheck`);
    * moments of (w_i - comb - beta0) t^q, the pi-scaled head matrix of the monomials (x/l)^(2k+par),
      KWin's LDL^T certificate (reused verbatim: KWin.psdCert), and the inverse Gram matrix by the
      CLOSED CAUCHY FORMULA (G_jk = l/(x_j + x_k), x_j = j + par/2 + 1/4), checked G G^-1 = I.
  Every Boolean checker here is evaluated by the kernel (`decide +kernel`) in the instance files.
  No `sorry`.
-/
import KWin_Data

open Finset

namespace KWin2
open KWin

/-! ## A. Parameters. -/

/-- The parameters of one window certificate (all exact rationals / naturals). -/
structure KPar where
  /-- head half-width `l` (the test support `[-L, L]` must lie inside `[-l, l]`) -/
  ell : ℚ
  /-- frequency cut `T` -/
  T : ℚ
  /-- envelope floor `beta0 <= betaStar L T` -/
  beta0 : ℚ
  /-- `|Psi_L - beta0| <= S0` on `[0, T]` -/
  S0 : ℚ
  /-- `cosh (l/2) <= Cp` -/
  Cp : ℚ
  /-- the breakpoints `0 = brk 0 < ... < brk nPc = T` -/
  brks : List ℚ
  /-- Taylor degrees per (piece, exact Lorentzian) -/
  degTab : List (List ℕ)
  /-- number of exact Lorentzians `x_j = j + 1/4`, `j < nS` -/
  nS : ℕ
  /-- alternating order: `1/(1+y) <= sum_{k <= 2 Kalt} (-y)^k` -/
  Kalt : ℕ
  /-- degree bound of the piece polynomials -/
  Dmax : ℕ
  /-- digamma series: explicit terms -/
  Nser : ℕ
  /-- digamma series: integral tail cut -/
  Mser : ℕ
  /-- `gamma <= gamUp` (proved in the instance file) -/
  gamUp : ℚ
  /-- `log pi <= logPiUp` (proved in the instance file) -/
  logPiUp : ℚ
  /-- transform Taylor order (head) -/
  Mt : ℕ
  /-- pole Taylor order (head) -/
  Mp : ℕ
  /-- `|log 2 - a0| <= da` -/
  a0 : ℚ
  da : ℚ
  /-- `|2 Lambda(2)/sqrt 2 - c0| <= dc` -/
  c0 : ℚ
  dc : ℚ
  /-- comb Taylor order: `cos y` by its Taylor polynomial of degree `< 2 Mc` -/
  Mc : ℕ
  /-- the comb constant (remainder + dc + c0 T da, rounded up) -/
  combK : ℚ
  /-- comb coefficient rounding: `t^p` coefficient ceiled at `10^-(Rc + 2p)` -/
  Rc : ℕ
  /-- head truncation error constant -/
  Econst : ℚ
  /-- the certified window floor -/
  lamFloor : ℚ

variable (P : KPar)

/-! ## B. The symbol minorant of Psi_0 (KWin's construction, parametric). -/

def nPc : ℕ := P.brks.length - 1
def brk (i : ℕ) : ℚ := P.brks.getD i P.T
def pcen (i : ℕ) : ℚ := (brk P i + brk P (i + 1)) / 2
def phw (i : ℕ) : ℚ := (brk P (i + 1) - brk P i) / 2
def deg (i j : ℕ) : ℕ := (P.degTab.getD i []).getD j 0

/-- Shifted coefficients of the exact-Lorentzian upper polynomial on piece `i`. -/
def uCoef (i k : ℕ) : ℚ := ∑ j ∈ range P.nS, if k ≤ deg P i j then kapR (bS j) (pcen P i) k else 0

def rhoRaw (i : ℕ) : ℚ := ∑ j ∈ range P.nS,
  (remB (bS j) (pcen P i) (phw P i) (deg P i j) + (∑ k ∈ range (deg P i j + 1), phw P i ^ k) / 10 ^ Rk)
def rhoR (i : ℕ) : ℚ := ceilR (rhoRaw P i) Rk

/-- `HNr <= H_Nser` (termwise floor at 10^-30). -/
def HNr : ℚ := (∑ n ∈ range P.Nser, ((10 ^ 30 / (n + 1) : ℕ) : ℚ)) / 10 ^ 30
def C0 : ℚ := -P.gamUp - P.logPiUp + HNr P + (1 / 4) / ((P.Nser : ℚ) + 5 / 4)
  - (1 / 2) * (((P.Nser : ℚ) + (P.Mser : ℚ) + 5 / 4) ^ 2 - ((P.Nser : ℚ) + (P.Mser : ℚ) + 1) ^ 2)
    / ((P.Nser : ℚ) + (P.Mser : ℚ) + 1) ^ 2
def C1 : ℚ := 1 / (8 * ((P.Nser : ℚ) + 5 / 4) ^ 2) - 1 / (8 * ((P.Nser : ℚ) + (P.Mser : ℚ) + 1) ^ 2)
def C2 : ℚ := -1 / (32 * ((P.Nser : ℚ) + 5 / 4) ^ 4)

/-- An upper bound on `(-1)^k sum_{nS <= j <= Nser} 4^(k+1) / (4 j + 1)^(2k+1)` (termwise ceiling /
floor at `10^-(30+3k)`). -/
def gAlt (k : ℕ) : ℚ :=
  if k % 2 = 0 then
    (∑ j ∈ Ico P.nS (P.Nser + 1), (((4 ^ (k + 1) * 10 ^ (30 + 3 * k) + (4 * j + 1) ^ (2 * k + 1) - 1)
      / (4 * j + 1) ^ (2 * k + 1) : ℕ) : ℚ)) / 10 ^ (30 + 3 * k)
  else
    -(∑ j ∈ Ico P.nS (P.Nser + 1), ((4 ^ (k + 1) * 10 ^ (30 + 3 * k) / (4 * j + 1) ^ (2 * k + 1) : ℕ) : ℚ))
      / 10 ^ (30 + 3 * k)

def globRaw (p : ℕ) : ℚ :=
  (if p = 0 then C0 P else if p = 2 then C1 P else if p = 4 then C2 P else 0)
  - (if p % 2 = 0 ∧ p / 2 < 2 * P.Kalt + 1 then gAlt P (p / 2) else 0)
def globC (p : ℕ) : ℚ := floorR (globRaw P p) (30 + 3 * (p / 2))
def globList : List ℚ := (List.range (P.Dmax + 1)).map (globC P)

def uList (i : ℕ) : List ℚ := (List.range (P.Dmax + 1)).map (uCoef P i)
/-- Power-basis coefficients of the Psi_0 minorant on piece `i`. -/
def wpCoef (i p : ℕ) : ℚ := (globList P).getD p 0
  - (∑ k ∈ range (P.Dmax + 1), if p ≤ k then (uList P i).getD k 0 * (k.choose p) * (-pcen P i) ^ (k - p) else 0)
  - (if p = 0 then rhoR P i else 0)
def wpList (i : ℕ) : List ℚ := (List.range (P.Dmax + 1)).map (wpCoef P i)

/-! ## C. The comb upper polynomial. -/

/-- Coefficient of `t^p` in the upper polynomial of `c cos(t a)` on `[0, T]`. -/
def combC (p : ℕ) : ℚ :=
  (if p % 2 = 0 ∧ p / 2 < P.Mc then
    ceilR (P.c0 * (-1) ^ (p / 2) * P.a0 ^ p / (p.factorial : ℚ)) (P.Rc + 2 * p) else 0)
  + (if p = 0 then P.combK else 0)
def combList : List ℚ := (List.range (2 * P.Mc + 1)).map (combC P)

/-! ## D. Moments and the head matrix. -/

/-- `int_{brk i}^{brk (i+1)} (w_i t - beta0) t^q dt`. -/
def momPiece (i q : ℕ) : ℚ :=
  (∑ p ∈ range (P.Dmax + 1), (wpList P i).getD p 0
      * (brk P (i + 1) ^ (p + q + 1) - brk P i ^ (p + q + 1)) / (p + q + 1))
  - P.beta0 * (brk P (i + 1) ^ (q + 1) - brk P i ^ (q + 1)) / (q + 1)
/-- `int_0^T comb(t) t^q dt`. -/
def momComb (q : ℕ) : ℚ :=
  ∑ p ∈ range (2 * P.Mc + 1), (combList P).getD p 0 * P.T ^ (p + q + 1) / (p + q + 1)
/-- `int_0^T (w - comb - beta0) t^q` over the pieces. -/
def mom (q : ℕ) : ℚ := (∑ i ∈ range (nPc P), momPiece P i q) - momComb P q
def momList (par : ℕ) : List ℚ := (List.range (2 * P.Mt)).map (fun s => mom P (2 * s + 2 * par))

/-- Gram matrix of the scaled monomials: `int_{-l}^{l} (x/l)^(2j+par) (x/l)^(2k+par) dx`. -/
def Gm (par j k : ℕ) : ℚ := 2 * P.ell / (2 * j + 2 * k + 2 * par + 1)
/-- Taylor coefficient matrix of the transforms: `c_m = sum_k Bm par m k a_k`. -/
def Bm (par m k : ℕ) : ℚ := (-1) ^ m * P.ell ^ (2 * m + par) / ((2 * m + par).factorial : ℚ) * Gm P par m k
/-- The truncated pole functional of `(x/l)^(2k+par)`. -/
def pv (par k : ℕ) : ℚ :=
  ∑ m ∈ range P.Mp, (P.ell / 2) ^ (2 * m + par) / ((2 * m + par).factorial : ℚ) * Gm P par m k

def WBrow (par N m : ℕ) : List ℚ :=
  (List.range N).map (fun k => ∑ m' ∈ range P.Mt, (momList P par).getD (m + m') 0 * Bm P par m' k)
def WBmat (par N : ℕ) : List (List ℚ) := (List.range P.Mt).map (WBrow P par N)

def diagc (lam : ℚ) : ℚ := piLoQ * (P.beta0 - lam) - 2 * P.ell * P.Econst

def headEntry (par N : ℕ) (lam : ℚ) (j k : ℕ) : ℚ :=
  2 * piEQ par * epsQ par * pv P par j * pv P par k + diagc P lam * Gm P par j k
  + ∑ m ∈ range P.Mt, Bm P par m j * ((WBmat P par N).getD m []).getD k 0
def headMat (par N : ℕ) (lam : ℚ) : List (List ℚ) :=
  (List.range N).map (fun j => (List.range N).map (headEntry P par N lam j))

/-! ## E. The inverse Gram matrix (closed Cauchy formula). -/

/-- The Cauchy nodes: `Gm par j k = l / (cx par j + cx par k)`. -/
def cx (par j : ℕ) : ℚ := (j : ℚ) + (par : ℚ) / 2 + 1 / 4

/-- `(G^-1)_{ij}` by Cauchy's formula (untrusted: re-verified by `ginvCheck`). -/
def ginvE (par N i j : ℕ) : ℚ :=
  (∏ k ∈ range N, (cx par j + cx par k)) * (∏ k ∈ range N, (cx par k + cx par i))
  / ((cx par j + cx par i)
      * (∏ k ∈ range N, (if k = j then 1 else cx par j - cx par k))
      * (∏ k ∈ range N, (if k = i then 1 else cx par i - cx par k)))
  / P.ell

def ginvM (par N : ℕ) : List (List ℚ) :=
  (List.range N).map (fun i => (List.range N).map (ginvE P par N i))

def ginvCheck (par N : ℕ) : Bool :=
  (List.range N).all (fun j => (List.range N).all (fun k =>
    decide ((∑ l ∈ range N, Gm P par j l * mget (ginvM P par N) l k) = if j = k then 1 else 0)))

/-! ## F. Side conditions. -/

/-- The breakpoints start at 0, end at T, and increase. -/
def brkCheck : Bool :=
  decide (brk P 0 = 0) && decide (brk P (nPc P) = P.T) &&
  (List.range (nPc P)).all (fun i => decide (brk P i ≤ brk P (i + 1)))

def pieceCheck : Bool :=
  (List.range (nPc P)).all (fun i => (List.range P.nS).all (fun j =>
    decide (phw P i < smax (bS j) (pcen P i)) && decide (deg P i j ≤ P.Dmax)))

/-- The comb constant covers the Taylor remainder, `dc` and `c0 T da`. -/
def combCheck : Bool :=
  decide (0 ≤ P.c0) && decide (0 ≤ P.a0) && decide (0 ≤ P.da) && decide (0 ≤ P.dc) &&
  decide (P.a0 * P.T ≤ ((2 * P.Mc + 1 : ℕ) : ℚ) / 2) &&
  decide (P.c0 * (2 * (P.a0 * P.T) ^ (2 * P.Mc) / ((2 * P.Mc).factorial : ℚ)) + P.dc + P.c0 * P.T * P.da
    ≤ P.combK)

/-- Structural conditions of the minorant construction (series split, alternating and base terms
inside the piece degree). -/
def minCheck : Bool :=
  decide (P.nS ≤ P.Nser + 1) && decide (4 * P.Kalt ≤ P.Dmax) && decide (4 ≤ P.Dmax)

/-- Positivity and size of the basic parameters. -/
def parCheck : Bool :=
  decide (0 < P.ell) && decide (P.ell ≤ 2) && decide (0 < P.T) && decide (0 ≤ P.S0) &&
  decide (0 ≤ P.Cp) && decide (0 ≤ P.Econst) && decide (0 < P.lamFloor) && decide (1 ≤ P.Mp)

/-- The head truncation error: pole (Mp terms) and transform (Mt terms) remainders. -/
def Ehead (par : ℕ) : ℚ :=
  2 * piHiQ * (2 * (P.ell / 2) ^ (2 * P.Mp + par) / ((2 * P.Mp + par).factorial : ℚ))
      * (2 * P.Cp + 2 * (P.ell / 2) ^ (2 * P.Mp + par) / ((2 * P.Mp + par).factorial : ℚ))
  + P.S0 * (2 * (2 * P.ell ^ (2 * P.Mt + par) * P.T ^ (2 * P.Mt + par + 1)
        / ((2 * P.Mt + par + 1) * ((2 * P.Mt + par).factorial : ℚ)))
      + 4 * P.ell ^ (2 * (2 * P.Mt + par)) * P.T ^ (2 * (2 * P.Mt + par) + 1)
        / ((2 * (2 * P.Mt + par) + 1) * ((2 * P.Mt + par).factorial : ℚ) ^ 2))

/-- Tail constants after `N` head modes: pole remainder, `int_0^T eps_N`, `int_0^T eps_N^2`. -/
def dPT (par N : ℕ) : ℚ := 2 * (P.ell / 2) ^ (2 * N + par) / ((2 * N + par).factorial : ℚ)
def I1T (par N : ℕ) : ℚ :=
  2 * P.ell ^ (2 * N + par) * P.T ^ (2 * N + par + 1) / ((2 * N + par + 1) * ((2 * N + par).factorial : ℚ))
def I2T (par N : ℕ) : ℚ :=
  4 * P.ell ^ (2 * (2 * N + par)) * P.T ^ (2 * (2 * N + par) + 1)
    / ((2 * (2 * N + par) + 1) * ((2 * N + par).factorial : ℚ) ^ 2)
/-- Coupling constant `|R(h, r)| <= kapT A1(h) A1(r)` (uses `1/pi <= 1/3`). -/
def kapT (par N : ℕ) : ℚ := 2 * P.Cp * dPT P par N + P.S0 / 3 * I1T P par N
/-- Tail floor `R(r, r) >= dT * int r^2`. -/
def dT (par N : ℕ) : ℚ := P.beta0 - 2 * P.ell * (2 * dPT P par N ^ 2 + P.S0 / 3 * I2T P par N)

def tailCond (par N : ℕ) (lam : ℚ) : Bool :=
  decide (P.lamFloor ≤ lam) && decide (P.lamFloor ≤ dT P par N) &&
  decide (4 * kapT P par N ^ 2 * P.ell ^ 2 ≤ (lam - P.lamFloor) * (dT P par N - P.lamFloor)) &&
  decide (Ehead P par ≤ P.Econst) && decide (lam < P.beta0) &&
  decide (P.T * P.ell ≤ ((2 * N + par + 1 : ℕ) : ℚ) / 2) &&
  decide (P.T * P.ell ≤ ((2 * P.Mt + par + 1 : ℕ) : ℚ) / 2) && decide (1 ≤ N)

/-! ## G. The real-valued polynomials. -/

/-- The Psi_0 minorant polynomial on piece `i`. -/
noncomputable def wpoly (i : ℕ) (t : ℝ) : ℝ :=
  ∑ p ∈ range (P.Dmax + 1), (((wpList P i).getD p 0 : ℚ) : ℝ) * t ^ p

/-- The comb upper polynomial. -/
noncomputable def combPoly (t : ℝ) : ℝ :=
  ∑ p ∈ range (2 * P.Mc + 1), (((combList P).getD p 0 : ℚ) : ℝ) * t ^ p

/-! ## H. Extraction of the side conditions. -/

theorem brkCheck_sound (h : brkCheck P = true) :
    brk P 0 = 0 ∧ brk P (nPc P) = P.T ∧ ∀ i < nPc P, brk P i ≤ brk P (i + 1) := by
  unfold brkCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem pieceCheck_sound (h : pieceCheck P = true) {i j : ℕ} (hi : i < nPc P) (hj : j < P.nS) :
    phw P i < smax (bS j) (pcen P i) ∧ deg P i j ≤ P.Dmax := by
  unfold pieceCheck at h
  rw [List.all_eq_true] at h
  have := h i (List.mem_range.mpr hi)
  rw [List.all_eq_true] at this
  have h2 := this j (List.mem_range.mpr hj)
  rw [Bool.and_eq_true] at h2
  exact ⟨of_decide_eq_true h2.1, of_decide_eq_true h2.2⟩

theorem combCheck_sound (h : combCheck P = true) :
    0 ≤ P.c0 ∧ 0 ≤ P.a0 ∧ 0 ≤ P.da ∧ 0 ≤ P.dc ∧ P.a0 * P.T ≤ ((2 * P.Mc + 1 : ℕ) : ℚ) / 2 ∧
      P.c0 * (2 * (P.a0 * P.T) ^ (2 * P.Mc) / ((2 * P.Mc).factorial : ℚ)) + P.dc + P.c0 * P.T * P.da
        ≤ P.combK := by
  unfold combCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem minCheck_sound (h : minCheck P = true) :
    P.nS ≤ P.Nser + 1 ∧ 4 * P.Kalt ≤ P.Dmax ∧ 4 ≤ P.Dmax := by
  unfold minCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem parCheck_sound (h : parCheck P = true) :
    0 < P.ell ∧ P.ell ≤ 2 ∧ 0 < P.T ∧ 0 ≤ P.S0 ∧ 0 ≤ P.Cp ∧ 0 ≤ P.Econst ∧ 0 < P.lamFloor
      ∧ 1 ≤ P.Mp := by
  unfold parCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem ginvCheck_sound {par N : ℕ} (h : ginvCheck P par N = true) {j k : ℕ} (hj : j < N)
    (hk : k < N) :
    (∑ l ∈ range N, Gm P par j l * mget (ginvM P par N) l k) = if j = k then 1 else 0 := by
  unfold ginvCheck at h
  rw [List.all_eq_true] at h
  have := h j (List.mem_range.mpr hj)
  rw [List.all_eq_true] at this
  exact of_decide_eq_true (this k (List.mem_range.mpr hk))

theorem tailCond_sound {par N : ℕ} {lam : ℚ} (h : tailCond P par N lam = true) :
    P.lamFloor ≤ lam ∧ P.lamFloor ≤ dT P par N
      ∧ 4 * kapT P par N ^ 2 * P.ell ^ 2 ≤ (lam - P.lamFloor) * (dT P par N - P.lamFloor)
      ∧ Ehead P par ≤ P.Econst ∧ lam < P.beta0
      ∧ P.T * P.ell ≤ ((2 * N + par + 1 : ℕ) : ℚ) / 2
      ∧ P.T * P.ell ≤ ((2 * P.Mt + par + 1 : ℕ) : ℚ) / 2 ∧ 1 ≤ N := by
  unfold tailCond at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

end KWin2
