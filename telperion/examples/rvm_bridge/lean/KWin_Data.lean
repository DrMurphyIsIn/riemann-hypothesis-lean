/-
  KWin_Data -- the exact-rational data of the prime-free window certificate at 2L = log 2
  (rvm_bridge island, 2026-09-24).

  conjecture1_proved = False.  A finite-window Weil positivity statement is NOT RH.  PR #604
  found that the 1.3e-3 full-class margin at this window is zero content (the zero sum over the
  first 200 zero pairs is 0.001301 against a least eigenvalue of 0.001329), and Connes-Consani's
  theorem is for a pole-free class (margin 0.547 on paperFT g (±i/2) = 0, 0.0723 on the
  one-condition class paperFT g (i/2) = 0), so nothing below is their result.

  WHAT THIS FILE IS.  Computable definitions over `ℚ` / `ℕ`, evaluated by the Lean kernel itself
  (`decide +kernel`: the kernel reduces the Boolean checker; no compiled-code evaluation and no
  trusted-reduction shortcut).  Nothing here is analysis; the modules KWin_Minorant / KWin_Head consume the
  data through the soundness lemmas of sections H-J.
    * B. the symbol minorant w_i on the 7 pieces [brk i, brk (i+1)] of [0, 20]: the island's
      series floor (psiR_ge_series with N = 400 explicit terms and the integral tail), the
      Lorentzians x/(x^2 + (r/2)^2), x = j + 1/4, j < 18, bounded on each piece by their
      geometric Taylor polynomial about the centre (coefficients `kap`, floor-rounded at
      10^-30, remainder `remB`), the Lorentzians 18 <= j <= 400 by the global alternating
      bound 1/(1+y) <= sum_{k<=10} (-y)^k, all constants rounded in the safe direction;
    * C. the moments of (w - beta0) t^q over [0, 20] and the pi-scaled head matrix of the
      scaled monomials (x/l)^(2k+par), l = 26/75, k < N (N = 12 even, N = 10 odd);
    * D. an LDL^T certificate: the kernel factors the head matrix exactly and re-verifies
      A = sum_s d_s v_s v_s^T entrywise with every d_s >= 0 (soundness is pure algebra);
    * E. the exact inverse of the Gram matrix of the head monomials (data; G * G^-1 = I checked).
  No `sorry`.
-/
import Mathlib

open Finset

namespace KWin

/-! ## A. Parameters. -/

/-- The head half-width `l = 26/75`; `log 2 / 2 < l`. -/
def ellQ : ℚ := 26 / 75
/-- The frequency cut `T = 20`. -/
def TQ : ℚ := 20
/-- The rational envelope floor `beta0 <= beta*(log 2 / 2, 20) = log (10/pi) - 1/20`. -/
def beta0Q : ℚ := 1107 / 1000
/-- `Real.pi_gt_d20`. -/
def piLoQ : ℚ := 314159265358979323846 / 10 ^ 20
/-- `Real.pi_lt_d20`. -/
def piHiQ : ℚ := 314159265358979323847 / 10 ^ 20
/-- `|Psi - beta0| <= S0` on `[0, 20]`. -/
def S0Q : ℚ := 6485 / 1000
/-- `cosh (l / 2) <= Cp`. -/
def CpQ : ℚ := 102 / 100
/-- `gamma <= H_16 - 4 * 0.6931471803 - 1/32 + 1/3072` (Euler-Maclaurin, KWin_Constants). -/
def gammaUpQ : ℚ := (∑ k ∈ range 16, (1 : ℚ) / (k + 1)) - 4 * (6931471803 / 10 ^ 10) - 1 / 32 + 1 / 3072
/-- `log pi <= 1.1447298859`. -/
def logPiUpQ : ℚ := 11447298859 / 10 ^ 10

/-! ## B. The symbol minorant. -/

/-- The breakpoints `0 = brk 0 < ... < brk 7 = 20` of the seven pieces. -/
def brk : ℕ → ℚ
  | 0 => 0
  | 1 => 3 / 10
  | 2 => 4 / 5
  | 3 => 8 / 5
  | 4 => 16 / 5
  | 5 => 32 / 5
  | 6 => 64 / 5
  | _ => 20

def nPc : ℕ := 7
def pcen (i : ℕ) : ℚ := (brk i + brk (i + 1)) / 2
def phw (i : ℕ) : ℚ := (brk (i + 1) - brk i) / 2

/-- Number of Lorentzians kept exact (per piece): `x_j = j + 1/4`, `j < 18`. -/
def nS : ℕ := 18
/-- `b_j = 2 x_j = 2 j + 1/2`. -/
def bS (j : ℕ) : ℚ := 2 * j + 1 / 2

/-- Taylor degrees per (piece, Lorentzian): chosen offline so each remainder is <= 1e-8. -/
def degTab : List (List ℕ) :=
  [[16, 6, 5, 4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 2],
   [18, 7, 6, 5, 4, 4, 4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
   [17, 9, 7, 6, 5, 5, 4, 4, 4, 4, 4, 3, 3, 3, 3, 3, 3, 3],
   [16, 12, 9, 8, 7, 6, 6, 5, 5, 5, 4, 4, 4, 4, 4, 4, 4, 4],
   [16, 15, 12, 10, 9, 8, 8, 7, 7, 6, 6, 6, 5, 5, 5, 5, 5, 5],
   [15, 15, 15, 13, 12, 11, 10, 9, 9, 8, 8, 8, 7, 7, 7, 7, 6, 6],
   [10, 10, 10, 10, 10, 9, 9, 9, 8, 8, 8, 7, 7, 7, 7, 7, 6, 6]]

def deg (i j : ℕ) : ℕ := (degTab.getD i []).getD j 0
def Dmax : ℕ := 20
def Rk : ℕ := 30

/-- A rational lower bound `s <= sqrt (b^2 + c^2)` (for `0 <= b, c`). -/
def smax (b c : ℚ) : ℚ := max (max b c) (7 / 10 * (b + c))

/-- Powers of the Gaussian rational `x + i y`: `(gpow x y n).1 + i (gpow x y n).2 = (x + i y)^n`. -/
def gpow (x y : ℚ) : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | n + 1 => match gpow x y n with
    | (p, q) => (p * x - q * y, p * y + q * x)

/-- `kap b c k = 2 Re (i^k / (b - i c)^(k+1))`, the Taylor coefficients of `2 Re (1/(b - i t))`
about `t = c`. -/
def kap (b c : ℚ) (k : ℕ) : ℚ :=
  2 * (if k % 4 = 0 then (gpow (b / (b * b + c * c)) (c / (b * b + c * c)) (k + 1)).1
    else if k % 4 = 1 then -(gpow (b / (b * b + c * c)) (c / (b * b + c * c)) (k + 1)).2
    else if k % 4 = 2 then -(gpow (b / (b * b + c * c)) (c / (b * b + c * c)) (k + 1)).1
    else (gpow (b / (b * b + c * c)) (c / (b * b + c * c)) (k + 1)).2)

def floorR (q : ℚ) (R : ℕ) : ℚ := (⌊q * 10 ^ R⌋ : ℚ) / 10 ^ R
def ceilR (q : ℚ) (R : ℕ) : ℚ := (⌈q * 10 ^ R⌉ : ℚ) / 10 ^ R

def kapR (b c : ℚ) (k : ℕ) : ℚ := floorR (kap b c k) Rk

/-- The geometric remainder `2 rho^(d+1) / ((1 - rho) s)`, `rho = h / s`. -/
def remB (b c h : ℚ) (d : ℕ) : ℚ :=
  2 * (h / smax b c) ^ (d + 1) / ((1 - h / smax b c) * smax b c)

/-- Shifted coefficients of the exact-Lorentzian upper polynomial on piece `i`. -/
def uCoef (i k : ℕ) : ℚ := ∑ j ∈ range nS, if k ≤ deg i j then kapR (bS j) (pcen i) k else 0

def rhoRaw (i : ℕ) : ℚ := ∑ j ∈ range nS,
  (remB (bS j) (pcen i) (phw i) (deg i j) + (∑ k ∈ range (deg i j + 1), phw i ^ k) / 10 ^ Rk)
def rhoR (i : ℕ) : ℚ := ceilR (rhoRaw i) Rk

def Nser : ℕ := 400
def Mser : ℕ := 10 ^ 9
def Kalt : ℕ := 5

/-- `HNr <= H_400` (termwise floor at 10^-30). -/
def HNr : ℚ := (∑ n ∈ range Nser, ((10 ^ 30 / (n + 1) : ℕ) : ℚ)) / 10 ^ 30
def NQ : ℚ := Nser
def MQ : ℚ := Mser
def C0 : ℚ := -gammaUpQ - logPiUpQ + HNr + (1 / 4) / (NQ + 5 / 4)
  - (1 / 2) * ((NQ + MQ + 5 / 4) ^ 2 - (NQ + MQ + 1) ^ 2) / (NQ + MQ + 1) ^ 2
def C1 : ℚ := 1 / (8 * (NQ + 5 / 4) ^ 2) - 1 / (8 * (NQ + MQ + 1) ^ 2)
def C2 : ℚ := -1 / (32 * (NQ + 5 / 4) ^ 4)

/-- An upper bound on `(-1)^k sum_{18 <= j <= 400} 4^(k+1) / (4 j + 1)^(2k+1)` (termwise
ceiling / floor at `10^-(30+3k)`). -/
def gAlt (k : ℕ) : ℚ :=
  if k % 2 = 0 then
    (∑ j ∈ Ico nS (Nser + 1), (((4 ^ (k + 1) * 10 ^ (30 + 3 * k) + (4 * j + 1) ^ (2 * k + 1) - 1)
      / (4 * j + 1) ^ (2 * k + 1) : ℕ) : ℚ)) / 10 ^ (30 + 3 * k)
  else
    -(∑ j ∈ Ico nS (Nser + 1), ((4 ^ (k + 1) * 10 ^ (30 + 3 * k) / (4 * j + 1) ^ (2 * k + 1) : ℕ) : ℚ))
      / 10 ^ (30 + 3 * k)

def globRaw (p : ℕ) : ℚ :=
  (if p = 0 then C0 else if p = 2 then C1 else if p = 4 then C2 else 0)
  - (if p % 2 = 0 ∧ p / 2 ≤ 2 * Kalt then gAlt (p / 2) else 0)
def globC (p : ℕ) : ℚ := floorR (globRaw p) (30 + 3 * (p / 2))
def globList : List ℚ := (List.range (Dmax + 1)).map globC

def uList (i : ℕ) : List ℚ := (List.range (Dmax + 1)).map (uCoef i)
/-- Power-basis coefficients of the minorant on piece `i`:
`w_i(t) = sum_p globC p t^p - sum_k uCoef i k (t - c_i)^k - rhoR i`. -/
def wpCoef (i p : ℕ) : ℚ := globList.getD p 0
  - (∑ k ∈ range (Dmax + 1), if p ≤ k then (uList i).getD k 0 * (k.choose p) * (-pcen i) ^ (k - p) else 0)
  - (if p = 0 then rhoR i else 0)
def wpList (i : ℕ) : List ℚ := (List.range (Dmax + 1)).map (wpCoef i)

/-! ## C. Moments and the head matrix. -/

/-- `int_{brk i}^{brk (i+1)} (w_i t - beta0) t^q dt`. -/
def momPiece (i q : ℕ) : ℚ :=
  (∑ p ∈ range (Dmax + 1), (wpList i).getD p 0 * (brk (i + 1) ^ (p + q + 1) - brk i ^ (p + q + 1)) / (p + q + 1))
  - beta0Q * (brk (i + 1) ^ (q + 1) - brk i ^ (q + 1)) / (q + 1)
def mom (q : ℕ) : ℚ := ∑ i ∈ range nPc, momPiece i q

def Mt : ℕ := 16
def Mp : ℕ := 8
def momList (par : ℕ) : List ℚ := (List.range (2 * Mt)).map (fun s => mom (2 * s + 2 * par))

/-- Gram matrix of the scaled monomials: `int_{-l}^{l} (x/l)^(2j+par) (x/l)^(2k+par) dx`. -/
def Gm (par j k : ℕ) : ℚ := 2 * ellQ / (2 * j + 2 * k + 2 * par + 1)
/-- Taylor coefficient matrix of the transforms: `c_m = sum_k Bm par m k a_k`. -/
def Bm (par m k : ℕ) : ℚ := (-1) ^ m * ellQ ^ (2 * m + par) / ((2 * m + par).factorial : ℚ) * Gm par m k
/-- The truncated pole functional of `(x/l)^(2k+par)`. -/
def pv (par k : ℕ) : ℚ := ∑ m ∈ range Mp, (ellQ / 2) ^ (2 * m + par) / ((2 * m + par).factorial : ℚ) * Gm par m k

def WBrow (par N m : ℕ) : List ℚ :=
  (List.range N).map (fun k => ∑ m' ∈ range Mt, (momList par).getD (m + m') 0 * Bm par m' k)
def WBmat (par N : ℕ) : List (List ℚ) := (List.range Mt).map (WBrow par N)

def epsQ (par : ℕ) : ℚ := if par = 0 then 1 else -1
def piEQ (par : ℕ) : ℚ := if par = 0 then piLoQ else piHiQ
/-- Upper bound for the head truncation error constant (checked in section G). -/
def Econst : ℚ := 1 / 10 ^ 6
def diagc (lam : ℚ) : ℚ := piLoQ * (beta0Q - lam) - 2 * ellQ * Econst

def headEntry (par N : ℕ) (lam : ℚ) (j k : ℕ) : ℚ :=
  2 * piEQ par * epsQ par * pv par j * pv par k + diagc lam * Gm par j k
  + ∑ m ∈ range Mt, Bm par m j * ((WBmat par N).getD m []).getD k 0
def headMat (par N : ℕ) (lam : ℚ) : List (List ℚ) :=
  (List.range N).map (fun j => (List.range N).map (headEntry par N lam j))

/-! ## D. The LDL^T certificate. -/

/-- Symmetric Gaussian elimination (untrusted: its output is re-verified by `psdCert`). -/
def ldlAux : ℕ → List (List ℚ) → ℕ → List (ℚ × List ℚ)
  | 0, _, _ => []
  | _ + 1, [], _ => []
  | f + 1, (r :: rs), s => match r with
    | [] => []
    | d :: a =>
      (d, List.replicate s 0 ++ (1 :: a.map (· / d))) ::
        ldlAux f (rs.map (fun row => match row with
          | [] => []
          | x :: xs => List.zipWith (fun y aj => y - x * aj / d) xs a)) (s + 1)

def mget (A : List (List ℚ)) (j k : ℕ) : ℚ := (A.getD j []).getD k 0

/-- `A = sum_s d_s v_s v_s^T` entrywise on `n x n`, every `d_s >= 0`. -/
def psdCert (A : List (List ℚ)) (n : ℕ) : Bool :=
  (ldlAux n A 0).all (fun p => decide (0 ≤ p.1)) &&
  (List.range n).all (fun j => (List.range n).all (fun k =>
    decide (mget A j k = ((ldlAux n A 0).map (fun p => p.1 * p.2.getD j 0 * p.2.getD k 0)).sum)))

/-! ## E. The inverse Gram matrices (data). -/

def ginvData0 : List (List ℚ) :=
  [[23730337878975/1099511627776, -2175280972239375/1099511627776, 58732586250463125/1099511627776, -729962143398613125/1099511627776, 2514314049484111875/549755813888, -10560119007833269875/549755813888, 28431089636474188125/549755813888, -50092872216644998125/549755813888, 114918942144067936875/1099511627776, -82660993472048866875/1099511627776, 33851644945696202625/1099511627776, -6021043567416320625/1099511627776],
   [-2175280972239375/1099511627776, 358921360419496875/1099511627776, -11536758013483828125/1099511627776, 156130791782481140625/1099511627776, -565720661133925171875/549755813888, 2457258461438126259375/549755813888, -6776076363359681503125/549755813888, 12154888111391801015625/549755813888, -28276108132816716046875/1099511627776, 20566842423402634734375/1099511627776, -8499706502669372615625/1099511627776, 1523324022556329118125/1099511627776],
   [58732586250463125/1099511627776, -11536758013483828125/1099511627776, 403786530471933984375/1099511627776, -5748451879264078359375/1099511627776, 21540902097022535390625/549755813888, -95833079996086924115625/549755813888, 269050090898105000859375/549755813888, -489394179221827777734375/549755813888, 1151241545407537724765625/1099511627776, -845028960439803905390625/1099511627776, 351887849210512026286875/1099511627776, -63471834273180379921875/1099511627776],
   [-729962143398613125/1099511627776, 156130791782481140625/1099511627776, -5748451879264078359375/1099511627776, 84634899207011122921875/1099511627776, -324836803623099833690625/549755813888, 1471319639939922776128125/549755813888, -4188685099350497855484375/549755813888, 7704462650035060158046875/549755813888, -18289724377909316723015625/1099511627776, 13527223598720380917493125/1099511627776, -5669304237280471534621875/1099511627776, 1028243715225522154734375/1099511627776],
   [2514314049484111875/549755813888, -565720661133925171875/549755813888, 21540902097022535390625/549755813888, -324836803623099833690625/549755813888, 1269320283065053971984375/274877906944, -5829965791340897015184375/274877906944, 16783234853860158074015625/274877906944, -31152827237098286726015625/274877906944, 74517562751139101848629375/549755813888, -55468774015916905878609375/549755813888, 23375407126126870317628125/549755813888, -4259866820220020355328125/549755813888],
   [-10560119007833269875/549755813888, 2457258461438126259375/549755813888, -95833079996086924115625/549755813888, 1471319639939922776128125/549755813888, -5829965791340897015184375/274877906944, 27076952230894388359411875/274877906944, -78662292054179349581690625/274877906944, 147124418765069508778063125/274877906944, -354188415545537706317559375/549755813888, 265102485469175281199146875/549755813888, -112252223898153336385513125/549755813888, 20542024444172098157915625/549755813888],
   [28431089636474188125/549755813888, -6776076363359681503125/549755813888, 269050090898105000859375/549755813888, -4188685099350497855484375/549755813888, 16783234853860158074015625/274877906944, -78662292054179349581690625/274877906944, 230265982194961368775494375/274877906944, -433447361681602088150859375/274877906944, 1049241544484429882351390625/549755813888, -789088043258688886853765625/549755813888, 335519732588144269912621875/549755813888, -61626073332516294473746875/549755813888],
   [-50092872216644998125/549755813888, 12154888111391801015625/549755813888, -489394179221827777734375/549755813888, 7704462650035060158046875/549755813888, -31152827237098286726015625/274877906944, 147124418765069508778063125/274877906944, -433447361681602088150859375/274877906944, 10665367347781292760165234375/3573412790272, -1995455826359080580934140625/549755813888, 1506966343019840414953828125/549755813888, -643123380675234150020896875/549755813888, 118511679485608258603359375/549755813888],
   [114918942144067936875/1099511627776, -28276108132816716046875/1099511627776, 1151241545407537724765625/1099511627776, -18289724377909316723015625/1099511627776, 74517562751139101848629375/549755813888, -354188415545537706317559375/549755813888, 1049241544484429882351390625/549755813888, -1995455826359080580934140625/549755813888, 4873749684986118024948234375/1099511627776, -3694220349460065931515384375/1099511627776, 1581735882201251558159503125/1099511627776, -292328809397833704554953125/1099511627776],
   [-82660993472048866875/1099511627776, 20566842423402634734375/1099511627776, -845028960439803905390625/1099511627776, 13527223598720380917493125/1099511627776, -55468774015916905878609375/549755813888, 265102485469175281199146875/549755813888, -789088043258688886853765625/549755813888, 1506966343019840414953828125/549755813888, -3694220349460065931515384375/1099511627776, 2809330260453203291851921875/1099511627776, -1206381766364654908862728125/1099511627776, 223545560127755185836140625/1099511627776],
   [33851644945696202625/1099511627776, -8499706502669372615625/1099511627776, 351887849210512026286875/1099511627776, -5669304237280471534621875/1099511627776, 23375407126126870317628125/549755813888, -112252223898153336385513125/549755813888, 335519732588144269912621875/549755813888, -643123380675234150020896875/549755813888, 1581735882201251558159503125/1099511627776, -1206381766364654908862728125/1099511627776, 519410069882805207230499375/1099511627776, -96477557528820659150334375/1099511627776],
   [-6021043567416320625/1099511627776, 1523324022556329118125/1099511627776, -63471834273180379921875/1099511627776, 1028243715225522154734375/1099511627776, -4259866820220020355328125/549755813888, 20542024444172098157915625/549755813888, -61626073332516294473746875/549755813888, 118511679485608258603359375/549755813888, -292328809397833704554953125/1099511627776, 223545560127755185836140625/1099511627776, -96477557528820659150334375/1099511627776, 17959025860343239582096875/1099511627776]]

def ginvData1 : List (List ℚ) :=
  [[45232685623125/17179869184, -1872633184797375/17179869184, 6687975659990625/4294967296, -46815829619934375/4294967296, 370270652448571875/8589934592, -882953094300440625/8589934592, 647498935820323125/4294967296, -571322590429696875/4294967296, 1112575570836778125/17179869184, -229579086045684375/17179869184],
   [-1872633184797375/17179869184, 92294064107870625/17179869184, -358921360419496875/4294967296, 2642966381270840625/4294967296, -21618109631420465625/8589934592, 52800595039166349375/8589934592, -39421258739649084375/4294967296, 35271652556528128125/4294967296, -69456503493667434375/17179869184, 14463482420878115625/17179869184],
   [6687975659990625/4294967296, -358921360419496875/4294967296, 1468314656261578125/1073741824, -11181780843838171875/1073741824, 93678475069488684375/2147483648, -232943801643380953125/2147483648, 176358262782640640625/1073741824, -159562237755722484375/1073741824, 317084037688481765625/4294967296, -66532019136039331875/4294967296],
   [-46815829619934375/4294967296, 2642966381270840625/4294967296, -11181780843838171875/1073741824, 87217890581937740625/1073741824, -743917302022410140625/2147483648, 1875810613233541359375/2147483648, -1436060139801502359375/1073741824, 1311185345036154328125/1073741824, -2625455832060629019375/4294967296, 554433492800327765625/4294967296],
   [370270652448571875/8589934592, -21618109631420465625/8589934592, 93678475069488684375/2147483648, -743917302022410140625/2147483648, 6434232103456985953125/4294967296, -16405899172883829984375/4294967296, 12674791668682825171875/2147483648, -11660808335188199158125/2147483648, 23499450348690815296875/8589934592, -4989901435202949890625/8589934592],
   [-882953094300440625/8589934592, 52800595039166349375/8589934592, -232943801643380953125/2147483648, 1875810613233541359375/2147483648, -16405899172883829984375/4294967296, 42214388780819657390625/4294967296, -32862278035530379445625/2147483648, 30428035218083684671875/2147483648, -61658432419605681515625/8589934592, 13155194692807776984375/8589934592],
   [647498935820323125/4294967296, -39421258739649084375/4294967296, 176358262782640640625/1073741824, -1436060139801502359375/1073741824, 12674791668682825171875/2147483648, -32862278035530379445625/2147483648, 334708387398920531390625/13958643712, -311625050336926011984375/13958643712, 634485159414652013015625/55834574848, -10456693217360027859375/4294967296],
   [-571322590429696875/4294967296, 35271652556528128125/4294967296, -159562237755722484375/1073741824, 1311185345036154328125/1073741824, -11660808335188199158125/2147483648, 30428035218083684671875/2147483648, -311625050336926011984375/13958643712, 291520208379704978953125/13958643712, -596031513389521587984375/55834574848, 9859167890653740553125/4294967296],
   [1112575570836778125/17179869184, -69456503493667434375/17179869184, 317084037688481765625/4294967296, -2625455832060629019375/4294967296, 23499450348690815296875/8589934592, -61658432419605681515625/8589934592, 634485159414652013015625/55834574848, -596031513389521587984375/55834574848, 1223116769493455225090625/223338299392, -20298286833698877609375/17179869184],
   [-229579086045684375/17179869184, 14463482420878115625/17179869184, -66532019136039331875/4294967296, 554433492800327765625/4294967296, -4989901435202949890625/8589934592, 13155194692807776984375/8589934592, -10456693217360027859375/4294967296, 9859167890653740553125/4294967296, -20298286833698877609375/17179869184, 4392026975712622640625/17179869184]]

def ginv (par : ℕ) : List (List ℚ) := if par = 0 then ginvData0 else ginvData1

def ginvCheck (par N : ℕ) : Bool :=
  (List.range N).all (fun j => (List.range N).all (fun k =>
    decide ((∑ l ∈ range N, Gm par j l * mget (ginv par) l k) = if j = k then 1 else 0)))

/-! ## F. Side conditions. -/

def pieceCheck : Bool :=
  (List.range nPc).all (fun i => (List.range nS).all (fun j =>
    decide (phw i < smax (bS j) (pcen i)) && decide (deg i j ≤ Dmax)))

/-- The head truncation error: pole (Mp terms) and transform (Mt terms) remainders. -/
def Ehead (par : ℕ) : ℚ :=
  2 * piHiQ * (2 * (ellQ / 2) ^ (2 * Mp + par) / ((2 * Mp + par).factorial : ℚ))
      * (2 * CpQ + 2 * (ellQ / 2) ^ (2 * Mp + par) / ((2 * Mp + par).factorial : ℚ))
  + S0Q * (2 * (2 * ellQ ^ (2 * Mt + par) * TQ ^ (2 * Mt + par + 1)
        / ((2 * Mt + par + 1) * ((2 * Mt + par).factorial : ℚ)))
      + 4 * ellQ ^ (2 * (2 * Mt + par)) * TQ ^ (2 * (2 * Mt + par) + 1)
        / ((2 * (2 * Mt + par) + 1) * ((2 * Mt + par).factorial : ℚ) ^ 2))

/-- Tail constants after `N` head modes: pole remainder, `int_0^T eps_N`, `int_0^T eps_N^2`. -/
def dPT (par N : ℕ) : ℚ := 2 * (ellQ / 2) ^ (2 * N + par) / ((2 * N + par).factorial : ℚ)
def I1T (par N : ℕ) : ℚ :=
  2 * ellQ ^ (2 * N + par) * TQ ^ (2 * N + par + 1) / ((2 * N + par + 1) * ((2 * N + par).factorial : ℚ))
def I2T (par N : ℕ) : ℚ :=
  4 * ellQ ^ (2 * (2 * N + par)) * TQ ^ (2 * (2 * N + par) + 1)
    / ((2 * (2 * N + par) + 1) * ((2 * N + par).factorial : ℚ) ^ 2)
/-- Coupling constant `|R(h, r)| <= kapT A1(h) A1(r)` (uses `1/pi <= 1/3`). -/
def kapT (par N : ℕ) : ℚ := 2 * CpQ * dPT par N + S0Q / 3 * I1T par N
/-- Tail floor `R(r, r) >= dT * int r^2`. -/
def dT (par N : ℕ) : ℚ := beta0Q - 2 * ellQ * (2 * dPT par N ^ 2 + S0Q / 3 * I2T par N)

def lamE : ℚ := 915 / 10 ^ 6
def lamO : ℚ := 1 / 100
/-- The window floor certified in both sectors. -/
def lamFloor : ℚ := 9 / 10000

def tailCond (par N : ℕ) (lam : ℚ) : Bool :=
  decide (lamFloor ≤ lam) && decide (lamFloor ≤ dT par N) &&
  decide (4 * kapT par N ^ 2 * ellQ ^ 2 ≤ (lam - lamFloor) * (dT par N - lamFloor)) &&
  decide (Ehead par ≤ Econst) && decide (lam < beta0Q) &&
  decide (TQ * ellQ ≤ ((2 * N + par + 1 : ℕ) : ℚ) / 2) && decide (TQ * ellQ ≤ ((2 * Mt + par + 1 : ℕ) : ℚ) / 2)

/-! ## H. Soundness of the elementary computable pieces. -/

theorem getD_map_range {α : Type*} (f : ℕ → α) {n i : ℕ} (d : α) (h : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

theorem mget_map_range (f : ℕ → ℕ → ℚ) {n m j k : ℕ} (hj : j < n) (hk : k < m) :
    mget ((List.range n).map (fun j => (List.range m).map (f j))) j k = f j k := by
  unfold mget
  rw [getD_map_range _ _ hj, getD_map_range _ _ hk]

theorem floorR_le (q : ℚ) (R : ℕ) : floorR q R ≤ q := by
  unfold floorR
  have h := Int.floor_le (q * 10 ^ R)
  have hp : (0 : ℚ) < 10 ^ R := by positivity
  rw [div_le_iff₀ hp]
  exact h

theorem sub_floorR_le (q : ℚ) (R : ℕ) : q - floorR q R ≤ 1 / 10 ^ R := by
  unfold floorR
  have h := Int.lt_floor_add_one (q * 10 ^ R)
  have hp : (0 : ℚ) < 10 ^ R := by positivity
  have e : q - (⌊q * 10 ^ R⌋ : ℚ) / 10 ^ R = (q * 10 ^ R - (⌊q * 10 ^ R⌋ : ℚ)) / 10 ^ R := by
    field_simp
  rw [e, div_le_div_iff_of_pos_right hp]
  linarith

theorem le_ceilR (q : ℚ) (R : ℕ) : q ≤ ceilR q R := by
  unfold ceilR
  have h := Int.le_ceil (q * 10 ^ R)
  have hp : (0 : ℚ) < 10 ^ R := by positivity
  rw [le_div_iff₀ hp]
  exact h

theorem gpow_cast (x y : ℚ) (n : ℕ) :
    ((gpow x y n).1 : ℂ) + ((gpow x y n).2 : ℂ) * Complex.I = ((x : ℂ) + (y : ℂ) * Complex.I) ^ n := by
  induction n with
  | zero => simp [gpow]
  | succ n ih =>
    rcases hgp : gpow x y n with ⟨p, q⟩
    rw [hgp] at ih
    simp only [gpow, hgp]
    rw [pow_succ, ← ih]
    push_cast
    linear_combination (-(q : ℂ) * (y : ℂ)) * Complex.I_sq

theorem re_I_pow_mul (k : ℕ) (P Q : ℝ) :
    (Complex.I ^ k * ((P : ℂ) + (Q : ℂ) * Complex.I)).re
      = if k % 4 = 0 then P else if k % 4 = 1 then -Q else if k % 4 = 2 then -P else Q := by
  have hk : Complex.I ^ k = Complex.I ^ (k % 4) := by
    conv_lhs => rw [← Nat.div_add_mod k 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]
  rw [hk]
  have h4 : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases (k % 4) <;> simp [pow_succ, Complex.mul_re, Complex.mul_im]

/-- `kap` is the Taylor coefficient: `kap b c k = 2 Re (I^k / (b - c I)^(k+1))` (`b > 0`). -/
theorem kap_eq {b c : ℚ} (hb : 0 < b) (k : ℕ) :
    ((kap b c k : ℚ) : ℝ) = 2 * (Complex.I ^ k / ((b : ℂ) - (c : ℂ) * Complex.I) ^ (k + 1)).re := by
  have hn : (0 : ℚ) < b * b + c * c := by nlinarith [mul_pos hb hb, mul_self_nonneg c]
  have hz : ((b : ℂ) - (c : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact absurd this (by exact_mod_cast hb.ne')
  have hinv : ((b : ℂ) - (c : ℂ) * Complex.I)⁻¹
      = (((b / (b * b + c * c) : ℚ) : ℂ) + ((c / (b * b + c * c) : ℚ) : ℂ) * Complex.I) := by
    apply inv_eq_of_mul_eq_one_right
    have hnC : ((b * b + c * c : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have e1 : (((b / (b * b + c * c) : ℚ) : ℂ) + ((c / (b * b + c * c) : ℚ) : ℂ) * Complex.I)
        = ((b : ℂ) + (c : ℂ) * Complex.I) / ((b * b + c * c : ℚ) : ℂ) := by push_cast; ring
    have e2 : ((b : ℂ) - (c : ℂ) * Complex.I) * ((b : ℂ) + (c : ℂ) * Complex.I)
        = ((b * b + c * c : ℚ) : ℂ) := by
      push_cast; linear_combination (-(c : ℂ) ^ 2) * Complex.I_sq
    rw [e1, mul_div_assoc', e2, div_self hnC]
  have hdiv : Complex.I ^ k / ((b : ℂ) - (c : ℂ) * Complex.I) ^ (k + 1)
      = Complex.I ^ k * ((((gpow (b / (b * b + c * c)) (c / (b * b + c * c)) (k + 1)).1 : ℚ) : ℝ) : ℂ)
        + Complex.I ^ k * (((((gpow (b / (b * b + c * c)) (c / (b * b + c * c)) (k + 1)).2 : ℚ) : ℝ) : ℂ)
          * Complex.I) := by
    rw [div_eq_mul_inv, ← inv_pow, hinv, ← mul_add]
    congr 1
    rw [← gpow_cast]
    push_cast
    ring
  rw [hdiv, ← mul_add, re_I_pow_mul]
  unfold kap
  split_ifs <;> push_cast <;> ring

/-! ## I. Soundness of the LDL^T certificate. -/

theorem sum_quad_cert (n : ℕ) (x : ℕ → ℝ) (C : List (ℚ × List ℚ)) :
    ∑ j ∈ range n, ∑ k ∈ range n, x j * x k
        * (((C.map (fun p => p.1 * p.2.getD j 0 * p.2.getD k 0)).sum : ℚ) : ℝ)
      = (C.map (fun p => (p.1 : ℝ) * (∑ j ∈ range n, x j * (p.2.getD j 0 : ℝ)) ^ 2)).sum := by
  induction C with
  | nil => simp
  | cons p C ih =>
    simp only [List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul, mul_add,
      Finset.sum_add_distrib, ih]
    congr 1
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

theorem psdCert_sound {A : List (List ℚ)} {n : ℕ} (h : psdCert A n = true) (x : ℕ → ℝ) :
    0 ≤ ∑ j ∈ range n, ∑ k ∈ range n, x j * x k * ((mget A j k : ℚ) : ℝ) := by
  unfold psdCert at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  obtain ⟨hpos, heq⟩ := h
  have hA : ∀ j ∈ range n, ∀ k ∈ range n, mget A j k
      = ((ldlAux n A 0).map (fun p => p.1 * p.2.getD j 0 * p.2.getD k 0)).sum := by
    intro j hj k hk
    have := heq j (List.mem_range.mpr (Finset.mem_range.mp hj))
    rw [List.all_eq_true] at this
    exact of_decide_eq_true (this k (List.mem_range.mpr (Finset.mem_range.mp hk)))
  rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => by rw [hA j hj k hk],
    sum_quad_cert]
  apply List.sum_nonneg
  intro y hy
  rw [List.mem_map] at hy
  obtain ⟨p, hp, rfl⟩ := hy
  have := of_decide_eq_true (hpos p hp)
  have h0 : (0 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast this
  positivity

/-! ## J. Extraction of the side conditions. -/

theorem ginvCheck_sound {par N : ℕ} (h : ginvCheck par N = true) {j k : ℕ} (hj : j < N) (hk : k < N) :
    (∑ l ∈ range N, Gm par j l * mget (ginv par) l k) = if j = k then 1 else 0 := by
  unfold ginvCheck at h
  rw [List.all_eq_true] at h
  have := h j (List.mem_range.mpr hj)
  rw [List.all_eq_true] at this
  exact of_decide_eq_true (this k (List.mem_range.mpr hk))

theorem pieceCheck_sound (h : pieceCheck = true) {i j : ℕ} (hi : i < nPc) (hj : j < nS) :
    phw i < smax (bS j) (pcen i) ∧ deg i j ≤ Dmax := by
  unfold pieceCheck at h
  rw [List.all_eq_true] at h
  have := h i (List.mem_range.mpr hi)
  rw [List.all_eq_true] at this
  have h2 := this j (List.mem_range.mpr hj)
  rw [Bool.and_eq_true] at h2
  exact ⟨of_decide_eq_true h2.1, of_decide_eq_true h2.2⟩

theorem tailCond_sound {par N : ℕ} {lam : ℚ} (h : tailCond par N lam = true) :
    lamFloor ≤ lam ∧ lamFloor ≤ dT par N
      ∧ 4 * kapT par N ^ 2 * ellQ ^ 2 ≤ (lam - lamFloor) * (dT par N - lamFloor)
      ∧ Ehead par ≤ Econst ∧ lam < beta0Q
      ∧ TQ * ellQ ≤ ((2 * N + par + 1 : ℕ) : ℚ) / 2 ∧ TQ * ellQ ≤ ((2 * Mt + par + 1 : ℕ) : ℚ) / 2 := by
  unfold tailCond at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

end KWin
