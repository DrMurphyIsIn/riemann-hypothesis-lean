/-
  Hodge1_Par5493 -- the parameters of the DIRECT pole-free certificate at l = 5493/10000 (2L = 1.0986,
  just below log 3 = 1.098612...; the prime comb is {2}) (HODGE-1 Phase 1b-B, 2026-10-12; design
  notes, unpublished, section 3(b)).

  conjecture1_proved = False.  No zeros enter.  The prime p = 2 is INSIDE the symbol:
      weilSymbol L t = Psi t - c2 cos(t log 2),  c2 = 2 Lambda(2)/sqrt 2,
  and the pole coefficient 2 eps of KWin2 is replaced by the penalty pc = 1000 (on the two-condition
  pole-free class every parity piece has vanishing pole functional, so the penalty is free).  The strip
  block of Hodge1_KPen is switched off (w2up = 0, s0 = 0, no leakage matrix).

  Choices (generator ../hodge1/hodge1_gen.py h5493, exact-rational mirror; output ../hodge1/h5493*.txt):
    * KWin2_Par12's data (T = 40, beta0 = 1057/1250 <= betaStar = 0.845744, S0 = 7.23, the 11-piece
      Psi_0 minorant on [0, 40] with nS = 44, the degree-<96 comb polynomial and combK, gamma <= gamUp32),
      with l = 5493/10000, Cp = 10385/10000 >= cosh(l/2), Nser = 400 (the minorant gap costs 1e-6 of the
      even head margin against Nser = 1200), Mt = 37, Mp = 8, Econst = 1e-6;
    * even sector N = 32, lam = 55/100000 (head eigenvalue 6.3071e-4); odd sector N = 31, lam = 13/1000
      (head eigenvalue 1.37858e-2); both by psdCertR at R = 60 (R = 50 already passes);
    * the certified window floor lamFloor = 5/10000;
    * NEGATIVE CONTROLS (same pipeline, must return false): lam = 631/1000000 above the even head
      eigenvalue; the comb with the prime location moved to q = 2.1 (lag log 2.1, weight 2 log 2.1/sqrt 2.1;
      even head eigenvalue -0.0716); the comb weight 1.05 c2 (even head eigenvalue -0.00684).  The fake
      controls keep beta0 = 1057/1250 (optimistic for them: their own betaStar is smaller), so a `false`
      is a strict failure.
  No `sorry`.
-/
import Hodge1_KPen
import KWin2_Par12

namespace Hodge1
open KWin KWin2

/-- The KWin2 window data at `l = 5493/10000`, `T = 40`, comb {2} kept. -/
def P5493 : KPar :=
  { P12 with
    ell := 5493 / 10000
    Cp := 10385 / 10000
    Nser := 400
    Mt := 37
    Econst := 1 / 10 ^ 6
    lamFloor := 5 / 10 ^ 4 }

/-- The direct pole-free certificate: penalty 1000, no strip block. -/
def H5493 : HPar where
  K := P5493
  pc := 1000
  s0 := 0
  w2up := 0

def NE5493 : ℕ := 32
def lamE5493 : ℚ := 55 / 10 ^ 5
def NO5493 : ℕ := 31
def lamO5493 : ℚ := 13 / 1000
/-- The Young parameter is unused (no strip block); any positive value. -/
def eta5493 : ℚ := 1
/-- No leakage matrix. -/
def D5493 : List (List ℚ) := []
def R5493 : ℕ := 60

/-- Control: the prime location moved to q = 2.1 (a0 ~ log 2.1, c0 ~ 2 log 2.1 / sqrt 2.1). -/
def H5493q21 : HPar where
  K := { P5493 with a0 := 7419373447293773 / 10 ^ 16, c0 := 10239708175753177 / 10 ^ 16 }
  pc := 1000
  s0 := 0
  w2up := 0

/-- Control: the comb weight 1.05 c2. -/
def H5493w105 : HPar where
  K := { P5493 with c0 := 5146355253209873 / 5000000000000000 }
  pc := 1000
  s0 := 0
  w2up := 0

end Hodge1
