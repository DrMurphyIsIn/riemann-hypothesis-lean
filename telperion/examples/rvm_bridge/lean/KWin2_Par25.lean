/-
  KWin2_Par25 -- the parameters of the window certificate at L = 2/5 (2L = 0.8 > log 2, so the prime
  comb term n = 2 is present) (rvm_bridge island, 2026-09-24).

  conjecture1_proved = False.  A finite-window statement; not RH; not Connes-Consani (pole terms
  kept); cf. PR #604.

  Choices (scratch designer mirror.py / gen25.py, exact-rational mirror of KWin2_Data):
    * head half-width l = L = 2/5 (the support [-L, L] is the head interval itself);
    * frequency cut T = 24: betaStar(2/5, 24) = log(12/pi) - 1/24 - sqrt 2 log 2 = 0.31820 > beta0 = 0.318;
    * S0 = 6.68 >= |Psi_{2/5} - beta0| on [0, 24]; Cp = 1.0203 >= cosh(1/5);
    * the Psi_0 minorant: 8 pieces of [0, 24], nS = 24 exact Lorentzians (Taylor degrees chosen so
      each geometric remainder is <= 1e-10), alternating order 10, Nser = 400, Mser = 10^9;
    * the comb 2 Lambda(2)/sqrt 2 cos(t log 2): a0 = 0.6931471805599453 (|log 2 - a0| <= 1e-16),
      c0 = 0.9802581434685472 (|c2 - c0| <= 1e-16), cos by its Taylor polynomial of degree < 64 in
      t a0 <= 16.64 (remainder 2.2e-11), coefficients ceiled at 10^-(16+2p);
    * head: Mt = 20 transform terms, Mp = 8 pole terms, Econst = 1e-6; even sector N = 16 at
      lam = 45e-6 (head eigenvalue 4.70e-5), odd sector N = 14 at lam = 1e-3 (5.73e-3);
    * the certified window floor lamFloor = 4e-5 (lambda*(2/5) ~ 1.82e-4, numerical).
  No `sorry`.
-/
import KWin2_Data

namespace KWin2
open KWin

/-- The window certificate parameters at `L = 2/5`. -/
def P25 : KPar where
  ell := 2 / 5
  T := 24
  beta0 := 318 / 1000
  S0 := 668 / 100
  Cp := 10203 / 10000
  brks := [0, 3 / 10, 4 / 5, 8 / 5, 16 / 5, 32 / 5, 64 / 5, 20, 24]
  degTab := [[20, 8, 6, 5, 5, 5, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
    [22, 9, 7, 6, 6, 5, 5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3, 3],
    [21, 12, 9, 7, 7, 6, 6, 5, 5, 5, 5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4],
    [21, 15, 12, 10, 9, 8, 7, 7, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5, 5, 5, 5, 4, 4],
    [20, 19, 15, 13, 12, 11, 10, 9, 9, 8, 8, 7, 7, 7, 7, 6, 6, 6, 6, 6, 6, 6, 6, 5],
    [19, 19, 19, 17, 15, 14, 13, 12, 12, 11, 11, 10, 10, 9, 9, 9, 8, 8, 8, 8, 7, 7, 7, 7],
    [13, 13, 13, 13, 13, 12, 12, 11, 11, 10, 10, 10, 9, 9, 9, 9, 9, 8, 8, 8, 8, 8, 7, 7],
    [8, 8, 8, 8, 8, 8, 8, 8, 7, 7, 7, 7, 7, 7, 7, 6, 6, 6, 6, 6, 6, 6, 6, 6]]
  nS := 24
  Kalt := 5
  Dmax := 22
  Nser := 400
  Mser := 10 ^ 9
  gamUp := gammaUpQ
  logPiUp := logPiUpQ
  Mt := 20
  Mp := 8
  a0 := 6931471805599453 / 10 ^ 16
  da := 1 / 10 ^ 16
  c0 := 9802581434685472 / 10 ^ 16
  dc := 1 / 10 ^ 16
  Mc := 32
  combK := 2164470881 / 100000000000000000000
  Rc := 16
  Econst := 1 / 10 ^ 6
  lamFloor := 4 / 10 ^ 5

/-- The even-sector head level. -/
def lamE25 : ℚ := 45 / 10 ^ 6
/-- The odd-sector head level. -/
def lamO25 : ℚ := 1 / 1000

end KWin2
