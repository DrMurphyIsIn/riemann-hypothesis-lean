/-
  KWin2_Par920 -- the parameters of the window certificate at L = 9/20 (2L = 0.9; the prime comb
  term n = 2 is present, n = 3 is not: log 3 > 0.9) (rvm_bridge island, 2026-09-24).

  conjecture1_proved = False.  A finite-window statement; not RH; not Connes-Consani (pole terms
  kept); cf. PR #604.

  Choices (scratch designer gen_L.py, exact-rational mirror of KWin2_Data):
    * l = L = 9/20; frequency cut T = 30: betaStar(9/20, 30) = log(15/pi) - 1/30 - sqrt 2 log 2
      = 0.549705 > beta0 = 0.5496;
    * S0 = 6.91, Cp = 1.0257 >= cosh(9/40);
    * the Psi_0 minorant: 9 pieces of [0, 30], nS = 34 exact Lorentzians, alternating order 10,
      Nser = 1200 series terms and gamma <= gamUp32 (KWin2_Consts) so that the minorant gap is
      1.2e-7 at low frequency (KWin's Nser = 400, gamma + 1.3e-7 would cost 1.1e-6, a fifth of the
      margin here);
    * the comb 2 Lambda(2)/sqrt 2 cos(t log 2): cos by its Taylor polynomial of degree < 76 in
      t a0 <= 20.8 (remainder 1.5e-11);
    * head: Mt = 26, Mp = 8, Econst = 1e-7; even sector N = 22 at lam = 5e-6 (head eigenvalue
      5.18e-6), odd sector N = 19 at lam = 1e-3 (1.12e-3);
    * the certified window floor lamFloor = 4.5e-6 (lambda*(9/20) ~ 1.62e-5, numerical).
  No `sorry`.
-/
import KWin2_Data
import KWin2_Consts

namespace KWin2
open KWin

/-- The window certificate parameters at `L = 9/20`. -/
def P920 : KPar where
  ell := 9 / 20
  T := 30
  beta0 := 687 / 1250
  S0 := 691 / 100
  Cp := 10257 / 10000
  brks := [0, 3 / 10, 4 / 5, 8 / 5, 16 / 5, 32 / 5, 64 / 5, 20, 25, 30]
  degTab := [[20, 8, 6, 5, 5, 5, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
    [22, 9, 7, 6, 6, 5, 5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
    [21, 12, 9, 7, 7, 6, 6, 5, 5, 5, 5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3, 3, 3],
    [21, 15, 12, 10, 9, 8, 7, 7, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5, 5, 5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4],
    [20, 19, 15, 13, 12, 11, 10, 9, 9, 8, 8, 7, 7, 7, 7, 6, 6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5],
    [19, 19, 19, 17, 15, 14, 13, 12, 12, 11, 11, 10, 10, 9, 9, 9, 8, 8, 8, 8, 7, 7, 7, 7, 7, 7, 7, 6, 6, 6, 6, 6, 6, 6],
    [13, 13, 13, 13, 13, 12, 12, 11, 11, 10, 10, 10, 9, 9, 9, 9, 9, 8, 8, 8, 8, 8, 7, 7, 7, 7, 7, 7, 7, 7, 6, 6, 6, 6],
    [9, 9, 9, 9, 9, 9, 9, 8, 8, 8, 8, 8, 7, 7, 7, 7, 7, 7, 7, 7, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5],
    [8, 8, 8, 8, 8, 8, 8, 8, 8, 7, 7, 7, 7, 7, 7, 7, 7, 7, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5]]
  nS := 34
  Kalt := 5
  Dmax := 24
  Nser := 1200
  Mser := 10 ^ 9
  gamUp := gamUp32
  logPiUp := logPiUpQ
  Mt := 26
  Mp := 8
  a0 := 6931471805599453 / 10 ^ 16
  da := 1 / 10 ^ 16
  c0 := 9802581434685472 / 10 ^ 16
  dc := 1 / 10 ^ 16
  Mc := 38
  combK := 1516989583 / 100000000000000000000
  Rc := 16
  Econst := 1 / 10000000
  lamFloor := 9 / 2000000

/-- The even-sector head level. -/
def lamE920 : ℚ := 5 / 10 ^ 6
/-- The odd-sector head level. -/
def lamO920 : ℚ := 1 / 1000

end KWin2
