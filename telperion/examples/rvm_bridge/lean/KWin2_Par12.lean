/-
  KWin2_Par12 -- the parameters of the window certificate at L = 1/2 (2L = 1; the prime comb term
  n = 2 is present, n = 3 is not: log 3 > 1) (rvm_bridge island, 2026-09-24).

  conjecture1_proved = False.  A finite-window statement; not RH; not Connes-Consani (pole terms
  kept); cf. PR #604.

  Choices (scratch designer gen_L.py, exact-rational mirror of KWin2_Data):
    * l = L = 1/2; frequency cut T = 40: betaStar(1/2, 40) = log(20/pi) - 1/40 - sqrt 2 log 2
      = 0.845744 > beta0 = 0.8456;
    * S0 = 7.23, Cp = 1.0318 >= cosh(1/4);
    * the Psi_0 minorant: 11 pieces of [0, 40], nS = 44 exact Lorentzians, alternating order 10,
      Nser = 1200 series terms, gamma <= gamUp32: minorant gap ~1.2e-7 at low frequency (Nser =
      1500 makes the kernel's `Finset.range` sum too deep: `decide` gets stuck);
    * the comb: cos(t a0) by its Taylor polynomial of degree < 96 in t a0 <= 27.8 (remainder
      6.5e-12);
    * head: Mt = 36, Mp = 8, Econst = 1e-8; even sector N = 31 at lam = 4.2e-7 (head eigenvalue
      4.50e-7), odd sector N = 29 at lam = 1e-4 (1.07e-4); both certified by the ROUNDED checker
      psdCertR at R = 70 (KWin2_Round: floor at 10^-70, diagonal shift 31e-70);
    * the certified window floor lamFloor = 3.5e-7 (lambda*(1/2) ~ 9.38e-7, numerical).
  No `sorry`.
-/
import KWin2_Data
import KWin2_Consts

namespace KWin2
open KWin

/-- The window certificate parameters at `L = 1/2`. -/
def P12 : KPar where
  ell := 1 / 2
  T := 40
  beta0 := 1057 / 1250
  S0 := 723 / 100
  Cp := 5159 / 5000
  brks := [0, 3 / 10, 4 / 5, 8 / 5, 16 / 5, 32 / 5, 64 / 5, 20, 25, 30, 35, 40]
  degTab := [[20, 8, 6, 5, 5, 5, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
    [22, 9, 7, 6, 6, 5, 5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
    [21, 12, 9, 7, 7, 6, 6, 5, 5, 5, 5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
    [21, 15, 12, 10, 9, 8, 7, 7, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5, 5, 5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4],
    [20, 19, 15, 13, 12, 11, 10, 9, 9, 8, 8, 7, 7, 7, 7, 6, 6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 4, 4, 4, 4, 4],
    [19, 19, 19, 17, 15, 14, 13, 12, 12, 11, 11, 10, 10, 9, 9, 9, 8, 8, 8, 8, 7, 7, 7, 7, 7, 7, 7, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5, 5, 5],
    [13, 13, 13, 13, 13, 12, 12, 11, 11, 10, 10, 10, 9, 9, 9, 9, 9, 8, 8, 8, 8, 8, 7, 7, 7, 7, 7, 7, 7, 7, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6],
    [9, 9, 9, 9, 9, 9, 9, 8, 8, 8, 8, 8, 7, 7, 7, 7, 7, 7, 7, 7, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5],
    [8, 8, 8, 8, 8, 8, 8, 8, 8, 7, 7, 7, 7, 7, 7, 7, 7, 7, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5],
    [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5],
    [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5]]
  nS := 44
  Kalt := 5
  Dmax := 24
  Nser := 1200
  Mser := 10 ^ 9
  gamUp := gamUp32
  logPiUp := logPiUpQ
  Mt := 36
  Mp := 8
  a0 := 6931471805599453 / 10 ^ 16
  da := 1 / 10 ^ 16
  c0 := 9802581434685472 / 10 ^ 16
  dc := 1 / 10 ^ 16
  Mc := 48
  combK := 650536633 / 100000000000000000000
  Rc := 16
  Econst := 1 / 100000000
  lamFloor := 7 / 20000000

/-- The even-sector head level. -/
def lamE12 : ℚ := 42 / 10 ^ 8
/-- The odd-sector head level. -/
def lamO12 : ℚ := 1 / 10 ^ 4

end KWin2
