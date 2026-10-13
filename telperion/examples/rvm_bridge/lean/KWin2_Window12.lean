/-
  KWin2_Window12 -- THE WINDOW FLOOR AT L = 1/2 (2L = 1, prime comb term n = 2 present), on the goal
  node's full test class, with no Arb seam (rvm_bridge island, 2026-09-24).

  conjecture1_proved = False.  A finite-window Weil positivity statement is NOT RH.  As at the
  prime-free edge (PR #604: on a window the Weil form IS the zero sum, so certifying its margin says
  nothing new about the zeros), a positive floor here samples the low zeros and constrains none of
  them; the numerical window floor is lambda*(1/2) ~ 9.38e-7 (Rayleigh-Ritz).  Not Connes-Consani
  / Yoshida (pole-free class, 2L <= log 2): the pole terms are kept and 2L = 1 > log 2.

  PROVED HERE, hypothesis-free (the guard prints only propext / Classical.choice / Quot.sound):
    * windowFloor12 : WeilWindow.WindowFloor (1/2) (7/20000000)   (lam = 3.5e-7);
    * weil_positivity_window_half: for all g, L with L <= 1/2 and tsupport g in [-L, L],
      0 <= Re weilForm (autocorr g).
  Route: KWin2_Window.windowFloor_of_cert, fed with the kernel evaluations of this file
  (structural checks, `sideCheck`) and of KWin2_Cert12E / KWin2_Cert12O (the two head matrices,
  certified by the ROUNDED checker psdCertR of KWin2_Round; KWin2_Cert12N is the negative control).
  No `sorry`.
-/
import KWin2_Window
import KWin2_Cert12E
import KWin2_Cert12O
import KWin2_Cert12N

open Real

namespace KWin2
open KWin (log_pi_le)

theorem par12 : parCheck P12 = true := by decide +kernel
theorem brk12 : brkCheck P12 = true := by decide +kernel
theorem piece12 : pieceCheck P12 = true := by decide +kernel
theorem min12 : minCheck P12 = true := by decide +kernel
theorem comb12 : combCheck P12 = true := by decide +kernel
theorem tailE12 : tailCond P12 0 31 lamE12 = true := by decide +kernel
theorem tailO12 : tailCond P12 1 29 lamO12 = true := by decide +kernel
theorem ginvE12 : ginvCheck P12 0 31 = true := by decide +kernel
theorem ginvO12 : ginvCheck P12 1 29 = true := by decide +kernel
/-- The rational side conditions at L = 1/2 (xT = 2.9958 >= log 20). -/
theorem side12 : sideCheck P12 (29958 / 10000) = true := by decide +kernel

lemma lR12 : lR P12 = 1 / 2 := by norm_num [lR, P12]

lemma log_two_lt_12 : Real.log 2 < 2 * (1 / 2 : ℝ) := by
  have := Real.log_two_lt_d9; norm_num at this ⊢; linarith

lemma twoL_le_log_three_12 : 2 * (1 / 2 : ℝ) ≤ Real.log 3 := by
  have h : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  linarith

/-- **THE WINDOW FLOOR AT L = 1/2**: every smooth compactly supported test `f` (complex, no
parity) supported in `[-1/2, 1/2]` has `Re weilForm (autocorr f) >= 3.5e-7 ||f||_2^2`. -/
theorem windowFloor12 : WeilWindow.WindowFloor (1 / 2) (7 / 20000000) := by
  have h := windowFloor_of_cert P12 31 29 lamE12 lamO12 (29958 / 10000) log_two_lt_12
    twoL_le_log_three_12 (by rw [lR12]) gamma_le32 log_pi_le side12 par12 brk12 piece12 min12
    comb12 tailE12 tailO12 ginvE12 ginvO12 (headPSD_of_psdCertR certE12) (headPSD_of_psdCertR certO12)
  have e : ((P12.lamFloor : ℚ) : ℝ) = 7 / 20000000 := by norm_num [P12]
  rwa [e] at h

/-- **Weil positivity on every window with L <= 1/2** (goal node's full class, pole terms kept),
in the explicit-binder shape of `weil_positivity_prime_free_window`. -/
theorem weil_positivity_window_half (g : ℝ → ℂ) (hg : WeilExplicit.IsWeilTest g) (L : ℝ)
    (hL : L ≤ 1 / 2) (hsupp : tsupport g ⊆ Set.Icc (-L) L) :
    0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re :=
  weil_positivity_of_windowFloor (by norm_num) windowFloor12 g hg L hL hsupp

end KWin2
