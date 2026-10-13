/-
  KWin2_Window920 -- THE WINDOW FLOOR AT L = 9/20 (2L = 0.9, prime comb term n = 2 present), on the
  goal node's full test class, with no Arb seam (rvm_bridge island, 2026-09-24).

  conjecture1_proved = False.  A finite-window Weil positivity statement is NOT RH.  As at the
  prime-free edge (PR #604: on a window the Weil form IS the zero sum, so certifying its margin says
  nothing new about the zeros), a positive floor here samples the low zeros and constrains none of
  them; the numerical window floor is lambda*(9/20) ~ 1.62e-5 (Rayleigh-Ritz).  Not Connes-Consani
  / Yoshida (pole-free class, 2L <= log 2): the pole terms are kept and 2L = 0.9 > log 2.

  PROVED HERE, hypothesis-free (the guard prints only propext / Classical.choice / Quot.sound):
    * windowFloor920 : WeilWindow.WindowFloor (9/20) (9/2000000)   (lam = 4.5e-6);
    * weil_positivity_window_nine_twentieths: for all g, L with L <= 9/20 and tsupport g in
      [-L, L], 0 <= Re weilForm (autocorr g).
  Route: the generic assembly KWin2_Window.windowFloor_of_cert, fed with the kernel evaluations of
  this file (structural checks, the rational side conditions `sideCheck`) and of KWin2_Cert920E /
  KWin2_Cert920O (the two head certificates; KWin2_Cert920N is the negative control).
  No `sorry`.
-/
import KWin2_Window
import KWin2_Cert920E
import KWin2_Cert920O
import KWin2_Cert920N

open Real

namespace KWin2
open KWin (log_pi_le)

theorem par920 : parCheck P920 = true := by decide +kernel
theorem brk920 : brkCheck P920 = true := by decide +kernel
theorem piece920 : pieceCheck P920 = true := by decide +kernel
theorem min920 : minCheck P920 = true := by decide +kernel
theorem comb920 : combCheck P920 = true := by decide +kernel
theorem tailE920 : tailCond P920 0 22 lamE920 = true := by decide +kernel
theorem tailO920 : tailCond P920 1 19 lamO920 = true := by decide +kernel
theorem ginvE920 : ginvCheck P920 0 22 = true := by decide +kernel
theorem ginvO920 : ginvCheck P920 1 19 = true := by decide +kernel
/-- The rational side conditions at L = 9/20 (xT = 2.7081 >= log 15). -/
theorem side920 : sideCheck P920 (27081 / 10000) = true := by decide +kernel

lemma lR920 : lR P920 = 9 / 20 := by norm_num [lR, P920]

lemma log_two_lt_920 : Real.log 2 < 2 * (9 / 20 : ℝ) := by
  have := Real.log_two_lt_d9; norm_num at this ⊢; linarith

lemma twoL_le_log_three_920 : 2 * (9 / 20 : ℝ) ≤ Real.log 3 := by
  have h : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  linarith

/-- **THE WINDOW FLOOR AT L = 9/20**: every smooth compactly supported test `f` (complex, no
parity) supported in `[-9/20, 9/20]` has `Re weilForm (autocorr f) >= 4.5e-6 ||f||_2^2`. -/
theorem windowFloor920 : WeilWindow.WindowFloor (9 / 20) (9 / 2000000) := by
  have h := windowFloor_of_cert P920 22 19 lamE920 lamO920 (27081 / 10000) log_two_lt_920
    twoL_le_log_three_920 (by rw [lR920]) gamma_le32 log_pi_le side920 par920 brk920 piece920 min920
    comb920 tailE920 tailO920 ginvE920 ginvO920 (headPSD_of_psdCert certE920)
    (headPSD_of_psdCert certO920)
  have e : ((P920.lamFloor : ℚ) : ℝ) = 9 / 2000000 := by norm_num [P920]
  rwa [e] at h

/-- **Weil positivity on every window with L <= 9/20** (goal node's full class, pole terms kept),
in the explicit-binder shape of `weil_positivity_prime_free_window`. -/
theorem weil_positivity_window_nine_twentieths (g : ℝ → ℂ) (hg : WeilExplicit.IsWeilTest g) (L : ℝ)
    (hL : L ≤ 9 / 20) (hsupp : tsupport g ⊆ Set.Icc (-L) L) :
    0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re :=
  weil_positivity_of_windowFloor (by norm_num) windowFloor920 g hg L hL hsupp

end KWin2
