/-
  Hodge1_Window5493 -- WEIL POSITIVITY ON THE TWO-CONDITION POLE-FREE CLASS UP TO L = 5493/10000,
  i.e. on (almost) the whole one-prime window (log 2)/2 < L < (log 3)/2 = 0.549306, by the DIRECT
  certificate (HODGE-1 Phase 1b-B, 2026-10-12).

  conjecture1_proved = False.  A finite-window positivity statement on a subclass is not RH.  But it is
  a NEW range on the pole-free class: KWin2's full-class theorem stops at L = 1/2, and Connes-Consani's
  Theorem 1 (pole-free class) at 2L = log 2.  The prime p = 2 sits inside the window and inside the
  certified symbol Psi - c2 cos(t log 2).  The certificate is prime-specific: with the prime moved to
  q = 2.1, or its weight raised to 1.05 c2, the same kernel pipeline returns `false`
  (Hodge1_Cert5493Q / Hodge1_Cert5493W; B's truth on the hyperplane: -0.0695 and -0.0066 at L = 0.549).

  PROVED HERE (kernel-checked numerics; Hodge1_Guard prints only propext / Classical.choice / Quot.sound):
    * log3_q: exp(5493/10000)^2 <= 3 with a 20-term Taylor upper bound, i.e. 2 * 5493/10000 <= log 3
      (margin 1.2e-5);
    * poleFree2_floor5493: (1/2000) int |g|^2 <= Re weilForm (autocorr g) for every IsWeilTest g in
      PoleFree2 supported in [-5493/10000, 5493/10000] (from poleFree2_floor_of_cert at the window
      L* = 5493/10000: the comb of weilSymbol L* is {2});
    * weil_positivity_poleFree2_window5493: for every L <= 5493/10000 and tsupport g in [-L, L],
      0 <= Re weilForm (autocorr g)  (the window L* contains every smaller support, so no case split
      at (log 2)/2 is needed).
  No `sorry`.
-/
import Hodge1_PoleFreeWindow
import Hodge1_Ldl5493E
import Hodge1_Ldl5493O

open Real MeasureTheory Set Finset

noncomputable section

namespace Hodge1
open KWin (log_pi_le)
open KWin2 WeilExplicit

/-! ## A. Kernel checks (structural, tail, Gram inverse, rational side conditions). -/

theorem par5493 : parCheck P5493 = true := by decide +kernel
theorem brk5493 : brkCheck P5493 = true := by decide +kernel
theorem piece5493 : pieceCheck P5493 = true := by decide +kernel
theorem min5493 : minCheck P5493 = true := by decide +kernel
theorem comb5493 : combCheck P5493 = true := by decide +kernel
theorem side5493 : sideCheck P5493 (29958 / 10000) = true := by decide +kernel
theorem tailE5493 : tailCondP H5493 0 NE5493 lamE5493 eta5493 = true := by decide +kernel
theorem tailO5493 : tailCondP H5493 1 NO5493 lamO5493 eta5493 = true := by decide +kernel
theorem ginvE5493 : ginvCheck P5493 0 NE5493 = true := by decide +kernel
theorem ginvO5493 : ginvCheck P5493 1 NO5493 = true := by decide +kernel

/-- `exp(5493/10000)^2 <= 3` (Taylor upper bound, 20 terms). -/
theorem log3_q : expUp (5493 / 10000) 20 ^ 2 ≤ 3 := by decide +kernel

/-! ## B. The window. -/

/-- The window half-width `L* = 5493/10000`. -/
def Lstar : ℝ := 5493 / 10000

lemma lR5493 : lR H5493.K = Lstar := by norm_num [lR, H5493, P5493, Lstar]

lemma log_two_lt_5493 : Real.log 2 < 2 * Lstar := by
  have := Real.log_two_lt_d9; unfold Lstar; norm_num at this ⊢; linarith

/-- **`2 L* <= log 3`** from the kernel-checked `exp(L*)^2 <= 3`. -/
theorem twoL_le_log_three_5493 : 2 * Lstar ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h0 : (0 : ℚ) ≤ 5493 / 10000 := by norm_num
  have h1 : (5493 / 10000 : ℚ) ≤ 1 := by norm_num
  have e := exp_le_expUp h0 h1 (n := 20) (by norm_num)
  have hq : ((expUp (5493 / 10000) 20 : ℚ) : ℝ) ^ 2 ≤ 3 := by exact_mod_cast log3_q
  have hpos : 0 ≤ Real.exp (((5493 / 10000 : ℚ) : ℝ)) := (Real.exp_pos _).le
  have hsq := pow_le_pow_left₀ hpos e 2
  have he2 : Real.exp (2 * Lstar) = Real.exp (((5493 / 10000 : ℚ) : ℝ)) ^ 2 := by
    rw [← Real.exp_nat_mul]; unfold Lstar; push_cast; ring_nf
  rw [he2]
  linarith

lemma lamFloor5493_cast : ((H5493.K.lamFloor : ℚ) : ℝ) = 1 / 2000 := by
  norm_num [H5493, P5493]

/-- **THE POLE-FREE WINDOW FLOOR AT L* = 5493/10000**: every smooth compactly supported g with
int g e^{u/2} = int g e^{-u/2} = 0, supported in [-L*, L*], has
Re weilForm (autocorr g) >= (1/2000) ||g||_2^2. -/
theorem poleFree2_floor5493 (g : ℝ → ℂ) (hg : IsWeilTest g) (hP : PoleFree2 g)
    (hs : tsupport g ⊆ Icc (-Lstar) Lstar) :
    (1 / 2000 : ℝ) * (∫ x, ‖g x‖ ^ 2) ≤ (weilForm (autocorr g)).re := by
  have h := poleFree2_floor_of_cert H5493 rfl NE5493 NO5493 lamE5493 lamO5493 eta5493 D5493 D5493
    (29958 / 10000) log_two_lt_5493 twoL_le_log_three_5493 (le_of_eq lR5493.symm) gamma_le32 log_pi_le
    side5493 par5493 brk5493 piece5493 min5493 comb5493 tailE5493 tailO5493 ginvE5493 ginvO5493
    certE5493 certO5493 g hg hP hs
  rwa [lamFloor5493_cast] at h

/-- **WEIL POSITIVITY ON THE TWO-CONDITION POLE-FREE CLASS FOR L <= 5493/10000** (the one-prime
window up to (log 3)/2 - 6e-6; new on the pole-free class past L = 1/2). -/
theorem weil_positivity_poleFree2_window5493 (g : ℝ → ℂ) (hg : IsWeilTest g) (hP : PoleFree2 g)
    (L : ℝ) (hL : L ≤ 5493 / 10000) (hsupp : tsupport g ⊆ Icc (-L) L) :
    0 ≤ (weilForm (autocorr g)).re := by
  have hs' : tsupport g ⊆ Icc (-Lstar) Lstar :=
    hsupp.trans (Icc_subset_Icc (by unfold Lstar; linarith) (by unfold Lstar; exact hL))
  have h := poleFree2_floor5493 g hg hP hs'
  have hm : 0 ≤ (1 / 2000 : ℝ) * (∫ x, ‖g x‖ ^ 2) :=
    mul_nonneg (by norm_num) (integral_nonneg fun x => by positivity)
  linarith

end Hodge1

end
