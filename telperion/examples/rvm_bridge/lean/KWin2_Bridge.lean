/-
  KWin2_Bridge.lean -- the window PAST the prime-free boundary at L = 2/5, in the explicit-binder
  registry shape of `weil_positivity_prime_free_window` (KWin_Bridge) and as a WeilWindow floor
  (rvm_bridge island, 2026-09-24).
  2L = 0.8 > log 2: the prime comb term n = 2 is present and kept exactly on [0, T] by the
  kernel-native certificate of KWin2_*.  Goal-node test class, pole terms kept: NOT Connes-Consani
  (pole-free class, 2L <= log 2).  Per PR #604 a finite-window margin samples the zeros and proves
  nothing about them.  A finite-window Weil positivity statement; conjecture1_proved = False.
-/
import KWin2_Window25

/-- Weil positivity on every window with `2L <= 4/5` (contains the prime-free window). -/
theorem weil_positivity_window_two_fifths (g : ℝ → ℂ) (hg : WeilExplicit.IsWeilTest g) (L : ℝ)
    (hL : 2 * L ≤ 4 / 5) (hsupp : tsupport g ⊆ Set.Icc (-L) L) :
    0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re :=
  KWin2.weil_positivity_window_two_fifths g hg L (by linarith) hsupp

/-- Zhu's window floor at `L = 2/5`: `Re weilForm (autocorr f) >= (1/25000) ||f||_2^2`. -/
theorem weil_window_floor_two_fifths : WeilWindow.WindowFloor (2 / 5) (1 / 25000) :=
  KWin2.windowFloor25
