/-
  KWin2_BridgeHeavy.lean -- the windows L = 9/20 and L = 1/2 (past the prime-free boundary, prime
  comb term n = 2 present), in the explicit-binder registry shape of
  `weil_positivity_prime_free_window` and as WeilWindow floors (rvm_bridge island, 2026-09-24).
  HEAVY: imports the L = 9/20 and L = 1/2 head certificates (kernel ~6 min / ~50 min CPU, peak
  ~17 GB / ~19 GB), so it is not in defaultTargets; KWin2_GuardHeavy prints its axioms.
  Goal-node test class, pole terms kept: NOT Connes-Consani.  Per PR #604 a finite-window margin
  samples the zeros and proves nothing about them.  conjecture1_proved = False.
-/
import KWin2_Window920
import KWin2_Window12

/-- Weil positivity on every window with `2L <= 9/10`. -/
theorem weil_positivity_window_nine_twentieths (g : ℝ → ℂ) (hg : WeilExplicit.IsWeilTest g) (L : ℝ)
    (hL : 2 * L ≤ 9 / 10) (hsupp : tsupport g ⊆ Set.Icc (-L) L) :
    0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re :=
  KWin2.weil_positivity_window_nine_twentieths g hg L (by linarith) hsupp

/-- Zhu's window floor at `L = 9/20`: `Re weilForm (autocorr f) >= 4.5e-6 ||f||_2^2`. -/
theorem weil_window_floor_nine_twentieths : WeilWindow.WindowFloor (9 / 20) (9 / 2000000) :=
  KWin2.windowFloor920

/-- Weil positivity on every window with `2L <= 1`. -/
theorem weil_positivity_window_half (g : ℝ → ℂ) (hg : WeilExplicit.IsWeilTest g) (L : ℝ)
    (hL : 2 * L ≤ 1) (hsupp : tsupport g ⊆ Set.Icc (-L) L) :
    0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re :=
  KWin2.weil_positivity_window_half g hg L (by linarith) hsupp

/-- Zhu's window floor at `L = 1/2`: `Re weilForm (autocorr f) >= 3.5e-7 ||f||_2^2`. -/
theorem weil_window_floor_half : WeilWindow.WindowFloor (1 / 2) (7 / 20000000) :=
  KWin2.windowFloor12
