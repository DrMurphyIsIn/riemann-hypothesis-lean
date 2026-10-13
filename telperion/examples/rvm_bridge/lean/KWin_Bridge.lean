/-
  KWin_Bridge.lean -- the mirrormere prime-free window, as the named Props of E6Bridge31.
  PrimeFreeWindowPositivity (2L <= log 2, goal-node test class with pole terms kept) is proved
  hypothesis-free by the kernel-native certificate of KWin_*. Per PR #604 the 1.3e-3 margin is
  zero content (first 200 zero pairs), so this is NOT Connes-Consani (pole-free class).
  A finite-window Weil positivity statement; conjecture1_proved = False.
-/
import KWin_Window
import E6Bridge31

theorem kwin_primeFreeWindowPositivity : RvMBridge31.PrimeFreeWindowPositivity :=
  KWin.kwin_primeFreeWindow

theorem kwin_primeFreeWindowArchPositivity : RvMBridge31.PrimeFreeWindowArchPositivity :=
  RvMBridge31.primeFreeWindow_iff_arch.mp KWin.kwin_primeFreeWindow

/-- The full prime-free window in the explicit-binder shape of `MM_weil_positivity_window_tenth`
    (which it contains: L <= 1/10 implies 2L <= log 2). -/
theorem weil_positivity_prime_free_window (g : ℝ → ℂ) (hg : WeilExplicit.IsWeilTest g) (L : ℝ)
    (hL : 2 * L ≤ Real.log 2) (hsupp : tsupport g ⊆ Set.Icc (-L) L) :
    0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re :=
  kwin_primeFreeWindowPositivity g L hg hsupp hL

/-- The L <= 1/10 window (`MM_weil_positivity_window_tenth`, statement verbatim) as a corollary of the full
    prime-free window: L <= 1/10 gives 2L <= 1/5 <= log 2. -/
theorem weil_positivity_window_tenth_of_prime_free (g : ℝ → ℂ) (hg : WeilExplicit.IsWeilTest g) (L : ℝ)
    (hL : L ≤ 1 / 10) (hsupp : tsupport g ⊆ Set.Icc (-L) L) :
    0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re := by
  have hlog : (1 : ℝ) / 5 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  exact weil_positivity_prime_free_window g hg L (by linarith) hsupp
