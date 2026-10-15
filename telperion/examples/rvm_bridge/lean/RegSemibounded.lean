import PFSemibounded

/-!
# Registry-shape statements: the pole-free Weil form is semibounded iff RH (e9, 2026-10-14)

Two root-namespace theorems whose statements are the registry statements VERBATIM (fully qualified; the
pole-free class spelled out as the two conditions paperFT g (I/2) = 0 and paperFT g (-I/2) = 0, the same
class as MM_polefree_weil_converse and the HODGE-1 nodes), proved from `PFSemibounded`:
* `polefree_weil_semibounded_iff_rh`       : RH iff there is C with -C ∫ ‖g‖^2 <= Re weilForm (g * g~)
                                             for every pole-free Weil test g;
* `polefree_weil_shift_semibounded_iff_rh` : for EVERY real c, RH iff the shifted form
                                             Re weilForm (g * g~) + c ∫ ‖g‖^2 is semibounded in the same sense.
The second is gate 12.1's dichotomy (Theorem 2) with hypothesis (F) removed: the archimedean delta coefficient
does not decide RH.  Both are RH-EQUIVALENT reformulations (a soft form of Weil's criterion), not progress on RH.
conjecture1_proved = False.
-/

/-- Registry shape of `MM_polefree_weil_semibounded`. -/
theorem polefree_weil_semibounded_iff_rh :
    RiemannHypothesis ↔ ∃ C : ℝ, ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g →
      Zeta23.paperFT g (Complex.I / 2) = 0 → Zeta23.paperFT g (-Complex.I / 2) = 0 →
      -C * ∫ x, ‖g x‖ ^ 2 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re := by
  rw [RvMBridgePF.rh_iff_poleFree_weil_semibounded]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun g hg h1 h2 => hC g hg ⟨h1, h2⟩⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, fun g hg hpf => hC g hg hpf.1 hpf.2⟩

/-- Registry shape of `MM_polefree_weil_shift_semibounded`. -/
theorem polefree_weil_shift_semibounded_iff_rh (c : ℝ) :
    RiemannHypothesis ↔ ∃ C : ℝ, ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g →
      Zeta23.paperFT g (Complex.I / 2) = 0 → Zeta23.paperFT g (-Complex.I / 2) = 0 →
      -C * ∫ x, ‖g x‖ ^ 2
        ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re + c * ∫ x, ‖g x‖ ^ 2 := by
  rw [RvMBridgePF.rh_iff_poleFree_weil_shift_semibounded c]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun g hg h1 h2 => hC g hg ⟨h1, h2⟩⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, fun g hg hpf => hC g hg hpf.1 hpf.2⟩
