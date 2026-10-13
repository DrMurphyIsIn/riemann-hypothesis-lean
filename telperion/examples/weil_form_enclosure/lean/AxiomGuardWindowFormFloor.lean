/-
  AxiomGuardWindowFormFloor -- CI axiom guard for the window_form_floor dogfood.

  `#print axioms` over every theorem the `window_form_floor` emitter ships into this island
  (Zhu, arXiv:2608.24827, Theorem 1.1 / Theorem 1.2).  CI greps the output for `sorryAx` and
  FAILS if it appears, so a `sorry` in the emitted instances or in the abstract rounding lemma
  they delegate to cannot ship.  The expected axiom set is mathlib's three (`propext`,
  `Classical.choice`, `Quot.sound`).

  What the guard does NOT say, and must never be read to say:

  * These theorems are CONSEQUENCES of a hypothesis `hred`, not unconditional facts.  `hred`
    bundles the four undischarged analytic inputs of Zhu Theorem 1.1 -- the frequency-side symbol
    representation (eq. 2), the digamma envelope (Lemma 3.1), the Legendre / spherical-Bessel
    localization (eqs. 6 and 12) -- together with the Arb/mpmath certified block floor `lam0` and
    the tail constants `eps_D`, `eps_B`.  A kernel-clean axiom list certifies the DERIVATION, never
    the enclosure.
  * What the kernel actually proves here is that the published rounding is sound: from a window
    floor at the raw certified constant, a window floor at the rounded-down published one.
  * A positive window floor at a FIXED `L` is a finite fragment of RH, and is what RH predicts.
    It confirms nothing.  The RH-equivalent clause is a window floor at EVERY `L`, and Zhu's own
    Theorem 1.4 shows the pointwise-envelope route to it closes doubly exponentially fast.

  No RH progress.  PRE-WALL.  conjecture1_proved = False.
-/
import WindowFormFloorInstances

#print axioms WindowFormFloorInstances.windowFloor_of_le
#print axioms WindowFormFloorInstances.zhu_window_floor_L08_T200
#print axioms WindowFormFloorInstances.zhu_window_floor_L08_T150
