/-
  AxiomGuardWeilForm -- CI axiom guard for the weil_form_enclosure dogfood island.

  `#print axioms` over every theorem this island claims.  CI greps the output for `sorryAx`
  and FAILS if it appears, so a `sorry` anywhere in the emitted ladder (or in the two abstract
  box lemmas it delegates to) cannot ship.  The expected axiom set is mathlib's three
  (`propext`, `Classical.choice`, `Quot.sound`).

  What the guard does NOT say: these theorems are CONSEQUENCES of Arb enclosures carried as
  named hypotheses, not unconditional facts about zeta.  A kernel-clean axiom list certifies
  the derivation, never the enclosure (python-flint is the documented non-kernel trust seam).
  conjecture1_proved = False.
-/
import WeilFormEnclosure

#print axioms WeilFormEnclosure.box_pos
#print axioms WeilFormEnclosure.box_minor_pos
#print axioms WeilFormEnclosure.weil_negative_refutes_rh
#print axioms WeilFormEnclosure.weil_autocorr_pos_bump_w1
#print axioms WeilFormEnclosure.weil_autocorr_pos_bump_w3o2
#print axioms WeilFormEnclosure.weil_gram_minor_0_1
