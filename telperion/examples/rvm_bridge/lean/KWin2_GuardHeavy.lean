/-
  KWin2_GuardHeavy -- the axiom guard of the HEAVY KWin2 window instances (rvm_bridge island,
  2026-09-24).  Not in defaultTargets and not imported by AxiomGuardRvMBridge: the head
  certificates at L = 9/20 (kernel ~6 min, ~17 GB peak) and L = 1/2 (kernel ~50 min CPU, ~19 GB
  peak per sector) exceed the hosted CI runner.  Run locally:
      lake build KWin2_GuardHeavy && lake env lean KWin2_GuardHeavy.lean
  Every line must print exactly [propext, Classical.choice, Quot.sound].
  conjecture1_proved = False.  A finite-window statement is not RH; not Connes-Consani (pole terms
  kept); cf. PR #604.  No `sorry`.
-/
import KWin2_Window920
import KWin2_Window12
import KWin2_BridgeHeavy

-- L = 9/20 (2L = 0.9, comb n = 2): WindowFloor (9/20) (4.5e-6)
#print axioms KWin2.certE920
#print axioms KWin2.certO920
#print axioms KWin2.certE920_negative_control
#print axioms KWin2.side920
#print axioms KWin2.windowFloor920
#print axioms KWin2.weil_positivity_window_nine_twentieths

-- L = 1/2 (2L = 1, comb n = 2): WindowFloor (1/2) (3.5e-7), rounded checker psdCertR
#print axioms KWin2.certE12
#print axioms KWin2.certO12
#print axioms KWin2.certE12_negative_control
#print axioms KWin2.side12
#print axioms KWin2.windowFloor12
#print axioms KWin2.weil_positivity_window_half

-- registry-shape bridges (KWin2_BridgeHeavy)
#print axioms weil_positivity_window_nine_twentieths
#print axioms weil_window_floor_nine_twentieths
#print axioms weil_positivity_window_half
#print axioms weil_window_floor_half
