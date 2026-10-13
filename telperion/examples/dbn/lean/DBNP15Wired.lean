/-
  DBNP15Wired.lean -- the Polymath15 criterion with the parametric de Bruijn step DISCHARGED.

  Wires lane M4 (`DBN.m4_p15_criterion_of_M1aStep`, P15 Prop 3.3 + the Thm 1.2 closing step taken
  as the hypothesis `M1aStep`) to lane M1 (`dbn_debruijn_parametric`, which proves that step for
  every real t0), and lane M6gap (`M6gap.p15_prop33_i_of_le`, P15 condition (i) in H_0 form at
  every X <= 55/8, hypothesis-free).

  Result: for X <= 55/8, P15's conditions (ii) canopy and (iii) barrier ALONE imply that every
  zero of H_t is real for t >= t0 + y0^2/2. Neither condition is verified here for any parameters,
  so this proves no bound Lambda <= c; it reduces such a bound to two finite obligations.
  conjecture1_proved = False; nothing here proves RH (RH is Lambda <= 0).
-/
import DBNM4P15Criterion
import DBNM1Parametric
import M6gapP15ZeroFree

/-- M1 discharges M4's step hypothesis. -/
theorem dbn_m1aStep_holds : DBN.M1aStep := dbn_debruijn_parametric

/-- The Polymath15 criterion (P15 Thm 1.2 conclusion from Prop 3.3's conditions), unconditional. -/
theorem dbn_p15_criterion (X t0 y0 : ℝ) (hX : 0 < X) (ht0 : 0 < t0)
    (hy0 : 0 < y0) (hy1 : y0 ≤ 1) :
    DBN.P15ZeroFreeRect X y0 t0 → DBN.P15Canopy X y0 t0 → DBN.P15Barrier X y0 t0 →
    ∀ t : ℝ, t0 + y0 ^ 2 / 2 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im = 0 :=
  DBN.m4_p15_criterion_of_M1aStep dbn_m1aStep_holds X t0 y0 hX ht0 hy0 hy1

/-- Condition (i) holds at every X <= 55/8 (lane M6gap), in the M4 vocabulary. -/
theorem dbn_p15ZeroFreeRect_of_le {X : ℝ} (hX : X ≤ 55 / 8) (y0 t0 : ℝ) :
    DBN.P15ZeroFreeRect X y0 t0 := by
  unfold DBN.P15ZeroFreeRect
  exact M6gap.p15_prop33_i_of_le hX y0 t0

/-- At X <= 55/8 only the canopy (ii) and the barrier (iii) remain. -/
theorem dbn_p15_criterion_low (X t0 y0 : ℝ) (hX : 0 < X) (hX' : X ≤ 55 / 8) (ht0 : 0 < t0)
    (hy0 : 0 < y0) (hy1 : y0 ≤ 1) :
    DBN.P15Canopy X y0 t0 → DBN.P15Barrier X y0 t0 →
    ∀ t : ℝ, t0 + y0 ^ 2 / 2 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im = 0 :=
  dbn_p15_criterion X t0 y0 hX ht0 hy0 hy1 (dbn_p15ZeroFreeRect_of_le hX' y0 t0)

#print axioms dbn_m1aStep_holds
#print axioms dbn_p15_criterion
#print axioms dbn_p15ZeroFreeRect_of_le
#print axioms dbn_p15_criterion_low
