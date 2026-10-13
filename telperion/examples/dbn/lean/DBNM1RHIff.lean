/-
  DBNM1RHIff -- lane m1, Route C milestone M1c (telperion/docs/ROUTE_C_SYNTHESIS_2026-09-23.md
  sections 5.2 rank 1 and 7.2): the sInf-free statement of the C10 wall as an EQUIVALENCE.

    `dbn_rh_iff_real_zeros_nonneg_t`:  strip-RH  <->  for every `t ≥ 0`, every zero of `H_t` is real.

  The left side is verbatim the left side of the C4 node `dbn_rh_iff_H0_real_zeros`
  (DBNRealZerosIffFinal).  Proof: C4 turns strip-RH into "every zero of `H_0` is real"; the up-set
  property `dbn_real_zeros_upset` (DBNM1Parametric, M1b) carries that to every `t ≥ 0`; the
  converse specialises at `t = 0`.

  SCOPE.  Classically the right side is `Λ ≤ 0`, which is RH itself.  This is an equivalence
  between two restatements of the same OPEN conjecture and proves NEITHER side.  The de
  Bruijn-Newman constant `Λ` is not defined on this island (no `sInf`).  `Λ ≤ 0` is RH; nothing
  here proves it.  conjecture1_proved = False.
-/
import DBNM1Parametric
import DBNRealZerosIffFinal

/-- **M1c** (proposed registry node `RH_dbn_rh_iff_real_zeros_nonneg_t`, statement as sketched in
ROUTE_C_SYNTHESIS_2026-09-23.md section 7.2): strip-RH (the left side of the C4 node
`dbn_rh_iff_H0_real_zeros`, verbatim) holds iff for every `t ≥ 0` every zero of `H_t` is real.
The sInf-free form of the C10 wall (`Λ ≤ 0`) as an equivalence.  It proves neither side.
Nothing here proves RH.  conjecture1_proved = False. -/
theorem dbn_rh_iff_real_zeros_nonneg_t :
    (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re = 1 / 2) ↔
    ∀ t : ℝ, 0 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im = 0 := by
  rw [dbn_rh_iff_H0_real_zeros]
  constructor
  · intro h0 t ht z hz
    exact dbn_real_zeros_upset 0 t ht h0 z hz
  · intro h
    exact h 0 le_rfl
