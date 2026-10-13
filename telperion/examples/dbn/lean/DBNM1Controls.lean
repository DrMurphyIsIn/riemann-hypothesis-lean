/-
  DBNM1Controls -- lane m1, kernel-checked controls for the parametric de Bruijn theorem
  `dbn_debruijn_parametric` (DBNM1Parametric, milestone M1a of
  telperion/docs/ROUTE_C_SYNTHESIS_2026-09-23.md section 7.2).

  POSITIVE CONTROLS (the hypothesis is satisfiable and the theorem reproduces C3 by a second,
  independent route).  At `t0 = 0`, `Y = 1` the hypothesis of `dbn_debruijn_parametric` is
  exactly the proved strip node `dbn_H0_zero_strip` (DBNStrip).  Feeding it in gives

    * `m1_control_contraction_via_parametric`: for every `t ≥ 0` every zero of `H_t` has
      `(Im z)² ≤ max (1 − 2t) 0` -- the statement of `DBN.H_zero_im_sq_le` (DBNHadamardApprox);
    * `m1_control_debruijn_via_parametric`: for every `t ≥ 1/2` every zero of `H_t` is real --
      the statement of the registry node `dbn_debruijn_real_zeros`, character for character.

  Neither control imports DBNDeBruijnReduction or DBNHadamardApprox: the route is
  strip -> parametric theorem, not strip -> `H0ZeroFreeOffStrip`/`approxHadamard` -> C3.  So the
  two proofs of de Bruijn's `t ≥ 1/2` theorem on the island share only DBNStep, DBNHurwitz,
  DBNHeatApprox and the Hadamard factorisation.

  SCOPE.  Both are the known half (`Λ ≤ 1/2`, de Bruijn 1950).  Nothing here says anything about
  the zeros of `H_0` inside the strip.  `Λ ≤ 0` is RH; nothing here proves it.
  conjecture1_proved = False.
-/
import DBNM1Parametric
import DBNStrip

/-- **Positive control 1**: the parametric theorem at `t0 = 0`, `Y = 1`, fed with the strip node
`dbn_H0_zero_strip`, reproduces the quantitative contraction of C3 (`DBN.H_zero_im_sq_le`):
for `t ≥ 0`, every zero of `H_t` has `(Im z)² ≤ max (1 − 2t) 0`. -/
theorem m1_control_contraction_via_parametric :
    ∀ t : ℝ, 0 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im ^ 2 ≤ max (1 - 2 * t) 0 := by
  intro t ht z hz
  have h := dbn_debruijn_parametric 0 1 dbn_H0_zero_strip t ht z hz
  rwa [sub_zero] at h

/-- **Positive control 2**: de Bruijn's `t ≥ 1/2` theorem (the registry statement of
`dbn_debruijn_real_zeros`, character for character) by the parametric route. -/
theorem m1_control_debruijn_via_parametric :
    ∀ t : ℝ, 1 / 2 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im = 0 := by
  intro t ht z hz
  have h := m1_control_contraction_via_parametric t (by linarith) z hz
  rw [max_eq_right (by linarith)] at h
  exact (pow_eq_zero_iff two_ne_zero).mp (le_antisymm h (sq_nonneg _))
