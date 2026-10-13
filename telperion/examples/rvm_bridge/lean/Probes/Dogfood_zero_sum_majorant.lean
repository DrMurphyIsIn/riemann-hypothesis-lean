/-
  Dogfood_zero_sum_majorant -- the Telperion `zero_sum_majorant` kind (SHAPES_AUDIT_48H_2026-09-22.md
  section 2 rank 2; audit C 3.1 + B N5) regenerating three hand-proof sites of this island and the
  tail-envelope consumer face, 2026-09-22:

    E6Bridge19  zbound / norm_zterm_le_zbound             -> zbound_regen_{strip,le,summable}
    E6Bridge18  polBound / norm_polTerm_le / summable_polTerm -> polBound_regen_{strip,le,summable}
    E6Bridge15  liBound / norm_liPaired_le / summable_liPaired -> liBound_regen_{strip,le,summable}
    E6Bridge12  tail_bound_window (the B N5 envelope)      -> tail_regen_{envelope,rate}

  Each zero_window instance's certificate is ONE strip inequality (1/|rho|^2 <= (9/4)/(1 + |gamma|^2)
  twice, 1/(Im rho - Im s)^2 <= (13/4 + 2 (Im s)^2)/(1 + |gamma|^2) once) certified as an exact
  nonnegative Bernstein / Polya combination checked by `ring`; the composition with the prelude atom
  RvMBridgeXi.zeroBoundAt is the frozen skeleton.

  The block between the telperion provenance header and `end DogfoodZeroSumMajorant` is the FROZEN
  emitter output (examples/rvm_bridge/dogfood_zero_sum_majorant.py regenerates it; a test pins the
  bytes).  After it, generator-appended and hand-written: the instance GLUE (each family's own
  far-region norm shape, copied from the hand proof; the emitted theorems take it as the named
  hypothesis `hshape`) and kernel CROSS-CHECKS that apply each regenerated theorem to the ORIGINAL's
  statement, so the kernel confirms the regeneration is interchangeable with the hand proof.  Nothing
  in E6Bridge12 / 15 / 18 / 19 is modified.

  Run: cd telperion/examples/rvm_bridge/lean && lake env lean Probes/Dogfood_zero_sum_majorant.lean
  Expected axioms for every theorem: [propext, Classical.choice, Quot.sound].

  conjecture1_proved = False.  Nothing here bears on RH: every statement is a summability or
  pointwise-majorant fact about a family indexed by the nontrivial zeros, or a rational inequality on
  the open strip, true whatever the real parts of the zeros are.
-/
/- telperion 0.1.6 | family DogfoodZeroSumMajorant | input-hash bb537ba3657fb274
   11 theorems, 15 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import E6Bridge12
import E6Bridge15
import E6Bridge18
import E6Bridge19
import RvMBridgeXi

namespace DogfoodZeroSumMajorant

/-- `zbound_regen_strip` -- zero_sum_majorant, the per-instance certificate (the strip
    inequality): on a nontrivial zero with `1 <= |ρ.im|`, `N / D <= C / (1 + |gamma_rho|^2)`
    with `N = 1`, `D = normSq rho`, `C = (9 / 4)`. Cleared, `C * D - N * (1 + |gamma_rho|^2)` is
    the EXACT nonnegative combination `key` (3 term(s)) of the generators `Re rho`, `1 - Re
    rho`, `ρ.im ^ 2 - 1` -- the Bernstein / Polya form on the strip after `w^2 -> h^2 + t` --
    checked by `ring`, each summand nonnegative by an explicit `mul_nonneg` term. A strip
    inequality: nothing about WHERE the zeros are. conjecture1_proved = False. -/
theorem zbound_regen_strip {ρ : ℂ} (hz : Zeta23.IsNontrivialZero ρ)
    (him : (1 : ℝ) ≤ |ρ.im|) :
    1 / Complex.normSq ρ ≤ (9 / 4) / (1 + Complex.normSq (Zeta23.gammaOf ρ)) := by
  have hre : (0 : ℝ) < ρ.re := hz.2.1
  have hre1 : ρ.re < 1 := hz.2.2
  have hx0 : (0 : ℝ) ≤ ρ.re := hre.le
  have hu0 : (0 : ℝ) ≤ 1 - ρ.re := by linarith
  have ht0 : (0 : ℝ) ≤ ρ.im ^ 2 - 1 := by
    have h2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) him 2
    rw [sq_abs] at h2
    linarith
  have hg : Complex.normSq (Zeta23.gammaOf ρ) = ρ.im ^ 2 + (1 / 2 - ρ.re) ^ 2 := by
    rw [Complex.normSq_apply, Zeta23.WeilEF.gammaOf_re, Zeta23.WeilEF.gammaOf_im]
    ring
  have hn : Complex.normSq ρ = ρ.re ^ 2 + ρ.im ^ 2 := by
    rw [Complex.normSq_apply]
    ring
  have hden : (0 : ℝ) < (ρ.re ^ 2 + ρ.im ^ 2) :=
    add_pos_of_pos_of_nonneg (pow_pos hre 2) (sq_nonneg _)
  have hγ : (0 : ℝ) < (1 + (ρ.im ^ 2 + (1 / 2 - ρ.re) ^ 2)) := by positivity
  rw [hn, hg, div_le_div_iff₀ hden hγ]
  have key : (9 / 4) * (ρ.re ^ 2 + ρ.im ^ 2) - 1 * (1 + (ρ.im ^ 2 + (1 / 2 - ρ.re) ^ 2))
      = (5 / 4) * (ρ.im ^ 2 - 1) + 1 * (ρ.re * (1 - ρ.re)) + (9 / 4) * ρ.re ^ 2 := by
    ring
  have t1 : (0 : ℝ) ≤ (5 / 4) * (ρ.im ^ 2 - 1) := mul_nonneg (by norm_num) ht0
  have t2 : (0 : ℝ) ≤ 1 * (ρ.re * (1 - ρ.re)) := mul_nonneg (by norm_num) (mul_nonneg hx0 hu0)
  have t3 : (0 : ℝ) ≤ (9 / 4) * ρ.re ^ 2 := mul_nonneg (by norm_num) (pow_nonneg hx0 2)
  linarith only [key, t1, t2, t3]

/-- `zbound_regen_le` -- the zero-sum majorant: a family vanishing off the nontrivial zeros,
    bounded by `b` on the finite ordinate window `|ρ.im| < 1` and by `m(rho) * (K * (1 /
    Complex.normSq ρ))` off it, is bounded pointwise by the island atom
    `RvMBridgeXi.zeroBoundAt` (the window indicator plus the local-count tail `m(rho) C/(1 +
    |gamma_rho|^2)`), through the certified `zbound_regen_strip`. conjecture1_proved = False. -/
theorem zbound_regen_le {f : ℂ → ℂ} {b : ℂ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hzero : ∀ ρ, ¬ Zeta23.IsNontrivialZero ρ → f ρ = 0)
    (hwin : ∀ ρ, Zeta23.IsNontrivialZero ρ → |ρ.im| < (1 : ℝ) → ‖f ρ‖ ≤ b ρ)
    (hshape : ∀ ρ, Zeta23.IsNontrivialZero ρ → (1 : ℝ) ≤ |ρ.im| →
      ‖f ρ‖ ≤ (WeilExplicit.zeroMult ρ : ℝ) * (K * (1 / Complex.normSq ρ)))
    (ρ : ℂ) :
    ‖f ρ‖ ≤ RvMBridgeXi.zeroBoundAt 0 1 (K * (9 / 4)) b ρ := by
  refine RvMBridgeXi.norm_le_zeroBoundAt hzero
    (fun ρ hz hw => hwin ρ hz (by simpa using hw)) (fun ρ hz him => ?_)
    (mul_nonneg hK (by positivity)) ρ
  have him' : (1 : ℝ) ≤ |ρ.im| := by simpa using him
  refine (hshape ρ hz him').trans ?_
  have hm : (0 : ℝ) ≤ (WeilExplicit.zeroMult ρ : ℝ) := Nat.cast_nonneg _
  refine mul_le_mul_of_nonneg_left ?_ hm
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (zbound_regen_strip hz him') hK

/-- `zbound_regen_summable` -- `Summable f` from `zbound_regen_le` with `b := ‖f‖` on the window
    (finite by `zetaSeam.finite_window`) and the tail summed by
    `summable_mult_div_one_add_normSq` (`RvMBridgeXi.summable_zeroBoundAt`). conjecture1_proved
    = False. -/
theorem zbound_regen_summable {f : ℂ → ℂ} {K : ℝ} (hK : 0 ≤ K)
    (hzero : ∀ ρ, ¬ Zeta23.IsNontrivialZero ρ → f ρ = 0)
    (hshape : ∀ ρ, Zeta23.IsNontrivialZero ρ → (1 : ℝ) ≤ |ρ.im| →
      ‖f ρ‖ ≤ (WeilExplicit.zeroMult ρ : ℝ) * (K * (1 / Complex.normSq ρ))) :
    Summable f :=
  Summable.of_norm_bounded
    (RvMBridgeXi.summable_zeroBoundAt 0 1 (K * (9 / 4)) (fun ρ => ‖f ρ‖))
    (zbound_regen_le (b := fun ρ => ‖f ρ‖) hK hzero (fun _ _ _ => le_rfl) hshape)

/-- `polBound_regen_strip` -- zero_sum_majorant, the per-instance certificate (the strip
    inequality): on a nontrivial zero with `1 <= |ρ.im - s.im|`, `N / D <= C / (1 +
    |gamma_rho|^2)` with `N = 1`, `D = (Im rho - a)^2`, `C = (13 / 4) + 2 * s.im ^ 2`. Cleared,
    `C * D - N * (1 + |gamma_rho|^2)` is the EXACT nonnegative combination `key` (4 term(s)) of
    the generators `Re rho`, `1 - Re rho`, `(ρ.im - s.im) ^ 2 - 1`, the parameter squares, the
    declared squares `(ρ.im - 2 * s.im) ^ 2` -- the Bernstein / Polya form on the strip after
    `w^2 -> h^2 + t` -- checked by `ring`, each summand nonnegative by an explicit `mul_nonneg`
    term. A strip inequality: nothing about WHERE the zeros are. conjecture1_proved = False. -/
theorem polBound_regen_strip (s : ℂ) {ρ : ℂ} (hz : Zeta23.IsNontrivialZero ρ)
    (him : (1 : ℝ) ≤ |ρ.im - s.im|) :
    1 / (ρ.im - s.im) ^ 2 ≤ ((13 / 4) + 2 * s.im ^ 2) / (1 + Complex.normSq (Zeta23.gammaOf ρ)) := by
  have hre : (0 : ℝ) < ρ.re := hz.2.1
  have hre1 : ρ.re < 1 := hz.2.2
  have hx0 : (0 : ℝ) ≤ ρ.re := hre.le
  have hu0 : (0 : ℝ) ≤ 1 - ρ.re := by linarith
  have ht0 : (0 : ℝ) ≤ (ρ.im - s.im) ^ 2 - 1 := by
    have h2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) him 2
    rw [sq_abs] at h2
    linarith
  have hg : Complex.normSq (Zeta23.gammaOf ρ) = ρ.im ^ 2 + (1 / 2 - ρ.re) ^ 2 := by
    rw [Complex.normSq_apply, Zeta23.WeilEF.gammaOf_re, Zeta23.WeilEF.gammaOf_im]
    ring
  have hden : (0 : ℝ) < (ρ.im - s.im) ^ 2 := by linarith
  have hγ : (0 : ℝ) < (1 + (ρ.im ^ 2 + (1 / 2 - ρ.re) ^ 2)) := by positivity
  rw [hg, div_le_div_iff₀ hden hγ]
  have key : ((13 / 4) + 2 * s.im ^ 2) * (ρ.im - s.im) ^ 2
      - 1 * (1 + (ρ.im ^ 2 + (1 / 2 - ρ.re) ^ 2))
      = 1 * (ρ.im - 2 * s.im) ^ 2 + (5 / 4) * ((ρ.im - s.im) ^ 2 - 1) +
        2 * (((ρ.im - s.im) ^ 2 - 1) * s.im ^ 2) + 1 * (ρ.re * (1 - ρ.re)) := by
    ring
  have t1 : (0 : ℝ) ≤ 1 * (ρ.im - 2 * s.im) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg (ρ.im - 2 * s.im))
  have t2 : (0 : ℝ) ≤ (5 / 4) * ((ρ.im - s.im) ^ 2 - 1) := mul_nonneg (by norm_num) ht0
  have t3 : (0 : ℝ) ≤ 2 * (((ρ.im - s.im) ^ 2 - 1) * s.im ^ 2) :=
    mul_nonneg (by norm_num) (mul_nonneg ht0 (sq_nonneg s.im))
  have t4 : (0 : ℝ) ≤ 1 * (ρ.re * (1 - ρ.re)) := mul_nonneg (by norm_num) (mul_nonneg hx0 hu0)
  linarith only [key, t1, t2, t3, t4]

/-- `polBound_regen_le` -- the zero-sum majorant: a family vanishing off the nontrivial zeros,
    bounded by `b` on the finite ordinate window `|ρ.im - s.im| < 1` and by `m(rho) * (1 / (ρ.im
    - s.im) ^ 2)` off it, is bounded pointwise by the island atom `RvMBridgeXi.zeroBoundAt` (the
    window indicator plus the local-count tail `m(rho) C/(1 + |gamma_rho|^2)`), through the
    certified `polBound_regen_strip`. conjecture1_proved = False. -/
theorem polBound_regen_le (s : ℂ) {f : ℂ → ℂ} {b : ℂ → ℝ}
    (hzero : ∀ ρ, ¬ Zeta23.IsNontrivialZero ρ → f ρ = 0)
    (hwin : ∀ ρ, Zeta23.IsNontrivialZero ρ → |ρ.im - s.im| < (1 : ℝ) → ‖f ρ‖ ≤ b ρ)
    (hshape : ∀ ρ, Zeta23.IsNontrivialZero ρ → (1 : ℝ) ≤ |ρ.im - s.im| →
      ‖f ρ‖ ≤ (WeilExplicit.zeroMult ρ : ℝ) * (1 / (ρ.im - s.im) ^ 2))
    (ρ : ℂ) :
    ‖f ρ‖ ≤ RvMBridgeXi.zeroBoundAt s.im 1 ((13 / 4) + 2 * s.im ^ 2) b ρ := by
  refine RvMBridgeXi.norm_le_zeroBoundAt hzero hwin (fun ρ hz him => ?_)
    (by positivity) ρ
  refine (hshape ρ hz him).trans ?_
  have hm : (0 : ℝ) ≤ (WeilExplicit.zeroMult ρ : ℝ) := Nat.cast_nonneg _
  refine mul_le_mul_of_nonneg_left ?_ hm
  exact polBound_regen_strip s hz him

/-- `polBound_regen_summable` -- `Summable f` from `polBound_regen_le` with `b := ‖f‖` on the
    window (finite by `zetaSeam.finite_window`) and the tail summed by
    `summable_mult_div_one_add_normSq` (`RvMBridgeXi.summable_zeroBoundAt`). conjecture1_proved
    = False. -/
theorem polBound_regen_summable (s : ℂ) {f : ℂ → ℂ}
    (hzero : ∀ ρ, ¬ Zeta23.IsNontrivialZero ρ → f ρ = 0)
    (hshape : ∀ ρ, Zeta23.IsNontrivialZero ρ → (1 : ℝ) ≤ |ρ.im - s.im| →
      ‖f ρ‖ ≤ (WeilExplicit.zeroMult ρ : ℝ) * (1 / (ρ.im - s.im) ^ 2)) :
    Summable f :=
  Summable.of_norm_bounded
    (RvMBridgeXi.summable_zeroBoundAt s.im 1 ((13 / 4) + 2 * s.im ^ 2) (fun ρ => ‖f ρ‖))
    (polBound_regen_le s (b := fun ρ => ‖f ρ‖) hzero (fun _ _ _ => le_rfl) hshape)

/-- `liBound_regen_strip` -- zero_sum_majorant, the per-instance certificate (the strip
    inequality): on a nontrivial zero with `1 <= |ρ.im|`, `N / D <= C / (1 + |gamma_rho|^2)`
    with `N = 1`, `D = normSq rho`, `C = (9 / 4)`. Cleared, `C * D - N * (1 + |gamma_rho|^2)` is
    the EXACT nonnegative combination `key` (3 term(s)) of the generators `Re rho`, `1 - Re
    rho`, `ρ.im ^ 2 - 1` -- the Bernstein / Polya form on the strip after `w^2 -> h^2 + t` --
    checked by `ring`, each summand nonnegative by an explicit `mul_nonneg` term. A strip
    inequality: nothing about WHERE the zeros are. conjecture1_proved = False. -/
theorem liBound_regen_strip {ρ : ℂ} (hz : Zeta23.IsNontrivialZero ρ)
    (him : (1 : ℝ) ≤ |ρ.im|) :
    1 / Complex.normSq ρ ≤ (9 / 4) / (1 + Complex.normSq (Zeta23.gammaOf ρ)) := by
  have hre : (0 : ℝ) < ρ.re := hz.2.1
  have hre1 : ρ.re < 1 := hz.2.2
  have hx0 : (0 : ℝ) ≤ ρ.re := hre.le
  have hu0 : (0 : ℝ) ≤ 1 - ρ.re := by linarith
  have ht0 : (0 : ℝ) ≤ ρ.im ^ 2 - 1 := by
    have h2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) him 2
    rw [sq_abs] at h2
    linarith
  have hg : Complex.normSq (Zeta23.gammaOf ρ) = ρ.im ^ 2 + (1 / 2 - ρ.re) ^ 2 := by
    rw [Complex.normSq_apply, Zeta23.WeilEF.gammaOf_re, Zeta23.WeilEF.gammaOf_im]
    ring
  have hn : Complex.normSq ρ = ρ.re ^ 2 + ρ.im ^ 2 := by
    rw [Complex.normSq_apply]
    ring
  have hden : (0 : ℝ) < (ρ.re ^ 2 + ρ.im ^ 2) :=
    add_pos_of_pos_of_nonneg (pow_pos hre 2) (sq_nonneg _)
  have hγ : (0 : ℝ) < (1 + (ρ.im ^ 2 + (1 / 2 - ρ.re) ^ 2)) := by positivity
  rw [hn, hg, div_le_div_iff₀ hden hγ]
  have key : (9 / 4) * (ρ.re ^ 2 + ρ.im ^ 2) - 1 * (1 + (ρ.im ^ 2 + (1 / 2 - ρ.re) ^ 2))
      = (5 / 4) * (ρ.im ^ 2 - 1) + 1 * (ρ.re * (1 - ρ.re)) + (9 / 4) * ρ.re ^ 2 := by
    ring
  have t1 : (0 : ℝ) ≤ (5 / 4) * (ρ.im ^ 2 - 1) := mul_nonneg (by norm_num) ht0
  have t2 : (0 : ℝ) ≤ 1 * (ρ.re * (1 - ρ.re)) := mul_nonneg (by norm_num) (mul_nonneg hx0 hu0)
  have t3 : (0 : ℝ) ≤ (9 / 4) * ρ.re ^ 2 := mul_nonneg (by norm_num) (pow_nonneg hx0 2)
  linarith only [key, t1, t2, t3]

/-- `liBound_regen_le` -- the zero-sum majorant: a family vanishing off the nontrivial zeros,
    bounded by `b` on the finite ordinate window `|ρ.im| < 1` and by `m(rho) * (K * (1 /
    Complex.normSq ρ))` off it, is bounded pointwise by the island atom
    `RvMBridgeXi.zeroBoundAt` (the window indicator plus the local-count tail `m(rho) C/(1 +
    |gamma_rho|^2)`), through the certified `liBound_regen_strip`. conjecture1_proved = False. -/
theorem liBound_regen_le {f : ℂ → ℂ} {b : ℂ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hzero : ∀ ρ, ¬ Zeta23.IsNontrivialZero ρ → f ρ = 0)
    (hwin : ∀ ρ, Zeta23.IsNontrivialZero ρ → |ρ.im| < (1 : ℝ) → ‖f ρ‖ ≤ b ρ)
    (hshape : ∀ ρ, Zeta23.IsNontrivialZero ρ → (1 : ℝ) ≤ |ρ.im| →
      ‖f ρ‖ ≤ (WeilExplicit.zeroMult ρ : ℝ) * (K * (1 / Complex.normSq ρ)))
    (ρ : ℂ) :
    ‖f ρ‖ ≤ RvMBridgeXi.zeroBoundAt 0 1 (K * (9 / 4)) b ρ := by
  refine RvMBridgeXi.norm_le_zeroBoundAt hzero
    (fun ρ hz hw => hwin ρ hz (by simpa using hw)) (fun ρ hz him => ?_)
    (mul_nonneg hK (by positivity)) ρ
  have him' : (1 : ℝ) ≤ |ρ.im| := by simpa using him
  refine (hshape ρ hz him').trans ?_
  have hm : (0 : ℝ) ≤ (WeilExplicit.zeroMult ρ : ℝ) := Nat.cast_nonneg _
  refine mul_le_mul_of_nonneg_left ?_ hm
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (liBound_regen_strip hz him') hK

/-- `liBound_regen_summable` -- `Summable f` from `liBound_regen_le` with `b := ‖f‖` on the
    window (finite by `zetaSeam.finite_window`) and the tail summed by
    `summable_mult_div_one_add_normSq` (`RvMBridgeXi.summable_zeroBoundAt`). conjecture1_proved
    = False. -/
theorem liBound_regen_summable {f : ℂ → ℂ} {K : ℝ} (hK : 0 ≤ K)
    (hzero : ∀ ρ, ¬ Zeta23.IsNontrivialZero ρ → f ρ = 0)
    (hshape : ∀ ρ, Zeta23.IsNontrivialZero ρ → (1 : ℝ) ≤ |ρ.im| →
      ‖f ρ‖ ≤ (WeilExplicit.zeroMult ρ : ℝ) * (K * (1 / Complex.normSq ρ))) :
    Summable f :=
  Summable.of_norm_bounded
    (RvMBridgeXi.summable_zeroBoundAt 0 1 (K * (9 / 4)) (fun ρ => ‖f ρ‖))
    (liBound_regen_le (b := fun ρ => ‖f ρ‖) hK hzero (fun _ _ _ => le_rfl) hshape)

/-- `tail_regen_envelope` -- the tail-envelope face (audit B N5): a family bounded on `S` by `E`
    times a nonnegative summable weight has its subtype sum bounded by `E` times the WHOLE
    weight sum; a symbolic `E` with `0 <= E` as a hypothesis (the prelude's own statement). The
    audit's skeleton `norm_tsum_le_tsum_norm` + `tsum_le_tsum` + `tsum_subtype_le` +
    `tsum_mul_left`, Mathlib only. conjecture1_proved = False. -/
theorem tail_regen_envelope {ι : Type*} {f : ι → ℂ} {w : ι → ℝ} (S : Set ι) {E : ℝ} (hE : 0 ≤ E)
    (hw : Summable w) (hw0 : ∀ x, 0 ≤ w x) (hle : ∀ x : S, ‖f x‖ ≤ E * w x) :
    ‖∑' x : S, f x‖ ≤ E * ∑' x : ι, w x := by
  have hM : Summable (fun x => E * w x) := hw.mul_left E
  have hM0 : ∀ x, 0 ≤ E * w x := fun x => mul_nonneg hE (hw0 x)
  have hsumM : Summable (fun x : S => E * w x) := hM.subtype S
  have hsumN : Summable (fun x : S => ‖f x‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsumM
  calc ‖∑' x : S, f x‖
      ≤ ∑' x : S, ‖f x‖ := norm_tsum_le_tsum_norm hsumN
    _ ≤ ∑' x : S, E * w x := hsumN.tsum_le_tsum hle hsumM
    _ ≤ ∑' x : ι, E * w x := hM.tsum_subtype_le _ _ hM0
    _ = E * ∑' x : ι, w x := tsum_mul_left

/-- `tail_regen_rate` -- the rate-splitting companion at the rational `P = (-(1 / 4)) < 0`: for
    `1 <= lam` and `phi <= P` the lam-dependence decouples from the summand, AND the envelope
    factor `exp (2 (lam - 1) P)` is at most 1 (what `P < 0` buys; FALSE for every `P > 0` at lam
    = 2, so a forged sign cannot compile). conjecture1_proved = False. -/
theorem tail_regen_rate {lam φ : ℝ} (hlam : 1 ≤ lam) (hφ : φ ≤ (-(1 / 4))) :
    Real.exp (2 * lam * φ) ≤ Real.exp (2 * (lam - 1) * (-(1 / 4))) * Real.exp (2 * φ)
      ∧ Real.exp (2 * (lam - 1) * (-(1 / 4))) ≤ 1 := by
  have hl : (0 : ℝ) ≤ lam - 1 := sub_nonneg.mpr hlam
  refine ⟨?_, ?_⟩
  · rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hφ hl])
  · rw [Real.exp_le_one_iff]
    have hP : ((-(1 / 4)) : ℝ) ≤ 0 := by norm_num
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) hl) hP

end DogfoodZeroSumMajorant

/-! ## Instance glue (generator-appended, hand-written; NOT emitted).  Each lemma is the term
    family's own analysis -- the far-region norm shape the emitted `hshape` hypothesis asks for, or
    the window bound `hwin` -- copied from the hand proof it replaces. -/

namespace DogfoodZeroSumMajorant.Glue
open Zeta23

/-- E6Bridge19: off the unit window the k-th Taylor term is at most
    `m(rho) ((k+1)! 2^(k+2)) (1 / normSq rho)` (norm_zterm_le and `|rho|^(k+2) >= |rho|^2`). -/
theorem zterm_shape (k : ℕ) {s : ℂ} (hs : s ∈ Metric.ball (0 : ℂ) (RvMBridge19.zeroRadius / 2))
    {ρ : ℂ} (h : IsNontrivialZero ρ) (him : (1 : ℝ) ≤ |ρ.im|) :
    ‖RvMBridge19.zterm k ρ s‖ ≤ (WeilExplicit.zeroMult ρ : ℝ)
      * ((((k + 1).factorial : ℝ) * 2 ^ (k + 2)) * (1 / Complex.normSq ρ)) := by
  refine (RvMBridge19.norm_zterm_le hs h).trans ?_
  have hρ1 := RvMBridge19.one_le_norm_of_nontrivial him
  have hρ := RvMBridge19.norm_pos_of_nontrivial h
  have hpow : ‖ρ‖ ^ 2 ≤ ‖ρ‖ ^ (k + 2) := pow_le_pow_right₀ hρ1 (by omega)
  rw [Complex.normSq_eq_norm_sq]
  calc (WeilExplicit.zeroMult ρ : ℝ) * ((k + 1).factorial : ℝ) * 2 ^ (k + 2) / ‖ρ‖ ^ (k + 2)
      ≤ (WeilExplicit.zeroMult ρ : ℝ) * ((k + 1).factorial : ℝ) * 2 ^ (k + 2) / ‖ρ‖ ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
    _ = _ := by ring

/-- E6Bridge19: on the finitely many small zeros the k-th term is bounded by `zbound`'s window
    function `m(rho) (k+1)! 2^(k+2) / zeroRadius^(k+2)` (the radius is below every `|rho|`). -/
theorem zterm_window (k : ℕ) {s : ℂ} (hs : s ∈ Metric.ball (0 : ℂ) (RvMBridge19.zeroRadius / 2))
    {ρ : ℂ} (h : IsNontrivialZero ρ) :
    ‖RvMBridge19.zterm k ρ s‖ ≤ (WeilExplicit.zeroMult ρ : ℝ) * ((k + 1).factorial : ℝ)
      * 2 ^ (k + 2) / RvMBridge19.zeroRadius ^ (k + 2) := by
  refine (RvMBridge19.norm_zterm_le hs h).trans ?_
  have hr := RvMBridge19.zeroRadius_pos
  have hρ := RvMBridge19.norm_pos_of_nontrivial h
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  exact pow_le_pow_left₀ hr.le (RvMBridge19.zeroRadius_le h) _

/-- E6Bridge18: off the unit ordinate window about `Im s` the double-pole term is at most
    `m(rho) (1 / (Im rho - Im s)^2)` (the hand proof's `hd : (Im rho - Im s)^2 <= |s - rho|^2`). -/
theorem polTerm_shape {s ρ : ℂ} (hfar : (1 : ℝ) ≤ |ρ.im - s.im|) :
    ‖RvMBridge18.polTerm s ρ‖ ≤ (WeilExplicit.zeroMult ρ : ℝ) * (1 / (ρ.im - s.im) ^ 2) := by
  rw [RvMBridge18.norm_polTerm, ← mul_one_div]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have hd1 : 1 ≤ (ρ.im - s.im) ^ 2 := by
    have := sq_abs (ρ.im - s.im)
    nlinarith [abs_nonneg (ρ.im - s.im)]
  have hd : (ρ.im - s.im) ^ 2 ≤ ‖s - ρ‖ ^ 2 := by
    have := Complex.abs_im_le_norm (s - ρ)
    rw [Complex.sub_im] at this
    have h2 : |s.im - ρ.im| ^ 2 = (s.im - ρ.im) ^ 2 := sq_abs _
    nlinarith [abs_nonneg (s.im - ρ.im)]
  exact one_div_le_one_div_of_le (by linarith) hd

/-- E6Bridge15: off the unit window the paired Li term is at most `m(rho) (2^n (1 / normSq rho))`
    (abs_re_liKernel_le, the binomial expansion with the `j = 1` pairing). -/
theorem liPaired_shape (n : ℕ) {ρ : ℂ} (h : IsNontrivialZero ρ) (him : (1 : ℝ) ≤ |ρ.im|) :
    ‖RvMBridge15.liPaired n ρ‖ ≤ (WeilExplicit.zeroMult ρ : ℝ) * (2 ^ n * (1 / Complex.normSq ρ)) := by
  rw [RvMBridge15.norm_liPaired]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have hρ : 1 ≤ ‖ρ‖ := him.trans (Complex.abs_im_le_norm ρ)
  rw [mul_one_div]
  exact RvMBridge15.abs_re_liKernel_le h.2.1 h.2.2 hρ

end DogfoodZeroSumMajorant.Glue

/-! ## Kernel cross-checks against the hand-written originals (generator-appended).  Each
    `example` is closed by applying one side to the other's statement, so a drift in either
    statement fails to elaborate. -/

section CrossChecks
open Zeta23 DogfoodZeroSumMajorant

/-- The 9/4 strip certificate proves the prelude's hand-proved `RvMBridgeXi.inv_normSq_le_majorant`
    statement (the inequality E6Bridge19's `zbound` and E6Bridge15's `liBound` close with) ... -/
example {ρ : ℂ} (h : IsNontrivialZero ρ) (him : (1 : ℝ) ≤ |ρ.im|) :
    1 / Complex.normSq ρ ≤ (9 / 4) / (1 + Complex.normSq (gammaOf ρ)) :=
  zbound_regen_strip h him

/-- ... and the hand-proved lemma proves the regenerated statement: the two are interchangeable. -/
example {ρ : ℂ} (h : IsNontrivialZero ρ) (him : (1 : ℝ) ≤ |ρ.im|) :
    1 / Complex.normSq ρ ≤ (9 / 4) / (1 + Complex.normSq (gammaOf ρ)) :=
  RvMBridgeXi.inv_normSq_le_majorant h him

/-- E6Bridge19 `norm_zterm_le_zbound`, VERBATIM: with `K := (k+1)! 2^(k+2)` the emitted constant
    `K * (9/4)` is `zbound`'s constant on the nose, and `zeroBoundAt 0 1` is `zeroBound`. -/
example (k : ℕ) (ρ : ℂ) {s : ℂ} (hs : s ∈ Metric.ball (0 : ℂ) (RvMBridge19.zeroRadius / 2)) :
    ‖RvMBridge19.zterm k ρ s‖ ≤ RvMBridge19.zbound k ρ := by
  unfold RvMBridge19.zbound
  rw [RvMBridgeXi.zeroBound_eq]
  exact zbound_regen_le (f := fun ρ => RvMBridge19.zterm k ρ s)
    (K := ((k + 1).factorial : ℝ) * 2 ^ (k + 2)) (by positivity)
    (fun _ h => RvMBridge19.zterm_eq_zero_of_not_nontrivial h s)
    (fun _ h _ => Glue.zterm_window k hs h)
    (fun _ h him => Glue.zterm_shape k hs h him) ρ

/-- The original proves the same statement. -/
example (k : ℕ) (ρ : ℂ) {s : ℂ} (hs : s ∈ Metric.ball (0 : ℂ) (RvMBridge19.zeroRadius / 2)) :
    ‖RvMBridge19.zterm k ρ s‖ ≤ RvMBridge19.zbound k ρ :=
  RvMBridge19.norm_zterm_le_zbound k ρ hs

/-- The k-th Taylor terms are summable on the ball (the family `iteratedDeriv_tsum_ball` sums). -/
example (k : ℕ) {s : ℂ} (hs : s ∈ Metric.ball (0 : ℂ) (RvMBridge19.zeroRadius / 2)) :
    Summable (fun ρ => RvMBridge19.zterm k ρ s) :=
  zbound_regen_summable (K := ((k + 1).factorial : ℝ) * 2 ^ (k + 2)) (by positivity)
    (fun _ h => RvMBridge19.zterm_eq_zero_of_not_nontrivial h s)
    (fun _ h him => Glue.zterm_shape k hs h him)

/-- E6Bridge18 `norm_polTerm_le_majorant`: the regenerated ordinate strip plus the glue. -/
example {s ρ : ℂ} (h : IsNontrivialZero ρ) (hfar : 1 ≤ |ρ.im - s.im|) :
    ‖RvMBridge18.polTerm s ρ‖ ≤ (WeilExplicit.zeroMult ρ : ℝ)
      * ((13 / 4 + 2 * s.im ^ 2) / (1 + Complex.normSq (gammaOf ρ))) :=
  (Glue.polTerm_shape hfar).trans
    (mul_le_mul_of_nonneg_left (polBound_regen_strip s h hfar) (Nat.cast_nonneg _))

/-- The original proves the same statement. -/
example {s ρ : ℂ} (h : IsNontrivialZero ρ) (hfar : 1 ≤ |ρ.im - s.im|) :
    ‖RvMBridge18.polTerm s ρ‖ ≤ (WeilExplicit.zeroMult ρ : ℝ)
      * ((13 / 4 + 2 * s.im ^ 2) / (1 + Complex.normSq (gammaOf ρ))) :=
  RvMBridge18.norm_polTerm_le_majorant h hfar

/-- E6Bridge18 `norm_polTerm_le`, VERBATIM: `polBound s` IS `zeroBoundAt (Im s) 1 (13/4 + 2 (Im s)^2)`
    with the window bound `norm (polTerm s)`, definitionally. -/
example (s ρ : ℂ) : ‖RvMBridge18.polTerm s ρ‖ ≤ RvMBridge18.polBound s ρ :=
  polBound_regen_le s (b := fun ρ => ‖RvMBridge18.polTerm s ρ‖)
    (fun _ h => RvMBridge18.polTerm_eq_zero_of_not_nontrivial h) (fun _ _ _ => le_rfl)
    (fun _ _ hfar => Glue.polTerm_shape hfar) ρ

/-- E6Bridge18 `summable_polTerm`, VERBATIM. -/
example (s : ℂ) : Summable (RvMBridge18.polTerm s) :=
  polBound_regen_summable s (fun _ h => RvMBridge18.polTerm_eq_zero_of_not_nontrivial h)
    (fun _ _ hfar => Glue.polTerm_shape hfar)

/-- E6Bridge15 `norm_liPaired_le`, VERBATIM: with `K := 2^n` the regenerated majorant equals
    `liBound n` (`liC n = (9/4) 2^n`; `zeroBoundAt 0 1` is the small-zero window). -/
example (n : ℕ) (ρ : ℂ) : ‖RvMBridge15.liPaired n ρ‖ ≤ RvMBridge15.liBound n ρ := by
  have hle := liBound_regen_le (f := RvMBridge15.liPaired n)
    (b := fun ρ => ‖RvMBridge15.liPaired n ρ‖) (K := 2 ^ n) (by positivity)
    (fun _ h => RvMBridge15.liPaired_eq_zero_of_not_nontrivial h) (fun _ _ _ => le_rfl)
    (fun _ h him => Glue.liPaired_shape n h him) ρ
  have heq : RvMBridgeXi.zeroBoundAt 0 1 (2 ^ n * (9 / 4)) (fun ρ => ‖RvMBridge15.liPaired n ρ‖) ρ
      = RvMBridge15.liBound n ρ := by
    simp only [RvMBridgeXi.zeroBoundAt, RvMBridge15.liBound, RvMBridge15.liC,
      RvMBridgeXi.windowZeros, sub_zero]
    ring
  exact hle.trans heq.le

/-- E6Bridge15 `summable_liPaired`, VERBATIM. -/
example (n : ℕ) : Summable (RvMBridge15.liPaired n) :=
  liBound_regen_summable (K := 2 ^ n) (by positivity)
    (fun _ h => RvMBridge15.liPaired_eq_zero_of_not_nontrivial h)
    (fun _ h him => Glue.liPaired_shape n h him)

/-- The regenerated envelope (symbolic `E`) and the prelude's `norm_tsum_subtype_le_mul_tsum` prove
    each other's statement ... -/
example {ι : Type*} {f : ι → ℂ} {w : ι → ℝ} (S : Set ι) {E : ℝ} (hE : 0 ≤ E)
    (hw : Summable w) (hw0 : ∀ x, 0 ≤ w x) (hle : ∀ x : S, ‖f x‖ ≤ E * w x) :
    ‖∑' x : S, f x‖ ≤ E * ∑' x : ι, w x :=
  RvMBridgeGauss.norm_tsum_subtype_le_mul_tsum S hE hw hw0 hle

example {ι : Type*} {f : ι → ℂ} {w : ι → ℝ} (S : Set ι) {E : ℝ} (hE : 0 ≤ E)
    (hw : Summable w) (hw0 : ∀ x, 0 ≤ w x) (hle : ∀ x : S, ‖f x‖ ≤ E * w x) :
    ‖∑' x : S, f x‖ ≤ E * ∑' x : ι, w x :=
  tail_regen_envelope S hE hw hw0 hle

/-- ... and the regenerated envelope re-derives E6Bridge12's `tail_bound_window` line for line
    (E6Bridge12.lean:271-281 with the envelope swapped in). -/
example {c D : ℝ} (hD : 0 ≤ D) {lam : ℝ} (hlam : 1 ≤ lam) :
    ‖∑' ρ : ↥(RvMBridgeGauss.winSet c D)ᶜ, RvMBridge7.term c lam ρ‖
      ≤ Real.exp (2 * (lam - 1) * (1 / 4 - D ^ 2)) * RvMBridge7.constB c := by
  rw [← RvMBridge12.tsum_tailWeight c]
  refine tail_regen_envelope (RvMBridgeGauss.winSet c D)ᶜ (Real.exp_pos _).le
    (RvMBridge12.summable_tailWeight c) (RvMBridge12.tailWeight_nonneg c) fun ρ => ?_
  have hfar : D < |(ρ : ℂ).im - c| := by
    have h := ρ.2
    simp only [RvMBridgeGauss.winSet, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at h
    exact h
  exact RvMBridge12.norm_term_le_tail hD hlam hfar

/-- The original proves the same statement. -/
example {c D : ℝ} (hD : 0 ≤ D) {lam : ℝ} (hlam : 1 ≤ lam) :
    ‖∑' ρ : ↥(RvMBridgeGauss.winSet c D)ᶜ, RvMBridge7.term c lam ρ‖
      ≤ Real.exp (2 * (lam - 1) * (1 / 4 - D ^ 2)) * RvMBridge7.constB c :=
  RvMBridge12.tail_bound_window hD hlam

/-- The rate face's first conjunct is the prelude companion `exp_two_mul_le_of_le` at `P = -1/4`;
    the second is what `P < 0` buys (the envelope factor is at most 1). -/
example {lam φ : ℝ} (hlam : 1 ≤ lam) (hφ : φ ≤ -(1 / 4)) :
    Real.exp (2 * lam * φ) ≤ Real.exp (2 * (lam - 1) * (-(1 / 4))) * Real.exp (2 * φ) :=
  (tail_regen_rate hlam hφ).1

example {lam φ : ℝ} (hlam : 1 ≤ lam) (hφ : φ ≤ -(1 / 4)) :
    Real.exp (2 * lam * φ) ≤ Real.exp (2 * (lam - 1) * (-(1 / 4))) * Real.exp (2 * φ) :=
  RvMBridgeGauss.exp_two_mul_le_of_le hlam hφ

end CrossChecks

#print axioms DogfoodZeroSumMajorant.zbound_regen_strip
#print axioms DogfoodZeroSumMajorant.zbound_regen_le
#print axioms DogfoodZeroSumMajorant.zbound_regen_summable
#print axioms DogfoodZeroSumMajorant.polBound_regen_strip
#print axioms DogfoodZeroSumMajorant.polBound_regen_le
#print axioms DogfoodZeroSumMajorant.polBound_regen_summable
#print axioms DogfoodZeroSumMajorant.liBound_regen_strip
#print axioms DogfoodZeroSumMajorant.liBound_regen_le
#print axioms DogfoodZeroSumMajorant.liBound_regen_summable
#print axioms DogfoodZeroSumMajorant.tail_regen_envelope
#print axioms DogfoodZeroSumMajorant.tail_regen_rate
#print axioms DogfoodZeroSumMajorant.Glue.zterm_shape
#print axioms DogfoodZeroSumMajorant.Glue.zterm_window
#print axioms DogfoodZeroSumMajorant.Glue.polTerm_shape
#print axioms DogfoodZeroSumMajorant.Glue.liPaired_shape
