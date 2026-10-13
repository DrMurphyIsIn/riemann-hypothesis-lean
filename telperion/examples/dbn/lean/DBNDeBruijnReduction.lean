/-
  DBNDeBruijnReduction -- Route C / C3 (de Bruijn's heat-flow theorem, t ≥ 1/2) REDUCED to its two
  open inputs, assembled from the Hadamard-independent groundwork of `DBNStep` (L4),
  `DBNHurwitz` (L2e) and `DBNHeatApprox` (L2a-d), following the route of
  telperion/docs/DESIGN_RH_dbn_debruijn_real_zeros_2026-09-22.md section 2.

  The two inputs are carried as NAMED Prop OBLIGATIONS.  Neither is proved on this island:

    * `H0ZeroFreeOffStrip` -- `H_0` has no zero with `(Im z)² > 1`.  This is the contrapositive
      of the registry lemma node `RH.dbn_H0_zero_strip` (obligation L1 of the memo: termwise
      Gamma integrals on the absolutely convergent half-plane plus the Euler product).  It is
      written in contrapositive form deliberately, so that no text in this module coincides with
      a registry statement.
    * `ApproxHadamard` -- every approximant `Gδ δ k` with `δ > 0` carries abstract even Hadamard
      data (`DBNStep.EvenHadamardData`).  This is obligation L3 of the memo (Hadamard
      factorisation of even real entire functions of order `< 2`; the approximants have order 1
      by `DBNHeatApprox.norm_Gδ_le`).  Mathlib at the pin has no Hadamard factorisation.

  GIVEN both obligations, this module proves:

    * `G_zero_im_sq_le_of_obligations`: for `t ≥ 0` and `N ≥ 1` every zero of the approximant
      `G t N` satisfies `(Im z)² ≤ max (1 − 2t) 0` (the step lemma iterated `N` times with
      `δ² = 2t/N`, starting from the strip `(Im z)² ≤ 1` of `G t N` at `N = 0`, i.e. of `H 0`);
    * `H_zero_im_sq_le_of_obligations`: the same strip for `H t` itself, `t ≥ 0` (Hurwitz);
    * `H_ne_zero_of_obligations`: for `t ≥ 1/2`, `H t` has no zero off the real axis.

  These are CONDITIONAL theorems.  The registry node `RH.dbn_debruijn_real_zeros` is NOT stated
  here and is NOT proved: it follows only when both obligations become island theorems.  Nothing
  here says anything about the zeros of `H_0` inside the strip (which is where RH lives), and
  nothing here bounds the de Bruijn-Newman constant (which is not even defined on the island).
  Nothing here proves RH.  conjecture1_proved = False.
-/
import DBNHeatApprox

open Set Filter Topology ComplexConjugate

namespace DBN

/-- **Obligation L1 (NOT proved here)**: `H_0` has no zero with `(Im z)² > 1`; the contrapositive
of the registry lemma node `RH.dbn_H0_zero_strip`. -/
def H0ZeroFreeOffStrip : Prop := ∀ z : ℂ, 1 < z.im ^ 2 → H 0 z ≠ 0

/-- **Obligation L3 (NOT proved here)**: every de Bruijn approximant `Gδ δ k` with `δ > 0` carries
abstract even Hadamard data. -/
def ApproxHadamard : Prop := ∀ δ : ℝ, 0 < δ → ∀ k : ℕ, Nonempty (EvenHadamardData (Gδ δ k))

/-- With `δ = 0` the kernel weight is trivial: `Gδ 0 N = H 0`. -/
theorem Gδ_zero_delta (N : ℕ) : Gδ 0 N = H 0 := by
  funext z
  unfold Gδ H GδIntegrand HIntegrand
  congr 1
  funext u
  simp

/-- **Strip contraction for the approximants, GIVEN L1 and L3**: for `t ≥ 0` and `N ≥ 1`, every
zero of `G t N` satisfies `(Im z)² ≤ max (1 − 2t) 0`. -/
theorem G_zero_im_sq_le_of_obligations (hstrip : H0ZeroFreeOffStrip) (hHad : ApproxHadamard)
    {t : ℝ} (ht : 0 ≤ t) {N : ℕ} (hN : 1 ≤ N) {z : ℂ} (hz : G t N z = 0) :
    z.im ^ 2 ≤ max (1 - 2 * t) 0 := by
  have h0 : ∀ w : ℂ, H 0 w = 0 → w.im ^ 2 ≤ 1 := by
    intro w hw
    by_contra hlt
    push Not at hlt
    exact hstrip w hlt hw
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · -- `t = 0`: the approximant is `H 0` itself
    subst ht0
    have hz' : H 0 z = 0 := by
      have hG : G 0 N = H 0 := by
        unfold G
        rw [show (2 * (0 : ℝ) / N) = 0 by simp, Real.sqrt_zero, Gδ_zero_delta]
      rw [← hG]
      exact hz
    rw [mul_zero, sub_zero, max_eq_left zero_le_one]
    exact h0 z hz'
  · -- `t > 0`: iterate the step lemma `N` times with `δ = √(2t/N)`
    set δ : ℝ := Real.sqrt (2 * t / N) with hδ_def
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hδ : 0 < δ := Real.sqrt_pos.mpr (by positivity)
    have hδsq : (N : ℝ) * δ ^ 2 = 2 * t := by
      rw [hδ_def, Real.sq_sqrt (by positivity)]
      field_simp
    have hF0 : ∀ w : ℂ, Gδ δ 0 w = 0 → w.im ^ 2 ≤ 1 := by
      intro w hw
      rw [Gδ_zero] at hw
      exact h0 w hw
    have hiter := zero_im_sq_le_of_shiftAvg_iterate (F := Gδ δ) hδ (fun k ↦ Gδ_succ δ k)
      (hHad δ hδ) (fun k w ↦ Gδ_conj δ k w) hF0 N z hz
    rwa [hδsq] at hiter

/-- **Strip contraction for the heat flow, GIVEN L1 and L3** (Polymath15 section 1 shape): for
`t ≥ 0`, every zero of `H t` satisfies `(Im z)² ≤ max (1 − 2t) 0`.  Hurwitz closure of
`G_zero_im_sq_le_of_obligations` on the open set `{w | max (1 − 2t) 0 < (Im w)²}`. -/
theorem H_zero_im_sq_le_of_obligations (hstrip : H0ZeroFreeOffStrip) (hHad : ApproxHadamard)
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : H t z = 0) : z.im ^ 2 ≤ max (1 - 2 * t) 0 := by
  by_contra hlt
  push Not at hlt
  have hU : IsOpen {w : ℂ | max (1 - 2 * t) 0 < w.im ^ 2} :=
    isOpen_lt continuous_const (Complex.continuous_im.pow 2)
  refine H_ne_zero_of_approx_on ht hU ?_ hlt hz
  filter_upwards [eventually_ge_atTop 1] with N hN w hw hGw
  exact absurd (G_zero_im_sq_le_of_obligations hstrip hHad ht hN hGw) (not_le.mpr hw)

/-- **De Bruijn's `t ≥ 1/2` conclusion, CONDITIONAL on L1 and L3**: for `t ≥ 1/2`, `H t` has no
zero off the real axis.  NOT the registry node (which is unconditional); it becomes the registry
node only when `H0ZeroFreeOffStrip` and `ApproxHadamard` are island theorems. -/
theorem H_ne_zero_of_obligations (hstrip : H0ZeroFreeOffStrip) (hHad : ApproxHadamard)
    {t : ℝ} (ht : 1 / 2 ≤ t) {z : ℂ} (hz : z.im ≠ 0) : H t z ≠ 0 := by
  intro hH
  have h := H_zero_im_sq_le_of_obligations hstrip hHad (by linarith) hH
  rw [max_eq_right (by linarith)] at h
  exact hz ((pow_eq_zero_iff two_ne_zero).mp (le_antisymm h (sq_nonneg _)))

end DBN
