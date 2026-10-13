/-
  DBNM4LocalStep -- lane m4 (Route C milestone M4): the LOCAL discrete de Bruijn step and the
  abstract discrete barrier induction.  Pure complex analysis over `DBNStep` (imports only
  Mathlib and `DBNStep`; mentions neither `Φ` nor `H_t`).

  * `m4_shiftAvg_ne_zero_local` (local step lemma).  Let `f` be real
    (`f (conj z) = conj (f z)`) with even Hadamard data (`DBNStep.EvenHadamardData`), `δ > 0`
    and `Im w > 0`.  If EVERY zero `ζ` of `f` satisfies
      `(Im ζ)² < (Re w − Re ζ)² + (Im w)² + δ²`,
    then `T_δ f (w) ≠ 0` (`T_δ = DBN.shiftAvg δ`).  This is `DBNStep.norm_lt_norm` with the
    uniform strip hypothesis `(Im ζ)² ≤ Δ2 < (Im w)² + δ²` replaced by the pointwise condition
    above: the conjugate-pair parabola gives the difference of squares
    `8 y δ (y² + δ² + a² − q²)` with `a = Re w − Re ζ`, so the `a²` term, which the global step
    lemma throws away, is kept.  It is what lets a zero FAR from `w` horizontally sit HIGHER
    than `w` without spoiling the step.

  * `m4_barrier_induction` (abstract discrete barrier).  Iterating the local step along
    `F (k+1) = T_δ (F k)`: if `F 0` has no zero in `{|Re| ≤ X, |Im| ≥ Y 0}`, every `F n` has no
    zero in the barrier strip `{X < |Re| ≤ X + W, |Im| ≥ Y n}`, every zero of `F n` has
    `(Im)² ≤ W² + (Y n)²`, and `(Y n)² = (Y (n+1))² + δ²`, then every `F n` (`n ≤ N`) has no
    zero in `{|Re| ≤ X, |Im| ≥ Y n}`.  This is the discrete replacement for the continuous zero
    dynamics (Polymath15 Prop 3.1: implicit function theorem, Hermite expansion at repeated
    zeros, Rouche, minimal bad time) in the proof of Polymath15 Prop 3.3; it needs no zero
    tracking and no multiplicity case split.

  * `m4_compact_margin` (general topology): a function nonvanishing on the part `{φ ≤ 0}` of a
    compact set is bounded below by some `ε > 0` on the larger part `{φ ≤ η}` for some `η > 0`.

  Nothing here proves RH.  conjecture1_proved = False.
-/
import DBNStep

open Complex ComplexConjugate Filter Topology Set

namespace DBN

/-! ### The local step lemma -/

/-- **One conjugate pair grows under the upward shift, local form.**  For `y = Im w > 0`, `δ > 0`
and `(Im σ)² < (Re w − Re σ)² + y² + δ²`, the pair modulus `‖z − σ‖ ‖z − conj σ‖` is strictly
larger at `w + iδ` than at `w − iδ`. -/
lemma m4_pair_lt_local {w σ : ℂ} {δ : ℝ} (hy : 0 < w.im) (hδ : 0 < δ)
    (hσ : σ.im ^ 2 < (w.re - σ.re) ^ 2 + w.im ^ 2 + δ ^ 2) :
    ‖(w - I * δ) - σ‖ * ‖(w - I * δ) - conj σ‖ < ‖(w + I * δ) - σ‖ * ‖(w + I * δ) - conj σ‖ := by
  apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
  rw [sq_norm_sub_mul_norm_sub_conj, sq_norm_sub_mul_norm_sub_conj]
  have hre1 : (w - I * δ).re = w.re := by simp
  have hre2 : (w + I * δ).re = w.re := by simp
  have him1 : (w - I * δ).im = w.im - δ := by simp
  have him2 : (w + I * δ).im = w.im + δ := by simp
  rw [hre1, hre2, him1, him2]
  set a := w.re - σ.re
  set q := σ.im
  set y := w.im
  have key : (a ^ 2 + (y + δ) ^ 2 + q ^ 2) ^ 2 - 4 * (y + δ) ^ 2 * q ^ 2
      - ((a ^ 2 + (y - δ) ^ 2 + q ^ 2) ^ 2 - 4 * (y - δ) ^ 2 * q ^ 2)
      = 8 * y * δ * (y ^ 2 + δ ^ 2 + a ^ 2 - q ^ 2) := by ring
  have hpos : 0 < 8 * y * δ * (y ^ 2 + δ ^ 2 + a ^ 2 - q ^ 2) := by
    have h1 : 0 < y ^ 2 + δ ^ 2 + a ^ 2 - q ^ 2 := by linarith
    positivity
  linarith

/-- **Each nontrivial factor grows strictly, local form**: the pointwise condition is imposed on
the two zeros `± τ⁻¹` of the factor `1 − z²τ²`. -/
lemma m4_hadQ_lt_local {τ w : ℂ} {δ : ℝ} (hτ : τ ≠ 0) (hy : 0 < w.im) (hδ : 0 < δ)
    (h1 : (τ⁻¹).im ^ 2 < (w.re - (τ⁻¹).re) ^ 2 + w.im ^ 2 + δ ^ 2)
    (h2 : (-τ⁻¹).im ^ 2 < (w.re - (-τ⁻¹).re) ^ 2 + w.im ^ 2 + δ ^ 2) :
    hadQ τ (w - I * δ) < hadQ τ (w + I * δ) := by
  rw [hadQ_eq hτ, hadQ_eq hτ]
  have hp1 := m4_pair_lt_local (σ := τ⁻¹) hy hδ h1
  have hp2 := m4_pair_lt_local (σ := -τ⁻¹) hy hδ h2
  have hτ4 : 0 < ‖τ‖ ^ 4 := by positivity
  exact mul_lt_mul_of_pos_left (mul_lt_mul'' hp1 hp2 (by positivity) (by positivity)) hτ4

namespace EvenHadamardData

variable {f : ℂ → ℂ} (D : EvenHadamardData f)
include D

/-- **The main inequality, local form.**  For real `f` with even Hadamard data, not constant
(`m ≠ 0` or some `τ k ≠ 0`), `Im w > 0`, `f(w − iδ) ≠ 0`, and every zero `ζ` of `f` satisfying
`(Im ζ)² < (Re w − Re ζ)² + (Im w)² + δ²`: `‖f(w − iδ)‖ < ‖f(w + iδ)‖`. -/
theorem m4_norm_lt_norm_local (hreal : ∀ z, f (conj z) = conj (f z)) {δ : ℝ} (hδ : 0 < δ)
    {w : ℂ} (hy : 0 < w.im)
    (hloc : ∀ ζ, f ζ = 0 → ζ.im ^ 2 < (w.re - ζ.re) ^ 2 + w.im ^ 2 + δ ^ 2)
    (hne : f (w - I * δ) ≠ 0) (hnd : D.m ≠ 0 ∨ ∃ k, D.τ k ≠ 0) :
    ‖f (w - I * δ)‖ < ‖f (w + I * δ)‖ := by
  set zm := w - I * δ with hzm
  set zp := w + I * δ with hzp
  -- the squared-modulus partial products at `zp` (A) and `zm` (B)
  set X : ℝ := ‖D.c‖ ^ 2 * ‖zp‖ ^ (4 * D.m) with hX
  set Y : ℝ := ‖D.c‖ ^ 2 * ‖zm‖ ^ (4 * D.m) with hY
  set A : ℕ → ℝ := fun n ↦ X * ∏ k ∈ Finset.range n, hadQ (D.τ k) zp with hA
  set B : ℕ → ℝ := fun n ↦ Y * ∏ k ∈ Finset.range n, hadQ (D.τ k) zm with hB
  have hAlim : Tendsto A atTop (𝓝 (‖f zp‖ ^ 2)) := D.tendsto_sq_norm hreal zp
  have hBlim : Tendsto B atTop (𝓝 (‖f zm‖ ^ 2)) := D.tendsto_sq_norm hreal zm
  have hfm : 0 < ‖f zm‖ ^ 2 := by positivity
  have hBne : ∀ n, B n ≠ 0 := prod_ne_zero_of_tendsto hBlim hfm.ne'
  -- consequences of `B n ≠ 0`
  have hY0 : Y ≠ 0 := by
    have := hBne 0
    simpa [hB] using this
  have hQm : ∀ k, 0 < hadQ (D.τ k) zm := by
    intro k
    refine lt_of_le_of_ne (hadQ_nonneg _ _) (Ne.symm fun h0 ↦ hBne (k + 1) ?_)
    simp only [hB, Finset.prod_range_succ, h0, mul_zero]
  -- each factor grows (weakly), nontrivial ones strictly: the local condition at `± τ⁻¹`
  have hQlt : ∀ k, D.τ k ≠ 0 → hadQ (D.τ k) zm < hadQ (D.τ k) zp := by
    intro k hk
    have hz1 : f (D.τ k)⁻¹ = 0 := D.apply_inv_eq_zero hk
    have hz2 : f (-(D.τ k)⁻¹) = 0 := by rw [D.even]; exact hz1
    exact m4_hadQ_lt_local hk hy hδ (hloc _ hz1) (hloc _ hz2)
  have hQle : ∀ k, hadQ (D.τ k) zm ≤ hadQ (D.τ k) zp := by
    intro k
    by_cases hk : D.τ k = 0
    · rw [hk, hadQ_zero, hadQ_zero]
    · exact (hQlt k hk).le
  -- the ratio sequence
  set r : ℕ → ℝ := fun n ↦ A n / B n with hr
  have hr_succ : ∀ n, r (n + 1) = r n * (hadQ (D.τ n) zp / hadQ (D.τ n) zm) := by
    intro n
    simp only [hr, hA, hB, Finset.prod_range_succ]
    rw [← mul_assoc, ← mul_assoc, mul_div_mul_comm]
  have hratio_ge : ∀ n, 1 ≤ hadQ (D.τ n) zp / hadQ (D.τ n) zm := fun n ↦
    (one_le_div (hQm n)).mpr (hQle n)
  have hr0 : 1 ≤ r 0 := by
    have hYpos : 0 < Y := lt_of_le_of_ne (by positivity) (Ne.symm hY0)
    simp only [hr, hA, hB, Finset.range_zero, Finset.prod_empty, mul_one]
    rw [one_le_div hYpos]
    have hn : ‖zm‖ ≤ ‖zp‖ := (norm_sub_lt_norm_add hy hδ).le
    have := pow_le_pow_left₀ (norm_nonneg zm) hn (4 * D.m)
    simp only [hX, hY]
    gcongr
  have hr_pos : ∀ n, 0 < r n := by
    intro n
    induction n with
    | zero => linarith
    | succ n ih =>
      rw [hr_succ]
      exact mul_pos ih (lt_of_lt_of_le one_pos (hratio_ge n))
  have hmono : Monotone r := by
    refine monotone_nat_of_le_succ fun n ↦ ?_
    rw [hr_succ]
    exact le_mul_of_one_le_right (hr_pos n).le (hratio_ge n)
  have hrlim : Tendsto r atTop (𝓝 (‖f zp‖ ^ 2 / ‖f zm‖ ^ 2)) := hAlim.div hBlim hfm.ne'
  have hle_lim : ∀ n, r n ≤ ‖f zp‖ ^ 2 / ‖f zm‖ ^ 2 := fun n ↦ hmono.ge_of_tendsto hrlim n
  -- some term of the ratio sequence is strictly above `1`
  have hstrict : ∃ n, 1 < r n := by
    rcases hnd with hm | ⟨k, hk⟩
    · refine ⟨0, ?_⟩
      have hYpos : 0 < Y := lt_of_le_of_ne (by positivity) (Ne.symm hY0)
      simp only [hr, hA, hB, Finset.range_zero, Finset.prod_empty, mul_one]
      rw [one_lt_div hYpos]
      have hc : 0 < ‖D.c‖ ^ 2 := by
        rcases eq_or_ne ‖D.c‖ 0 with h | h
        · exfalso; apply hY0; simp [hY, h]
        · positivity
      have hn := norm_sub_lt_norm_add hy hδ
      have h4 : ‖zm‖ ^ (4 * D.m) < ‖zp‖ ^ (4 * D.m) :=
        pow_lt_pow_left₀ hn (norm_nonneg _) (by omega)
      simp only [hX, hY]
      exact mul_lt_mul_of_pos_left h4 hc
    · refine ⟨k + 1, ?_⟩
      rw [hr_succ]
      have h1 : 1 ≤ r k := le_trans hr0 (hmono (Nat.zero_le k))
      have h2 : 1 < hadQ (D.τ k) zp / hadQ (D.τ k) zm :=
        (one_lt_div (hQm k)).mpr (hQlt k hk)
      nlinarith
  obtain ⟨n, hn⟩ := hstrict
  have hlim1 : 1 < ‖f zp‖ ^ 2 / ‖f zm‖ ^ 2 := lt_of_lt_of_le hn (hle_lim n)
  rw [one_lt_div hfm] at hlim1
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hlim1

/-- **The local discrete de Bruijn step.**  If `f` is real with even Hadamard data, `δ > 0`,
`Im w > 0`, and every zero `ζ` of `f` satisfies `(Im ζ)² < (Re w − Re ζ)² + (Im w)² + δ²`, then
`T_δ f (w) = shiftAvg δ f w ≠ 0`. -/
theorem m4_shiftAvg_ne_zero_local (hreal : ∀ z, f (conj z) = conj (f z)) {δ : ℝ} (hδ : 0 < δ)
    {w : ℂ} (hy : 0 < w.im)
    (hloc : ∀ ζ, f ζ = 0 → ζ.im ^ 2 < (w.re - ζ.re) ^ 2 + w.im ^ 2 + δ ^ 2) :
    shiftAvg δ f w ≠ 0 := by
  intro hsum
  unfold shiftAvg at hsum
  have hsum' : f (w + I * δ) = -f (w - I * δ) := by linear_combination (2 : ℂ) * hsum
  by_cases hm : f (w - I * δ) = 0
  · -- then `w + iδ` would be a zero of `f` directly above `w`, violating the local condition
    have hp : f (w + I * δ) = 0 := by rw [hsum', hm, neg_zero]
    have hz := hloc _ hp
    have hre : (w + I * δ).re = w.re := by simp
    have him : (w + I * δ).im = w.im + δ := by simp
    rw [hre, him, sub_self] at hz
    nlinarith [mul_pos hy hδ]
  · by_cases hdeg : D.m = 0 ∧ ∀ k, D.τ k = 0
    · have hc1 := D.eq_const hdeg.1 hdeg.2 (w + I * δ)
      have hc2 := D.eq_const hdeg.1 hdeg.2 (w - I * δ)
      rw [hc1, hc2] at hsum'
      apply hm
      rw [hc2]
      linear_combination hsum' / 2
    · have hnd : D.m ≠ 0 ∨ ∃ k, D.τ k ≠ 0 := by
        by_contra h
        push Not at h
        exact hdeg ⟨h.1, h.2⟩
      have hlt' := D.m4_norm_lt_norm_local hreal hδ hy hloc hm hnd
      rw [hsum', norm_neg] at hlt'
      exact lt_irrefl _ hlt'

end EvenHadamardData

/-! ### Symmetry of the zero set of an even real function -/

/-- For `f` even and real, a zero `z` gives the zero `|Re z| + i |Im z|` (first quadrant). -/
lemma m4_zero_abs_of_zero {f : ℂ → ℂ} (heven : ∀ z, f (-z) = f z)
    (hreal : ∀ z, f (conj z) = conj (f z)) {z : ℂ} (hz : f z = 0) :
    f (((|z.re| : ℝ) : ℂ) + ((|z.im| : ℝ) : ℂ) * I) = 0 := by
  have hconj : f (conj z) = 0 := by rw [hreal, hz, map_zero]
  rcases le_or_gt 0 z.re with hre | hre <;> rcases le_or_gt 0 z.im with him | him
  · have e : ((|z.re| : ℝ) : ℂ) + ((|z.im| : ℝ) : ℂ) * I = z := by
      apply Complex.ext <;> simp [abs_of_nonneg hre, abs_of_nonneg him]
    rw [e]; exact hz
  · have e : ((|z.re| : ℝ) : ℂ) + ((|z.im| : ℝ) : ℂ) * I = conj z := by
      apply Complex.ext <;> simp [abs_of_nonneg hre, abs_of_neg him]
    rw [e]; exact hconj
  · have e : ((|z.re| : ℝ) : ℂ) + ((|z.im| : ℝ) : ℂ) * I = -conj z := by
      apply Complex.ext <;> simp [abs_of_neg hre, abs_of_nonneg him]
    rw [e, heven]; exact hconj
  · have e : ((|z.re| : ℝ) : ℂ) + ((|z.im| : ℝ) : ℂ) * I = -z := by
      apply Complex.ext <;> simp [abs_of_neg hre, abs_of_neg him]
    rw [e, heven]; exact hz

/-! ### The abstract discrete barrier induction -/

/-- **Discrete barrier induction.**  Let `F (k+1) = T_δ (F k)` with `δ > 0`, every `F k` real
with even Hadamard data, and let `Y : ℕ → ℝ` be a positive barrier curve with
`(Y n)² = (Y (n+1))² + δ²` for `n < N`.  Suppose

* `F 0` has no zero with `|Re| ≤ X`, `|Im| ≥ Y 0`;
* for `n < N`, `F n` has no zero in the barrier strip `X < |Re| ≤ X + W`, `|Im| ≥ Y n`;
* for `n < N`, every zero of `F n` has `(Im)² ≤ W² + (Y n)²`.

Then for every `n ≤ N`, `F n` has no zero with `|Re| ≤ X`, `|Im| ≥ Y n`. -/
theorem m4_barrier_induction {F : ℕ → ℂ → ℂ} {δ X W : ℝ} {Y : ℕ → ℝ} {N : ℕ} (hδ : 0 < δ)
    (hW : 0 ≤ W) (hsucc : ∀ k, F (k + 1) = shiftAvg δ (F k))
    (hdata : ∀ k, Nonempty (EvenHadamardData (F k)))
    (hreal : ∀ k z, F k (conj z) = conj (F k z))
    (hYpos : ∀ n ≤ N, 0 < Y n) (hYstep : ∀ n < N, Y n ^ 2 = Y (n + 1) ^ 2 + δ ^ 2)
    (h0 : ∀ z : ℂ, |z.re| ≤ X → Y 0 ≤ |z.im| → F 0 z ≠ 0)
    (hbar : ∀ n < N, ∀ z : ℂ, X < |z.re| → |z.re| ≤ X + W → Y n ≤ |z.im| → F n z ≠ 0)
    (hfar : ∀ n < N, ∀ z : ℂ, F n z = 0 → z.im ^ 2 ≤ W ^ 2 + Y n ^ 2) :
    ∀ n ≤ N, ∀ z : ℂ, |z.re| ≤ X → Y n ≤ |z.im| → F n z ≠ 0 := by
  intro n
  induction n with
  | zero => intro _; exact h0
  | succ n ih =>
    intro hn z hzre hzim hFz
    have hnN : n < N := hn
    have ih' := ih hnN.le
    obtain ⟨D⟩ := hdata n
    have hY1 : 0 < Y (n + 1) := hYpos (n + 1) hn
    -- move to the upper half-plane: `w = z` or `w = conj z`, with `Im w = |Im z|`
    obtain ⟨w, hwre, hwim, hFw⟩ : ∃ w : ℂ, w.re = z.re ∧ w.im = |z.im| ∧ F (n + 1) w = 0 := by
      rcases le_or_gt 0 z.im with h | h
      · exact ⟨z, rfl, (abs_of_nonneg h).symm, hFz⟩
      · refine ⟨conj z, by simp, by simp [abs_of_neg h], ?_⟩
        rw [hreal, hFz, map_zero]
    have hwpos : 0 < w.im := by rw [hwim]; linarith
    have hwY : Y (n + 1) ≤ w.im := by rw [hwim]; exact hzim
    rw [hsucc] at hFw
    refine D.m4_shiftAvg_ne_zero_local (hreal n) hδ hwpos ?_ hFw
    -- the local condition at `w`, for every zero `ζ` of `F n`
    intro ζ hζ
    have hwsq : Y (n + 1) ^ 2 ≤ w.im ^ 2 := pow_le_pow_left₀ hY1.le hwY 2
    have hstep := hYstep n hnN
    rcases lt_or_ge |ζ.im| (Y n) with hlow | hhigh
    · -- below the barrier curve: `(Im ζ)² < (Y n)² = (Y (n+1))² + δ² ≤ (Im w)² + δ²`
      have hsq : ζ.im ^ 2 < Y n ^ 2 := by
        rw [← sq_abs ζ.im]
        exact pow_lt_pow_left₀ hlow (abs_nonneg _) (by norm_num)
      nlinarith [sq_nonneg (w.re - ζ.re)]
    · rcases le_or_gt |ζ.re| X with hin | hout
      · exact absurd hζ (ih' ζ hin hhigh)
      · rcases le_or_gt |ζ.re| (X + W) with hbarr | hfarr
        · exact absurd hζ (hbar n hnN ζ hout hbarr hhigh)
        · -- beyond the barrier: `|Re w − Re ζ| > W`
          have hwre' : |w.re| ≤ X := by rw [hwre]; exact hzre
          have hdist : W < |w.re - ζ.re| := by
            have h1 : |ζ.re| - |w.re| ≤ |w.re - ζ.re| := by
              have := abs_sub_abs_le_abs_sub ζ.re w.re
              rwa [abs_sub_comm] at this
            linarith
          have hdsq : W ^ 2 < (w.re - ζ.re) ^ 2 := by
            rw [← sq_abs (w.re - ζ.re)]
            exact pow_lt_pow_left₀ hdist hW (by norm_num)
          have hfar' := hfar n hnN ζ hζ
          nlinarith

/-! ### A compactness margin -/

/-- **Compactness margin.**  Let `C` be compact (in a Hausdorff space), `g` and `φ` continuous on
`C`, and suppose `g p ≠ 0` for every `p ∈ C` with `φ p ≤ 0`.  Then there are `η > 0` and `ε > 0`
with `ε ≤ ‖g p‖` for every `p ∈ C` with `φ p ≤ η`. -/
theorem m4_compact_margin {T E : Type*} [TopologicalSpace T] [T2Space T] [NormedAddCommGroup E]
    {C : Set T} (hC : IsCompact C) {g : T → E} (hg : ContinuousOn g C) {φ : T → ℝ}
    (hφ : ContinuousOn φ C) (hne : ∀ p ∈ C, φ p ≤ 0 → g p ≠ 0) :
    ∃ η > 0, ∃ ε > 0, ∀ p ∈ C, φ p ≤ η → ε ≤ ‖g p‖ := by
  have hCc : IsClosed C := hC.isClosed
  -- the zero set of `g` in `C` is compact, and `φ > 0` on it
  set Z : Set T := C ∩ g ⁻¹' {0} with hZdef
  have hZ : IsCompact Z :=
    hC.of_isClosed_subset (hg.preimage_isClosed_of_isClosed hCc isClosed_singleton)
      inter_subset_left
  obtain ⟨η, hη, hηZ⟩ : ∃ η > 0, ∀ p ∈ Z, η < φ p := by
    rcases Z.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, fun p hp ↦ by rw [h] at hp; exact absurd hp (notMem_empty p)⟩
    · obtain ⟨p₁, hp₁, hmin⟩ := hZ.exists_isMinOn h (hφ.mono inter_subset_left)
      have hpos : 0 < φ p₁ := by
        by_contra hle
        push Not at hle
        exact hne p₁ hp₁.1 hle hp₁.2
      refine ⟨φ p₁ / 2, by positivity, fun p hp ↦ ?_⟩
      have : φ p₁ ≤ φ p := hmin hp
      linarith
  -- on the compact set `C ∩ {φ ≤ η}` the function `g` does not vanish
  set Cη : Set T := C ∩ φ ⁻¹' Iic η with hCηdef
  have hCη : IsCompact Cη :=
    hC.of_isClosed_subset (hφ.preimage_isClosed_of_isClosed hCc isClosed_Iic) inter_subset_left
  have hgne : ∀ p ∈ Cη, g p ≠ 0 := by
    intro p hp hgp
    have := hηZ p ⟨hp.1, hgp⟩
    have h2 : φ p ≤ η := hp.2
    linarith
  obtain ⟨ε, hε, hεC⟩ : ∃ ε > 0, ∀ p ∈ Cη, ε ≤ ‖g p‖ := by
    rcases Cη.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, fun p hp ↦ by rw [h] at hp; exact absurd hp (notMem_empty p)⟩
    · obtain ⟨p₂, hp₂, hmin⟩ :=
        hCη.exists_isMinOn h (continuous_norm.comp_continuousOn (hg.mono inter_subset_left))
      refine ⟨‖g p₂‖, norm_pos_iff.mpr (hgne p₂ hp₂), fun p hp ↦ ?_⟩
      exact hmin hp
  exact ⟨η, hη, ε, hε, fun p hp hφp ↦ hεC p ⟨hp, hφp⟩⟩

end DBN
