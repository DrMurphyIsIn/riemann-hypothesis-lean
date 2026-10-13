/-  EMZeta.lean -- A2 Theorem 1: the Euler-Maclaurin representation of ζ with explicit

    M6GAP CROSS-PIN PORT (lane m6gap, 2026-09-23): a copy of
    telperion/examples/zeta_reflection/lean/EMZeta.lean (Lean v4.32.0, Mathlib v4.32.0) onto the dbn
    island (Lean v4.34.0-rc1, Mathlib de5ce8a9).  The ONLY edits are: module names prefixed `M6gap`
    in the imports, every namespace prefixed `M6gap.` (so no declaration can clash with a sibling
    lane's port), and comment wording on this island's word-level placeholder scan.  No proof was
    changed.  Consumed by M6gapHeightFloor (the 55/16 height floor on this island).

    remainder.

    Euler-Maclaurin summation is ABSENT from Mathlib (confirmed: `find Mathlib -iname
    '*maclaurin*'` is empty; `Mathlib/Analysis/SumIntegralComparisons.lean` has only crude
    monotone sum/integral bounds).  This file builds it bottom-up and is upstreamable.

    Architecture (proven bottom-up; only fully-proven lemmas live here, WIP in EMZetaWip.lean):

      A.  Periodized ("saw") Bernoulli  `sawBernoulli k x := bernoulliFun k (Int.fract x)`.
          Reuses `Mathlib.NumberTheory.ZetaValues.bernoulliFun` and its derivative/integral
          API (`hasDerivAt_bernoulliFun`, `integral_bernoulliFun`, `contDiff_bernoulliFun`).

      B.  One-step Euler-Maclaurin over `[m, m+1]` for a C^1 function f:
              ∫ f = (f m + f (m+1))/2 - ∫ B̃₁(x) f'(x) dx
          via integration by parts (`intervalIntegral.integral_mul_deriv_eq_deriv_mul`)
          with the saw-1 antiderivative.  This is `em_unit_step`.

      C.  Summed over `m = 0 .. N-1`: the classical first-order Euler-Maclaurin formula
              ∑_{n=1}^{N} f n = ∫_0^N f + (f N - f 0)/2 + ∫_0^N B̃₁(x) f'(x) dx
          (`euler_maclaurin_one`).  Telescoping of the integral (`intervalIntegral.sum_integral_
          adjacent_intervals`) + telescoping of the trapezoid endpoints.

      D.  Specialisation to `f x = x^{-s}` on `[1, N]` (real `s`) and the tail limit `N → ∞`
          giving the K=1 Euler-Maclaurin representation of `ζ` for real `s > 1`
          (`em_zeta_real_K1`), matching the Mathlib fractional-part representation route
          used in `Mathlib.NumberTheory.Harmonic.ZetaAsymp`.

    NOT YET in this file (see EMZetaWip.lean, never imported by a guard, no placeholder proof here):
      - the general order-K induction (periodized `bernoulliFun k` for k ≥ 2);
      - the complex interval-σ form valid `Re s > 1 - 2K` by analytic continuation
        (`AnalyticOnNhd.eqOn`);
      - the explicit remainder BOUND `|R_K| ≤ (|B_{2K}|/(2K)!) ∫ |f^{(2K)}|`.

    conjecture1_proved = False.  This is NOT a proof of RH; it is a classical analysis lemma.
-/
import Mathlib.NumberTheory.ZetaValues
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory intervalIntegral Set Filter Topology
open scoped Real

namespace M6gap.ZetaReflection

/-! ## A. The periodized ("saw") Bernoulli functions -/

/-- The periodized Bernoulli function `B̃ₖ(x) = Bₖ({x})` on `ℝ`, where `{x} = Int.fract x`.
    For `k = 1` this is the classical sawtooth `{x} - 1/2` (away from integers).  We build EM
    on this `ℝ → ℝ` form rather than Mathlib's `AddCircle`-valued `periodizedBernoulli`, since
    the finite-sum induction wants a plain real function with `bernoulliFun`'s derivative and
    integral API directly available. -/
noncomputable def sawBernoulli (k : ℕ) (x : ℝ) : ℝ := bernoulliFun k (Int.fract x)

@[simp] lemma sawBernoulli_zero (x : ℝ) : sawBernoulli 0 x = 1 := by
  simp [sawBernoulli, bernoulliFun_zero]

/-- The saw is measurable: `bernoulliFun k` is continuous and `Int.fract` is measurable. -/
lemma sawBernoulli_measurable (k : ℕ) : Measurable (sawBernoulli k) :=
  (contDiff_bernoulliFun (k := k)).continuous.measurable.comp measurable_fract

/-- The order-1 saw is bounded by `1/2` (it is `{x} − 1/2` with `{x} ∈ [0, 1)`). -/
lemma abs_sawBernoulli_one_le (x : ℝ) : |sawBernoulli 1 x| ≤ 1 / 2 := by
  rw [sawBernoulli, bernoulliFun_one, abs_le]
  have h0 : (0 : ℝ) ≤ Int.fract x := Int.fract_nonneg x
  have h1 : Int.fract x < 1 := Int.fract_lt_one x
  constructor <;> linarith

/-- On the half-open unit cell starting at an integer, the saw agrees with the raw Bernoulli
    function shifted to that cell. -/
lemma sawBernoulli_eq_on_Ico (k : ℕ) {m : ℤ} {x : ℝ} (hx : x ∈ Ico (m : ℝ) (m + 1)) :
    sawBernoulli k x = bernoulliFun k (x - m) := by
  have hfloor : ⌊x⌋ = m := by
    rw [Int.floor_eq_iff]
    exact ⟨hx.1, by push_cast; linarith [hx.2]⟩
  have hfract : Int.fract x = x - m := by
    rw [Int.fract, hfloor]
  rw [sawBernoulli, hfract]

/-- The order-1 saw on the cell `[m, m+1)` is the affine sawtooth `x - m - 1/2`. -/
lemma sawBernoulli_one_eq_on_Ico {m : ℤ} {x : ℝ} (hx : x ∈ Ico (m : ℝ) (m + 1)) :
    sawBernoulli 1 x = x - m - 1 / 2 := by
  rw [sawBernoulli_eq_on_Ico 1 hx, bernoulliFun_one]

/-! ## B. One-step Euler-Maclaurin over a unit cell

    For a `C¹` function `f` on `[m, m+1]` (real, integer `m`), integration by parts with the
    order-1 antiderivative `w x = x - m - 1/2` of the constant `1` (equal to `sawBernoulli 1`
    on the cell) yields the trapezoidal Euler-Maclaurin step
        ∫_m^{m+1} f = (f m + f(m+1))/2 − ∫_m^{m+1} (sawBernoulli 1 x) · f'(x) dx.
-/

/-- **One-step Euler-Maclaurin** over the unit cell `[m, m+1]`.

    Hypotheses: `f` has derivative `f'` at every point of the cell and `f'` is interval
    integrable there.  The saw factor is written via `sawBernoulli 1` so the summed form in
    part C reads as a single integral of `sawBernoulli 1 · f'` over `[0, N]`. -/
theorem em_unit_step {f f' : ℝ → ℝ} (m : ℤ)
    (hf : ∀ x ∈ Icc (m : ℝ) (m + 1), HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume (m : ℝ) (m + 1)) :
    (∫ x in (m : ℝ)..(m + 1), f x)
      = (f m + f (m + 1)) / 2 - ∫ x in (m : ℝ)..(m + 1), sawBernoulli 1 x * f' x := by
  -- The affine antiderivative `w x = x - m - 1/2` of the constant `1`.
  set w : ℝ → ℝ := fun x => x - m - 1 / 2 with hw
  have hcc : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  have hw' : ∀ x, HasDerivAt w 1 x := by
    intro x
    have := ((hasDerivAt_id x).sub_const (m : ℝ)).sub_const (1 / 2 : ℝ)
    simpa [hw] using this
  have hwcont : Continuous w := by fun_prop
  have huv : ∀ x ∈ uIcc (m : ℝ) (m + 1), HasDerivAt w (1 : ℝ) x := fun x _ => hw' x
  have hfd : ∀ x ∈ uIcc (m : ℝ) (m + 1), HasDerivAt f (f' x) x := by
    intro x hx
    rw [uIcc_of_le hcc] at hx
    exact hf x hx
  have hw'int : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (m : ℝ) (m + 1) :=
    intervalIntegrable_const
  -- `integral_deriv_mul_eq_sub`: ∫ (w' · f + w · f') = w·f |end - w·f |start,  w' = 1.
  have hIBP := integral_deriv_mul_eq_sub huv hfd hw'int hf'
  -- Endpoint values of `w`.
  have hwL : w (m : ℝ) = -(1 / 2) := by simp only [hw]; ring
  have hwR : w ((m : ℝ) + 1) = 1 / 2 := by simp only [hw]; ring
  -- The `w · f'` term is interval integrable (continuous · integrable).
  have hwf'int : IntervalIntegrable (fun x => w x * f' x) volume (m : ℝ) (m + 1) :=
    hf'.continuousOn_mul hwcont.continuousOn
  -- Split the LHS integrand `1 * f x + w x * f' x`.
  have hsplit :
      (∫ x in (m : ℝ)..(m + 1), (1 : ℝ) * f x + w x * f' x)
        = (∫ x in (m : ℝ)..(m + 1), f x) + ∫ x in (m : ℝ)..(m + 1), w x * f' x := by
    have hfcont : ContinuousOn f (uIcc (m : ℝ) (m + 1)) := fun x hx =>
      (hfd x hx).continuousAt.continuousWithinAt
    have hfint : IntervalIntegrable f volume (m : ℝ) (m + 1) :=
      hfcont.intervalIntegrable
    rw [intervalIntegral.integral_add (by simpa using hfint) hwf'int]
    simp
  -- Identify `sawBernoulli 1 · f'` with `w · f'` on the cell.
  -- `sawBernoulli 1` and `w` agree on the half-open cell `[m, m+1)`; they disagree only at the
  -- right endpoint `m+1` (the saw jumps there), a null set, so the integrals coincide.
  have hsaw : (∫ x in (m : ℝ)..(m + 1), sawBernoulli 1 x * f' x)
      = ∫ x in (m : ℝ)..(m + 1), w x * f' x := by
    apply intervalIntegral.integral_congr_ae
    -- a.e. on `Ι m (m+1) = Ioc m (m+1)`, exclude the single point `{m+1}`.
    have hnull : ∀ᵐ x, x ≠ ((m : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico (m : ℝ) (m + 1) := ⟨le_of_lt hxmem.1, lt_of_le_of_ne hxmem.2 hxne⟩
    rw [sawBernoulli_one_eq_on_Ico hxIco]
  -- Assemble.
  rw [hsaw]
  have key : (∫ x in (m : ℝ)..(m + 1), f x) + ∫ x in (m : ℝ)..(m + 1), w x * f' x
      = w ((m : ℝ) + 1) * f ((m : ℝ) + 1) - w (m : ℝ) * f (m : ℝ) := by
    rw [← hsplit]; exact hIBP
  rw [hwL, hwR] at key
  linarith [key]

/-! ## C. Summed first-order Euler-Maclaurin over `[0, N]`

    Summing `em_unit_step` over the cells `[0,1], [1,2], …, [N-1,N]` and telescoping the two
    integrals with `intervalIntegral.sum_integral_adjacent_intervals` gives the classical
    first-order Euler-Maclaurin formula (sum indexed `1..N`, integral over `[0,N]`)
        ∑_{n=1}^{N} f n = ∫_0^N f + (f N − f 0)/2 + ∫_0^N (sawBernoulli 1 x)·f'(x) dx.
    (Equivalently `∑_{n=0}^{N} f n = ∫_0^N f + (f 0 + f N)/2 + remainder`, the textbook form.)
-/

/-- Trapezoid-sum bookkeeping (real function evaluated at natural casts):
    `∑_{m<N} (f m + f (m+1))/2 = ∑_{n=1}^{N} f n + (f 0 − f N)/2`. -/
private lemma trapezoid_sum (f : ℝ → ℝ) (N : ℕ) :
    (∑ m ∈ Finset.range N, (f (m : ℝ) + f ((m : ℝ) + 1)) / 2)
      = (∑ n ∈ Finset.Icc 1 N, f (n : ℝ)) + (f 0 - f (N : ℝ)) / 2 := by
  induction N with
  | zero => simp
  | succ p ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by lia : 1 ≤ p + 1)]
      push_cast; ring

/-- Trapezoid-sum bookkeeping over a general window `[M, N)`:
    `∑_{k∈[M,N)} (f k + f (k+1))/2 = ∑_{n∈[M,N)} f n + (f N − f M)/2`. -/
private lemma trapezoid_sum_window (f : ℝ → ℝ) {M N : ℕ} (hMN : M ≤ N) :
    (∑ k ∈ Finset.Ico M N, (f (k : ℝ) + f ((k : ℝ) + 1)) / 2)
      = (∑ n ∈ Finset.Ico M N, f (n : ℝ)) + (f N - f M) / 2 := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ p hp ih =>
      rw [Finset.sum_Ico_succ_top hp (fun k => (f (k : ℝ) + f ((k : ℝ) + 1)) / 2),
          Finset.sum_Ico_succ_top hp (fun n => f (n : ℝ)), ih]
      push_cast; ring

/-- **First-order Euler-Maclaurin summation** over `[0, N]`.

    For `f` with derivative `f'` on all of `[0, N]` and `f'` interval-integrable on each unit
    cell, the sum `∑_{n=1}^{N} f n` equals the integral `∫_0^N f`, plus the trapezoidal
    endpoint correction `(f N − f 0)/2`, plus the order-1 saw remainder
    `∫_0^N (sawBernoulli 1 x)·f'(x) dx`. -/
theorem euler_maclaurin_one {f f' : ℝ → ℝ} (N : ℕ)
    (hf : ∀ x ∈ Icc (0 : ℝ) N, HasDerivAt f (f' x) x)
    (hf' : ∀ k < N, IntervalIntegrable f' volume (k : ℝ) (k + 1)) :
    (∑ n ∈ Finset.Icc 1 N, f n)
      = (∫ x in (0 : ℝ)..N, f x) + (f N - f 0) / 2
        + ∫ x in (0 : ℝ)..N, sawBernoulli 1 x * f' x := by
  -- Per-cell derivative availability, cast the ℕ cell `[k, k+1]` into the global `[0, N]`.
  have hcell : ∀ k, k < N → ∀ x ∈ Icc (k : ℝ) (k + 1), HasDerivAt f (f' x) x := by
    intro k hk x hx
    refine hf x ⟨le_trans (by positivity) hx.1, ?_⟩
    have : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hk
    linarith [hx.2]
  -- Apply the one-step identity in each cell.
  have hstep : ∀ k ∈ Finset.range N,
      (∫ x in (k : ℝ)..(k + 1), f x)
        = (f k + f (k + 1)) / 2 - ∫ x in (k : ℝ)..(k + 1), sawBernoulli 1 x * f' x := by
    intro k hk
    have hkN : k < N := Finset.mem_range.mp hk
    have hcast : (((k : ℤ)) : ℝ) = (k : ℝ) := by push_cast; ring
    have hstepZ := em_unit_step (f := f) (f' := f') (k : ℤ)
      (by intro x hx; rw [hcast] at hx; exact hcell k hkN x hx)
      (by rw [hcast]; exact hf' k hkN)
    simp only [hcast] at hstepZ
    exact hstepZ
  -- Sum the per-cell identity over `range N`.
  have hsum := Finset.sum_congr rfl hstep
  -- Telescope `∫ f` over cells → `∫_0^N f`.
  have hfint_cell : ∀ k < N, IntervalIntegrable f volume (k : ℝ) (k + 1) := by
    intro k hk
    have hcont : ContinuousOn f (uIcc (k : ℝ) (k + 1)) := by
      rw [uIcc_of_le (by linarith)]
      exact fun x hx => (hcell k hk x hx).continuousAt.continuousWithinAt
    exact hcont.intervalIntegrable
  have htel_f : (∑ k ∈ Finset.range N, ∫ x in (k : ℝ)..(k + 1), f x)
      = ∫ x in (0 : ℝ)..N, f x := by
    have := intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ))
      (f := f) (n := N) (by intro k hk; simpa using hfint_cell k hk)
    simpa using this
  -- Telescope the saw remainder over cells → `∫_0^N saw·f'`.
  -- `sawBernoulli 1` is discontinuous (jumps at integers), but on the cell it equals the
  -- continuous affine `x - k - 1/2` a.e., so the product is interval integrable there.
  have hsawf'_cell : ∀ k < N,
      IntervalIntegrable (fun x => sawBernoulli 1 x * f' x) volume (k : ℝ) (k + 1) := by
    intro k hk
    have hcc : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
    -- The continuous affine surrogate on the cell.
    have hcont : IntervalIntegrable (fun x => (x - k - 1 / 2) * f' x) volume (k : ℝ) (k + 1) :=
      (hf' k hk).continuousOn_mul (by fun_prop)
    -- a.e. equality of the two integrands on `Ι k (k+1)`.
    refine (intervalIntegrable_congr_ae ?_).mpr hcont
    have hnull : ∀ᵐ x, x ≠ ((k : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico ((k : ℤ) : ℝ) (((k : ℤ) : ℝ) + 1) := by
      refine ⟨?_, ?_⟩
      · have : (k : ℝ) < x := hxmem.1
        push_cast; linarith
      · have : x ≤ (k : ℝ) + 1 := hxmem.2
        have hlt : x < (k : ℝ) + 1 := lt_of_le_of_ne this hxne
        push_cast; linarith
    rw [sawBernoulli_one_eq_on_Ico hxIco]
    push_cast; ring_nf
  have htel_saw : (∑ k ∈ Finset.range N, ∫ x in (k : ℝ)..(k + 1), sawBernoulli 1 x * f' x)
      = ∫ x in (0 : ℝ)..N, sawBernoulli 1 x * f' x := by
    have := intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ))
      (f := fun x => sawBernoulli 1 x * f' x) (n := N)
      (by intro k hk; simpa using hsawf'_cell k hk)
    simpa using this
  -- Assemble: LHS sum = trapezoid sum − saw sum; substitute telescopes + trapezoid_sum.
  rw [Finset.sum_sub_distrib] at hsum
  rw [htel_f, htel_saw, trapezoid_sum f N] at hsum
  linarith [hsum]

/-! ## D. Zeta base case: first-order Euler-Maclaurin for `f x = x^{-s}` on `[1, N]`

    The reusable finite-`N` statement.  Specialising the general `[M, N]` machinery below to
    `M = 1`, `f x = x^{-s}` with derivative `f' x = -s · x^{-s-1}` (valid for `x ≠ 0`, hence on
    all of `[1, N]`), we get the classical finite Euler-Maclaurin representation of the partial
    zeta sum.  Taking `N → ∞` (real `s > 1`) matches the fractional-part representation in
    `Mathlib.NumberTheory.Harmonic.ZetaAsymp` (`zeta_limit_aux1`, `termTSum`).
-/

/-- **First-order Euler-Maclaurin over a general integer window `[M, N]`.**

    Half-open indexing: the sum runs over `n ∈ [M, N)` (i.e. `n = M, …, N-1`), the integrals
    over `[M, N]`:
        ∑_{n=M}^{N-1} f n = ∫_M^N f − (f N − f M)/2 + ∫_M^N (sawBernoulli 1 x)·f'(x) dx.
    This is the form the zeta base case needs (window `[1, N]`, avoiding the singularity of
    `x^{-s}` at `0`).  The requirement is `f` differentiable on `[M, N]` with `f'` interval
    integrable on each cell. -/
theorem euler_maclaurin_one_window {f f' : ℝ → ℝ} (M N : ℕ) (hMN : M ≤ N)
    (hf : ∀ x ∈ Icc (M : ℝ) N, HasDerivAt f (f' x) x)
    (hf' : ∀ k ∈ Finset.Ico M N, IntervalIntegrable f' volume (k : ℝ) (k + 1)) :
    (∑ n ∈ Finset.Ico M N, f (n : ℝ))
      = (∫ x in (M : ℝ)..N, f x) - (f N - f M) / 2
        + ∫ x in (M : ℝ)..N, sawBernoulli 1 x * f' x := by
  -- Per-cell derivative availability on each `[k, k+1] ⊆ [M, N]`.
  have hcell : ∀ k ∈ Finset.Ico M N, ∀ x ∈ Icc (k : ℝ) (k + 1), HasDerivAt f (f' x) x := by
    intro k hk x hx
    rw [Finset.mem_Ico] at hk
    refine hf x ⟨?_, ?_⟩
    · exact le_trans (by exact_mod_cast hk.1) hx.1
    · have : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hk.2
      linarith [hx.2]
  -- One-step identity per cell (recast the ℤ cell into ℕ).
  have hstep : ∀ k ∈ Finset.Ico M N,
      (∫ x in (k : ℝ)..(k + 1), f x)
        = (f k + f (k + 1)) / 2 - ∫ x in (k : ℝ)..(k + 1), sawBernoulli 1 x * f' x := by
    intro k hk
    have hcast : (((k : ℤ)) : ℝ) = (k : ℝ) := by push_cast; ring
    have hstepZ := em_unit_step (f := f) (f' := f') (k : ℤ)
      (by intro x hx; rw [hcast] at hx; exact hcell k hk x hx)
      (by rw [hcast]; exact hf' k hk)
    simp only [hcast] at hstepZ
    exact hstepZ
  have hsum := Finset.sum_congr rfl hstep
  -- Telescope `∫ f` over `Ico M N` → `∫_M^N f`.
  have hfint_cell : ∀ k ∈ Finset.Ico M N, IntervalIntegrable f volume (k : ℝ) (k + 1) := by
    intro k hk
    have hcont : ContinuousOn f (uIcc (k : ℝ) (k + 1)) := by
      rw [uIcc_of_le (by linarith)]
      exact fun x hx => (hcell k hk x hx).continuousAt.continuousWithinAt
    exact hcont.intervalIntegrable
  have htel_f : (∑ k ∈ Finset.Ico M N, ∫ x in (k : ℝ)..(k + 1), f x)
      = ∫ x in (M : ℝ)..N, f x := by
    have hint : ∀ k ∈ Set.Ico M N,
        IntervalIntegrable f volume ((fun k : ℕ => (k : ℝ)) k) ((fun k : ℕ => (k : ℝ)) (k + 1)) := by
      intro k hk
      simpa [Nat.cast_succ] using hfint_cell k (Finset.mem_Ico.mpr hk)
    have := intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun k : ℕ => (k : ℝ)) (f := f) (μ := volume) hMN hint
    simpa using this
  -- Telescope the saw remainder over `Ico M N` → `∫_M^N saw·f'`.
  have hsawf'_cell : ∀ k ∈ Finset.Ico M N,
      IntervalIntegrable (fun x => sawBernoulli 1 x * f' x) volume (k : ℝ) (k + 1) := by
    intro k hk
    have hcc : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
    have hcont : IntervalIntegrable (fun x => (x - k - 1 / 2) * f' x) volume (k : ℝ) (k + 1) :=
      (hf' k hk).continuousOn_mul (by fun_prop)
    refine (intervalIntegrable_congr_ae ?_).mpr hcont
    have hnull : ∀ᵐ x, x ≠ ((k : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico ((k : ℤ) : ℝ) (((k : ℤ) : ℝ) + 1) := by
      refine ⟨?_, ?_⟩
      · have : (k : ℝ) < x := hxmem.1
        push_cast; linarith
      · have hlt : x < (k : ℝ) + 1 := lt_of_le_of_ne hxmem.2 hxne
        push_cast; linarith
    rw [sawBernoulli_one_eq_on_Ico hxIco]
    push_cast; ring_nf
  have htel_saw : (∑ k ∈ Finset.Ico M N, ∫ x in (k : ℝ)..(k + 1), sawBernoulli 1 x * f' x)
      = ∫ x in (M : ℝ)..N, sawBernoulli 1 x * f' x := by
    have hint : ∀ k ∈ Set.Ico M N,
        IntervalIntegrable (fun x => sawBernoulli 1 x * f' x) volume
          ((fun k : ℕ => (k : ℝ)) k) ((fun k : ℕ => (k : ℝ)) (k + 1)) := by
      intro k hk
      simpa [Nat.cast_succ] using hsawf'_cell k (Finset.mem_Ico.mpr hk)
    have := intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun k : ℕ => (k : ℝ)) (f := fun x => sawBernoulli 1 x * f' x) (μ := volume) hMN hint
    simpa using this
  rw [Finset.sum_sub_distrib, htel_f, htel_saw, trapezoid_sum_window f hMN] at hsum
  linarith [hsum]

/-- **First-order Euler-Maclaurin representation of the partial zeta sum** (real exponent).

    For real `s` and `N ≥ 1`, applying `euler_maclaurin_one_window` to `f x = x^{-s}` (real
    `rpow`, derivative `-s·x^{-s-1}`, valid on `[1, N]` since `x ≠ 0` there) gives
        ∑_{n=1}^{N-1} n^{-s} = ∫_1^N x^{-s} dx − (N^{-s} − 1)/2
                               + ∫_1^N (sawBernoulli 1 x)·(−s·x^{-s-1}) dx.
    Taking `N → ∞` for `s > 1` recovers `ζ(s)` up to the (convergent) integral remainder;
    this matches Mathlib's fractional-part route in `Mathlib.NumberTheory.Harmonic.ZetaAsymp`
    (`zeta_limit_aux1`, `termTSum`).  The `N → ∞` limit and the general-K refinement are WIP
    (see EMZetaWip.lean). -/
theorem em_zeta_partial_real (s : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ico 1 N, (n : ℝ) ^ (-s))
      = (∫ x in (1 : ℝ)..N, x ^ (-s)) - ((N : ℝ) ^ (-s) - (1 : ℝ) ^ (-s)) / 2
        + ∫ x in (1 : ℝ)..N, sawBernoulli 1 x * (-s * x ^ (-s - 1)) := by
  have hderiv : ∀ x ∈ Icc ((1 : ℕ) : ℝ) N, HasDerivAt (fun x => x ^ (-s)) (-s * x ^ (-s - 1)) x := by
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := by have := hx.1; push_cast at this; linarith
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hx1)
    simpa [neg_mul] using Real.hasDerivAt_rpow_const (x := x) (p := -s) (Or.inl hx0)
  have hf'int : ∀ k ∈ Finset.Ico 1 N,
      IntervalIntegrable (fun x => -s * x ^ (-s - 1)) volume (k : ℝ) (k + 1) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
    -- On `[k, k+1]` with `k ≥ 1`, `x^{-s-1}` is continuous (argument bounded away from 0).
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith)]
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.rpow_const continuousOn_id
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := le_trans hk1 hx.1
    exact Or.inl (by simp only [id_eq]; exact ne_of_gt (by linarith))
  simpa using euler_maclaurin_one_window (f := fun x => x ^ (-s))
    (f' := fun x => -s * x ^ (-s - 1)) 1 N hN hderiv hf'int

/-- The order-1 saw remainder integrand `sawBernoulli 1 · (−s·x^{−s−1})` is integrable on
    `(1, ∞)` when `s > 1`: dominate by `(s/2)·x^{−s−1}`, integrable there since the exponent
    `−s−1 < −1`.  This is the convergence input for the `N → ∞` limit (Part D'). -/
theorem em_zeta_remainder_integrableOn (s : ℝ) (hs : 1 < s) :
    IntegrableOn (fun x : ℝ => sawBernoulli 1 x * (-s * x ^ (-s - 1))) (Ioi 1) := by
  have hbase : IntegrableOn (fun x : ℝ => (s * (1 / 2)) * x ^ (-s - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (a := -s - 1) (c := (1 : ℝ)) (by linarith) (by norm_num)).const_mul _
  have hrpowmeas : Measurable (fun x : ℝ => x ^ (-s - 1)) := by measurability
  refine Integrable.mono' hbase ?_ ?_
  · exact (sawBernoulli_measurable 1).aestronglyMeasurable.mul
      ((measurable_const.mul hrpowmeas).aestronglyMeasurable)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hxpos : (0 : ℝ) < x := by have : (1 : ℝ) < x := hx; linarith
    have hrpownn : (0 : ℝ) ≤ x ^ (-s - 1) := Real.rpow_nonneg hxpos.le _
    have hsaw := abs_sawBernoulli_one_le x
    have heq : ‖sawBernoulli 1 x * (-s * x ^ (-s - 1))‖
        = |sawBernoulli 1 x| * (s * x ^ (-s - 1)) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_neg (by linarith : (-s : ℝ) < 0),
        abs_of_nonneg hrpownn, neg_neg]
    rw [heq]
    calc |sawBernoulli 1 x| * (s * x ^ (-s - 1))
        ≤ (1 / 2) * (s * x ^ (-s - 1)) := by gcongr
      _ = (s * (1 / 2)) * x ^ (-s - 1) := by ring

/-- **First-order Euler-Maclaurin representation of the real zeta series** (Part D').

    For real `s > 1`, taking `N → ∞` in `em_zeta_partial_real`:
        ∑' n, n^{-s} = ∫_1^∞ x^{-s} dx + 1^{-s}/2 + ∫_1^∞ (sawBernoulli 1 x)·(−s·x^{−s−1}) dx.
    All three limits are legitimate:
      * the partial sum `∑_{n<N} n^{-s} → ∑' n` since the series is summable (`Real.summable_nat_rpow`);
      * the two finite integrals converge to their improper integrals over `(1, ∞)`
        (`intervalIntegral_tendsto_integral_Ioi`, using `em_zeta_remainder_integrableOn` and
        `integrableOn_Ioi_rpow_of_lt`);
      * the endpoint term `N^{-s} → 0` (`tendsto_rpow_neg_atTop`).
    Note `∑' n, n^{-s}` here is the real-`rpow` Dirichlet series; connecting it to `riemannZeta`
    (a complex-`cpow` object) is a separate small bridge, left to the complex extension (E).

    This is the clean unconditional real-`s > 1` statement.  Euler-Maclaurin is absent from
    Mathlib; this is upstreamable. -/
theorem em_zeta_real (s : ℝ) (hs : 1 < s) :
    (∑' n : ℕ, (n : ℝ) ^ (-s))
      = (∫ x in Ioi (1 : ℝ), x ^ (-s)) + (1 : ℝ) ^ (-s) / 2
        + ∫ x in Ioi (1 : ℝ), sawBernoulli 1 x * (-s * x ^ (-s - 1)) := by
  have hI : IntegrableOn (fun x : ℝ => x ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (a := -s) (c := (1 : ℝ)) (by linarith) (by norm_num)
  have hR := em_zeta_remainder_integrableOn s hs
  have hsummable : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) := by
    rw [Real.summable_nat_rpow]; linarith
  have h0 : ((0 : ℕ) : ℝ) ^ (-s) = 0 := by rw [Nat.cast_zero, Real.zero_rpow (by linarith)]
  -- LHS: partial sum over `Ico 1 N` → the tsum (the `n = 0` term is `0^{-s} = 0`).
  have hLHS : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Ico 1 N, (n : ℝ) ^ (-s)) atTop
      (𝓝 (∑' n : ℕ, (n : ℝ) ^ (-s))) := by
    have hrange : (fun N : ℕ => ∑ n ∈ Finset.Ico 1 N, (n : ℝ) ^ (-s))
        = (fun N : ℕ => ∑ n ∈ Finset.range N, (n : ℝ) ^ (-s)) := by
      funext N
      rcases Nat.eq_zero_or_pos N with hN | hN
      · subst hN; simp
      · rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive (fun n => (n : ℝ) ^ (-s))
            (Nat.zero_le 1) (by lia : 1 ≤ N), Nat.Ico_zero_eq_range, Finset.sum_range_one,
            h0, zero_add]
    rw [hrange]; exact hsummable.hasSum.tendsto_sum_nat
  -- RHS component limits: the two finite integrals → improper, and the endpoint term → 0.
  have hA : Tendsto (fun N : ℕ => ∫ x in (1 : ℝ)..(N : ℝ), x ^ (-s)) atTop
      (𝓝 (∫ x in Ioi (1 : ℝ), x ^ (-s))) :=
    intervalIntegral_tendsto_integral_Ioi 1 hI tendsto_natCast_atTop_atTop
  have hEnd : Tendsto (fun N : ℕ => -((((N : ℝ)) ^ (-s) - (1 : ℝ) ^ (-s)) / 2)) atTop
      (𝓝 ((1 : ℝ) ^ (-s) / 2)) := by
    have hz : Tendsto (fun N : ℕ => ((N : ℝ)) ^ (-s)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (y := s) (by linarith)).comp tendsto_natCast_atTop_atTop
    have h2 := ((hz.sub_const ((1 : ℝ) ^ (-s))).div_const 2).neg
    convert h2 using 2; ring
  have hRem : Tendsto
      (fun N : ℕ => ∫ x in (1 : ℝ)..(N : ℝ), sawBernoulli 1 x * (-s * x ^ (-s - 1))) atTop
      (𝓝 (∫ x in Ioi (1 : ℝ), sawBernoulli 1 x * (-s * x ^ (-s - 1)))) :=
    intervalIntegral_tendsto_integral_Ioi 1 hR tendsto_natCast_atTop_atTop
  -- The finite identity from `em_zeta_partial_real`, eventually in `N`.
  have hEq : ∀ᶠ N : ℕ in atTop, (∑ n ∈ Finset.Ico 1 N, (n : ℝ) ^ (-s))
      = (∫ x in (1 : ℝ)..(N : ℝ), x ^ (-s)) + -((((N : ℝ)) ^ (-s) - (1 : ℝ) ^ (-s)) / 2)
        + ∫ x in (1 : ℝ)..(N : ℝ), sawBernoulli 1 x * (-s * x ^ (-s - 1)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hp := em_zeta_partial_real s (N := N) hN
    rw [hp]; ring
  have hRHS := (hA.add hEnd).add hRem
  have hLHS' : Tendsto (fun N : ℕ =>
      (∫ x in (1 : ℝ)..(N : ℝ), x ^ (-s)) + -((((N : ℝ)) ^ (-s) - (1 : ℝ) ^ (-s)) / 2)
        + ∫ x in (1 : ℝ)..(N : ℝ), sawBernoulli 1 x * (-s * x ^ (-s - 1))) atTop
      (𝓝 (∑' n : ℕ, (n : ℝ) ^ (-s))) := hLHS.congr' hEq
  exact tendsto_nhds_unique hLHS' hRHS

end M6gap.ZetaReflection
