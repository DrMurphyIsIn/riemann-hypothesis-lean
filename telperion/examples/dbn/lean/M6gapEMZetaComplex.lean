/-  EMZetaComplex.lean -- A2 Theorem 1, E-track: the COMPLEX Euler-Maclaurin representation of ζ

    M6GAP CROSS-PIN PORT (lane m6gap, 2026-09-23): a copy of
    telperion/examples/zeta_reflection/lean/EMZetaComplex.lean (Lean v4.32.0, Mathlib v4.32.0) onto the dbn
    island (Lean v4.34.0-rc1, Mathlib de5ce8a9).  The ONLY edits are: module names prefixed `M6gap`
    in the imports, every namespace prefixed `M6gap.` (so no declaration can clash with a sibling
    lane's port), and comment wording on this island's word-level placeholder scan.  No proof was
    changed.  Consumed by M6gapHeightFloor (the 55/16 height floor on this island).

    and its K=1 analytic continuation into the critical strip.

    Builds on `EMZeta.lean` (real-s EM chain, Parts A-D', kernel-clean).  This file is the
    complex lift and the analytic continuation:

      E1.  `em_unit_step_cpow`   -- one-step EM over [m,m+1] for a ℂ-valued C¹ function.
           `em_cpow_partial`      -- finite-N EM for `f x = (x:ℂ)^(-s)`, s : ℂ, on [1,N].
      E2.  `em_zeta_cpow`         -- N→∞ complex representation, valid Re s > 1, tied to riemannZeta.
      E3.  `em_zeta_strip`        -- K=1 analytic continuation to 0 < Re s (s ≠ 1) with explicit
                                     remainder bound (THE PRIZE — covers the critical strip).
      E4.  `em_zeta_strip_enclosure` -- evaluator-facing finite-sum + explicit-tail enclosure shape.

    Only fully-proven lemmas (no placeholder proofs) live here.  General-K (K ≥ 2) stays in EMZetaWip.lean.

    conjecture1_proved = False.  This is a classical analysis lemma (Euler-Maclaurin + identity
    theorem), NOT a proof of RH.
-/
import M6gapEMZeta
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Analytic.Uniqueness

open MeasureTheory intervalIntegral Set Filter Topology Complex
open scoped Real

namespace M6gap.ZetaReflection

/-! ## E1a. One-step Euler-Maclaurin over a unit cell, ℂ-valued integrand.

    Direct lift of `em_unit_step`: the saw antiderivative `w x = x - m - 1/2` is real, cast to ℂ,
    and the IBP `intervalIntegral.integral_deriv_mul_eq_sub` runs in the `NormedRing ℂ`. -/

/-- **One-step Euler-Maclaurin over `[m, m+1]`, ℂ-valued `f`.**  Same statement as `em_unit_step`
    but `f, f' : ℝ → ℂ`; the saw factor `sawBernoulli 1 x` is cast to ℂ. -/
theorem em_unit_step_cpow {f f' : ℝ → ℂ} (m : ℤ)
    (hf : ∀ x ∈ Icc (m : ℝ) (m + 1), HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume (m : ℝ) (m + 1)) :
    (∫ x in (m : ℝ)..(m + 1), f x)
      = (f m + f (m + 1)) / 2
        - ∫ x in (m : ℝ)..(m + 1), (sawBernoulli 1 x : ℂ) * f' x := by
  -- The affine antiderivative `w x = x - m - 1/2` of the constant `1`, valued in ℂ.
  set w : ℝ → ℂ := fun x => (x : ℂ) - m - 1 / 2 with hw
  have hcc : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  have hw' : ∀ x, HasDerivAt w 1 x := by
    intro x
    have hbase : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
      simpa using (hasDerivAt_id (x : ℂ)).comp_ofReal
    have := (hbase.sub_const (m : ℂ)).sub_const (1 / 2 : ℂ)
    simpa [hw] using this
  have hwcont : Continuous w := by fun_prop
  have huv : ∀ x ∈ uIcc (m : ℝ) (m + 1), HasDerivAt w (1 : ℂ) x := fun x _ => hw' x
  have hfd : ∀ x ∈ uIcc (m : ℝ) (m + 1), HasDerivAt f (f' x) x := by
    intro x hx
    rw [uIcc_of_le hcc] at hx
    exact hf x hx
  have hw'int : IntervalIntegrable (fun _ : ℝ => (1 : ℂ)) volume (m : ℝ) (m + 1) :=
    intervalIntegrable_const
  have hIBP := integral_deriv_mul_eq_sub huv hfd hw'int hf'
  have hwL : w (m : ℝ) = -(1 / 2) := by simp only [hw]; push_cast; ring
  have hwR : w ((m : ℝ) + 1) = 1 / 2 := by simp only [hw]; push_cast; ring
  have hwf'int : IntervalIntegrable (fun x => w x * f' x) volume (m : ℝ) (m + 1) :=
    hf'.continuousOn_mul hwcont.continuousOn
  have hsplit :
      (∫ x in (m : ℝ)..(m + 1), (1 : ℂ) * f x + w x * f' x)
        = (∫ x in (m : ℝ)..(m + 1), f x) + ∫ x in (m : ℝ)..(m + 1), w x * f' x := by
    have hfcont : ContinuousOn f (uIcc (m : ℝ) (m + 1)) := fun x hx =>
      (hfd x hx).continuousAt.continuousWithinAt
    have hfint : IntervalIntegrable f volume (m : ℝ) (m + 1) :=
      hfcont.intervalIntegrable
    rw [intervalIntegral.integral_add (by simpa using hfint) hwf'int]
    simp
  -- Identify `(sawBernoulli 1 · : ℂ) · f'` with `w · f'` a.e. on the cell.
  have hsaw : (∫ x in (m : ℝ)..(m + 1), (sawBernoulli 1 x : ℂ) * f' x)
      = ∫ x in (m : ℝ)..(m + 1), w x * f' x := by
    apply intervalIntegral.integral_congr_ae
    have hnull : ∀ᵐ x, x ≠ ((m : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico (m : ℝ) (m + 1) := ⟨le_of_lt hxmem.1, lt_of_le_of_ne hxmem.2 hxne⟩
    rw [sawBernoulli_one_eq_on_Ico hxIco]
    simp only [hw]; push_cast; ring
  rw [hsaw]
  have key : (∫ x in (m : ℝ)..(m + 1), f x) + ∫ x in (m : ℝ)..(m + 1), w x * f' x
      = w ((m : ℝ) + 1) * f ((m : ℝ) + 1) - w (m : ℝ) * f (m : ℝ) := by
    rw [← hsplit]; exact hIBP
  rw [hwL, hwR] at key
  -- Solve for `∫ f` (ℂ is not ordered — use `linear_combination`).
  linear_combination key

/-! ## E1b. Summed complex EM over an integer window, and the partial-ζ identity.

    Lift of `euler_maclaurin_one_window` to ℂ-valued `f`.  The telescoping and per-cell
    integrability arguments are identical to the real proof; the trapezoid bookkeeping is over ℂ. -/

/-- Complex trapezoid-sum bookkeeping over `[M, N)`.  ℂ version of `trapezoid_sum_window`. -/
private lemma trapezoid_sum_window_cpow (f : ℝ → ℂ) {M N : ℕ} (hMN : M ≤ N) :
    (∑ k ∈ Finset.Ico M N, (f (k : ℝ) + f ((k : ℝ) + 1)) / 2)
      = (∑ n ∈ Finset.Ico M N, f (n : ℝ)) + (f N - f M) / 2 := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ p hp ih =>
      rw [Finset.sum_Ico_succ_top hp (fun k => (f (k : ℝ) + f ((k : ℝ) + 1)) / 2),
          Finset.sum_Ico_succ_top hp (fun n => f (n : ℝ)), ih]
      push_cast; ring

/-- **Complex first-order Euler-Maclaurin over the integer window `[M, N]`.**  ℂ version of
    `euler_maclaurin_one_window`. -/
theorem euler_maclaurin_one_window_cpow {f f' : ℝ → ℂ} (M N : ℕ) (hMN : M ≤ N)
    (hf : ∀ x ∈ Icc (M : ℝ) N, HasDerivAt f (f' x) x)
    (hf' : ∀ k ∈ Finset.Ico M N, IntervalIntegrable f' volume (k : ℝ) (k + 1)) :
    (∑ n ∈ Finset.Ico M N, f (n : ℝ))
      = (∫ x in (M : ℝ)..N, f x) - (f N - f M) / 2
        + ∫ x in (M : ℝ)..N, (sawBernoulli 1 x : ℂ) * f' x := by
  have hcell : ∀ k ∈ Finset.Ico M N, ∀ x ∈ Icc (k : ℝ) (k + 1), HasDerivAt f (f' x) x := by
    intro k hk x hx
    rw [Finset.mem_Ico] at hk
    refine hf x ⟨?_, ?_⟩
    · exact le_trans (by exact_mod_cast hk.1) hx.1
    · have : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hk.2
      linarith [hx.2]
  have hstep : ∀ k ∈ Finset.Ico M N,
      (∫ x in (k : ℝ)..(k + 1), f x)
        = (f k + f (k + 1)) / 2 - ∫ x in (k : ℝ)..(k + 1), (sawBernoulli 1 x : ℂ) * f' x := by
    intro k hk
    have hcast : (((k : ℤ)) : ℝ) = (k : ℝ) := by push_cast; ring
    have hstepZ := em_unit_step_cpow (f := f) (f' := f') (k : ℤ)
      (by intro x hx; rw [hcast] at hx; exact hcell k hk x hx)
      (by rw [hcast]; exact hf' k hk)
    simp only [hcast] at hstepZ
    exact hstepZ
  have hsum := Finset.sum_congr rfl hstep
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
  have hsawf'_cell : ∀ k ∈ Finset.Ico M N,
      IntervalIntegrable (fun x => (sawBernoulli 1 x : ℂ) * f' x) volume (k : ℝ) (k + 1) := by
    intro k hk
    have hcc : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
    have hcont : IntervalIntegrable (fun x => ((x - k - 1 / 2 : ℝ) : ℂ) * f' x) volume
        (k : ℝ) (k + 1) := (hf' k hk).continuousOn_mul (by fun_prop)
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
  have htel_saw : (∑ k ∈ Finset.Ico M N, ∫ x in (k : ℝ)..(k + 1), (sawBernoulli 1 x : ℂ) * f' x)
      = ∫ x in (M : ℝ)..N, (sawBernoulli 1 x : ℂ) * f' x := by
    have hint : ∀ k ∈ Set.Ico M N,
        IntervalIntegrable (fun x => (sawBernoulli 1 x : ℂ) * f' x) volume
          ((fun k : ℕ => (k : ℝ)) k) ((fun k : ℕ => (k : ℝ)) (k + 1)) := by
      intro k hk
      simpa [Nat.cast_succ] using hsawf'_cell k (Finset.mem_Ico.mpr hk)
    have := intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun k : ℕ => (k : ℝ)) (f := fun x => (sawBernoulli 1 x : ℂ) * f' x) (μ := volume)
      hMN hint
    simpa using this
  rw [Finset.sum_sub_distrib, htel_f, htel_saw, trapezoid_sum_window_cpow f hMN] at hsum
  -- `hsum : ∑ f = (∫ f - ∑ saw) - (∑ f + (fN - fM)/2)` rearranged; finish over ℂ.
  linear_combination -hsum

/-- The complex-power derivative on the positive reals (E1's `hasDerivAt_cpow_neg_wip`):
    `HasDerivAt (fun x:ℝ => (x:ℂ)^(-s)) (-s·(x:ℂ)^(-s-1)) x` for `x > 0` and `s ≠ 0`.
    Anchored on `hasDerivAt_ofReal_cpow_const`. -/
theorem hasDerivAt_cpow_neg {s : ℂ} (hs : s ≠ 0) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-s)) (-s * (x : ℂ) ^ (-s - 1)) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hneg : (-s : ℂ) ≠ 0 := neg_ne_zero.mpr hs
  have := hasDerivAt_ofReal_cpow_const (x := x) hx0 (r := -s) hneg
  simpa using this

/-- **Complex finite-`N` Euler-Maclaurin representation of the partial ζ sum.**  For `s : ℂ`,
    `s ≠ 0`, `N ≥ 1`, applying `euler_maclaurin_one_window_cpow` to `f x = (x:ℂ)^(-s)`:
        ∑_{n=1}^{N-1} n^{-s} = ∫_1^N x^{-s} − (N^{-s} − 1^{-s})/2
                               + ∫_1^N (sawBernoulli 1 x)·(−s·x^{−s−1}). -/
theorem em_cpow_partial {s : ℂ} (hs : s ≠ 0) {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
      = (∫ x in (1 : ℝ)..N, (x : ℂ) ^ (-s))
        - (((N : ℝ) : ℂ) ^ (-s) - ((1 : ℝ) : ℂ) ^ (-s)) / 2
        + ∫ x in (1 : ℝ)..N, (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) := by
  have hderiv : ∀ x ∈ Icc ((1 : ℕ) : ℝ) N,
      HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-s)) (-s * (x : ℂ) ^ (-s - 1)) x := by
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := by have := hx.1; push_cast at this; linarith
    exact hasDerivAt_cpow_neg hs (lt_of_lt_of_le zero_lt_one hx1)
  have hf'int : ∀ k ∈ Finset.Ico 1 N,
      IntervalIntegrable (fun x => -s * (x : ℂ) ^ (-s - 1)) volume (k : ℝ) (k + 1) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith)]
    apply ContinuousOn.mul continuousOn_const
    -- `x ↦ (x:ℂ)^(-s-1)` is continuous on `[k, k+1]` (arg bounded away from 0, in slitPlane).
    apply ContinuousOn.cpow_const
    · exact Complex.continuous_ofReal.continuousOn
    · intro x hx
      have hx1 : (1 : ℝ) ≤ x := le_trans hk1 hx.1
      exact Or.inl (by simp only [Complex.ofReal_re]; linarith)
  have hEM := euler_maclaurin_one_window_cpow (f := fun x => (x : ℂ) ^ (-s))
    (f' := fun x => -s * (x : ℂ) ^ (-s - 1)) 1 N hN hderiv hf'int
  simpa using hEM

/-! ## E2. The `N → ∞` complex representation for `Re s > 1`, tied to `riemannZeta`.

    Lift of `em_zeta_real` (Part D').  The three limits: partial sum → tsum (`summable_one_div_
    nat_cpow`), the two finite integrals → improper (`intervalIntegral_tendsto_integral_Ioi`),
    endpoint `N^{-s} → 0` (norm → 0).  Then `zeta_eq_tsum_one_div_nat_cpow` ties it to `ζ`. -/

/-- The complex `x^{-s}` is integrable on `(1, ∞)` for `Re s > 1`: its norm is `x^{-Re s}`,
    integrable there since `-Re s < -1`. -/
theorem cpow_neg_integrableOn_Ioi {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s)) (Ioi 1) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (x : ℂ) ^ (-s)) (volume.restrict (Ioi 1)) := by
    apply Measurable.aestronglyMeasurable
    exact (Complex.measurable_ofReal.pow_const _)
  have hbase : IntegrableOn (fun x : ℝ => x ^ (-s.re)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (a := -s.re) (c := (1 : ℝ)) (by linarith) (by norm_num)
  refine (integrable_norm_iff hmeas).mp ?_
  refine hbase.congr_fun ?_ measurableSet_Ioi
  intro x hx
  have hxpos : (0 : ℝ) < x := lt_trans zero_lt_one hx
  simp only [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, Complex.neg_re]

/-- The complex saw remainder integrand is integrable on `(1, ∞)` for `Re s > 1`: dominate its
    norm by `(‖s‖/2)·x^{−Re s−1}`, integrable there since `−Re s − 1 < −1`. -/
theorem em_cpow_remainder_integrableOn {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1))) (Ioi 1) := by
  have hbase : IntegrableOn (fun x : ℝ => (‖s‖ * (1 / 2)) * x ^ (-s.re - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (a := -s.re - 1) (c := (1 : ℝ)) (by linarith)
      (by norm_num)).const_mul _
  refine Integrable.mono' hbase ?_ ?_
  · apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · exact Complex.measurable_ofReal.comp (sawBernoulli_measurable 1)
    · exact measurable_const.mul (Complex.measurable_ofReal.pow_const _)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hxpos : (0 : ℝ) < x := lt_trans zero_lt_one hx
    have hsaw := abs_sawBernoulli_one_le x
    have hnormcpow : ‖(x : ℂ) ^ (-s - 1)‖ = x ^ (-s.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, Complex.sub_re, Complex.neg_re,
        Complex.one_re]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hnormcpow, norm_neg]
    have hrpownn : (0 : ℝ) ≤ x ^ (-s.re - 1) := Real.rpow_nonneg hxpos.le _
    calc |sawBernoulli 1 x| * (‖s‖ * x ^ (-s.re - 1))
        ≤ (1 / 2) * (‖s‖ * x ^ (-s.re - 1)) := by
          gcongr
      _ = (‖s‖ * (1 / 2)) * x ^ (-s.re - 1) := by ring

/-- **Complex first-order Euler-Maclaurin representation of the ζ series** (`Re s > 1`).
        ∑' n, n^{-s} = ∫_1^∞ x^{-s} + 1^{-s}/2 + ∫_1^∞ (sawBernoulli 1 x)·(−s·x^{−s−1}). -/
theorem em_zeta_cpow {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, (n : ℂ) ^ (-s))
      = (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s)) + ((1 : ℝ) : ℂ) ^ (-s) / 2
        + ∫ x in Ioi (1 : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  have hI : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s)) (Ioi 1) := cpow_neg_integrableOn_Ioi hs
  have hR := em_cpow_remainder_integrableOn hs
  have hsummable : Summable (fun n : ℕ => (n : ℂ) ^ (-s)) := by
    have hsm := (Complex.summable_one_div_nat_cpow (p := s)).mpr hs
    refine hsm.congr (fun n => ?_)
    rw [Complex.cpow_neg, one_div]
  have h0 : ((0 : ℕ) : ℂ) ^ (-s) = 0 := by
    rw [Nat.cast_zero, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
  -- LHS: partial sum over `Ico 1 N` → the tsum.
  have hLHS : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)) atTop
      (𝓝 (∑' n : ℕ, (n : ℂ) ^ (-s))) := by
    have hrange : (fun N : ℕ => ∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
        = (fun N : ℕ => ∑ n ∈ Finset.range N, (n : ℂ) ^ (-s)) := by
      funext N
      rcases Nat.eq_zero_or_pos N with hN | hN
      · subst hN; simp
      · rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive (fun n => (n : ℂ) ^ (-s))
            (Nat.zero_le 1) (by lia : 1 ≤ N), Nat.Ico_zero_eq_range, Finset.sum_range_one,
            h0, zero_add]
    rw [hrange]; exact hsummable.hasSum.tendsto_sum_nat
  -- RHS component limits.
  have hA : Tendsto (fun N : ℕ => ∫ x in (1 : ℝ)..(N : ℝ), (x : ℂ) ^ (-s)) atTop
      (𝓝 (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s))) :=
    intervalIntegral_tendsto_integral_Ioi 1 hI tendsto_natCast_atTop_atTop
  have hEnd : Tendsto (fun N : ℕ => -((((N : ℝ) : ℂ) ^ (-s) - ((1 : ℝ) : ℂ) ^ (-s)) / 2)) atTop
      (𝓝 (((1 : ℝ) : ℂ) ^ (-s) / 2)) := by
    have hz : Tendsto (fun N : ℕ => (((N : ℝ) : ℂ)) ^ (-s)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hnorm : (fun N : ℕ => ‖(((N : ℝ) : ℂ)) ^ (-s)‖)
          =ᶠ[atTop] (fun N : ℕ => (N : ℝ) ^ (-s.re)) := by
        filter_upwards [eventually_gt_atTop 0] with N hN
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hN), Complex.neg_re]
      refine Tendsto.congr' hnorm.symm ?_
      exact (tendsto_rpow_neg_atTop (y := s.re) (by linarith)).comp tendsto_natCast_atTop_atTop
    have h2 := ((hz.sub_const (((1 : ℝ) : ℂ) ^ (-s))).div_const 2).neg
    convert h2 using 2; ring
  have hRem : Tendsto
      (fun N : ℕ => ∫ x in (1 : ℝ)..(N : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
      atTop
      (𝓝 (∫ x in Ioi (1 : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))) :=
    intervalIntegral_tendsto_integral_Ioi 1 hR tendsto_natCast_atTop_atTop
  have hEq : ∀ᶠ N : ℕ in atTop, (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
      = (∫ x in (1 : ℝ)..(N : ℝ), (x : ℂ) ^ (-s))
        + -((((N : ℝ) : ℂ) ^ (-s) - ((1 : ℝ) : ℂ) ^ (-s)) / 2)
        + ∫ x in (1 : ℝ)..(N : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hp := em_cpow_partial hs0 (N := N) hN
    rw [hp]; ring
  have hRHS := (hA.add hEnd).add hRem
  have hLHS' : Tendsto (fun N : ℕ =>
      (∫ x in (1 : ℝ)..(N : ℝ), (x : ℂ) ^ (-s))
        + -((((N : ℝ) : ℂ) ^ (-s) - ((1 : ℝ) : ℂ) ^ (-s)) / 2)
        + ∫ x in (1 : ℝ)..(N : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1))) atTop
      (𝓝 (∑' n : ℕ, (n : ℂ) ^ (-s))) := hLHS.congr' hEq
  exact tendsto_nhds_unique hLHS' hRHS

/-- **Euler-Maclaurin representation of `riemannZeta`** for `Re s > 1`, via
    `zeta_eq_tsum_one_div_nat_cpow`. -/
theorem em_zeta_cpow_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s
      = (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s)) + ((1 : ℝ) : ℂ) ^ (-s) / 2
        + ∫ x in Ioi (1 : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) := by
  rw [zeta_eq_tsum_one_div_nat_cpow hs, ← em_zeta_cpow hs]
  refine tsum_congr (fun n => ?_)
  rw [Complex.cpow_neg, one_div]

/-! ## E3. K=1 analytic continuation into the critical strip (THE PRIZE).

    Define the EM closed form on `{Re s > 0}`:
        emZetaRemainder s := ∫_1^∞ (sawBernoulli 1 x)·(−s·x^{−s−1})   -- converges for Re s > 0
        emZetaClosed s     := 1/(s−1) + 1/2 + emZetaRemainder s
    For `Re s > 1`, `∫_1^∞ x^{−s} = 1/(s−1)` and `1^{−s} = 1`, so `emZetaClosed s = riemannZeta s`
    (from `em_zeta_cpow_riemannZeta`).  Both `riemannZeta` and `emZetaClosed` are analytic on
    `{Re s > 0} \ {1}`, agree on the open set `{Re s > 1}` (which has accumulation points in the
    larger strip), so by the identity theorem they agree on all of `{Re s > 0} \ {1}`.  That is
    `em_zeta_strip`, which covers the whole critical strip. -/

/-- The EM remainder integral `R(s) = ∫_1^∞ (sawBernoulli 1 x)·(−s·x^{−s−1})`.  Converges
    absolutely for `Re s > 0` (integrand norm ≤ `(‖s‖/2)·x^{−Re s−1}`). -/
noncomputable def emZetaRemainder (s : ℂ) : ℂ :=
  ∫ x in Ioi (1 : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1))

/-- The EM closed form `1/(s−1) + 1/2 + R(s)` — analytic on `{Re s > 0} \ {1}`, agreeing with
    `riemannZeta` there.  For `Re s > 1` the `1/(s−1)` is exactly `∫_1^∞ x^{−s}` and `1/2` is
    `1^{−s}/2`. -/
noncomputable def emZetaClosed (s : ℂ) : ℂ :=
  1 / (s - 1) + 1 / 2 + emZetaRemainder s

/-- The saw remainder integrand is integrable on `(1, ∞)` for the *weaker* hypothesis `Re s > 0`
    (not just `Re s > 1`): the same domination `‖·‖ ≤ (‖s‖/2)·x^{−Re s−1}` works, integrable since
    `−Re s − 1 < −1 ⇔ Re s > 0`.  This is the convergence that powers the continuation. -/
theorem em_cpow_remainder_integrableOn_strip {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1))) (Ioi 1) := by
  have hbase : IntegrableOn (fun x : ℝ => (‖s‖ * (1 / 2)) * x ^ (-s.re - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (a := -s.re - 1) (c := (1 : ℝ)) (by linarith)
      (by norm_num)).const_mul _
  refine Integrable.mono' hbase ?_ ?_
  · apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · exact Complex.measurable_ofReal.comp (sawBernoulli_measurable 1)
    · exact measurable_const.mul (Complex.measurable_ofReal.pow_const _)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hxpos : (0 : ℝ) < x := lt_trans zero_lt_one hx
    have hsaw := abs_sawBernoulli_one_le x
    have hnormcpow : ‖(x : ℂ) ^ (-s - 1)‖ = x ^ (-s.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, Complex.sub_re, Complex.neg_re,
        Complex.one_re]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hnormcpow, norm_neg]
    have hrpownn : (0 : ℝ) ≤ x ^ (-s.re - 1) := Real.rpow_nonneg hxpos.le _
    calc |sawBernoulli 1 x| * (‖s‖ * x ^ (-s.re - 1))
        ≤ (1 / 2) * (‖s‖ * x ^ (-s.re - 1)) := by gcongr
      _ = (‖s‖ * (1 / 2)) * x ^ (-s.re - 1) := by ring

/-- **Explicit remainder bound** (E3, valid for all `Re s > 0`):
        ‖emZetaRemainder s‖ ≤ ‖s‖ / (2 · Re s).
    Absolute integral bound: `‖∫‖ ≤ ∫‖·‖ ≤ (‖s‖/2)·∫_1^∞ x^{−Re s−1} = (‖s‖/2)·(1/Re s)`. -/
theorem emZetaRemainder_bound {s : ℂ} (hs : 0 < s.re) :
    ‖emZetaRemainder s‖ ≤ ‖s‖ / (2 * s.re) := by
  have hint := em_cpow_remainder_integrableOn_strip hs
  -- ‖∫‖ ≤ ∫ ‖·‖
  have hbound1 : ‖emZetaRemainder s‖
      ≤ ∫ x in Ioi (1 : ℝ), ‖(sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1))‖ :=
    norm_integral_le_integral_norm _
  -- pointwise: ‖·‖ ≤ (‖s‖/2)·x^{−Re s−1}
  have hdom : IntegrableOn (fun x : ℝ => (‖s‖ * (1 / 2)) * x ^ (-s.re - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (a := -s.re - 1) (c := (1 : ℝ)) (by linarith)
      (by norm_num)).const_mul _
  have hptwise : ∀ x ∈ Ioi (1 : ℝ),
      ‖(sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1))‖
        ≤ (‖s‖ * (1 / 2)) * x ^ (-s.re - 1) := by
    intro x hx
    have hxpos : (0 : ℝ) < x := lt_trans zero_lt_one hx
    have hsaw := abs_sawBernoulli_one_le x
    have hnormcpow : ‖(x : ℂ) ^ (-s - 1)‖ = x ^ (-s.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, Complex.sub_re, Complex.neg_re,
        Complex.one_re]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hnormcpow, norm_neg]
    have hrpownn : (0 : ℝ) ≤ x ^ (-s.re - 1) := Real.rpow_nonneg hxpos.le _
    calc |sawBernoulli 1 x| * (‖s‖ * x ^ (-s.re - 1))
        ≤ (1 / 2) * (‖s‖ * x ^ (-s.re - 1)) := by gcongr
      _ = (‖s‖ * (1 / 2)) * x ^ (-s.re - 1) := by ring
  have hbound2 : (∫ x in Ioi (1 : ℝ), ‖(sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1))‖)
      ≤ ∫ x in Ioi (1 : ℝ), (‖s‖ * (1 / 2)) * x ^ (-s.re - 1) := by
    apply setIntegral_mono_on hint.norm hdom measurableSet_Ioi hptwise
  -- closed form of the dominating integral: (‖s‖/2)·∫ x^{−σ−1} = (‖s‖/2)·(1/σ)
  have hclosed : (∫ x in Ioi (1 : ℝ), (‖s‖ * (1 / 2)) * x ^ (-s.re - 1))
      = ‖s‖ / (2 * s.re) := by
    rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (a := -s.re - 1) (by linarith)
      (by norm_num : (0:ℝ) < 1)]
    have hexp : (-s.re - 1 + 1) = -s.re := by ring
    rw [hexp, Real.one_rpow]
    have hne : s.re ≠ 0 := ne_of_gt hs
    field_simp
  calc ‖emZetaRemainder s‖ ≤ _ := hbound1
    _ ≤ _ := hbound2
    _ = ‖s‖ / (2 * s.re) := hclosed

/-- For `Re s > 1`, `emZetaClosed s = riemannZeta s` (unconditional identity in the region of
    convergence).  The `1/(s−1)` is `∫_1^∞ x^{−s}` and `1/2` is `1^{−s}/2`. -/
theorem emZetaClosed_eq_riemannZeta_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    emZetaClosed s = riemannZeta s := by
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at hs; simp at hs
  -- ∫_1^∞ x^{−s} = 1/(s−1)
  have hIntClosed : (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s)) = 1 / (s - 1) := by
    have hI := integral_Ioi_cpow_of_lt (a := -s) (by rw [Complex.neg_re]; linarith)
      (c := (1 : ℝ)) (by norm_num)
    rw [hI, Complex.ofReal_one, Complex.one_cpow]
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    rw [div_eq_div_iff (by simpa [neg_add_eq_sub] using sub_ne_zero.mpr (Ne.symm hs1)) hs1']
    ring
  have hone : ((1 : ℝ) : ℂ) ^ (-s) = 1 := by
    rw [Complex.ofReal_one, Complex.one_cpow]
  rw [emZetaClosed, emZetaRemainder, em_zeta_cpow_riemannZeta hs, hIntClosed, hone]

/-! ### E3 helpers for the analytic continuation. -/

/-- Elementary global bound `log x ≤ x^δ / δ` for `x ≥ 1`, `δ > 0` (log grows slower than any
    positive power).  `δ·log x = log(x^δ) ≤ x^δ − 1 ≤ x^δ`. -/
theorem log_le_rpow_div {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ x ^ δ / δ := by
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hlog : δ * Real.log x = Real.log (x ^ δ) := (Real.log_rpow hxpos δ).symm
  have hxδpos : (0 : ℝ) < x ^ δ := Real.rpow_pos_of_pos hxpos δ
  have hle : Real.log (x ^ δ) ≤ x ^ δ - 1 := Real.log_le_sub_one_of_pos hxδpos
  rw [le_div_iff₀ hδ]
  calc Real.log x * δ = δ * Real.log x := by ring
    _ = Real.log (x ^ δ) := hlog
    _ ≤ x ^ δ - 1 := hle
    _ ≤ x ^ δ := by linarith

/-- The `s`-derivative of the EM remainder integrand at fixed real `x > 0`:
        ∂_s [ ↑(saw x)·(−s·x^{−s−1}) ] = ↑(saw x)·((−1 + s·log(x:ℂ))·x^{−s−1}).
    From `HasDerivAt.const_cpow` (derivative in the exponent) and the product/const-mul rules. -/
theorem hasDerivAt_emIntegrand (x : ℝ) (hx : 0 < x) (s : ℂ) :
    HasDerivAt (fun s : ℂ => (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
      ((sawBernoulli 1 x : ℂ) * ((-1 + s * Complex.log (x : ℂ)) * (x : ℂ) ^ (-s - 1))) s := by
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx
  -- exponent map e s = -s - 1, derivative -1.
  have he : HasDerivAt (fun s : ℂ => -s - 1) (-1) s := by
    simpa using ((hasDerivAt_id s).neg.sub_const (1 : ℂ))
  -- (x:ℂ)^(e s) via const_cpow: derivative (x:ℂ)^(e s)·log(x:ℂ)·(-1).
  have hcpow : HasDerivAt (fun s : ℂ => (x : ℂ) ^ (-s - 1))
      ((x : ℂ) ^ (-s - 1) * Complex.log (x : ℂ) * (-1)) s :=
    he.const_cpow (Or.inl hxc)
  -- -s, derivative -1.
  have hlin : HasDerivAt (fun s : ℂ => -s) (-1) s := (hasDerivAt_id s).neg
  -- product (-s)·(x:ℂ)^(e s), then const-mul by ↑(saw x); package as the target function.
  have hfull : HasDerivAt (fun s : ℂ => (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
      ((sawBernoulli 1 x : ℂ)
        * (-1 * (x : ℂ) ^ (-s - 1) + -s * ((x : ℂ) ^ (-s - 1) * Complex.log (x : ℂ) * -1))) s :=
    (hlin.mul hcpow).const_mul (sawBernoulli 1 x : ℂ)
  -- reconcile the derivative value algebraically.
  have hval : (sawBernoulli 1 x : ℂ)
        * (-1 * (x : ℂ) ^ (-s - 1) + -s * ((x : ℂ) ^ (-s - 1) * Complex.log (x : ℂ) * -1))
      = (sawBernoulli 1 x : ℂ) * ((-1 + s * Complex.log (x : ℂ)) * (x : ℂ) ^ (-s - 1)) := by
    ring
  rw [hval] at hfull
  exact hfull

/-- Integrability on `(1,∞)` of the dominating bound `C · x^{−σ−1} + D · x^{δ−σ−1}` used for
    differentiation under the integral, when `0 < δ < σ` (so both exponents are `< −1`). -/
private theorem bound_integrableOn {C D σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) (hδσ : δ < σ) :
    IntegrableOn (fun x : ℝ => C * x ^ (-σ - 1) + D * x ^ (δ - σ - 1)) (Ioi 1) := by
  have h1 : IntegrableOn (fun x : ℝ => C * x ^ (-σ - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (a := -σ - 1) (by linarith) (by norm_num : (0:ℝ) < 1)).const_mul _
  have h2 : IntegrableOn (fun x : ℝ => D * x ^ (δ - σ - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (a := δ - σ - 1) (by linarith) (by norm_num : (0:ℝ) < 1)).const_mul _
  exact h1.add h2

/-- **The EM remainder integral is complex-differentiable on `{Re s > 0}`** (E3 analytic core).
    Differentiation under the integral sign via `hasDerivAt_integral_of_dominated_loc_of_deriv_le`,
    with the local uniform domination `‖∂_s integrand‖ ≤ bound x` on a ball inside the half-plane
    and `bound` integrable by `bound_integrableOn`. -/
theorem emZetaRemainder_hasDerivAt {s₀ : ℂ} (hs₀ : 0 < s₀.re) :
    HasDerivAt emZetaRemainder
      (∫ x in Ioi (1 : ℝ),
        (sawBernoulli 1 x : ℂ) * ((-1 + s₀ * Complex.log (x : ℂ)) * (x : ℂ) ^ (-s₀ - 1))) s₀ := by
  set σ : ℝ := s₀.re / 2 with hσdef
  set ε : ℝ := s₀.re / 2 with hεdef
  set δ : ℝ := σ / 2 with hδdef
  have hσpos : 0 < σ := by rw [hσdef]; linarith
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδσ : δ < σ := by rw [hδdef]; linarith
  -- The ball `s` region and the re-lower-bound on it.
  set S : Set ℂ := Metric.ball s₀ ε with hSdef
  have hS_nhds : S ∈ 𝓝 s₀ := Metric.ball_mem_nhds s₀ hεpos
  have hre_lb : ∀ s ∈ S, σ ≤ s.re := by
    intro s hs
    rw [hSdef, Metric.mem_ball] at hs
    have h1 : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
      simpa using Complex.abs_re_le_norm (s - s₀)
    have h2 : ‖s - s₀‖ < ε := by rwa [Complex.dist_eq] at hs
    have : |s.re - s₀.re| < ε := lt_of_le_of_lt h1 h2
    have := (abs_lt.mp this).1
    rw [hσdef, hεdef]; rw [hεdef] at this; linarith
  -- Integrand F and derivative F'.
  set F : ℂ → ℝ → ℂ := fun s x => (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) with hFdef
  set F' : ℂ → ℝ → ℂ := fun s x =>
    (sawBernoulli 1 x : ℂ) * ((-1 + s * Complex.log (x : ℂ)) * (x : ℂ) ^ (-s - 1)) with hF'def
  -- The dominating bound.
  set bnd : ℝ → ℝ := fun x => (1 / 2) * x ^ (-σ - 1)
    + ((1 / 2) * (‖s₀‖ + ε) * (1 / δ)) * x ^ (δ - σ - 1) with hbnddef
  -- (a) measurability of F near s₀
  have hF_meas : ∀ᶠ s in 𝓝 s₀, AEStronglyMeasurable (F s) (volume.restrict (Ioi 1)) := by
    filter_upwards with s
    apply Measurable.aestronglyMeasurable
    rw [hFdef]
    exact (Complex.measurable_ofReal.comp (sawBernoulli_measurable 1)).mul
      (measurable_const.mul (Complex.measurable_ofReal.pow_const _))
  -- (b) F s₀ integrable
  have hF_int : Integrable (F s₀) (volume.restrict (Ioi 1)) :=
    em_cpow_remainder_integrableOn_strip hs₀
  -- (c) F' s₀ measurable
  have hF'_meas : AEStronglyMeasurable (F' s₀) (volume.restrict (Ioi 1)) := by
    apply Measurable.aestronglyMeasurable
    rw [hF'def]
    apply (Complex.measurable_ofReal.comp (sawBernoulli_measurable 1)).mul
    apply Measurable.mul
    · exact measurable_const.add (measurable_const.mul
        (Complex.measurable_log.comp Complex.measurable_ofReal))
    · exact Complex.measurable_ofReal.pow_const _
  -- (d) uniform bound on S
  have h_bound : ∀ᵐ x ∂(volume.restrict (Ioi 1)), ∀ s ∈ S, ‖F' s x‖ ≤ bnd x := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx s hs
    have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
    have hsre : σ ≤ s.re := hre_lb s hs
    have hslt : ‖s‖ ≤ ‖s₀‖ + ε := by
      have : ‖s - s₀‖ < ε := by rw [hSdef, Metric.mem_ball, Complex.dist_eq] at hs; exact hs
      calc ‖s‖ = ‖s₀ + (s - s₀)‖ := by ring_nf
        _ ≤ ‖s₀‖ + ‖s - s₀‖ := norm_add_le _ _
        _ ≤ ‖s₀‖ + ε := by linarith
    -- ‖F' s x‖ = |saw|·‖(-1 + s log x)·x^{-s-1}‖ ≤ (1/2)·(1 + ‖s‖ log x)·x^{-σ-1}
    have hlogeq : Complex.log (x : ℂ) = ((Real.log x : ℝ) : ℂ) := (Complex.ofReal_log hxpos.le).symm
    have hnormcpow : ‖(x : ℂ) ^ (-s - 1)‖ = x ^ (-s.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, Complex.sub_re, Complex.neg_re,
        Complex.one_re]
    have hlognn : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hcpownn : (0 : ℝ) ≤ x ^ (-s.re - 1) := Real.rpow_nonneg hxpos.le _
    have hsaw := abs_sawBernoulli_one_le x
    -- factor bound
    have hfac : ‖(-1 + s * Complex.log (x : ℂ)) * (x : ℂ) ^ (-s - 1)‖
        ≤ (1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1) := by
      rw [norm_mul, hnormcpow]
      gcongr
      calc ‖(-1 + s * Complex.log (x : ℂ))‖
          ≤ ‖(-1 : ℂ)‖ + ‖s * Complex.log (x : ℂ)‖ := norm_add_le _ _
        _ = 1 + ‖s‖ * ‖Complex.log (x : ℂ)‖ := by rw [norm_mul]; norm_num
        _ = 1 + ‖s‖ * Real.log x := by
            rw [hlogeq, Complex.norm_real, Real.norm_of_nonneg hlognn]
    -- log bound: log x ≤ x^δ / δ
    have hlogbd : Real.log x ≤ x ^ δ / δ := log_le_rpow_div hδpos hx1
    have hxδdivnn : (0 : ℝ) ≤ x ^ δ / δ := by positivity
    have hs₀εnn : (0 : ℝ) ≤ ‖s₀‖ + ε := by positivity
    have hexpmono : x ^ (-s.re - 1) ≤ x ^ (-σ - 1) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hcpowσnn : (0 : ℝ) ≤ x ^ (-σ - 1) := Real.rpow_nonneg hxpos.le _
    rw [hF'def, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |sawBernoulli 1 x| * ‖(-1 + s * Complex.log (x : ℂ)) * (x : ℂ) ^ (-s - 1)‖
        ≤ (1 / 2) * ((1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1)) := by
          gcongr
      _ ≤ (1 / 2) * ((1 + (‖s₀‖ + ε) * (x ^ δ / δ)) * x ^ (-σ - 1)) := by
          gcongr
      _ = bnd x := by
          have hxadd : x ^ (δ - σ - 1) = x ^ δ * x ^ (-σ - 1) := by
            rw [← Real.rpow_add hxpos]; congr 1; ring
          have hδne : δ ≠ 0 := ne_of_gt hδpos
          simp only [hbnddef, hxadd]
          field_simp
  -- Assemble via the parametric-integral differentiation lemma.
  have hbnd_int : Integrable bnd (volume.restrict (Ioi 1)) := by
    rw [hbnddef]
    exact bound_integrableOn (C := 1 / 2) (D := (1 / 2) * (‖s₀‖ + ε) * (1 / δ))
      hσpos hδpos hδσ
  have h_diff : ∀ᵐ x ∂(volume.restrict (Ioi 1)), ∀ s ∈ S, HasDerivAt (fun s => F s x) (F' s x) s := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx s _
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one (le_of_lt hx)
    exact hasDerivAt_emIntegrand x hxpos s
  obtain ⟨_, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := bnd) (F := F) (F' := F') hS_nhds hF_meas hF_int hF'_meas h_bound hbnd_int h_diff
  exact hderiv

/-- `emZetaRemainder` is differentiable at every `s` with `Re s > 0`. -/
theorem emZetaRemainder_differentiableAt {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ emZetaRemainder s :=
  (emZetaRemainder_hasDerivAt hs).differentiableAt

/-! ### The critical-strip half-plane, slit at `1`, is preconnected. -/

/-- The open right half-plane `{Re s > 0}`. -/
def rightHalfPlane : Set ℂ := {s : ℂ | 0 < s.re}

/-- The half-plane slit at `1` is preconnected: cover by four convex half-space intersections
    (im>0, im<0, re<1, re>1), each avoiding `1` (whose im=0, re=1), chained by shared points. -/
theorem isPreconnected_rightHalfPlane_diff_one :
    IsPreconnected (rightHalfPlane \ {1}) := by
  have hHconv : Convex ℝ rightHalfPlane := convex_halfSpace_re_gt 0
  -- Four convex pieces.
  set U₁ : Set ℂ := rightHalfPlane ∩ {s : ℂ | 0 < s.im} with hU₁
  set U₂ : Set ℂ := rightHalfPlane ∩ {s : ℂ | s.im < 0} with hU₂
  set U₃ : Set ℂ := rightHalfPlane ∩ {s : ℂ | s.re < 1} with hU₃
  set U₄ : Set ℂ := rightHalfPlane ∩ {s : ℂ | 1 < s.re} with hU₄
  have pc₁ : IsPathConnected U₁ :=
    (hHconv.inter (convex_halfSpace_im_gt 0)).isPathConnected ⟨1 + I, by
      constructor <;> simp [rightHalfPlane]⟩
  have pc₂ : IsPathConnected U₂ :=
    (hHconv.inter (convex_halfSpace_im_lt 0)).isPathConnected ⟨1 - I, by
      constructor <;> simp [rightHalfPlane]⟩
  have pc₃ : IsPathConnected U₃ :=
    (hHconv.inter (convex_halfSpace_re_lt 1)).isPathConnected ⟨1/2, by
      constructor <;> simp [rightHalfPlane] <;> norm_num⟩
  have pc₄ : IsPathConnected U₄ :=
    (hHconv.inter (convex_halfSpace_re_gt 1)).isPathConnected ⟨2, by
      constructor <;> simp [rightHalfPlane] <;> norm_num⟩
  -- Shared points to chain: (U₃∪U₄ region) ∪ (U₁) ∪ (U₂).
  -- First glue U₃ and U₁ via 1/2 + I; then that with U₂ via 1/2 - I; then with U₄ via 2 - I... but
  -- U₄ meets U₂ via 2 - I.  Chain: ((U₃ ∪ U₁) ∪ U₂) ∪ U₄.
  have g31 : IsPathConnected (U₃ ∪ U₁) :=
    pc₃.union pc₁ ⟨1/2 + I, by
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp [rightHalfPlane] <;> norm_num⟩
  have g312 : IsPathConnected ((U₃ ∪ U₁) ∪ U₂) :=
    g31.union pc₂ ⟨1/2 - I, by
      refine ⟨Or.inl ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp [rightHalfPlane] <;> norm_num⟩
  have g3124 : IsPathConnected (((U₃ ∪ U₁) ∪ U₂) ∪ U₄) :=
    g312.union pc₄ ⟨2 - I, by
      refine ⟨Or.inr ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp [rightHalfPlane] <;> norm_num⟩
  -- The union equals `H \ {1}`.
  have hcover : ((U₃ ∪ U₁) ∪ U₂) ∪ U₄ = rightHalfPlane \ {1} := by
    ext z
    simp only [hU₁, hU₂, hU₃, hU₄, Set.mem_union, Set.mem_inter_iff, Set.mem_diff,
      Set.mem_singleton_iff, Set.mem_setOf_eq, rightHalfPlane]
    constructor
    · rintro (((⟨hz, _⟩ | ⟨hz, _⟩) | ⟨hz, _⟩) | ⟨hz, _⟩) <;>
        exact ⟨hz, by
          rintro rfl <;> simp_all⟩
    · rintro ⟨hz, hz1⟩
      by_cases him : z.im = 0
      · -- on real axis, re ≠ 1
        have hre1 : z.re ≠ 1 := by
          intro h; exact hz1 (by apply Complex.ext <;> simp [h, him])
        rcases lt_or_gt_of_ne hre1 with h | h
        · exact Or.inl (Or.inl (Or.inl ⟨hz, h⟩))
        · exact Or.inr ⟨hz, h⟩
      · rcases lt_or_gt_of_ne him with h | h
        · exact Or.inl (Or.inr ⟨hz, h⟩)
        · exact Or.inl (Or.inl (Or.inr ⟨hz, h⟩))
  rw [← hcover]
  exact g3124.isConnected.isPreconnected

/-! ### E3 capstone: the identity theorem transfer. -/

/-- `emZetaClosed` is analytic on the slit half-plane `{Re s > 0} \ {1}`. -/
theorem emZetaClosed_analyticOnNhd :
    AnalyticOnNhd ℂ emZetaClosed (rightHalfPlane \ {1}) := by
  apply DifferentiableOn.analyticOnNhd _ ?_
  · intro s hs
    have hs0 : 0 < s.re := hs.1
    have hs1 : s ≠ 1 := by simpa using hs.2
    have hpole : DifferentiableAt ℂ (fun s : ℂ => 1 / (s - 1)) s := by
      apply DifferentiableAt.div (differentiableAt_const _)
        ((differentiableAt_id).sub (differentiableAt_const _))
      exact sub_ne_zero.mpr hs1
    have hrem : DifferentiableAt ℂ emZetaRemainder s := emZetaRemainder_differentiableAt hs0
    have : DifferentiableAt ℂ emZetaClosed s := by
      unfold emZetaClosed
      exact (hpole.add (differentiableAt_const _)).add hrem
    exact this.differentiableWithinAt
  · -- the slit half-plane is open
    apply IsOpen.sdiff _ isClosed_singleton
    exact (isOpen_lt continuous_const Complex.continuous_re)

/-- `riemannZeta` is analytic on the slit half-plane `{Re s > 0} \ {1}` (it is analytic on all of
    `{1}ᶜ`). -/
theorem riemannZeta_analyticOnNhd_strip :
    AnalyticOnNhd ℂ riemannZeta (rightHalfPlane \ {1}) := by
  apply DifferentiableOn.analyticOnNhd _ ?_
  · intro s hs
    have hs1 : s ≠ 1 := by simpa using hs.2
    exact (differentiableAt_riemannZeta hs1).differentiableWithinAt
  · apply IsOpen.sdiff _ isClosed_singleton
    exact (isOpen_lt continuous_const Complex.continuous_re)

/-- **THE PRIZE (E3): K=1 analytic continuation of the Euler-Maclaurin representation of ζ into
    the critical strip.**  For every `s` with `0 < Re s` and `s ≠ 1`,
        riemannZeta s = 1/(s−1) + 1/2 + ∫_1^∞ (sawBernoulli 1 x)·(−s·x^{−s−1}) dx,
    with the remainder integral converging absolutely and bounded by `‖s‖/(2·Re s)`
    (`emZetaRemainder_bound`).  This covers the entire critical strip `0 < Re s < 1`.

    Proof: both sides are analytic on the (preconnected) slit half-plane and agree on the open
    subset `{Re s > 1}` (where the series converges), so by the identity theorem
    (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, anchored at `s = 2`) they agree on the
    whole slit half-plane. -/
theorem em_zeta_strip {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s
      = 1 / (s - 1) + 1 / 2
        + ∫ x in Ioi (1 : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) := by
  -- reduce to `emZetaClosed s = riemannZeta s`.
  suffices h : Set.EqOn emZetaClosed riemannZeta (rightHalfPlane \ {1}) by
    have hmem : s ∈ rightHalfPlane \ {1} := ⟨hs, by simpa using hs1⟩
    have heq := h hmem
    rw [emZetaClosed, emZetaRemainder] at heq
    exact heq.symm
  -- identity theorem, anchored at s = 2.
  have h2mem : (2 : ℂ) ∈ rightHalfPlane \ {1} := by
    refine ⟨?_, ?_⟩ <;> simp [rightHalfPlane]
  have hevent : emZetaClosed =ᶠ[𝓝 (2 : ℂ)] riemannZeta := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hnhds : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      hopen.mem_nhds (by simp)
    filter_upwards [hnhds] with z hz
    exact emZetaClosed_eq_riemannZeta_of_one_lt hz
  exact emZetaClosed_analyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    riemannZeta_analyticOnNhd_strip isPreconnected_rightHalfPlane_diff_one h2mem hevent

/-! ## E4. Evaluator-facing enclosure (the A4 `checkBand` consumer shape).

    The A4 interval evaluator needs: an EXPLICIT finite part it can box with `DIntv` arithmetic,
    plus a RATIONAL error envelope on the (unevaluated) remainder.  `em_zeta_strip` already
    delivers exactly this at `K = 1`: the finite part is the elementary closed form
    `1/(s−1) + 1/2` (a reciprocal + a constant — directly boxable), and the remainder envelope is
    `‖s‖/(2·Re s)`.  We package it as a single norm enclosure, and give the `σ = 1/2 + it`
    critical-line specialization (the band the evaluator sweeps).

    Interface for A4 (`DIntvDef.DIntv.memR`): supplied dyadic-interval enclosures of `Re(1/(s−1))`,
    `Im(1/(s−1))`, the constant `1/2`, and the scalar envelope `‖s‖/(2·Re s)`, the evaluator boxes
    `Re(ζ s)` and `Im(ζ s)` within
        [Re(finite) − env, Re(finite) + env]  ×  [Im(finite) − env, Im(finite) + env].
    (`stirlingFinite`-style, mirroring `StirlingBinet.logDeriv_gammaR_enclosure`.) -/

/-- **The explicit finite part** of the `K = 1` EM enclosure of `ζ` on the strip: `1/(s−1) + 1/2`.
    Elementary (one reciprocal + a constant) — directly boxable by the `DIntv` evaluator, no `ζ`,
    no integral. -/
noncomputable def emZetaFinite (s : ℂ) : ℂ := 1 / (s - 1) + 1 / 2

/-- **THE ζ ENCLOSURE (A4 `checkBand` consumer, `K = 1`).**  For `0 < Re s`, `s ≠ 1`, the true
    `ζ(s)` differs from the explicit finite part `emZetaFinite s` by at most the rational envelope
    `‖s‖/(2·Re s)`:
        ‖riemannZeta s − emZetaFinite s‖ ≤ ‖s‖ / (2·Re s).
    This is the statement the interval evaluator instantiates: box `emZetaFinite s` with `DIntv`
    reciprocal+add, then widen by the envelope. -/
theorem em_zeta_strip_enclosure {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s - emZetaFinite s‖ ≤ ‖s‖ / (2 * s.re) := by
  have hstrip := em_zeta_strip hs hs1
  have hdiff : riemannZeta s - emZetaFinite s = emZetaRemainder s := by
    rw [hstrip, emZetaFinite, emZetaRemainder]; ring
  rw [hdiff]
  exact emZetaRemainder_bound hs

/-- **Real-part enclosure** (the evaluator boxes `Re(ζ s)`): `|Re(ζ s) − Re(emZetaFinite s)|` lies
    within the rational envelope.  Mirrors `StirlingBinet.re_logDeriv_gammaR_enclosure`. -/
theorem re_em_zeta_strip_enclosure {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    |(riemannZeta s).re - (emZetaFinite s).re| ≤ ‖s‖ / (2 * s.re) := by
  have h := em_zeta_strip_enclosure hs hs1
  rw [show (riemannZeta s).re - (emZetaFinite s).re
        = (riemannZeta s - emZetaFinite s).re from (Complex.sub_re _ _).symm]
  exact le_trans (Complex.abs_re_le_norm _) h

/-- **Imaginary-part enclosure** (the evaluator boxes `Im(ζ s)`).  Mirrors
    `StirlingBinet.im_logDeriv_gammaR_enclosure`. -/
theorem im_em_zeta_strip_enclosure {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    |(riemannZeta s).im - (emZetaFinite s).im| ≤ ‖s‖ / (2 * s.re) := by
  have h := em_zeta_strip_enclosure hs hs1
  rw [show (riemannZeta s).im - (emZetaFinite s).im
        = (riemannZeta s - emZetaFinite s).im from (Complex.sub_im _ _).symm]
  exact le_trans (Complex.abs_im_le_norm _) h

/-- **Critical-line specialization** (the `σ = 1/2` band the A4 evaluator sweeps).  For `s = 1/2 + it`
    with real `t`, `s ≠ 1` automatically (`Re s = 1/2 < 1`), and the envelope is
    `‖1/2 + it‖ / (2·(1/2)) = ‖1/2 + it‖`.  This is the ζ-band enclosure `checkBand` consumes on the
    critical line. -/
theorem em_zeta_critical_line_enclosure (t : ℝ) :
    ‖riemannZeta ((1 / 2 : ℂ) + t * I) - emZetaFinite ((1 / 2 : ℂ) + t * I)‖
      ≤ ‖(1 / 2 : ℂ) + t * I‖ / (2 * (1 / 2)) := by
  have hre : ((1 / 2 : ℂ) + t * I).re = 1 / 2 := by
    simp [Complex.add_re, Complex.mul_re, Complex.div_re]
  have hs : 0 < ((1 / 2 : ℂ) + t * I).re := by rw [hre]; norm_num
  have hs1 : (1 / 2 : ℂ) + t * I ≠ 1 := by
    intro h
    have : ((1 / 2 : ℂ) + t * I).re = (1 : ℂ).re := by rw [h]
    rw [hre] at this; simp at this
  have h := em_zeta_strip_enclosure hs hs1
  rw [hre] at h
  exact h

end M6gap.ZetaReflection
