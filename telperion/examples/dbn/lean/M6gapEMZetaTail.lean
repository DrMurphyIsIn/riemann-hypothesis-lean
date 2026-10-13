/-  EMZetaTail.lean -- A2 Theorem 1, TAIL track: the order-K Euler-Maclaurin tail engine.

    M6GAP CROSS-PIN PORT (lane m6gap, 2026-09-23): a copy of
    telperion/examples/zeta_reflection/lean/EMZetaTail.lean (Lean v4.32.0, Mathlib v4.32.0) onto the dbn
    island (Lean v4.34.0-rc1, Mathlib de5ce8a9).  The ONLY edits are: module names prefixed `M6gap`
    in the imports, every namespace prefixed `M6gap.` (so no declaration can clash with a sibling
    lane's port), and comment wording on this island's word-level placeholder scan.  No proof was
    changed.  Consumed by M6gapHeightFloor (the 55/16 height floor on this island).


    The blocker of PROGRAM ANDÚRIL's reflection track.  Builds on `EMZeta.lean` /
    `EMZetaComplex.lean` (the K=1 chain).  The K=1 remainder envelope `‖s‖/(2·Re s)` proven in
    `EMZetaComplex.em_zeta_strip_enclosure` is sign-LOOSE (≈14 at s=1/2+14i), so the G2 reflected
    band could not be made sign-tight from it.  This file raises the Euler-Maclaurin order and cuts
    the sum at a finite `N`, producing a remainder that DECAYS like `N^{-Re s - K + 1}`, small enough
    to make `gLine` boxes sign-tight.

    Architecture (bottom-up), ALL kernel-clean (AxiomGuardEMTail):

      F.  Order-2/3 periodized "saw" Bernoulli sup bounds: `|sawBernoulli 2| ≤ 1/6`,
          `|sawBernoulli 3| ≤ 1/12` (via `B₃ = y(1−y)(1/2−y)`), and `bernoulliFun_three` closed form.
      G.  `em_saw_step` — the one IBP step raising the saw order by one over a unit cell (the proven
          form of `EMZetaWip.em_saw_step_wip`), via the continuous polynomial surrogate
          `B_{k+1}(x−m)/(k+1)`.  Endpoint saw values `B_{k+1}(0)`, `B_{k+1}(1)` (equal for `k+1≠1`).
      G'. `em_saw_step_window` — sum `em_saw_step` over `[M,N]`; interior boundary terms telescope
          (`bernoulliFun_endpoints_eq_of_ne_one`), leaving only `B_{k+1}(0)(fk N − fk M)/(k+1)`.
      H.  `em_tail_integral_bound` — the reusable engine: `‖∫_N^∞ saw_k · c·x^{−s−k}‖`
          ≤ `B·‖c‖·N^{−(Re s+k−1)}/(Re s+k−1)`, the `N`-decay that makes gLine boxes sign-tight.
      I.  `em_tail3_bound` (order-3, `B = 1/12`) and `em_tail3_number` — THE NUMBER: at the G2 pilot
          `s = 1/2 + 14i`, `N = 200`, the order-3 remainder is `≤ 10⁻³` (kernel-decided).  Clears the
          go/no-go the K=1 envelope `‖s‖/(2·Re s) ≈ 14` failed.

    REMAINING for the full ζ-order-K identity (handoff): tie `em_saw_step_window` to `riemannZeta` by
    raising the K=1 remainder `∫_1^∞ saw₁·(−s x^{−s−1})` (from `EMZetaComplex.em_zeta_strip`) to
    order 3 over `[N,∞)` — apply `em_saw_step_window` on `[N,M]` (complex cpow orders 2,3, derivative
    coefficients `s(s+1)…`), then `M → ∞` (boundary terms → 0; integral → `∫_N^∞`), reusing the
    `intervalIntegral_tendsto_integral_Ioi` limit pattern from `em_zeta_cpow`.  The remainder BOUND at
    the endpoint is already `em_tail3_bound`; only the identity plumbing remains.

    conjecture1_proved = False.  This is a classical analysis lemma (Euler-Maclaurin tail bound),
    NOT a proof of RH.
-/
import M6gapEMZeta
import M6gapEMZetaComplex

open MeasureTheory intervalIntegral Set Filter Topology Complex
open scoped Real

namespace M6gap.ZetaReflection

/-! ## F. Order-k periodized Bernoulli: derivative tower and explicit sup bounds. -/

/-- The order-2 saw on the cell `[m, m+1)` is `(x - m)^2 - (x - m) + 1/6`. -/
lemma sawBernoulli_two_eq_on_Ico {m : ℤ} {x : ℝ} (hx : x ∈ Ico (m : ℝ) (m + 1)) :
    sawBernoulli 2 x = (x - m) ^ 2 - (x - m) + 6⁻¹ := by
  rw [sawBernoulli_eq_on_Ico 2 hx, bernoulliFun_two]

/-- Explicit sup bound for the order-2 saw: `|sawBernoulli 2 x| ≤ 1/6`.
    On the unit cell `y := {x} ∈ [0,1)`, `B₂(y) = y² − y + 1/6 = (y − 1/2)² − 1/12 ∈ [−1/12, 1/6]`. -/
lemma abs_sawBernoulli_two_le (x : ℝ) : |sawBernoulli 2 x| ≤ 1 / 6 := by
  have h0 : (0 : ℝ) ≤ Int.fract x := Int.fract_nonneg x
  have h1 : Int.fract x < 1 := Int.fract_lt_one x
  rw [sawBernoulli, bernoulliFun_two, abs_le]
  constructor <;> nlinarith [sq_nonneg (Int.fract x - 1/2), h0, h1]

/-- The order-3 saw on `[0,1)` in closed form: `B₃(y) = y³ − (3/2)y² + (1/2)y`
    (`bernoulli 3 = 0` kills the constant term). -/
lemma bernoulliFun_three (y : ℝ) :
    bernoulliFun 3 y = y ^ 3 - (3/2) * y ^ 2 + (1/2) * y := by
  have h3zero : bernoulli 3 = 0 := bernoulli_eq_zero_of_odd (by decide) (by norm_num)
  simp only [bernoulliFun, Polynomial.bernoulli_def, Finset.sum_range_succ, Finset.sum_range_zero]
  simp [Polynomial.eval_finset_sum, h3zero]
  ring

/-- Explicit sup bound for the order-3 saw: `|sawBernoulli 3 x| ≤ 1/12`.
    `B₃(y) = y(1−y)(1/2−y)` on `[0,1)`; its exact extrema are `±√3/36 ≈ ±0.0481`, so the clean
    rational envelope `1/12 ≈ 0.083` (nlinarith-certifiable) is a valid — and, at the tail cut
    `N ≥ 50`, sign-tight — bound.  See the reported remainder number in the module header. -/
lemma abs_sawBernoulli_three_le (x : ℝ) : |sawBernoulli 3 x| ≤ 1 / 12 := by
  have h0 : (0 : ℝ) ≤ Int.fract x := Int.fract_nonneg x
  have h1 : Int.fract x < 1 := Int.fract_lt_one x
  set y := Int.fract x with hy
  have hy1 : y ≤ 1 := le_of_lt h1
  rw [sawBernoulli, bernoulliFun_three, abs_le]
  refine ⟨?_, ?_⟩
  · nlinarith [mul_nonneg h0 (sub_nonneg.mpr hy1), sq_nonneg (2*y-1),
      mul_nonneg (mul_nonneg h0 (sub_nonneg.mpr hy1)) (sq_nonneg (2*y-1))]
  · nlinarith [mul_nonneg h0 (sub_nonneg.mpr hy1), sq_nonneg (2*y-1),
      mul_nonneg (mul_nonneg h0 (sub_nonneg.mpr hy1)) (sq_nonneg (2*y-1))]

/-! ## G. The saw-order-raising IBP step over a unit cell.

    The antiderivative tower: `sawBernoulli (k+1) / (k+1)` has derivative `sawBernoulli k` on the
    OPEN cell `(m, m+1)` (from `antideriv_bernoulliFun`, since `Int.fract` has derivative `1` off
    ℤ and `bernoulliFun (k+1)/(k+1)` has derivative `bernoulliFun k`).  IBP with this antiderivative
    turns `∫ sawBernoulli k · fk` into a boundary term plus `∫ sawBernoulli (k+1) · fk'`, exactly
    one order higher.  The endpoint saw values are `bernoulliFun (k+1) 0` and `bernoulliFun (k+1) 1`
    (the cell is `[m, m+1]`), which for `k+1 ≠ 1` are EQUAL by `bernoulliFun_endpoints_eq_of_ne_one`
    — the mechanism that makes the interior Bernoulli boundary terms telescope to zero. -/

/-- On the OPEN cell `(m, m+1)`, the shifted Bernoulli antiderivative `bernoulliFun (k+1) ({x})/(k+1)`
    has derivative `sawBernoulli k x`.  (`Int.fract` is differentiable with derivative `1` there.) -/
lemma sawAntideriv_hasDerivAt_Ioo (k : ℕ) {m : ℤ} {x : ℝ} (hx : x ∈ Ioo (m : ℝ) (m + 1)) :
    HasDerivAt (fun y => sawBernoulli (k + 1) y / (k + 1)) (sawBernoulli k x) x := by
  -- `Int.fract` has derivative 1 on the open cell (floor is locally constant `= m`).
  have hfloor : ∀ᶠ y in 𝓝 x, ⌊y⌋ = m := by
    have hlt : (m : ℝ) < x := hx.1
    have hgt : x < (m : ℝ) + 1 := hx.2
    have hmem : x ∈ Ioo (m : ℝ) (m + 1) := hx
    filter_upwards [Ioo_mem_nhds hlt hgt] with y hy
    rw [Int.floor_eq_iff]
    exact ⟨le_of_lt hy.1, by have := hy.2; linarith⟩
  have hfract : HasDerivAt (fun y => Int.fract y) 1 x := by
    have hid : HasDerivAt (fun y : ℝ => y - (m : ℝ)) 1 x := by
      simpa using (hasDerivAt_id x).sub_const (m : ℝ)
    refine hid.congr_of_eventuallyEq ?_
    filter_upwards [hfloor] with y hy
    rw [Int.fract, hy]
  -- `bernoulliFun (k+1)/(k+1)` has derivative `bernoulliFun k` (Mathlib `antideriv_bernoulliFun`).
  have hanti : HasDerivAt (fun z => bernoulliFun (k + 1) z / (k + 1)) (bernoulliFun k (Int.fract x))
      (Int.fract x) := antideriv_bernoulliFun k (Int.fract x)
  -- Chain rule.
  have hcomp := hanti.comp x hfract
  rw [mul_one] at hcomp
  have hfun : ((fun z => bernoulliFun (k + 1) z / (↑k + 1)) ∘ Int.fract)
      = (fun y => sawBernoulli (k + 1) y / (k + 1)) := by
    funext y; simp [Function.comp, sawBernoulli]
  rw [hfun] at hcomp
  exact hcomp

/-- The continuous polynomial surrogate `W y = bernoulliFun (k+1) (y - m) / (k+1)` for the shifted
    saw antiderivative on the cell `[m, m+1]`.  It is C¹ everywhere with derivative
    `bernoulliFun k (y - m)`, and agrees with `sawBernoulli (k+1) ·/(k+1)` on `[m, m+1)`. -/
private noncomputable def sawSurrogate (k : ℕ) (m : ℤ) (y : ℝ) : ℝ :=
  bernoulliFun (k + 1) (y - m) / (k + 1)

private lemma sawSurrogate_hasDerivAt (k : ℕ) (m : ℤ) (y : ℝ) :
    HasDerivAt (sawSurrogate k m) (bernoulliFun k (y - m)) y := by
  have hshift : HasDerivAt (fun z : ℝ => z - (m : ℝ)) 1 y := by
    simpa using (hasDerivAt_id y).sub_const (m : ℝ)
  have hanti := antideriv_bernoulliFun k (y - m)
  have hcomp := hanti.comp y hshift
  rw [mul_one] at hcomp
  have hfun : ((fun z => bernoulliFun (k + 1) z / (↑k + 1)) ∘ (fun z : ℝ => z - (m : ℝ)))
      = sawSurrogate k m := by
    funext z; simp [Function.comp, sawSurrogate]
  rw [hfun] at hcomp
  exact hcomp

private lemma sawSurrogate_eq_saw_on_Ico (k : ℕ) {m : ℤ} {y : ℝ} (hy : y ∈ Ico (m : ℝ) (m + 1)) :
    sawSurrogate k m y = sawBernoulli (k + 1) y / (k + 1) := by
  rw [sawSurrogate, sawBernoulli_eq_on_Ico (k + 1) hy]

/-- **The saw-order-raising IBP step** (the proven form of `EMZetaWip.em_saw_step_wip`).
    Over the unit cell `[m, m+1]`, for `fk` with derivative `fk1` and `fk1` interval-integrable,
        ∫ sawBernoulli k · fk
          = (B_{k+1}(1)·fk(m+1) − B_{k+1}(0)·fk(m)) / (k+1)
            − (∫ sawBernoulli (k+1) · fk1) / (k+1).
    The endpoint saw values are written via the raw `bernoulliFun (k+1)` at `0` and `1` (the cell
    endpoints shifted), which coincide for `k+1 ≠ 1` (`bernoulliFun_endpoints_eq_of_ne_one`),
    the mechanism that makes the summed interior boundary terms telescope. -/
theorem em_saw_step (k : ℕ) (m : ℤ) (fk fk1 : ℝ → ℝ)
    (hd : ∀ x ∈ Icc (m : ℝ) (m + 1), HasDerivAt fk (fk1 x) x)
    (hi : IntervalIntegrable fk1 volume (m : ℝ) (m + 1)) :
    (∫ x in (m : ℝ)..(m + 1), sawBernoulli k x * fk x)
      = (bernoulliFun (k + 1) 1 * fk (m + 1) - bernoulliFun (k + 1) 0 * fk m) / (k + 1)
        - (∫ x in (m : ℝ)..(m + 1), sawBernoulli (k + 1) x * fk1 x) / (k + 1) := by
  have hcc : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  set W : ℝ → ℝ := sawSurrogate k m with hWdef
  -- W has derivative `bernoulliFun k (x - m)` everywhere; on the cell that equals `sawBernoulli k`.
  have hW' : ∀ x, HasDerivAt W (bernoulliFun k (x - m)) x := fun x => sawSurrogate_hasDerivAt k m x
  have hWcont : Continuous W := by
    rw [hWdef]
    unfold sawSurrogate
    fun_prop
  have huv : ∀ x ∈ uIcc (m : ℝ) (m + 1), HasDerivAt W (bernoulliFun k (x - m)) x :=
    fun x _ => hW' x
  have hfd : ∀ x ∈ uIcc (m : ℝ) (m + 1), HasDerivAt fk (fk1 x) x := by
    intro x hx; rw [uIcc_of_le hcc] at hx; exact hd x hx
  -- derivative of W is interval integrable (continuous polynomial).
  have hW'int : IntervalIntegrable (fun x => bernoulliFun k (x - m)) volume (m : ℝ) (m + 1) := by
    apply Continuous.intervalIntegrable; fun_prop
  -- IBP: ∫ (W'·fk + W·fk1) = W·fk |end - W·fk |start.
  have hIBP := integral_deriv_mul_eq_sub huv hfd hW'int hi
  -- Endpoint values of W (polynomial, exact).
  have hWL : W (m : ℝ) = bernoulliFun (k + 1) 0 / (k + 1) := by
    simp [hWdef, sawSurrogate]
  have hWR : W ((m : ℝ) + 1) = bernoulliFun (k + 1) 1 / (k + 1) := by
    simp only [hWdef, sawSurrogate, add_sub_cancel_left]
  -- Interval integrability of the two products.
  have hWfk1int : IntervalIntegrable (fun x => W x * fk1 x) volume (m : ℝ) (m + 1) :=
    hi.continuousOn_mul hWcont.continuousOn
  have hW'fkint : IntervalIntegrable (fun x => bernoulliFun k (x - m) * fk x) volume (m : ℝ) (m + 1) := by
    have hfkcont : ContinuousOn fk (uIcc (m : ℝ) (m + 1)) := fun x hx =>
      (hfd x hx).continuousAt.continuousWithinAt
    exact (hfkcont.intervalIntegrable).continuousOn_mul (by fun_prop)
  -- Split the LHS integrand.
  have hsplit :
      (∫ x in (m : ℝ)..(m + 1), bernoulliFun k (x - m) * fk x + W x * fk1 x)
        = (∫ x in (m : ℝ)..(m + 1), bernoulliFun k (x - m) * fk x)
          + ∫ x in (m : ℝ)..(m + 1), W x * fk1 x := by
    rw [intervalIntegral.integral_add hW'fkint hWfk1int]
  -- Convert the two saw-integrands (a.e. equal to the polynomial surrogates on the cell).
  have hsaw_k : (∫ x in (m : ℝ)..(m + 1), sawBernoulli k x * fk x)
      = ∫ x in (m : ℝ)..(m + 1), bernoulliFun k (x - m) * fk x := by
    apply intervalIntegral.integral_congr_ae
    have hnull : ∀ᵐ x, x ≠ ((m : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico (m : ℝ) (m + 1) := ⟨le_of_lt hxmem.1, lt_of_le_of_ne hxmem.2 hxne⟩
    rw [sawBernoulli_eq_on_Ico k hxIco]
  have hsaw_k1 : (∫ x in (m : ℝ)..(m + 1), sawBernoulli (k + 1) x * fk1 x)
      = ∫ x in (m : ℝ)..(m + 1), ((k + 1) * W x) * fk1 x := by
    apply intervalIntegral.integral_congr_ae
    have hnull : ∀ᵐ x, x ≠ ((m : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico (m : ℝ) (m + 1) := ⟨le_of_lt hxmem.1, lt_of_le_of_ne hxmem.2 hxne⟩
    have := sawSurrogate_eq_saw_on_Ico k hxIco
    rw [hWdef]
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    rw [this]; field_simp
  -- Assemble.
  rw [hsaw_k]
  have key : (∫ x in (m : ℝ)..(m + 1), bernoulliFun k (x - m) * fk x)
      + ∫ x in (m : ℝ)..(m + 1), W x * fk1 x
      = W ((m : ℝ) + 1) * fk ((m : ℝ) + 1) - W (m : ℝ) * fk (m : ℝ) := by
    rw [← hsplit]; exact hIBP
  rw [hWL, hWR] at key
  -- The saw(k+1) integral in terms of W.
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  rw [hsaw_k1]
  have hpull : (∫ x in (m : ℝ)..(m + 1), ((k + 1) * W x) * fk1 x)
      = ((k : ℝ) + 1) * ∫ x in (m : ℝ)..(m + 1), W x * fk1 x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _; ring
  rw [hpull]
  -- `((k+1)·I)/(k+1) = I`; then the goal is `∫saw_k·fk = boundary/(k+1) - I`, exactly `key`.
  have hcancel : (((k : ℝ) + 1) * ∫ x in (m : ℝ)..(m + 1), W x * fk1 x) / ((k : ℝ) + 1)
      = ∫ x in (m : ℝ)..(m + 1), W x * fk1 x := by
    rw [mul_comm]; exact mul_div_cancel_right₀ _ hk1
  rw [hcancel]
  linear_combination key

/-- Telescoping sum of first differences of a real function evaluated at ℕ casts. -/
private lemma sum_telescope_diff (g : ℝ → ℝ) {M N : ℕ} (hMN : M ≤ N) :
    (∑ j ∈ Finset.Ico M N, (g ((j : ℝ) + 1) - g (j : ℝ))) = g (N : ℝ) - g (M : ℝ) := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ p hp ih => rw [Finset.sum_Ico_succ_top hp, ih]; push_cast; ring

/-- ℂ-valued telescoping sum of first differences. -/
private lemma sum_telescope_diff_cpow (g : ℝ → ℂ) {M N : ℕ} (hMN : M ≤ N) :
    (∑ j ∈ Finset.Ico M N, (g ((j : ℝ) + 1) - g (j : ℝ))) = g (N : ℝ) - g (M : ℝ) := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ p hp ih => rw [Finset.sum_Ico_succ_top hp, ih]; push_cast; ring

/-! ## G'. Summed saw-order-raising over an integer window `[M, N]`.

    Summing `em_saw_step` over the cells `[M,M+1], …, [N-1,N]` and telescoping via
    `sum_integral_adjacent_intervals_Ico`, the interior boundary terms cancel (for `k+1 ≠ 1` the
    saw endpoint values `B_{k+1}(0) = B_{k+1}(1)` agree, so adjacent cells contribute
    `+B_{k+1}(0)·f(j)` and `−B_{k+1}(0)·f(j)`), leaving only the two outer endpoints:
        ∫_M^N saw_k · fk
          = B_{k+1}(0)·(fk N − fk M)/(k+1)  −  (∫_M^N saw_{k+1} · fk1)/(k+1).
    (Here `k ≥ 1` so `k + 1 ≠ 1`, which is what makes the telescoping clean.) -/

/-- **Summed saw-order-raising over `[M, N]`.**  For `k ≥ 1`, `fk` differentiable on `[M,N]` with
    `fk1` interval-integrable per cell. -/
theorem em_saw_step_window {k : ℕ} (hk : 1 ≤ k) (M N : ℕ) (hMN : M ≤ N) (fk fk1 : ℝ → ℝ)
    (hd : ∀ x ∈ Icc (M : ℝ) N, HasDerivAt fk (fk1 x) x)
    (hi : ∀ j ∈ Finset.Ico M N, IntervalIntegrable fk1 volume (j : ℝ) (j + 1)) :
    (∫ x in (M : ℝ)..N, sawBernoulli k x * fk x)
      = bernoulliFun (k + 1) 0 * (fk N - fk M) / (k + 1)
        - (∫ x in (M : ℝ)..N, sawBernoulli (k + 1) x * fk1 x) / (k + 1) := by
  have hk1ne : k + 1 ≠ 1 := by omega
  have hendeq : bernoulliFun (k + 1) 1 = bernoulliFun (k + 1) 0 :=
    bernoulliFun_endpoints_eq_of_ne_one hk1ne
  -- Per-cell derivative availability.
  have hcell : ∀ j ∈ Finset.Ico M N, ∀ x ∈ Icc (j : ℝ) (j + 1), HasDerivAt fk (fk1 x) x := by
    intro j hj x hx
    rw [Finset.mem_Ico] at hj
    refine hd x ⟨le_trans (by exact_mod_cast hj.1) hx.1, ?_⟩
    have : (j : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hj.2
    linarith [hx.2]
  -- Per-cell one-step identity.
  have hstep : ∀ j ∈ Finset.Ico M N,
      (∫ x in (j : ℝ)..(j + 1), sawBernoulli k x * fk x)
        = (bernoulliFun (k + 1) 1 * fk (j + 1) - bernoulliFun (k + 1) 0 * fk j) / (k + 1)
          - (∫ x in (j : ℝ)..(j + 1), sawBernoulli (k + 1) x * fk1 x) / (k + 1) := by
    intro j hj
    have hcast : (((j : ℤ)) : ℝ) = (j : ℝ) := by push_cast; ring
    have := em_saw_step k (j : ℤ) fk fk1
      (by intro x hx; rw [hcast] at hx; exact hcell j hj x hx)
      (by rw [hcast]; exact hi j hj)
    simpa [hcast] using this
  have hsum := Finset.sum_congr rfl hstep
  -- Telescope the saw_k integral and the saw_{k+1} remainder over cells.
  have hint_k : ∀ j ∈ Finset.Ico M N,
      IntervalIntegrable (fun x => sawBernoulli k x * fk x) volume (j : ℝ) (j + 1) := by
    intro j hj
    have hcc : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
    have hfkcont : ContinuousOn fk (Icc (j : ℝ) (j + 1)) :=
      fun x hx => (hcell j hj x hx).continuousAt.continuousWithinAt
    -- saw_k·fk = (poly surrogate)·fk a.e. on the cell; both factors continuous ⇒ integrable.
    have hcont : IntervalIntegrable (fun x => bernoulliFun k (x - j) * fk x) volume (j : ℝ) (j + 1) := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hcc]
      exact (Continuous.continuousOn (by fun_prop)).mul hfkcont
    refine (intervalIntegrable_congr_ae ?_).mpr hcont
    have hnull : ∀ᵐ x, x ≠ ((j : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico ((j : ℤ) : ℝ) (((j : ℤ) : ℝ) + 1) := by
      refine ⟨?_, ?_⟩
      · have : (j : ℝ) < x := hxmem.1; push_cast; linarith
      · have hlt : x < (j : ℝ) + 1 := lt_of_le_of_ne hxmem.2 hxne; push_cast; linarith
    rw [sawBernoulli_eq_on_Ico k hxIco]
    norm_num
  have htel_k : (∑ j ∈ Finset.Ico M N, ∫ x in (j : ℝ)..(j + 1), sawBernoulli k x * fk x)
      = ∫ x in (M : ℝ)..N, sawBernoulli k x * fk x := by
    have hint : ∀ j ∈ Set.Ico M N,
        IntervalIntegrable (fun x => sawBernoulli k x * fk x) volume
          ((fun j : ℕ => (j : ℝ)) j) ((fun j : ℕ => (j : ℝ)) (j + 1)) := by
      intro j hj; simpa [Nat.cast_succ] using hint_k j (Finset.mem_Ico.mpr hj)
    have := intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun j : ℕ => (j : ℝ)) (f := fun x => sawBernoulli k x * fk x) (μ := volume) hMN hint
    simpa using this
  have hint_k1 : ∀ j ∈ Finset.Ico M N,
      IntervalIntegrable (fun x => sawBernoulli (k + 1) x * fk1 x) volume (j : ℝ) (j + 1) := by
    intro j hj
    have hcc : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
    have hcont : IntervalIntegrable (fun x => bernoulliFun (k + 1) (x - j) * fk1 x) volume
        (j : ℝ) (j + 1) := (hi j hj).continuousOn_mul (by fun_prop)
    refine (intervalIntegrable_congr_ae ?_).mpr hcont
    have hnull : ∀ᵐ x, x ≠ ((j : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico ((j : ℤ) : ℝ) (((j : ℤ) : ℝ) + 1) := by
      refine ⟨?_, ?_⟩
      · have : (j : ℝ) < x := hxmem.1; push_cast; linarith
      · have hlt : x < (j : ℝ) + 1 := lt_of_le_of_ne hxmem.2 hxne; push_cast; linarith
    rw [sawBernoulli_eq_on_Ico (k + 1) hxIco]
    norm_num
  have htel_k1 : (∑ j ∈ Finset.Ico M N, ∫ x in (j : ℝ)..(j + 1), sawBernoulli (k + 1) x * fk1 x)
      = ∫ x in (M : ℝ)..N, sawBernoulli (k + 1) x * fk1 x := by
    have hint : ∀ j ∈ Set.Ico M N,
        IntervalIntegrable (fun x => sawBernoulli (k + 1) x * fk1 x) volume
          ((fun j : ℕ => (j : ℝ)) j) ((fun j : ℕ => (j : ℝ)) (j + 1)) := by
      intro j hj; simpa [Nat.cast_succ] using hint_k1 j (Finset.mem_Ico.mpr hj)
    have := intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun j : ℕ => (j : ℝ)) (f := fun x => sawBernoulli (k + 1) x * fk1 x) (μ := volume) hMN hint
    simpa using this
  -- The boundary-sum telescopes: (∑ (B(1)f(j+1) - B(0)f(j)))/(k+1) = B(0)(f N - f M)/(k+1).
  have hbdry : (∑ j ∈ Finset.Ico M N,
        (bernoulliFun (k + 1) 1 * fk (j + 1) - bernoulliFun (k + 1) 0 * fk j)) / (k + 1)
      = bernoulliFun (k + 1) 0 * (fk N - fk M) / (k + 1) := by
    congr 1
    rw [hendeq]
    have : (∑ j ∈ Finset.Ico M N,
        (bernoulliFun (k + 1) 0 * fk (j + 1) - bernoulliFun (k + 1) 0 * fk j))
        = (∑ j ∈ Finset.Ico M N,
            bernoulliFun (k + 1) 0 * (fk ((j : ℝ) + 1) - fk (j : ℝ))) := by
      apply Finset.sum_congr rfl; intro j _; ring
    rw [this, ← Finset.mul_sum, sum_telescope_diff fk hMN]
  -- Assemble: sum of per-cell identities, telescoped.
  rw [Finset.sum_sub_distrib] at hsum
  rw [← Finset.sum_div, ← Finset.sum_div, htel_k1, htel_k, hbdry] at hsum
  exact hsum

/-! ## H. The order-K tail remainder integrals and their explicit `N`-decaying bounds.

    The consumer needs a remainder over the TAIL `[N, ∞)` whose norm decays in `N`.  We work with
    the complex integrand `sawBernoulli k x · (c · (x:ℂ)^(-s-k))` where `c` is the falling-factorial
    coefficient `(-1)^k s(s+1)…(s+k-1)` (the k-th derivative coefficient of `x^{-s}`).  The norm
    bound is the clean product form
        ‖∫_N^∞ saw_k · c·x^{-s-k}‖ ≤ Bsup_k · ‖c‖ · N^{-Re s - k + 1} / (Re s + k - 1),
    from `‖saw_k‖ ≤ Bsup_k`, `‖x^{-s-k}‖ = x^{-Re s - k}`, and `∫_N^∞ x^{-Re s -k} = N^{-Re s -k+1}/(Re s+k-1)`. -/

/-- Generic explicit tail bound for a saw-weighted power integrand on `[N, ∞)`.
    If `‖sawBernoulli k x‖ ≤ B` for all `x` (as a real bound on the real saw) and the integrand is
    `sawBernoulli k x · (c · (x:ℂ)^(-s-k))`, then over `[N,∞)` with `N ≥ 1` and `Re s + k > 1`,
        ‖∫‖ ≤ B · ‖c‖ · N^{-(Re s + k - 1)} / (Re s + k - 1).
    This is the single reusable engine for all K. -/
theorem em_tail_integral_bound {k : ℕ} {s c : ℂ} {B : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hexp : 1 < s.re + k) (hB : 0 ≤ B)
    (hsawB : ∀ x : ℝ, |sawBernoulli k x| ≤ B) :
    ‖∫ x in Ioi (N : ℝ), (sawBernoulli k x : ℂ) * (c * (x : ℂ) ^ (-s - k))‖
      ≤ B * ‖c‖ * (N : ℝ) ^ (-(s.re + k - 1)) / (s.re + k - 1) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hσk1 : 0 < s.re + k - 1 := by linarith
  -- exponent for the norm: -(Re s + k) < -1.
  have hexplt : -(s.re + (k : ℝ)) < -1 := by
    have : (1 : ℝ) < s.re + k := hexp
    linarith
  -- integrand norm domination: ‖·‖ ≤ (B·‖c‖) · x^{-(Re s + k)} on (N,∞).
  have hdom : IntegrableOn (fun x : ℝ => (B * ‖c‖) * x ^ (-(s.re + (k : ℝ)))) (Ioi (N : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (a := -(s.re + (k : ℝ))) hexplt hNpos).const_mul _
  have hInt : IntegrableOn (fun x : ℝ => (sawBernoulli k x : ℂ) * (c * (x : ℂ) ^ (-s - k)))
      (Ioi (N : ℝ)) := by
    refine Integrable.mono' hdom ?_ ?_
    · apply Measurable.aestronglyMeasurable
      exact (Complex.measurable_ofReal.comp (sawBernoulli_measurable k)).mul
        (measurable_const.mul (Complex.measurable_ofReal.pow_const _))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      have hxpos : (0 : ℝ) < x := lt_trans hNpos hx
      have hnormcpow : ‖(x : ℂ) ^ (-s - k)‖ = x ^ (-(s.re + (k : ℝ))) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
        congr 1
        rw [Complex.sub_re, Complex.neg_re, Complex.natCast_re]
        ring
      have hrpownn : (0 : ℝ) ≤ x ^ (-(s.re + (k : ℝ))) := Real.rpow_nonneg hxpos.le _
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hnormcpow]
      calc |sawBernoulli k x| * (‖c‖ * x ^ (-(s.re + (k : ℝ))))
          ≤ B * (‖c‖ * x ^ (-(s.re + (k : ℝ)))) := by
            gcongr; exact hsawB x
        _ = (B * ‖c‖) * x ^ (-(s.re + (k : ℝ))) := by ring
  -- ‖∫‖ ≤ ∫‖·‖ ≤ ∫ dom = (B‖c‖)·N^{-(σ+k-1)}/(σ+k-1).
  calc ‖∫ x in Ioi (N : ℝ), (sawBernoulli k x : ℂ) * (c * (x : ℂ) ^ (-s - k))‖
      ≤ ∫ x in Ioi (N : ℝ), ‖(sawBernoulli k x : ℂ) * (c * (x : ℂ) ^ (-s - k))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x in Ioi (N : ℝ), (B * ‖c‖) * x ^ (-(s.re + (k : ℝ))) := by
        apply setIntegral_mono_on hInt.norm hdom measurableSet_Ioi
        intro x hx
        have hxpos : (0 : ℝ) < x := lt_trans hNpos hx
        have hnormcpow : ‖(x : ℂ) ^ (-s - k)‖ = x ^ (-(s.re + (k : ℝ))) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
          congr 1
          rw [Complex.sub_re, Complex.neg_re, Complex.natCast_re]; ring
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hnormcpow]
        calc |sawBernoulli k x| * (‖c‖ * x ^ (-(s.re + (k : ℝ))))
            ≤ B * (‖c‖ * x ^ (-(s.re + (k : ℝ)))) := by
              gcongr; exact hsawB x
          _ = (B * ‖c‖) * x ^ (-(s.re + (k : ℝ))) := by ring
    _ = B * ‖c‖ * (N : ℝ) ^ (-(s.re + k - 1)) / (s.re + k - 1) := by
        rw [MeasureTheory.integral_const_mul,
          integral_Ioi_rpow_of_lt (a := -(s.re + (k : ℝ))) hexplt hNpos]
        have hexp1 : -(s.re + (k : ℝ)) + 1 = -(s.re + k - 1) := by ring
        rw [hexp1]
        have hne : s.re + (k : ℝ) - 1 ≠ 0 := ne_of_gt hσk1
        field_simp

/-! ## H'. The SHIFTED-BASE tail engine `(w + x)^{-a}` (the Binet / Γℝ substrate).

    The base-1 engine `em_tail_integral_bound` bounds saw-weighted `x^{-s-k}` tails.  The Binet
    remainder `μ_K(w)` (Stirling series for `ψ`) is, up to the finite Bernoulli peel, an
    Euler–Maclaurin tail of the trigamma power series `Σ (w+n)^{-2-k}` — a SHIFTED-BASE `(w+x)^{-a}`
    tail.  This subsection generalizes the engine to that base.  Crucially the exponent is kept REAL
    (`a : ℝ`, `a > 1`) — which is exactly the form the trigamma tail needs (`a = 2 + k ∈ ℕ`) — so
    the norm is `‖(w+x)^{-a}‖ = ‖w+x‖^{-a}` (`Complex.norm_cpow_real`, no `exp(arg·im)` factor), and
    the honest `N`-decay is driven by the base lower bound `‖w+x‖ ≥ Re(w+x) = Re w + x ≥ Re w + N`. -/

/-- Value of the shifted power tail integral: for `1 < a`, `0 < d`, `0 ≤ N`,
    `∫_{Ioi N} (d + x)^{-a} dx = (d + N)^{-(a-1)}/(a-1)`.  Antiderivative form (mirrors
    `integral_Ioi_rpow_of_lt` with an affine shift `d + x` in place of `x`). -/
theorem integral_Ioi_shift_rpow {a d : ℝ} (ha : 1 < a) (hd : 0 < d) (N : ℝ) (hN : 0 ≤ N) :
    ∫ x in Ioi (N : ℝ), (d + x) ^ (-a) = (d + N) ^ (-(a - 1)) / (a - 1) := by
  have hae : (-a) < -1 := by linarith
  have hd' : ∀ x ∈ Ici (N : ℝ), HasDerivAt (fun t : ℝ => (d + t) ^ (-a + 1) / (-a + 1))
      ((d + x) ^ (-a)) x := by
    intro x hx
    have hdx : 0 < d + x := by have := mem_Ici.mp hx; linarith
    have hbase : HasDerivAt (fun t : ℝ => d + t) 1 x := by
      simpa using (hasDerivAt_id x).const_add d
    have hcomp := (Real.hasDerivAt_rpow_const (p := -a + 1) (Or.inl hdx.ne')).comp x hbase
    simp only [mul_one] at hcomp
    have hne : (-a + 1) ≠ 0 := by intro h; linarith
    have hval : ((-a + 1) * (d + x) ^ (-a + 1 - 1)) / (-a + 1) = (d + x) ^ (-a) := by
      rw [show (-a + 1 - 1 : ℝ) = -a by ring, mul_comm, mul_div_assoc, div_self hne, mul_one]
    have := hcomp.div_const (-a + 1)
    rw [hval] at this
    exact this
  have ht : Tendsto (fun t : ℝ => (d + t) ^ (-a + 1) / (-a + 1)) atTop (𝓝 (0 / (-a + 1))) := by
    apply Tendsto.div_const
    rw [← neg_neg (-a + 1)]
    exact (tendsto_rpow_neg_atTop (by linarith : 0 < -(-a + 1))).comp
      (tendsto_atTop_add_const_left _ d tendsto_id)
  have hint : IntegrableOn (fun x : ℝ => (d + x) ^ (-a)) (Ioi (N : ℝ)) := by
    have := integrableOn_add_rpow_Ioi_of_lt (a := -a) (c := N) (m := d) hae (by linarith)
    simpa [add_comm] using this
  have hres := integral_Ioi_of_hasDerivAt_of_tendsto' hd' hint ht
  rw [hres]
  simp only [zero_div, zero_sub]
  rw [show (-a + 1) = -(a - 1) by ring]
  rw [div_neg, neg_neg]

/-- **The shifted-base tail engine.**  Generalization of `em_tail_integral_bound` to base `(w + x)`
    for a complex shift `w` with `Re w > 0` and a REAL exponent `a > 1`.  For the saw-weighted
    power integrand `sawBernoulli k x · (c · (w + x)^(-a))` on `[N, ∞)` with `‖sawBernoulli k‖ ≤ B`,
        ‖∫_N^∞ saw_k · c·(w+x)^{-a}‖ ≤ B · ‖c‖ · (Re w + N)^{-(a-1)} / (a - 1).
    The `N`-decay carries the honest constant `(Re w + N)^{-(a-1)}`: the shifted power decays from the
    base `Re(w+x) = Re w + x ≥ Re w + N`.  This is the reusable substrate for the Binet trigamma tail
    `Σ (w+n)^{-2-k}` and hence the K = 4 Stirling remainder (see `StirlingBinetWip`/`StirlingK4`). -/
theorem em_tail_integral_bound_shifted {k : ℕ} {w c : ℂ} {a B : ℝ} {N : ℕ}
    (hw : 0 < w.re) (ha : 1 < a) (hB : 0 ≤ B)
    (hsawB : ∀ x : ℝ, |sawBernoulli k x| ≤ B) :
    ‖∫ x in Ioi (N : ℝ), (sawBernoulli k x : ℂ) * (c * (w + (x : ℂ)) ^ (-(a : ℂ)))‖
      ≤ B * ‖c‖ * (w.re + N) ^ (-(a - 1)) / (a - 1) := by
  have hNnn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have ham1 : 0 < a - 1 := by linarith
  -- domination bound: ‖integrand‖ ≤ (B·‖c‖) · (Re w + x)^{-a} on (N,∞).
  have hdom : IntegrableOn (fun x : ℝ => (B * ‖c‖) * (w.re + x) ^ (-a)) (Ioi (N : ℝ)) := by
    have hbase : IntegrableOn (fun x : ℝ => (w.re + x) ^ (-a)) (Ioi (N : ℝ)) := by
      have := integrableOn_add_rpow_Ioi_of_lt (a := -a) (c := (N : ℝ)) (m := w.re)
        (by linarith) (by linarith)
      simpa [add_comm] using this
    exact hbase.const_mul _
  -- pointwise: ‖saw·(c·(w+x)^{-a})‖ ≤ (B·‖c‖)·(Re w + x)^{-a}.
  have hpt : ∀ x : ℝ, N < x →
      ‖(sawBernoulli k x : ℂ) * (c * (w + (x : ℂ)) ^ (-(a : ℂ)))‖
        ≤ (B * ‖c‖) * (w.re + x) ^ (-a) := by
    intro x hx
    have hxpos : (0 : ℝ) < x := lt_of_le_of_lt hNnn hx
    have hwx_norm : (w.re + x) ≤ ‖w + (x : ℂ)‖ := by
      calc (w.re + x) = (w + (x : ℂ)).re := by rw [Complex.add_re, Complex.ofReal_re]
        _ ≤ ‖w + (x : ℂ)‖ := Complex.re_le_norm _
    have hnormcpow : ‖(w + (x : ℂ)) ^ (-(a : ℂ))‖ = ‖w + (x : ℂ)‖ ^ (-a) := by
      rw [show (-(a : ℂ)) = ((-a : ℝ) : ℂ) by push_cast; ring, Complex.norm_cpow_real]
    have hbase_pos : (0 : ℝ) < w.re + x := by linarith
    have hantitone : ‖w + (x : ℂ)‖ ^ (-a) ≤ (w.re + x) ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos hbase_pos hwx_norm (by linarith)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hnormcpow]
    calc |sawBernoulli k x| * (‖c‖ * ‖w + (x : ℂ)‖ ^ (-a))
        ≤ B * (‖c‖ * (w.re + x) ^ (-a)) := by
          apply mul_le_mul (hsawB x) ?_ (by positivity) hB
          exact mul_le_mul_of_nonneg_left hantitone (norm_nonneg c)
      _ = (B * ‖c‖) * (w.re + x) ^ (-a) := by ring
  -- integrability of the integrand.
  have hInt : IntegrableOn (fun x : ℝ => (sawBernoulli k x : ℂ) * (c * (w + (x : ℂ)) ^ (-(a : ℂ))))
      (Ioi (N : ℝ)) := by
    refine Integrable.mono' hdom ?_ ?_
    · apply Measurable.aestronglyMeasurable
      exact (Complex.measurable_ofReal.comp (sawBernoulli_measurable k)).mul
        (measurable_const.mul ((measurable_const.add Complex.measurable_ofReal).pow_const _))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      exact hpt x hx
  calc ‖∫ x in Ioi (N : ℝ), (sawBernoulli k x : ℂ) * (c * (w + (x : ℂ)) ^ (-(a : ℂ)))‖
      ≤ ∫ x in Ioi (N : ℝ), ‖(sawBernoulli k x : ℂ) * (c * (w + (x : ℂ)) ^ (-(a : ℂ)))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x in Ioi (N : ℝ), (B * ‖c‖) * (w.re + x) ^ (-a) := by
        apply setIntegral_mono_on hInt.norm hdom measurableSet_Ioi
        intro x hx; exact hpt x hx
    _ = B * ‖c‖ * (w.re + N) ^ (-(a - 1)) / (a - 1) := by
        rw [MeasureTheory.integral_const_mul,
          integral_Ioi_shift_rpow ha hw (N : ℝ) hNnn]
        ring

/-! ## I. The K = 3 instance and THE NUMBER (the go/no-go for full reflection).

    The order-3 tail remainder integrand is `sawBernoulli 3 x · (c₃(s) · x^{-s-3})` where
    `c₃(s) = -s(s+1)(s+2)` is the coefficient of `x^{-s-3}` in `d³/dx³(x^{-s})`.  `em_tail_integral_bound`
    bounds this integral for ANY complex `c`; here we record it with the honest falling-factorial
    coefficient and the proven saw-3 sup bound `1/12`, then evaluate the numeric envelope at the G2
    pilot point `s = 1/2 + 14i` and certify a tail cut making it `< 10⁻³` (the K = 1 envelope
    `‖s‖/(2·Re s) ≈ 14` did NOT — see EMZetaComplex.em_zeta_strip_enclosure). -/

/-- The order-3 falling-factorial coefficient `c₃(s) = -s(s+1)(s+2)` (the `x^{-s-3}`-coefficient of
    the 3rd `x`-derivative of `x^{-s}`). -/
noncomputable def emTailCoeff3 (s : ℂ) : ℂ := -(s * (s + 1) * (s + 2))

/-- **The order-3 tail remainder bound.**  For `N ≥ 1` and `Re s > 0` (hence `Re s + 3 > 1`), the
    order-3 EM tail integral is bounded by the explicit `N`-decaying envelope with the proven saw-3
    sup constant `1/12`:
        ‖∫_N^∞ saw₃ · c₃(s)·x^{-s-3}‖ ≤ (1/12)·‖s(s+1)(s+2)‖·N^{-(Re s+2)}/(Re s+2). -/
theorem em_tail3_bound {s : ℂ} {N : ℕ} (hN : 1 ≤ N) (hs : 0 < s.re) :
    ‖∫ x in Ioi (N : ℝ), (sawBernoulli 3 x : ℂ) * (emTailCoeff3 s * (x : ℂ) ^ (-s - 3))‖
      ≤ (1 / 12) * ‖s * (s + 1) * (s + 2)‖ * (N : ℝ) ^ (-(s.re + 3 - 1)) / (s.re + 3 - 1) := by
  have hexp : (1 : ℝ) < s.re + ((3 : ℕ) : ℝ) := by push_cast; linarith
  have hcnorm : ‖emTailCoeff3 s‖ = ‖s * (s + 1) * (s + 2)‖ := by rw [emTailCoeff3, norm_neg]
  have hbnd := em_tail_integral_bound (k := 3) (s := s) (c := emTailCoeff3 s) (B := 1 / 12)
    (N := N) hN hexp (by norm_num) (fun x => abs_sawBernoulli_three_le x)
  rw [hcnorm] at hbnd
  have hcast : ((3 : ℕ) : ℝ) = (3 : ℝ) := by norm_num
  rw [hcast] at hbnd
  exact hbnd

/-- The numeric envelope bound at the pilot point, factored out for reuse by both `em_tail3_number`
    and the critical-line corollary: with `s = 1/2 + 14i`,
        (1/12)·‖s(s+1)(s+2)‖·200^{−5/2}/(5/2) ≤ 1/1000,
    via `‖s(s+1)(s+2)‖ ≤ 3375` and `200^{−5/2} ≤ 1/560000` (`√200 > 14`). -/
theorem em_tail3_envelope_le :
    (1 / 12) * ‖((1 / 2 : ℂ) + 14 * Complex.I) * ((1 / 2 : ℂ) + 14 * Complex.I + 1)
          * ((1 / 2 : ℂ) + 14 * Complex.I + 2)‖
        * (200 : ℝ) ^ (-(5 / 2 : ℝ)) / (5 / 2)
      ≤ 1 / 1000 := by
  set s : ℂ := (1 / 2 : ℂ) + 14 * Complex.I with hs
  -- Enclose the norm factor: ‖s(s+1)(s+2)‖ ≤ 3375. `‖a + b·I‖ ≤ 15` whenever `a² + b² ≤ 225`.
  have hfac : ∀ a b : ℝ, a ^ 2 + b ^ 2 ≤ 225 → ‖(a : ℂ) + b * Complex.I‖ ≤ 15 := by
    intro a b hab
    rw [Complex.norm_add_mul_I]
    rw [show (15 : ℝ) = Real.sqrt (225) by
      rw [show (225:ℝ) = 15^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hab
  have hs_eq : s = (1 / 2 : ℝ) + (14 : ℝ) * Complex.I := by rw [hs]; push_cast; ring
  have hs1_eq : s + 1 = (3 / 2 : ℝ) + (14 : ℝ) * Complex.I := by rw [hs]; push_cast; ring
  have hs2_eq : s + 2 = (5 / 2 : ℝ) + (14 : ℝ) * Complex.I := by rw [hs]; push_cast; ring
  have hn0 : ‖s‖ ≤ 15 := by rw [hs_eq]; exact hfac _ _ (by norm_num)
  have hn1 : ‖s + 1‖ ≤ 15 := by rw [hs1_eq]; exact hfac _ _ (by norm_num)
  have hn2 : ‖s + 2‖ ≤ 15 := by rw [hs2_eq]; exact hfac _ _ (by norm_num)
  have hnormle : ‖s * (s + 1) * (s + 2)‖ ≤ 3375 := by
    calc ‖s * (s + 1) * (s + 2)‖ = ‖s‖ * ‖s + 1‖ * ‖s + 2‖ := by rw [norm_mul, norm_mul]
      _ ≤ 15 * 15 * 15 := by gcongr
      _ = 3375 := by norm_num
  -- Enclose the power factor: 200^{-5/2} = 1/(200²·√200) ≤ 1/560000  (√200 > 14).
  have hsqrt : (14 : ℝ) ≤ (200 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow,
      show (14 : ℝ) = Real.sqrt 196 by rw [show (196:ℝ) = 14^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hpowle : (200 : ℝ) ^ (-(5 / 2 : ℝ)) ≤ 1 / 560000 := by
    rw [Real.rpow_neg (by norm_num),
      show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_two]
    have hden_pos : (0 : ℝ) < (200 : ℝ) ^ 2 * (200 : ℝ) ^ (1 / 2 : ℝ) :=
      mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)
    have hden_ge : (560000 : ℝ) ≤ (200 : ℝ) ^ 2 * (200 : ℝ) ^ (1 / 2 : ℝ) := by
      calc (560000 : ℝ) = 40000 * 14 := by norm_num
        _ ≤ (200 : ℝ) ^ 2 * (200 : ℝ) ^ (1 / 2 : ℝ) := by
              gcongr <;> norm_num
    calc ((200 : ℝ) ^ 2 * (200 : ℝ) ^ (1 / 2 : ℝ))⁻¹
        ≤ (560000 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hden_ge
      _ = 1 / 560000 := by rw [one_div]
  have hpownn : (0 : ℝ) ≤ (200 : ℝ) ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (by norm_num) _
  calc (1 / 12) * ‖s * (s + 1) * (s + 2)‖ * (200 : ℝ) ^ (-(5 / 2 : ℝ)) / (5 / 2)
      ≤ (1 / 12) * 3375 * (1 / 560000) / (5 / 2) := by gcongr
    _ ≤ 1 / 1000 := by norm_num

/-- **THE NUMBER (go/no-go for full reflection).**  At the G2 pilot point `s = 1/2 + 14·i` with a
    tail cut `N = 200`, the order-3 Euler-Maclaurin remainder is bounded (in-kernel) by `≤ 10⁻³` —
    the threshold that makes the `gLine` interval boxes sign-tight.  See `em_tail3_envelope_le` for
    the certified rational envelope (`‖s(s+1)(s+2)‖ ≤ 3375`, `200^{-5/2} ≤ 1/560000`). -/
theorem em_tail3_number :
    ‖∫ x in Ioi (200 : ℝ),
        (sawBernoulli 3 x : ℂ)
          * (emTailCoeff3 ((1 / 2 : ℂ) + 14 * Complex.I)
              * (x : ℂ) ^ (-((1 / 2 : ℂ) + 14 * Complex.I) - 3))‖
      ≤ (1 : ℝ) / 1000 := by
  have hsre : ((1 / 2 : ℂ) + 14 * Complex.I).re = 1 / 2 := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  have hs0 : 0 < ((1 / 2 : ℂ) + 14 * Complex.I).re := by rw [hsre]; norm_num
  have hbnd := em_tail3_bound (s := (1 / 2 : ℂ) + 14 * Complex.I) (N := 200) (by norm_num) hs0
  rw [hsre] at hbnd
  refine le_trans hbnd ?_
  have hexpeq : (-(1 / 2 + (3 : ℝ) - 1) : ℝ) = -(5 / 2 : ℝ) := by norm_num
  have hdeneq : ((1 / 2 : ℝ) + 3 - 1) = (5 / 2 : ℝ) := by norm_num
  rw [hexpeq, hdeneq]
  exact em_tail3_envelope_le

/-! ## J. The order-2 windowed EM identity for the ζ integrand (complex).

    We raise the K=1 windowed complex EM identity (`euler_maclaurin_one_window_cpow` applied to
    `f x = (x:ℂ)^(-s)`) to order 2 using `em_saw_step_window` (real coefficients, applied to the
    real and imaginary parts — but here directly to the ℂ integrand via linearity of the identity
    over the real saw).  The order-2 remainder integrand carries the coefficient `c₂(s) = s(s+1)`.

    We give the complex σ-direction derivatives to order 2 (the inputs `em_saw_step_window` needs),
    then the windowed order-2 identity.  This is the reusable step; iterating once more gives order 3,
    and the `[N,∞)` limit (handoff) yields the ζ representation. -/

/-- Second σ-direction derivative of `x^{-s}`: `d/dx(-s·x^{-s-1}) = s(s+1)·x^{-s-2}` for `x > 0`
    and `s ≠ -1` (so the intermediate exponent `-s-1 ≠ 0`; always holds on `Re s > 0`). -/
theorem hasDerivAt_cpow_neg2 {s : ℂ} (hs : s ≠ -1) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => -s * (x : ℂ) ^ (-s - 1)) (s * (s + 1) * (x : ℂ) ^ (-s - 2)) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hr : (-s - 1 : ℂ) ≠ 0 := by
    intro h; apply hs; linear_combination -h
  have hstep : HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-s - 1))
      ((-s - 1) * (x : ℂ) ^ (-s - 1 - 1)) x := hasDerivAt_ofReal_cpow_const hx0 hr
  have hfull := hstep.const_mul (-s)
  have hval : (-s) * ((-s - 1) * (x : ℂ) ^ (-s - 1 - 1)) = s * (s + 1) * (x : ℂ) ^ (-s - 2) := by
    rw [show (-s - 1 - 1 : ℂ) = -s - 2 by ring]; ring
  rw [hval] at hfull
  exact hfull

/-! ### ℂ-valued saw-order-raising over a window (for the ζ integrand).

    The ℂ lift of `em_saw_step` and `em_saw_step_window`.  The saw factor `sawBernoulli k x` stays
    REAL (cast to ℂ); `fk, fk1` are ℂ-valued.  Proof structure is identical to the real versions
    with `linear_combination` in place of `linarith` for the final ℂ arithmetic. -/

/-- ℂ-valued one-step saw-order-raising over the unit cell `[m, m+1]`. -/
theorem em_saw_step_cpow (k : ℕ) (m : ℤ) (fk fk1 : ℝ → ℂ)
    (hd : ∀ x ∈ Icc (m : ℝ) (m + 1), HasDerivAt fk (fk1 x) x)
    (hi : IntervalIntegrable fk1 volume (m : ℝ) (m + 1)) :
    (∫ x in (m : ℝ)..(m + 1), (sawBernoulli k x : ℂ) * fk x)
      = ((bernoulliFun (k + 1) 1 : ℂ) * fk (m + 1) - (bernoulliFun (k + 1) 0 : ℂ) * fk m) / (k + 1)
        - (∫ x in (m : ℝ)..(m + 1), (sawBernoulli (k + 1) x : ℂ) * fk1 x) / (k + 1) := by
  have hcc : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  -- ℂ-cast polynomial surrogate W x = B_{k+1}(x-m)/(k+1).
  set W : ℝ → ℂ := fun y => (bernoulliFun (k + 1) (y - m) / (k + 1) : ℝ) with hWdef
  have hW' : ∀ x, HasDerivAt W ((bernoulliFun k (x - m) : ℂ)) x := by
    intro x
    have hreal := sawSurrogate_hasDerivAt k m x
    have := hreal.ofReal_comp
    simpa [hWdef, sawSurrogate, Function.comp] using this
  have hWcont : Continuous W := by
    rw [hWdef]; fun_prop
  have huv : ∀ x ∈ uIcc (m : ℝ) (m + 1), HasDerivAt W ((bernoulliFun k (x - m) : ℂ)) x :=
    fun x _ => hW' x
  have hfd : ∀ x ∈ uIcc (m : ℝ) (m + 1), HasDerivAt fk (fk1 x) x := by
    intro x hx; rw [uIcc_of_le hcc] at hx; exact hd x hx
  have hW'int : IntervalIntegrable (fun x => (bernoulliFun k (x - m) : ℂ)) volume (m : ℝ) (m + 1) := by
    apply Continuous.intervalIntegrable; fun_prop
  have hIBP := integral_deriv_mul_eq_sub huv hfd hW'int hi
  have hWL : W (m : ℝ) = (bernoulliFun (k + 1) 0 : ℂ) / (k + 1) := by
    simp [hWdef]
  have hWR : W ((m : ℝ) + 1) = (bernoulliFun (k + 1) 1 : ℂ) / (k + 1) := by
    simp only [hWdef, add_sub_cancel_left]; push_cast; ring
  have hWfk1int : IntervalIntegrable (fun x => W x * fk1 x) volume (m : ℝ) (m + 1) :=
    hi.continuousOn_mul hWcont.continuousOn
  have hW'fkint : IntervalIntegrable (fun x => (bernoulliFun k (x - m) : ℂ) * fk x) volume (m : ℝ) (m + 1) := by
    have hfkcont : ContinuousOn fk (uIcc (m : ℝ) (m + 1)) := fun x hx =>
      (hfd x hx).continuousAt.continuousWithinAt
    exact (hfkcont.intervalIntegrable).continuousOn_mul (by fun_prop)
  have hsplit :
      (∫ x in (m : ℝ)..(m + 1), (bernoulliFun k (x - m) : ℂ) * fk x + W x * fk1 x)
        = (∫ x in (m : ℝ)..(m + 1), (bernoulliFun k (x - m) : ℂ) * fk x)
          + ∫ x in (m : ℝ)..(m + 1), W x * fk1 x := by
    rw [intervalIntegral.integral_add hW'fkint hWfk1int]
  have hsaw_k : (∫ x in (m : ℝ)..(m + 1), (sawBernoulli k x : ℂ) * fk x)
      = ∫ x in (m : ℝ)..(m + 1), (bernoulliFun k (x - m) : ℂ) * fk x := by
    apply intervalIntegral.integral_congr_ae
    have hnull : ∀ᵐ x, x ≠ ((m : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico (m : ℝ) (m + 1) := ⟨le_of_lt hxmem.1, lt_of_le_of_ne hxmem.2 hxne⟩
    rw [sawBernoulli_eq_on_Ico k hxIco]
  have hsaw_k1 : (∫ x in (m : ℝ)..(m + 1), (sawBernoulli (k + 1) x : ℂ) * fk1 x)
      = ∫ x in (m : ℝ)..(m + 1), ((k + 1 : ℂ) * W x) * fk1 x := by
    apply intervalIntegral.integral_congr_ae
    have hnull : ∀ᵐ x, x ≠ ((m : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico (m : ℝ) (m + 1) := ⟨le_of_lt hxmem.1, lt_of_le_of_ne hxmem.2 hxne⟩
    have hk1 : ((k : ℂ) + 1) ≠ 0 := by
      have : ((k : ℝ) + 1) ≠ 0 := by positivity
      exact_mod_cast this
    rw [sawBernoulli_eq_on_Ico (k + 1) hxIco, hWdef]
    push_cast
    field_simp
  rw [hsaw_k]
  have key : (∫ x in (m : ℝ)..(m + 1), (bernoulliFun k (x - m) : ℂ) * fk x)
      + ∫ x in (m : ℝ)..(m + 1), W x * fk1 x
      = W ((m : ℝ) + 1) * fk ((m : ℝ) + 1) - W (m : ℝ) * fk (m : ℝ) := by
    rw [← hsplit]; exact hIBP
  rw [hWL, hWR] at key
  have hk1 : ((k : ℂ) + 1) ≠ 0 := by
    have : ((k : ℝ) + 1) ≠ 0 := by positivity
    exact_mod_cast this
  rw [hsaw_k1]
  have hpull : (∫ x in (m : ℝ)..(m + 1), ((k + 1 : ℂ) * W x) * fk1 x)
      = ((k : ℂ) + 1) * ∫ x in (m : ℝ)..(m + 1), W x * fk1 x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _; push_cast; ring
  rw [hpull]
  have hcancel : (((k : ℂ) + 1) * ∫ x in (m : ℝ)..(m + 1), W x * fk1 x) / ((k : ℂ) + 1)
      = ∫ x in (m : ℝ)..(m + 1), W x * fk1 x := by
    rw [mul_comm]; exact mul_div_cancel_right₀ _ hk1
  rw [hcancel]
  push_cast
  linear_combination key

/-- ℂ-valued summed saw-order-raising over `[M, N]` (`k ≥ 1`).  ℂ lift of `em_saw_step_window`. -/
theorem em_saw_step_window_cpow {k : ℕ} (hk : 1 ≤ k) (M N : ℕ) (hMN : M ≤ N) (fk fk1 : ℝ → ℂ)
    (hd : ∀ x ∈ Icc (M : ℝ) N, HasDerivAt fk (fk1 x) x)
    (hi : ∀ j ∈ Finset.Ico M N, IntervalIntegrable fk1 volume (j : ℝ) (j + 1)) :
    (∫ x in (M : ℝ)..N, (sawBernoulli k x : ℂ) * fk x)
      = (bernoulliFun (k + 1) 0 : ℂ) * (fk N - fk M) / (k + 1)
        - (∫ x in (M : ℝ)..N, (sawBernoulli (k + 1) x : ℂ) * fk1 x) / (k + 1) := by
  have hk1ne : k + 1 ≠ 1 := by omega
  have hendeq : (bernoulliFun (k + 1) 1 : ℂ) = (bernoulliFun (k + 1) 0 : ℂ) := by
    exact_mod_cast bernoulliFun_endpoints_eq_of_ne_one hk1ne
  have hcell : ∀ j ∈ Finset.Ico M N, ∀ x ∈ Icc (j : ℝ) (j + 1), HasDerivAt fk (fk1 x) x := by
    intro j hj x hx
    rw [Finset.mem_Ico] at hj
    refine hd x ⟨le_trans (by exact_mod_cast hj.1) hx.1, ?_⟩
    have : (j : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hj.2
    linarith [hx.2]
  have hstep : ∀ j ∈ Finset.Ico M N,
      (∫ x in (j : ℝ)..(j + 1), (sawBernoulli k x : ℂ) * fk x)
        = ((bernoulliFun (k + 1) 1 : ℂ) * fk (j + 1) - (bernoulliFun (k + 1) 0 : ℂ) * fk j) / (k + 1)
          - (∫ x in (j : ℝ)..(j + 1), (sawBernoulli (k + 1) x : ℂ) * fk1 x) / (k + 1) := by
    intro j hj
    have hcast : (((j : ℤ)) : ℝ) = (j : ℝ) := by push_cast; ring
    have := em_saw_step_cpow k (j : ℤ) fk fk1
      (by intro x hx; rw [hcast] at hx; exact hcell j hj x hx)
      (by rw [hcast]; exact hi j hj)
    simpa [hcast] using this
  have hsum := Finset.sum_congr rfl hstep
  -- Integrability per cell (ℂ).
  have hint_k : ∀ j ∈ Finset.Ico M N,
      IntervalIntegrable (fun x => (sawBernoulli k x : ℂ) * fk x) volume (j : ℝ) (j + 1) := by
    intro j hj
    have hcc : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
    have hfkcont : ContinuousOn fk (Icc (j : ℝ) (j + 1)) :=
      fun x hx => (hcell j hj x hx).continuousAt.continuousWithinAt
    have hcont : IntervalIntegrable (fun x => (bernoulliFun k (x - j) : ℂ) * fk x) volume (j : ℝ) (j + 1) := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hcc]
      exact (Continuous.continuousOn (by fun_prop)).mul hfkcont
    refine (intervalIntegrable_congr_ae ?_).mpr hcont
    have hnull : ∀ᵐ x, x ≠ ((j : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico ((j : ℤ) : ℝ) (((j : ℤ) : ℝ) + 1) := by
      refine ⟨?_, ?_⟩
      · have : (j : ℝ) < x := hxmem.1; push_cast; linarith
      · have hlt : x < (j : ℝ) + 1 := lt_of_le_of_ne hxmem.2 hxne; push_cast; linarith
    rw [sawBernoulli_eq_on_Ico k hxIco]; norm_num
  have htel_k : (∑ j ∈ Finset.Ico M N, ∫ x in (j : ℝ)..(j + 1), (sawBernoulli k x : ℂ) * fk x)
      = ∫ x in (M : ℝ)..N, (sawBernoulli k x : ℂ) * fk x := by
    have hint : ∀ j ∈ Set.Ico M N,
        IntervalIntegrable (fun x => (sawBernoulli k x : ℂ) * fk x) volume
          ((fun j : ℕ => (j : ℝ)) j) ((fun j : ℕ => (j : ℝ)) (j + 1)) := by
      intro j hj; simpa [Nat.cast_succ] using hint_k j (Finset.mem_Ico.mpr hj)
    have := intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun j : ℕ => (j : ℝ)) (f := fun x => (sawBernoulli k x : ℂ) * fk x) (μ := volume) hMN hint
    simpa using this
  have hint_k1 : ∀ j ∈ Finset.Ico M N,
      IntervalIntegrable (fun x => (sawBernoulli (k + 1) x : ℂ) * fk1 x) volume (j : ℝ) (j + 1) := by
    intro j hj
    have hcc : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
    have hcont : IntervalIntegrable (fun x => (bernoulliFun (k + 1) (x - j) : ℂ) * fk1 x) volume
        (j : ℝ) (j + 1) := (hi j hj).continuousOn_mul (by fun_prop)
    refine (intervalIntegrable_congr_ae ?_).mpr hcont
    have hnull : ∀ᵐ x, x ≠ ((j : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico ((j : ℤ) : ℝ) (((j : ℤ) : ℝ) + 1) := by
      refine ⟨?_, ?_⟩
      · have : (j : ℝ) < x := hxmem.1; push_cast; linarith
      · have hlt : x < (j : ℝ) + 1 := lt_of_le_of_ne hxmem.2 hxne; push_cast; linarith
    rw [sawBernoulli_eq_on_Ico (k + 1) hxIco]; norm_num
  have htel_k1 : (∑ j ∈ Finset.Ico M N, ∫ x in (j : ℝ)..(j + 1), (sawBernoulli (k + 1) x : ℂ) * fk1 x)
      = ∫ x in (M : ℝ)..N, (sawBernoulli (k + 1) x : ℂ) * fk1 x := by
    have hint : ∀ j ∈ Set.Ico M N,
        IntervalIntegrable (fun x => (sawBernoulli (k + 1) x : ℂ) * fk1 x) volume
          ((fun j : ℕ => (j : ℝ)) j) ((fun j : ℕ => (j : ℝ)) (j + 1)) := by
      intro j hj; simpa [Nat.cast_succ] using hint_k1 j (Finset.mem_Ico.mpr hj)
    have := intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun j : ℕ => (j : ℝ)) (f := fun x => (sawBernoulli (k + 1) x : ℂ) * fk1 x) (μ := volume) hMN hint
    simpa using this
  -- Boundary telescoping (ℂ).
  have hbdry : (∑ j ∈ Finset.Ico M N,
        ((bernoulliFun (k + 1) 1 : ℂ) * fk (j + 1) - (bernoulliFun (k + 1) 0 : ℂ) * fk j)) / (k + 1)
      = (bernoulliFun (k + 1) 0 : ℂ) * (fk N - fk M) / (k + 1) := by
    congr 1
    rw [hendeq]
    have hcongr : (∑ j ∈ Finset.Ico M N,
        ((bernoulliFun (k + 1) 0 : ℂ) * fk (j + 1) - (bernoulliFun (k + 1) 0 : ℂ) * fk j))
        = (∑ j ∈ Finset.Ico M N,
            (bernoulliFun (k + 1) 0 : ℂ) * (fk ((j : ℝ) + 1) - fk (j : ℝ))) := by
      apply Finset.sum_congr rfl; intro j _; ring
    rw [hcongr, ← Finset.mul_sum, sum_telescope_diff_cpow fk hMN]
  rw [Finset.sum_sub_distrib] at hsum
  rw [← Finset.sum_div, ← Finset.sum_div, htel_k1, htel_k, hbdry] at hsum
  exact hsum

/-! ## K. The order-2 tail identity for the ζ integrand, and its `[N, ∞)` form.

    Raising the K=1 saw remainder integrand `saw₁·(−s x^{−s−1})` to order 2 on the tail `[N, ∞)`.
    Over a finite window `[N, M]` this is `em_saw_step_window_cpow` (k=1); taking `M → ∞` (the K=1
    endpoint value `−s·M^{−s−1} → 0`, and both integrals converge for `Re s > 0`) yields
        ∫_N^∞ saw₁·(−s x^{−s−1})
          = B₂(0)·(s·N^{−s−1})/2  −  (∫_N^∞ saw₂·(s(s+1) x^{−s−2}))/2,
    with `B₂(0) = bernoulli 2 = 1/6`.  This is the order-2 tail EM step in closed form. -/

/-- Integrability of the order-2 tail integrand `saw₂·(s(s+1) x^{−s−2})` on `(N, ∞)` for
    `Re s > 0` (dominated by `(‖s(s+1)‖·(1/6)) x^{−Re s−2}`, exponent `< −1`). -/
theorem em_tail2_integrableOn {s : ℂ} {N : ℕ} (hN : 1 ≤ N) (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (sawBernoulli 2 x : ℂ) * (s * (s + 1) * (x : ℂ) ^ (-s - 2))) (Ioi (N : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hbase : IntegrableOn (fun x : ℝ => (‖s * (s + 1)‖ * (1 / 6)) * x ^ (-s.re - 2)) (Ioi (N : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (a := -s.re - 2) (by linarith) hNpos).const_mul _
  refine Integrable.mono' hbase ?_ ?_
  · apply Measurable.aestronglyMeasurable
    exact (Complex.measurable_ofReal.comp (sawBernoulli_measurable 2)).mul
      (measurable_const.mul (Complex.measurable_ofReal.pow_const _))
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hxpos : (0 : ℝ) < x := lt_trans hNpos hx
    have hnormcpow : ‖(x : ℂ) ^ (-s - 2)‖ = x ^ (-s.re - 2) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
      congr 1
    have hsaw := abs_sawBernoulli_two_le x
    have hrpownn : (0 : ℝ) ≤ x ^ (-s.re - 2) := Real.rpow_nonneg hxpos.le _
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hnormcpow]
    calc |sawBernoulli 2 x| * (‖s * (s + 1)‖ * x ^ (-s.re - 2))
        ≤ (1 / 6) * (‖s * (s + 1)‖ * x ^ (-s.re - 2)) := by gcongr
      _ = (‖s * (s + 1)‖ * (1 / 6)) * x ^ (-s.re - 2) := by ring

/-- The K=1 saw remainder integrand `saw₁·(−s x^{−s−1})` is integrable on `(N, ∞)` for `Re s > 0`
    (the `Ioi 1` version is `EMZetaComplex.em_cpow_remainder_integrableOn_strip`; the `Ioi N`
    version follows since `(N,∞) ⊆ (1,∞)` — but we reprove directly for a clean `N`-based form). -/
theorem em_tail1_integrableOn {s : ℂ} {N : ℕ} (hN : 1 ≤ N) (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1))) (Ioi (N : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hbase : IntegrableOn (fun x : ℝ => (‖s‖ * (1 / 2)) * x ^ (-s.re - 1)) (Ioi (N : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (a := -s.re - 1) (by linarith) hNpos).const_mul _
  refine Integrable.mono' hbase ?_ ?_
  · apply Measurable.aestronglyMeasurable
    exact (Complex.measurable_ofReal.comp (sawBernoulli_measurable 1)).mul
      (measurable_const.mul (Complex.measurable_ofReal.pow_const _))
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hxpos : (0 : ℝ) < x := lt_trans hNpos hx
    have hnormcpow : ‖(x : ℂ) ^ (-s - 1)‖ = x ^ (-s.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, Complex.sub_re, Complex.neg_re, Complex.one_re]
    have hsaw := abs_sawBernoulli_one_le x
    have hrpownn : (0 : ℝ) ≤ x ^ (-s.re - 1) := Real.rpow_nonneg hxpos.le _
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hnormcpow, norm_neg]
    calc |sawBernoulli 1 x| * (‖s‖ * x ^ (-s.re - 1))
        ≤ (1 / 2) * (‖s‖ * x ^ (-s.re - 1)) := by gcongr
      _ = (‖s‖ * (1 / 2)) * x ^ (-s.re - 1) := by ring

/-- **Order-2 tail EM step** (closed form).  For `Re s > 0`, `N ≥ 1`, `s ≠ -1`:
        ∫_N^∞ saw₁·(−s x^{−s−1})
          = (bernoulli 2 : ℂ)·(s·N^{−s−1})/2  −  (∫_N^∞ saw₂·(s(s+1) x^{−s−2}))/2.
    Proven by `em_saw_step_window_cpow` (k=1) over `[N,M]` and `M → ∞`. -/
theorem em_tail2_step {s : ℂ} {N : ℕ} (hN : 1 ≤ N) (hs : 0 < s.re) (hs1 : s ≠ -1) :
    (∫ x in Ioi (N : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
      = (bernoulli 2 : ℂ) * (s * (N : ℝ) ^ (-s - 1)) / 2
        - (∫ x in Ioi (N : ℝ), (sawBernoulli 2 x : ℂ) * (s * (s + 1) * (x : ℂ) ^ (-s - 2))) / 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  set fk : ℝ → ℂ := fun x => -s * (x : ℂ) ^ (-s - 1) with hfk
  set fk1 : ℝ → ℂ := fun x => s * (s + 1) * (x : ℂ) ^ (-s - 2) with hfk1
  have hI1 := em_tail1_integrableOn hN hs
  have hI2 := em_tail2_integrableOn hN hs
  -- Finite-window identity for M ≥ N.
  have hwin : ∀ M : ℕ, N ≤ M →
      (∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli 1 x : ℂ) * fk x)
        = (6⁻¹ : ℂ) * (fk M - fk N) / (1 + 1)
          - (∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli 2 x : ℂ) * fk1 x) / (1 + 1) := by
    intro M hM
    have hd : ∀ x ∈ Icc (N : ℝ) M, HasDerivAt fk (fk1 x) x := by
      intro x hx
      have hx1 : (1 : ℝ) ≤ x := le_trans (by exact_mod_cast hN) hx.1
      exact hasDerivAt_cpow_neg2 hs1 (lt_of_lt_of_le zero_lt_one hx1)
    have hi : ∀ j ∈ Finset.Ico N M, IntervalIntegrable fk1 volume (j : ℝ) (j + 1) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast le_trans hN hj.1
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by linarith)]
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.cpow_const Complex.continuous_ofReal.continuousOn
      intro x hx
      have : (1 : ℝ) ≤ x := le_trans hj1 hx.1
      exact Or.inl (by simp only [Complex.ofReal_re]; linarith)
    have hstep := em_saw_step_window_cpow (k := 1) le_rfl N M hM fk fk1 hd hi
    have hb2 : (bernoulliFun (1 + 1) 0 : ℂ) = 6⁻¹ := by
      norm_num [bernoulliFun_eval_zero]
    rw [hb2] at hstep
    have h2 : (1 : ℕ) + 1 = 2 := rfl
    rw [h2] at hstep
    convert hstep using 3 <;> norm_num
  -- Limits as M → ∞ (over ℕ).
  have hA : Tendsto (fun M : ℕ => ∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli 1 x : ℂ) * fk x) atTop
      (𝓝 (∫ x in Ioi (N : ℝ), (sawBernoulli 1 x : ℂ) * fk x)) :=
    intervalIntegral_tendsto_integral_Ioi N hI1 tendsto_natCast_atTop_atTop
  have hB : Tendsto (fun M : ℕ => ∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli 2 x : ℂ) * fk1 x) atTop
      (𝓝 (∫ x in Ioi (N : ℝ), (sawBernoulli 2 x : ℂ) * fk1 x)) :=
    intervalIntegral_tendsto_integral_Ioi N hI2 tendsto_natCast_atTop_atTop
  -- endpoint `fk M = -s·M^{-s-1} → 0`.
  have hEnd0 : Tendsto (fun M : ℕ => fk (M : ℝ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnorm : (fun M : ℕ => ‖fk (M : ℝ)‖) =ᶠ[atTop] (fun M : ℕ => ‖s‖ * (M : ℝ) ^ (-s.re - 1)) := by
      filter_upwards [eventually_gt_atTop 0] with M hM
      have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
      rw [hfk, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hMpos,
        Complex.sub_re, Complex.neg_re, Complex.one_re]
    refine Tendsto.congr' hnorm.symm ?_
    have hz : Tendsto (fun M : ℕ => (M : ℝ) ^ (-s.re - 1)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun M : ℕ => (M : ℝ) ^ (-(s.re + 1))) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (y := s.re + 1) (by linarith)).comp tendsto_natCast_atTop_atTop
      refine h0.congr (fun M => ?_)
      rw [show -(s.re + 1) = -s.re - 1 by ring]
    simpa using hz.const_mul ‖s‖
  -- The RHS of the finite identity converges to the claimed limit.
  have hRHS : Tendsto (fun M : ℕ =>
      (6⁻¹ : ℂ) * (fk M - fk N) / (1 + 1)
        - (∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli 2 x : ℂ) * fk1 x) / (1 + 1)) atTop
      (𝓝 ((6⁻¹ : ℂ) * (0 - fk N) / (1 + 1)
        - (∫ x in Ioi (N : ℝ), (sawBernoulli 2 x : ℂ) * fk1 x) / (1 + 1))) := by
    apply Tendsto.sub
    · apply Tendsto.div_const
      apply Tendsto.const_mul
      exact hEnd0.sub_const (fk N)
    · exact hB.div_const (1 + 1)
  have hEq : ∀ᶠ M : ℕ in atTop,
      (∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli 1 x : ℂ) * fk x)
        = (6⁻¹ : ℂ) * (fk M - fk N) / (1 + 1)
          - (∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli 2 x : ℂ) * fk1 x) / (1 + 1) := by
    filter_upwards [eventually_ge_atTop N] with M hM using hwin M hM
  have hlim := tendsto_nhds_unique (hA.congr' hEq) hRHS
  rw [hlim, hfk]
  have hbern2 : (bernoulli 2 : ℂ) = 6⁻¹ := by norm_num
  rw [hbern2]
  push_cast
  ring

/-- Third σ-direction derivative of `x^{-s}`: `d/dx(s(s+1)·x^{-s-2}) = -s(s+1)(s+2)·x^{-s-3}` for
    `x > 0` and `s ≠ -2` (so `-s-2 ≠ 0`). -/
theorem hasDerivAt_cpow_neg3 {s : ℂ} (hs : s ≠ -2) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => s * (s + 1) * (x : ℂ) ^ (-s - 2))
      (-(s * (s + 1) * (s + 2)) * (x : ℂ) ^ (-s - 3)) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hr : (-s - 2 : ℂ) ≠ 0 := by intro h; apply hs; linear_combination -h
  have hstep : HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-s - 2))
      ((-s - 2) * (x : ℂ) ^ (-s - 2 - 1)) x := hasDerivAt_ofReal_cpow_const hx0 hr
  have hfull := hstep.const_mul (s * (s + 1))
  have hval : (s * (s + 1)) * ((-s - 2) * (x : ℂ) ^ (-s - 2 - 1))
      = -(s * (s + 1) * (s + 2)) * (x : ℂ) ^ (-s - 3) := by
    rw [show (-s - 2 - 1 : ℂ) = -s - 3 by ring]; ring
  rw [hval] at hfull
  exact hfull

/-- Integrability of the order-3 tail integrand `saw₃·(c₃(s) x^{−s−3})` on `(N, ∞)`. -/
theorem em_tail3_integrableOn {s : ℂ} {N : ℕ} (hN : 1 ≤ N) (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (sawBernoulli 3 x : ℂ) * (emTailCoeff3 s * (x : ℂ) ^ (-s - 3))) (Ioi (N : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hbase : IntegrableOn (fun x : ℝ => (‖emTailCoeff3 s‖ * (1 / 12)) * x ^ (-s.re - 3)) (Ioi (N : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (a := -s.re - 3) (by linarith) hNpos).const_mul _
  refine Integrable.mono' hbase ?_ ?_
  · apply Measurable.aestronglyMeasurable
    exact (Complex.measurable_ofReal.comp (sawBernoulli_measurable 3)).mul
      (measurable_const.mul (Complex.measurable_ofReal.pow_const _))
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hxpos : (0 : ℝ) < x := lt_trans hNpos hx
    have hnormcpow : ‖(x : ℂ) ^ (-s - 3)‖ = x ^ (-s.re - 3) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]; congr 1
    have hsaw := abs_sawBernoulli_three_le x
    have hrpownn : (0 : ℝ) ≤ x ^ (-s.re - 3) := Real.rpow_nonneg hxpos.le _
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hnormcpow]
    calc |sawBernoulli 3 x| * (‖emTailCoeff3 s‖ * x ^ (-s.re - 3))
        ≤ (1 / 12) * (‖emTailCoeff3 s‖ * x ^ (-s.re - 3)) := by gcongr
      _ = (‖emTailCoeff3 s‖ * (1 / 12)) * x ^ (-s.re - 3) := by ring

/-- **Order-3 tail EM step** (closed form).  For `Re s > 0`, `N ≥ 1`, `s ≠ -2`:
        ∫_N^∞ saw₂·(s(s+1) x^{−s−2}) = −(∫_N^∞ saw₃·(c₃(s) x^{−s−3}))/3.
    The boundary term VANISHES because `bernoulli 3 = 0` (odd Bernoulli numbers past B₁ are zero) —
    so the order-3 correction contributes no explicit finite term, only a smaller remainder. -/
theorem em_tail3_step {s : ℂ} {N : ℕ} (hN : 1 ≤ N) (hs : 0 < s.re) (hs2 : s ≠ -2) :
    (∫ x in Ioi (N : ℝ), (sawBernoulli 2 x : ℂ) * (s * (s + 1) * (x : ℂ) ^ (-s - 2)))
      = - (∫ x in Ioi (N : ℝ), (sawBernoulli 3 x : ℂ) * (emTailCoeff3 s * (x : ℂ) ^ (-s - 3))) / 3 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  set fk : ℝ → ℂ := fun x => s * (s + 1) * (x : ℂ) ^ (-s - 2) with hfk
  set fk1 : ℝ → ℂ := fun x => emTailCoeff3 s * (x : ℂ) ^ (-s - 3) with hfk1
  have hI2 := em_tail2_integrableOn hN hs
  have hI3 := em_tail3_integrableOn hN hs
  have hfk1_eq : ∀ x : ℝ, fk1 x = -(s * (s + 1) * (s + 2)) * (x : ℂ) ^ (-s - 3) := by
    intro x; rw [hfk1, emTailCoeff3]
  have hwin : ∀ M : ℕ, N ≤ M →
      (∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli 2 x : ℂ) * fk x)
        = (0 : ℂ) * (fk M - fk N) / (2 + 1)
          - (∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli 3 x : ℂ) * fk1 x) / (2 + 1) := by
    intro M hM
    have hd : ∀ x ∈ Icc (N : ℝ) M, HasDerivAt fk (fk1 x) x := by
      intro x hx
      have hx1 : (1 : ℝ) ≤ x := le_trans (by exact_mod_cast hN) hx.1
      rw [hfk1_eq x]
      exact hasDerivAt_cpow_neg3 hs2 (lt_of_lt_of_le zero_lt_one hx1)
    have hi : ∀ j ∈ Finset.Ico N M, IntervalIntegrable fk1 volume (j : ℝ) (j + 1) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast le_trans hN hj.1
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by linarith), hfk1]
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.cpow_const Complex.continuous_ofReal.continuousOn
      intro x hx
      have : (1 : ℝ) ≤ x := le_trans hj1 hx.1
      exact Or.inl (by simp only [Complex.ofReal_re]; linarith)
    have hstep := em_saw_step_window_cpow (k := 2) (by norm_num) N M hM fk fk1 hd hi
    have hb3 : (bernoulliFun (2 + 1) 0 : ℂ) = 0 := by
      norm_num [bernoulliFun_eval_zero, bernoulli_eq_zero_of_odd (by decide : Odd 3) (by norm_num)]
    rw [hb3] at hstep
    have h3 : (2 : ℕ) + 1 = 3 := rfl
    rw [h3] at hstep
    convert hstep using 3 <;> norm_num
  have hA : Tendsto (fun M : ℕ => ∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli 2 x : ℂ) * fk x) atTop
      (𝓝 (∫ x in Ioi (N : ℝ), (sawBernoulli 2 x : ℂ) * fk x)) :=
    intervalIntegral_tendsto_integral_Ioi N hI2 tendsto_natCast_atTop_atTop
  have hB : Tendsto (fun M : ℕ => ∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli 3 x : ℂ) * fk1 x) atTop
      (𝓝 (∫ x in Ioi (N : ℝ), (sawBernoulli 3 x : ℂ) * fk1 x)) :=
    intervalIntegral_tendsto_integral_Ioi N hI3 tendsto_natCast_atTop_atTop
  have hRHS : Tendsto (fun M : ℕ =>
      (0 : ℂ) * (fk M - fk N) / (2 + 1)
        - (∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli 3 x : ℂ) * fk1 x) / (2 + 1)) atTop
      (𝓝 ((0 : ℂ) * (0 - fk N) / (2 + 1)
        - (∫ x in Ioi (N : ℝ), (sawBernoulli 3 x : ℂ) * fk1 x) / (2 + 1))) := by
    apply Tendsto.sub
    · simp
    · exact hB.div_const (2 + 1)
  have hEq : ∀ᶠ M : ℕ in atTop,
      (∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli 2 x : ℂ) * fk x)
        = (0 : ℂ) * (fk M - fk N) / (2 + 1)
          - (∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli 3 x : ℂ) * fk1 x) / (2 + 1) := by
    filter_upwards [eventually_ge_atTop N] with M hM using hwin M hM
  have hlim := tendsto_nhds_unique (hA.congr' hEq) hRHS
  rw [hlim]
  ring

/-! ## L. The assembled order-3 tail identity and the ζ enclosure (checkBand consumer form). -/

/-- **Combined order-3 tail identity.**  Chaining `em_tail2_step` and `em_tail3_step`, the K=1 saw
    remainder over `[N, ∞)` equals an explicit `N`-decaying finite term plus the order-3 tail:
        ∫_N^∞ saw₁·(−s x^{−s−1})
          = (bernoulli 2 : ℂ)·(s·N^{−s−1})/2  +  (∫_N^∞ saw₃·(c₃(s) x^{−s−3}))/6.
    The `/6` remainder is bounded by `em_tail3_bound`; the finite term `B₂·s·N^{−s−1}/2` is
    elementary (directly boxable). -/
theorem em_tail_order3_identity {s : ℂ} {N : ℕ} (hN : 1 ≤ N) (hs : 0 < s.re)
    (hs1 : s ≠ -1) (hs2 : s ≠ -2) :
    (∫ x in Ioi (N : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
      = (bernoulli 2 : ℂ) * (s * (N : ℝ) ^ (-s - 1)) / 2
        + (∫ x in Ioi (N : ℝ), (sawBernoulli 3 x : ℂ) * (emTailCoeff3 s * (x : ℂ) ^ (-s - 3))) / 6 := by
  rw [em_tail2_step hN hs hs1, em_tail3_step hN hs hs2]
  ring

/-- **THE ASSEMBLED ζ IDENTITY (order-3, `[N,∞)` tail cut).**  For `0 < Re s`, `s ≠ 1`, `N ≥ 1`
    (and `s ≠ -1, -2`, automatic on the strip):
        riemannZeta s
          = 1/(s−1) + 1/2
            + ∫_1^N saw₁·(−s x^{−s−1})               -- the finite `[1,N]` saw part
            + (bernoulli 2 : ℂ)·(s·N^{−s−1})/2         -- the order-2 boundary correction at N
            + R₃(s, N),                                 -- the order-3 remainder
    where `R₃(s,N) = (∫_N^∞ saw₃·(c₃(s) x^{−s−3}))/6` and `‖R₃(s,N)‖` is `em_tail3_bound / 6`.
    At `s = 1/2 + 14i`, `N = 200`, `‖R₃‖ ≤ (1/6)·(1/1000) < 2·10⁻⁴` (`em_tail3_number`).

    This is the checkBand-consumer form: everything before `R₃` is elementary/boxable (a reciprocal,
    constants, one finite saw integral, one `N^{−s−1}` power), and `R₃` is the small controlled tail.
-/
theorem em_zeta_strip3 {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N)
    (hsm1 : s ≠ -1) (hsm2 : s ≠ -2) :
    riemannZeta s
      = 1 / (s - 1) + 1 / 2
        + (∫ x in (1 : ℝ)..(N : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
        + (bernoulli 2 : ℂ) * (s * (N : ℝ) ^ (-s - 1)) / 2
        + (∫ x in Ioi (N : ℝ), (sawBernoulli 3 x : ℂ) * (emTailCoeff3 s * (x : ℂ) ^ (-s - 3))) / 6 := by
  -- K=1 identity: ζ = 1/(s-1) + 1/2 + ∫_1^∞ saw₁·(-s x^{-s-1}).
  have hK1 := em_zeta_strip hs hs1
  -- Split ∫_1^∞ = ∫_1^N + ∫_N^∞.
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hI1_Ioi : IntegrableOn (fun x : ℝ => (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1))) (Ioi 1) :=
    em_cpow_remainder_integrableOn_strip hs
  have hsplit : (∫ x in Ioi (1 : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
      = (∫ x in (1 : ℝ)..(N : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
        + ∫ x in Ioi (N : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) := by
    have hIcc : IntegrableOn (fun x : ℝ => (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1))) (Ioc 1 N) :=
      hI1_Ioi.mono_set (Ioc_subset_Ioi_self)
    have hIoiN : IntegrableOn (fun x : ℝ => (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1))) (Ioi N) :=
      hI1_Ioi.mono_set (Ioi_subset_Ioi h1N)
    have hunion : (∫ x in Ioi (1 : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
        = (∫ x in Ioc (1:ℝ) N, (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
          + ∫ x in Ioi (N:ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) := by
      rw [← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hIcc hIoiN,
        Set.Ioc_union_Ioi_eq_Ioi h1N]
    rw [hunion, ← intervalIntegral.integral_of_le h1N]
  rw [hK1, hsplit, em_tail_order3_identity hN hs hsm1 hsm2]
  ring

/-- The explicit order-3 finite part of the ζ enclosure: everything except the order-3 tail
    remainder.  Elementary/boxable: a reciprocal, constants, one finite `[1,N]` saw integral, and an
    `N^{−s−1}` power. -/
noncomputable def emZetaFinite3 (s : ℂ) (N : ℕ) : ℂ :=
  1 / (s - 1) + 1 / 2
    + (∫ x in (1 : ℝ)..(N : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
    + (bernoulli 2 : ℂ) * (s * (N : ℝ) ^ (-s - 1)) / 2

/-- **THE ζ ENCLOSURE (order-3, checkBand consumer).**  `ζ(s)` differs from the explicit finite part
    `emZetaFinite3 s N` by exactly the order-3 tail remainder `R₃(s,N)/6`, whose norm is bounded by
    `em_tail3_bound / 6` — the sign-tight envelope the K=1 form could not provide. -/
theorem em_zeta_strip3_enclosure {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N)
    (hsm1 : s ≠ -1) (hsm2 : s ≠ -2) :
    ‖riemannZeta s - emZetaFinite3 s N‖
      ≤ (1 / 12) * ‖s * (s + 1) * (s + 2)‖ * (N : ℝ) ^ (-(s.re + 3 - 1)) / (s.re + 3 - 1) / 6 := by
  have hid := em_zeta_strip3 hs hs1 hN hsm1 hsm2
  have hdiff : riemannZeta s - emZetaFinite3 s N
      = (∫ x in Ioi (N : ℝ), (sawBernoulli 3 x : ℂ) * (emTailCoeff3 s * (x : ℂ) ^ (-s - 3))) / 6 := by
    rw [hid, emZetaFinite3]; ring
  rw [hdiff, norm_div, Complex.norm_ofNat]
  apply div_le_div_of_nonneg_right (em_tail3_bound hN hs) (by norm_num)

/-- **Critical-line order-3 enclosure** (the `σ = 1/2` band A4 sweeps).  For `s = 1/2 + it`,
    `‖ζ(s) − emZetaFinite3 s N‖ ≤ (1/12)·‖s(s+1)(s+2)‖·N^{−5/2}/(5/2)/6`.  At `t = 14`, `N = 200`
    this is `< 2·10⁻⁴` (`em_tail3_number`), making the `gLine` box sign-tight. -/
theorem em_zeta_critical_line3_enclosure (t : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta ((1 / 2 : ℂ) + t * Complex.I) - emZetaFinite3 ((1 / 2 : ℂ) + t * Complex.I) N‖
      ≤ (1 / 12) * ‖((1 / 2 : ℂ) + t * Complex.I) * ((1 / 2 : ℂ) + t * Complex.I + 1)
            * ((1 / 2 : ℂ) + t * Complex.I + 2)‖
          * (N : ℝ) ^ (-((1 / 2 : ℝ) + 3 - 1)) / ((1 / 2 : ℝ) + 3 - 1) / 6 := by
  set s : ℂ := (1 / 2 : ℂ) + t * Complex.I with hsdef
  have hre : s.re = 1 / 2 := by
    rw [hsdef]; simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hs1 : s ≠ 1 := by
    intro h; have : s.re = (1 : ℂ).re := by rw [h]
    rw [hre] at this; simp at this
  have hsm1 : s ≠ -1 := by
    intro h; have : s.re = (-1 : ℂ).re := by rw [h]
    rw [hre] at this; norm_num at this
  have hsm2 : s ≠ -2 := by
    intro h; have : s.re = (-2 : ℂ).re := by rw [h]
    rw [hre] at this; norm_num at this
  have h := em_zeta_strip3_enclosure hs hs1 hN hsm1 hsm2
  rw [hre] at h
  exact h

/-- **THE ζ-BOX NUMBER (in-kernel).**  At the G2 pilot point `s = 1/2 + 14·i` with tail cut
    `N = 200`, the true `ζ(s)` lies within `10⁻³` of the explicit finite part `emZetaFinite3 s N`:
        ‖riemannZeta (1/2 + 14i) − emZetaFinite3 (1/2 + 14i) 200‖ ≤ 1/1000.
    This is the sign-tight `gLine` box `checkBand` consumes on the critical line — the order-3 tail
    remainder is `em_tail3_number / 6 < 2·10⁻⁴`, well inside `10⁻³`.  The K=1 enclosure could not
    deliver this (its envelope at `t = 14` is `≈ 14`). -/
theorem em_zeta_critical_line3_number :
    ‖riemannZeta ((1 / 2 : ℂ) + 14 * Complex.I)
        - emZetaFinite3 ((1 / 2 : ℂ) + 14 * Complex.I) 200‖ ≤ (1 : ℝ) / 1000 := by
  set s : ℂ := (1 / 2 : ℂ) + 14 * Complex.I with hsdef
  have hre : s.re = 1 / 2 := by
    rw [hsdef]; simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hs1 : s ≠ 1 := by
    intro h; have : s.re = (1 : ℂ).re := by rw [h]
    rw [hre] at this; simp at this
  have hsm1 : s ≠ -1 := by
    intro h; have : s.re = (-1 : ℂ).re := by rw [h]
    rw [hre] at this; norm_num at this
  have hsm2 : s ≠ -2 := by
    intro h; have : s.re = (-2 : ℂ).re := by rw [h]
    rw [hre] at this; norm_num at this
  -- Reuse the order-3 enclosure and bound its envelope by em_tail3_envelope_le/6 ≤ 1/1000.
  have henc := em_zeta_strip3_enclosure hs hs1 (N := 200) (by norm_num) hsm1 hsm2
  rw [hre] at henc
  refine le_trans henc ?_
  -- The envelope is (1/12)·‖s(s+1)(s+2)‖·200^{-(1/2+3-1)}/(1/2+3-1)/6.  Normalise to -(5/2), 5/2.
  have hexpeq : (-(1 / 2 + (3 : ℝ) - 1) : ℝ) = -(5 / 2 : ℝ) := by norm_num
  have hdeneq : ((1 / 2 : ℝ) + 3 - 1) = (5 / 2 : ℝ) := by norm_num
  rw [hexpeq, hdeneq, hsdef]
  calc (1 / 12) * ‖((1 / 2 : ℂ) + 14 * Complex.I) * ((1 / 2 : ℂ) + 14 * Complex.I + 1)
            * ((1 / 2 : ℂ) + 14 * Complex.I + 2)‖ * (200 : ℝ) ^ (-(5 / 2 : ℝ)) / (5 / 2) / 6
      ≤ (1 / 1000) / 6 := by
        apply div_le_div_of_nonneg_right em_tail3_envelope_le (by norm_num)
    _ ≤ 1 / 1000 := by norm_num

end M6gap.ZetaReflection
