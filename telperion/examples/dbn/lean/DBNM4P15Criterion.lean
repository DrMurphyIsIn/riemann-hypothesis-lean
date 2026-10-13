/-
  DBNM4P15Criterion -- lane m4 (Route C milestone M4, synthesis section 7.2 node
  `RH_dbn_p15_criterion`): Polymath15's zero-free region criterion as a kernel theorem.

  * `m4_p15_prop33` -- **Polymath15 Prop 3.3** (arXiv:1904.12438v2 p.15), hypotheses verbatim
    (`DBNM4P15Defs`): if `t0, X > 0`, `0 < y0 ≤ 1`, and (i) `P15ZeroFreeRect X y0 t0`,
    (ii) `P15Canopy X y0 t0`, (iii) `P15Barrier X y0 t0`, then there are no zeroes
    `H_{t0}(x + iy) = 0` with `x ∈ ℝ` and `y ≥ y0`.  UNCONDITIONAL beyond (i)-(iii) and the side
    conditions: its only other inputs are island theorems (de Bruijn's strip contraction
    `H_zero_im_sq_le`, the strip `H0_zero_strip`, `approxHadamard`, Hurwitz).
  * `m4_p15_criterion_of_M1aStep` -- the conclusion of **Polymath15 Thm 1.2** from Prop 3.3's
    hypotheses: for `t ≥ t0 + y0²/2` every zero of `H_t` is real.  CONDITIONAL on the named
    hypothesis `M1aStep` (the parametric de Bruijn step, lane m1); this module does not prove
    `M1aStep`.  With lane m1's `dbn_debruijn_parametric : M1aStep` it becomes the synthesis
    statement of `RH_dbn_p15_criterion` (the lead wires them).

  PROOF METHOD (differs from P15).  P15 proves Prop 3.3 by continuous zero dynamics (its Prop 3.1:
  implicit function theorem, Hermite expansion at repeated zeros, Rouche, minimal bad time).  Here
  the proof is a DISCRETE BARRIER argument on the de Bruijn approximants
  `Gδ δ n = T_δ^n H_0`, `δ² = 2t0/N` (`DBNHeatApprox`):
    1. margins by compactness (`m4_barrier_margin`, `m4_rect_margin`): (iii) + de Bruijn give
       `|H_s| ≥ ε` slightly below the barrier curve `Y(s) = √(y0² + 2(t0 − s))`; (i) + the strip
       give `H_0 ≠ 0` slightly below `Y(0)`;
    2. the lowered curve `Yt(s) = √(y0² − κ + 2(t0 − s))` satisfies
       `Yt(s_n)² = Yt(s_{n+1})² + δ²` exactly along `s_n = n δ²/2`;
    3. `m4_barrier_induction` (`DBNM4LocalStep`): the local step lemma propagates
       "no zero in `{|Re| ≤ X, |Im| ≥ Yt(s_n)}`" from `n` to `n + 1`; the barrier strip is
       zero-free for the approximant by the uniform approximation bound
       `m4_norm_H_sub_Gδ_le` (`≤ t0² C / N < ε`), and zeros beyond the barrier are harmless
       because the iterated de Bruijn step keeps them in `(Im)² ≤ max(1 − 2s_n, 0)`;
    4. Hurwitz (`H_ne_zero_of_approx_on`) on `{|Re| < X, Im > √(y0² − κ)}` passes to `H_{t0}`;
       (ii), (iii) at `t = t0` and de Bruijn cover `|Re| ≥ X`.
  No zero is tracked, no multiplicity case split is needed, and no Rouche / argument principle
  is used (Mathlib at the pin has neither).

  SCOPE.  Prop 3.3 and Thm 1.2 are criteria: they turn hypotheses (i)-(iii) into zero-freeness.
  Nothing here verifies (i)-(iii) for any numbers, so no bound `Λ ≤ c` is proved, and the
  de Bruijn-Newman constant is not even defined on this island.  `Λ ≤ 0` is RH; nothing here
  proves RH.  conjecture1_proved = False.
-/
import DBNM4P15Defs
import DBNM4LocalStep
import DBNM4HeatUniform
import DBNHadamardApprox

open Complex ComplexConjugate Filter Topology Set

namespace DBN

/-! ### Small facts about `H_t` -/

/-- `H_t` is real: `H t (conj z) = conj (H t z)` (from `H_conj`). -/
lemma m4_H_real (t : ℝ) (z : ℂ) : H t (conj z) = conj (H t z) := (H_conj t z).symm

/-- De Bruijn's strip contraction in square-root form: a zero of `H_t` (`t ≥ 0`) has
`Im z ≤ √(1 − 2t)`. -/
lemma m4_im_le_sqrt_of_H_eq_zero {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : H t z = 0) :
    z.im ≤ Real.sqrt (1 - 2 * t) := by
  have h := H_zero_im_sq_le ht hz
  rcases le_total 0 (1 - 2 * t) with h1 | h1
  · rw [max_eq_left h1] at h
    exact (le_abs_self _).trans (Real.abs_le_sqrt h)
  · rw [max_eq_right h1] at h
    have h0 : z.im = 0 := (pow_eq_zero_iff two_ne_zero).mp (le_antisymm h (sq_nonneg _))
    rw [h0]
    exact Real.sqrt_nonneg _

lemma m4_re_add_im_mul_I (x y : ℝ) : ((x : ℂ) + (y : ℂ) * I).re = x := by simp

lemma m4_im_add_im_mul_I (x y : ℝ) : ((x : ℂ) + (y : ℂ) * I).im = y := by simp

/-! ### Margins by compactness -/

/-- **Barrier margin.**  From (iii) and de Bruijn's contraction: there are `η, ε > 0` such that
`‖H_s(x + iy)‖ ≥ ε` whenever `0 ≤ s ≤ t0`, `X ≤ x ≤ X + √(1 − y0²)`, `y0/2 ≤ y ≤ 2` and
`y ≥ √(y0² + 2(t0 − s)) − η`. -/
lemma m4_barrier_margin {X y0 t0 : ℝ} (hiii : P15Barrier X y0 t0) :
    ∃ η > 0, ∃ ε > 0, ∀ s x y : ℝ, 0 ≤ s → s ≤ t0 → X ≤ x → x ≤ X + Real.sqrt (1 - y0 ^ 2) →
      y0 / 2 ≤ y → y ≤ 2 → Real.sqrt (y0 ^ 2 + 2 * (t0 - s)) - y ≤ η →
      ε ≤ ‖H s ((x : ℂ) + (y : ℂ) * I)‖ := by
  set C : Set (ℝ × ℝ × ℝ) :=
    Icc 0 t0 ×ˢ (Icc X (X + Real.sqrt (1 - y0 ^ 2)) ×ˢ Icc (y0 / 2) 2) with hCdef
  have hC : IsCompact C := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hg : Continuous (fun p : ℝ × ℝ × ℝ ↦ H p.1 ((p.2.1 : ℂ) + (p.2.2 : ℂ) * I)) :=
    m4_continuous_H_uncurry.comp
      (by fun_prop : Continuous (fun p : ℝ × ℝ × ℝ ↦ (p.1, (p.2.1 : ℂ) + (p.2.2 : ℂ) * I)))
  have hφ : Continuous (fun p : ℝ × ℝ × ℝ ↦ Real.sqrt (y0 ^ 2 + 2 * (t0 - p.1)) - p.2.2) := by
    fun_prop
  obtain ⟨η, hη, ε, hε, hmar⟩ := m4_compact_margin hC hg.continuousOn hφ.continuousOn (by
    rintro ⟨s, x, y⟩ ⟨⟨hs0, hs1⟩, ⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ hφp
    simp only at hφp ⊢
    have hY : Real.sqrt (y0 ^ 2 + 2 * (t0 - s)) ≤ y := by linarith
    by_cases hup : y ≤ Real.sqrt (1 - 2 * s)
    · exact hiii s x y hx0 hx1 hY hup hs0 hs1
    · intro h0
      have := m4_im_le_sqrt_of_H_eq_zero hs0 h0
      rw [m4_im_add_im_mul_I] at this
      exact hup this)
  refine ⟨η, hη, ε, hε, fun s x y hs0 hs1 hx0 hx1 hy0 hy1 hφ ↦ ?_⟩
  exact hmar (s, x, y) ⟨⟨hs0, hs1⟩, ⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ hφ

/-- **Rectangle margin.**  From (i) and the strip of `H_0`: there is `η > 0` such that
`H_0(x + iy) ≠ 0` whenever `0 ≤ x ≤ X`, `y0/2 ≤ y ≤ 2` and `y ≥ √(y0² + 2t0) − η`. -/
lemma m4_rect_margin {X y0 t0 : ℝ} (hi : P15ZeroFreeRect X y0 t0) :
    ∃ η > 0, ∀ x y : ℝ, 0 ≤ x → x ≤ X → y0 / 2 ≤ y → y ≤ 2 →
      Real.sqrt (y0 ^ 2 + 2 * t0) - y ≤ η → H 0 ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by
  set C : Set (ℝ × ℝ) := Icc 0 X ×ˢ Icc (y0 / 2) 2 with hCdef
  have hC : IsCompact C := isCompact_Icc.prod isCompact_Icc
  have hg : Continuous (fun q : ℝ × ℝ ↦ H 0 ((q.1 : ℂ) + (q.2 : ℂ) * I)) :=
    (differentiable_H 0).continuous.comp (by fun_prop)
  have hφ : Continuous (fun q : ℝ × ℝ ↦ Real.sqrt (y0 ^ 2 + 2 * t0) - q.2) := by fun_prop
  obtain ⟨η, hη, ε, hε, hmar⟩ := m4_compact_margin hC hg.continuousOn hφ.continuousOn (by
    rintro ⟨x, y⟩ ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ hφq
    simp only at hφq ⊢
    have hY : Real.sqrt (y0 ^ 2 + 2 * t0) ≤ y := by linarith
    by_cases hup : y ≤ 1
    · exact hi x y hx0 hx1 hY hup
    · intro h0
      have := H0_zero_strip _ h0
      rw [m4_im_add_im_mul_I] at this
      nlinarith)
  refine ⟨η, hη, fun x y hx0 hx1 hy0 hy1 hφ h0 ↦ ?_⟩
  have := hmar (x, y) ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ hφ
  simp only [h0, norm_zero] at this
  linarith

/-! ### The lowered barrier curve -/

/-- Facts about the lowered curve `√(y0² − κ + 2(t0 − s))` against `√(y0² + 2(t0 − s))`. -/
lemma m4_lowered_curve {y0 t0 κ s : ℝ} (hy0 : 0 < y0) (hκ : 0 < κ) (hκy : κ ≤ 3 * y0 ^ 2 / 4)
    (hs : s ≤ t0) :
    y0 / 2 ≤ Real.sqrt (y0 ^ 2 - κ + 2 * (t0 - s)) ∧
    Real.sqrt (y0 ^ 2 - κ + 2 * (t0 - s)) ^ 2 = y0 ^ 2 - κ + 2 * (t0 - s) ∧
    Real.sqrt (y0 ^ 2 + 2 * (t0 - s)) - Real.sqrt (y0 ^ 2 - κ + 2 * (t0 - s)) ≤ κ / y0 := by
  have hA : 0 ≤ y0 ^ 2 - κ + 2 * (t0 - s) := by nlinarith
  have hA' : 0 ≤ y0 ^ 2 + 2 * (t0 - s) := by nlinarith
  refine ⟨?_, Real.sq_sqrt hA, ?_⟩
  · rw [Real.le_sqrt' (by positivity)]
    nlinarith
  · set a := Real.sqrt (y0 ^ 2 + 2 * (t0 - s)) with ha
    set b := Real.sqrt (y0 ^ 2 - κ + 2 * (t0 - s)) with hb
    have ha2 : a ^ 2 = y0 ^ 2 + 2 * (t0 - s) := Real.sq_sqrt hA'
    have hb2 : b ^ 2 = y0 ^ 2 - κ + 2 * (t0 - s) := Real.sq_sqrt hA
    have hb0 : 0 ≤ b := Real.sqrt_nonneg _
    have hay : y0 ≤ a := by
      rw [ha, Real.le_sqrt' hy0]
      nlinarith
    have hab : b ≤ a := Real.sqrt_le_sqrt (by linarith)
    rw [le_div_iff₀ hy0]
    nlinarith

/-! ### The discrete barrier along the heat path, for one `N` -/

/-- **The approximant `G t0 N` is zero-free on `{|Re| ≤ X, |Im| ≥ √(y0² − κ)}`**, given the two
margins, a small `κ`, and `N` so large that the approximation error `t0² C / N` is below the
barrier margin `ε`. -/
lemma m4_path_zero_free {X y0 t0 κ ηb ηr ε : ℝ} (ht0 : 0 < t0) (hy0 : 0 < y0) (hy1 : y0 ≤ 1)
    (hκ : 0 < κ) (hκt : κ ≤ 2 * t0) (hκy : κ ≤ 3 * y0 ^ 2 / 4) (hκb : κ ≤ y0 * ηb)
    (hκr : κ ≤ y0 * ηr)
    (hbarε : ∀ s x y : ℝ, 0 ≤ s → s ≤ t0 → X ≤ x → x ≤ X + Real.sqrt (1 - y0 ^ 2) →
      y0 / 2 ≤ y → y ≤ 2 → Real.sqrt (y0 ^ 2 + 2 * (t0 - s)) - y ≤ ηb →
      ε ≤ ‖H s ((x : ℂ) + (y : ℂ) * I)‖)
    (hrect : ∀ x y : ℝ, 0 ≤ x → x ≤ X → y0 / 2 ≤ y → y ≤ 2 →
      Real.sqrt (y0 ^ 2 + 2 * t0) - y ≤ ηr → H 0 ((x : ℂ) + (y : ℂ) * I) ≠ 0)
    {N : ℕ} (hN : 1 ≤ N) (hNε : t0 ^ 2 / N * m4ApproxConst t0 2 < ε) :
    ∀ z : ℂ, |z.re| ≤ X → Real.sqrt (y0 ^ 2 - κ) ≤ |z.im| → G t0 N z ≠ 0 := by
  set W : ℝ := Real.sqrt (1 - y0 ^ 2) with hWdef
  set δ : ℝ := Real.sqrt (2 * t0 / N) with hδdef
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ : 0 < δ := Real.sqrt_pos.mpr (by positivity)
  have hδsq : δ ^ 2 = 2 * t0 / N := Real.sq_sqrt (by positivity)
  have hW0 : 0 ≤ W := Real.sqrt_nonneg _
  have hW2 : W ^ 2 = 1 - y0 ^ 2 := Real.sq_sqrt (by nlinarith)
  -- the path times `s_n = n δ²/2 = n t0 / N`
  have hs_eq : ∀ n : ℕ, (n : ℝ) * δ ^ 2 / 2 = n * t0 / N := by
    intro n; rw [hδsq]; field_simp
  have hs0 : ∀ n : ℕ, 0 ≤ (n : ℝ) * δ ^ 2 / 2 := fun n ↦ by positivity
  have hs1 : ∀ n : ℕ, n ≤ N → (n : ℝ) * δ ^ 2 / 2 ≤ t0 := by
    intro n hn
    rw [hs_eq, div_le_iff₀ hNpos]
    have : (n : ℝ) ≤ N := by exact_mod_cast hn
    nlinarith
  -- the lowered barrier curve along the path
  set Yt : ℕ → ℝ := fun n ↦ Real.sqrt (y0 ^ 2 - κ + 2 * (t0 - n * δ ^ 2 / 2)) with hYtdef
  have hYt : ∀ n : ℕ, n ≤ N →
      y0 / 2 ≤ Yt n ∧ Yt n ^ 2 = y0 ^ 2 - κ + 2 * (t0 - n * δ ^ 2 / 2) ∧
      Real.sqrt (y0 ^ 2 + 2 * (t0 - n * δ ^ 2 / 2)) - Yt n ≤ κ / y0 :=
    fun n hn ↦ m4_lowered_curve hy0 hκ hκy (hs1 n hn)
  have hκb' : κ / y0 ≤ ηb := by rw [div_le_iff₀ hy0]; linarith
  have hκr' : κ / y0 ≤ ηr := by rw [div_le_iff₀ hy0]; linarith
  -- the iterated de Bruijn step for the approximants
  have hF0 : ∀ w : ℂ, Gδ δ 0 w = 0 → w.im ^ 2 ≤ 1 := by
    intro w hw
    rw [Gδ_zero] at hw
    exact H0_zero_strip w hw
  have hiter : ∀ n : ℕ, ∀ w : ℂ, Gδ δ n w = 0 → w.im ^ 2 ≤ max (1 - n * δ ^ 2) 0 :=
    fun n w hw ↦ zero_im_sq_le_of_shiftAvg_iterate (F := Gδ δ) hδ (fun k ↦ Gδ_succ δ k)
      (approxHadamard δ hδ) (fun k w ↦ Gδ_conj δ k w) hF0 n w hw
  have hiter1 : ∀ n : ℕ, ∀ w : ℂ, Gδ δ n w = 0 → |w.im| ≤ 1 := by
    intro n w hw
    have h := hiter n w hw
    have h1 : w.im ^ 2 ≤ 1 := h.trans (max_le (by nlinarith [sq_nonneg δ]) zero_le_one)
    rw [← sq_abs] at h1
    nlinarith [abs_nonneg w.im]
  -- the approximation error along the path is below `ε`
  have hA0 := m4ApproxConst_nonneg t0 2
  have happrox : ∀ n : ℕ, n ≤ N → ∀ w : ℂ, |w.im| ≤ 2 →
      ‖H (n * δ ^ 2 / 2) w - Gδ δ n w‖ < ε := by
    intro n hn w hw
    refine lt_of_le_of_lt (m4_norm_H_sub_Gδ_le δ n hw (hs1 n hn)) (lt_of_le_of_lt ?_ hNε)
    apply mul_le_mul_of_nonneg_right _ hA0
    have hδ4 : (n : ℝ) * δ ^ 4 / 4 = n * t0 ^ 2 / (N : ℝ) ^ 2 := by
      rw [show δ ^ 4 = (δ ^ 2) ^ 2 by ring, hδsq]
      field_simp
      ring
    rw [hδ4, div_le_div_iff₀ (by positivity) hNpos]
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn
    have h4 : 0 ≤ t0 ^ 2 * (N : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hnN h4]
  -- run the abstract barrier induction
  have hind := m4_barrier_induction (F := Gδ δ) (X := X) (W := W) (Y := Yt) (N := N) hδ hW0
    (fun k ↦ Gδ_succ δ k) (approxHadamard δ hδ) (fun k w ↦ Gδ_conj δ k w)
    (fun n hn ↦ lt_of_lt_of_le (by positivity) (hYt n hn).1)
    (fun n hn ↦ by
      rw [(hYt n hn.le).2.1, (hYt (n + 1) hn).2.1]
      push_cast
      ring)
    (by
      -- `n = 0`: the approximant is `H 0`
      intro w hwre hwim hw
      rw [Gδ_zero] at hw
      have hw' := m4_zero_abs_of_zero (H_neg 0) (m4_H_real 0) hw
      have hY0 := hYt 0 (Nat.zero_le N)
      simp only [Nat.cast_zero, zero_mul, zero_div, sub_zero] at hY0 hwim
      rcases le_or_gt |w.im| 2 with h2 | h2
      · refine hrect |w.re| |w.im| (abs_nonneg _) hwre (hY0.1.trans hwim) h2 ?_ hw'
        have := hY0.2.2
        linarith
      · have := H0_zero_strip _ hw'
        rw [m4_im_add_im_mul_I] at this
        nlinarith)
    (by
      -- the barrier strip, for the approximant: (iii) margin + uniform approximation
      intro n hn w hwre1 hwre2 hwim hw
      have hw' := m4_zero_abs_of_zero (Gδ_neg δ n) (Gδ_conj δ n) hw
      have hYn := hYt n hn.le
      have him1 : |w.im| ≤ 1 := hiter1 n w hw
      have hε' := hbarε (n * δ ^ 2 / 2) |w.re| |w.im| (hs0 n) (hs1 n hn.le) hwre1.le hwre2
        (hYn.1.trans hwim) (by linarith) (by linarith [hYn.2.2])
      have hap := happrox n hn.le (((|w.re| : ℝ) : ℂ) + ((|w.im| : ℝ) : ℂ) * I)
        (by rw [m4_im_add_im_mul_I, abs_abs]; linarith)
      rw [hw', sub_zero] at hap
      linarith)
    (by
      -- beyond the barrier: `(Im)² ≤ max (1 − 2 s_n) 0 ≤ W² + Yt(s_n)²`
      intro n hn w hw
      have h := hiter n w hw
      have hYn := (hYt n hn.le).2.1
      have hsn := hs1 n hn.le
      rw [hW2, hYn]
      refine h.trans (max_le ?_ ?_)
      · nlinarith
      · nlinarith)
  -- conclusion at `n = N`
  intro z hzre hzim
  have hNt : (N : ℝ) * δ ^ 2 / 2 = t0 := by rw [hs_eq]; field_simp
  have hYN : Yt N = Real.sqrt (y0 ^ 2 - κ) := by
    simp only [hYtdef, hNt, sub_self, mul_zero, add_zero]
  have := hind N le_rfl z hzre (by rw [hYN]; exact hzim)
  exact this

/-! ### The inner rectangle for `H_{t0}` (Hurwitz) -/

/-- **`H_{t0}` is zero-free on an open inner region `{|Re| < X, Im > yl}` with `yl < y0`**,
given (i) and (iii). -/
theorem m4_inner_zero_free {X t0 y0 : ℝ} (ht0 : 0 < t0) (hy0 : 0 < y0) (hy1 : y0 ≤ 1)
    (hi : P15ZeroFreeRect X y0 t0) (hiii : P15Barrier X y0 t0) :
    ∃ yl : ℝ, yl < y0 ∧ ∀ z : ℂ, |z.re| < X → yl < z.im → H t0 z ≠ 0 := by
  obtain ⟨ηb, hηb, ε, hε, hbarε⟩ := m4_barrier_margin hiii
  obtain ⟨ηr, hηr, hrect⟩ := m4_rect_margin hi
  set κ : ℝ := min (min (2 * t0) (3 * y0 ^ 2 / 4)) (y0 * min ηb ηr) with hκdef
  have hκ : 0 < κ := lt_min (lt_min (by positivity) (by positivity))
    (mul_pos hy0 (lt_min hηb hηr))
  have hκt : κ ≤ 2 * t0 := (min_le_left _ _).trans (min_le_left _ _)
  have hκy : κ ≤ 3 * y0 ^ 2 / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hκb : κ ≤ y0 * ηb :=
    (min_le_right _ _).trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hy0.le)
  have hκr : κ ≤ y0 * ηr :=
    (min_le_right _ _).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hy0.le)
  refine ⟨Real.sqrt (y0 ^ 2 - κ), ?_, ?_⟩
  · rw [Real.sqrt_lt' hy0]
    linarith
  · intro z hzre hzim
    have hlim : Tendsto (fun N : ℕ ↦ t0 ^ 2 / N * m4ApproxConst t0 2) atTop (𝓝 0) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (t0 ^ 2)).mul_const (m4ApproxConst t0 2)
      rwa [zero_mul] at this
    have hev : ∀ᶠ N : ℕ in atTop, t0 ^ 2 / N * m4ApproxConst t0 2 < ε :=
      hlim.eventually (gt_mem_nhds hε)
    have hU : IsOpen {w : ℂ | |w.re| < X ∧ Real.sqrt (y0 ^ 2 - κ) < w.im} :=
      (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const).inter
        (isOpen_lt continuous_const Complex.continuous_im)
    refine H_ne_zero_of_approx_on ht0.le hU ?_ ⟨hzre, hzim⟩
    filter_upwards [hev, eventually_ge_atTop 1] with N hNε hN w hw
    exact m4_path_zero_free ht0 hy0 hy1 hκ hκt hκy hκb hκr hbarε hrect hN hNε w hw.1.le
      (hw.2.le.trans (le_abs_self _))

/-! ### Polymath15 Prop 3.3 and the Thm 1.2 conclusion -/

/-- **Polymath15 Proposition 3.3 (zero-free region criterion)**, arXiv:1904.12438v2 p.15.
Suppose `t0, X > 0` and `0 < y0 ≤ 1` obey (i) `P15ZeroFreeRect`, (ii) `P15Canopy`,
(iii) `P15Barrier`.  Then there are no zeroes `H_{t0}(x + iy) = 0` with `x ∈ ℝ` and `y ≥ y0`.
Proved by the discrete barrier argument (module docstring), not by P15's zero dynamics.  The side
condition `0 < X` is kept because it is part of P15's statement; the proof does not use it (for
`X ≤ 0` the inner rectangle is empty and (ii), (iii) at `t = t0` do all the work). -/
theorem m4_p15_prop33 (X t0 y0 : ℝ) (_hX : 0 < X) (ht0 : 0 < t0) (hy0 : 0 < y0) (hy1 : y0 ≤ 1) :
    P15ZeroFreeRect X y0 t0 → P15Canopy X y0 t0 → P15Barrier X y0 t0 →
    ∀ x y : ℝ, y0 ≤ y → H t0 ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by
  intro hi hii hiii x y hy hzero
  obtain ⟨yl, hyl, hU⟩ := m4_inner_zero_free ht0 hy0 hy1 hi hiii
  -- pass to the first-quadrant representative `|x| + iy`
  have hz' := m4_zero_abs_of_zero (H_neg t0) (m4_H_real t0) hzero
  rw [m4_re_add_im_mul_I, m4_im_add_im_mul_I, abs_of_pos (by linarith : (0 : ℝ) < y)] at hz'
  have hup : y ≤ Real.sqrt (1 - 2 * t0) := by
    have := m4_im_le_sqrt_of_H_eq_zero ht0.le hz'
    rwa [m4_im_add_im_mul_I] at this
  rcases lt_or_ge |x| X with h1 | h1
  · -- inside the rectangle: the discrete barrier + Hurwitz
    refine hU _ ?_ ?_ hz'
    · rw [m4_re_add_im_mul_I, abs_abs]; exact h1
    · rw [m4_im_add_im_mul_I]; linarith
  · rcases le_or_gt |x| (X + Real.sqrt (1 - y0 ^ 2)) with h2 | h2
    · -- in the barrier strip at the final time: (iii) with `t = t0`
      refine hiii t0 |x| y h1 h2 ?_ hup ht0.le le_rfl hz'
      rw [sub_self, mul_zero, add_zero, Real.sqrt_sq hy0.le]
      exact hy
    · -- beyond the barrier: (ii)
      exact hii |x| y h2.le hy hup hz'

/-- Prop 3.3 in zero-set form: every zero of `H_{t0}` has `|Im z| < y0`. -/
theorem m4_p15_prop33_abs_im_lt (X t0 y0 : ℝ) (hX : 0 < X) (ht0 : 0 < t0) (hy0 : 0 < y0)
    (hy1 : y0 ≤ 1) (hi : P15ZeroFreeRect X y0 t0) (hii : P15Canopy X y0 t0)
    (hiii : P15Barrier X y0 t0) : ∀ z : ℂ, H t0 z = 0 → |z.im| < y0 := by
  intro z hz
  have hz' := m4_zero_abs_of_zero (H_neg t0) (m4_H_real t0) hz
  by_contra hge
  push Not at hge
  exact m4_p15_prop33 X t0 y0 hX ht0 hy0 hy1 hi hii hiii |z.re| |z.im| hge hz'

/-- Prop 3.3 in upper-region form: `H_{t0}` has no zero with `Im z ≥ y0` (the shape of the
`hfree` hypothesis of lane m1's closing step `m1_real_zeros_of_upper_zero_free`). -/
theorem m4_p15_prop33_upper (X t0 y0 : ℝ) (hX : 0 < X) (ht0 : 0 < t0) (hy0 : 0 < y0)
    (hy1 : y0 ≤ 1) (hi : P15ZeroFreeRect X y0 t0) (hii : P15Canopy X y0 t0)
    (hiii : P15Barrier X y0 t0) : ∀ z : ℂ, y0 ≤ z.im → H t0 z ≠ 0 := by
  intro z hz
  have h := m4_p15_prop33 X t0 y0 hX ht0 hy0 hy1 hi hii hiii z.re z.im hz
  rwa [Complex.re_add_im] at h

/-- **Polymath15 Thm 1.2 conclusion from Prop 3.3's hypotheses, CONDITIONAL on `M1aStep`.**
If `t0, X > 0`, `0 < y0 ≤ 1` and (i)-(iii) hold, then for every `t ≥ t0 + y0²/2` every zero of
`H_t` is real.  The parametric de Bruijn step `M1aStep` (P15 Thm 3.2) is a HYPOTHESIS here; it is
used once, at `(t0, Y) = (t0, y0²)`.  With `M1aStep` discharged (lane m1) this is the synthesis
statement of `RH_dbn_p15_criterion`.  A criterion: nothing here verifies (i)-(iii). -/
theorem m4_p15_criterion_of_M1aStep (hM1a : M1aStep) (X t0 y0 : ℝ) (hX : 0 < X) (ht0 : 0 < t0)
    (hy0 : 0 < y0) (hy1 : y0 ≤ 1) :
    P15ZeroFreeRect X y0 t0 → P15Canopy X y0 t0 → P15Barrier X y0 t0 →
    ∀ t : ℝ, t0 + y0 ^ 2 / 2 ≤ t → ∀ z : ℂ, H t z = 0 → z.im = 0 := by
  intro hi hii hiii t ht z hz
  have hsq : ∀ w : ℂ, H t0 w = 0 → w.im ^ 2 ≤ y0 ^ 2 := by
    intro w hw
    have h := m4_p15_prop33_abs_im_lt X t0 y0 hX ht0 hy0 hy1 hi hii hiii w hw
    rw [← sq_abs]
    exact (pow_lt_pow_left₀ h (abs_nonneg _) two_ne_zero).le
  have hy2 : 0 ≤ y0 ^ 2 := sq_nonneg y0
  have h := hM1a t0 (y0 ^ 2) hsq t (by linarith) z hz
  rw [max_eq_right (by linarith)] at h
  exact (pow_eq_zero_iff two_ne_zero).mp (le_antisymm h (sq_nonneg _))

/-! ### The practical barrier box -/

/-- **The "in practice" barrier implies (iii).**  Polymath15 (p.3) verifies the barrier
numerically on the larger box `X ≤ x ≤ X + 1`, `y0 ≤ y ≤ 1`, `0 ≤ t ≤ t0`; zero-freeness of `H_t`
there implies hypothesis (iii) `P15Barrier X y0 t0` (every `X`, `y0`, `t0`). -/
theorem m4_P15Barrier_of_box {X y0 t0 : ℝ}
    (hbox : ∀ t x y : ℝ, X ≤ x → x ≤ X + 1 → y0 ≤ y → y ≤ 1 → 0 ≤ t → t ≤ t0 →
      H t ((x : ℂ) + (y : ℂ) * I) ≠ 0) : P15Barrier X y0 t0 := by
  intro t x y hx0 hx1 hylo hyhi ht0 ht1
  have hW : Real.sqrt (1 - y0 ^ 2) ≤ 1 := by
    calc Real.sqrt (1 - y0 ^ 2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by nlinarith)
      _ = 1 := Real.sqrt_one
  have hT : Real.sqrt (1 - 2 * t) ≤ 1 := by
    calc Real.sqrt (1 - 2 * t) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
      _ = 1 := Real.sqrt_one
  have hY : y0 ≤ Real.sqrt (y0 ^ 2 + 2 * (t0 - t)) :=
    (le_abs_self y0).trans (Real.abs_le_sqrt (by linarith))
  exact hbox t x y hx0 (by linarith) (hY.trans hylo) (hyhi.trans hT) ht0 ht1

/-! ### Control -/

/-- **Positive control (the hypotheses are consistent).**  At `(X, y0, t0) = (1, 1, 1)` all three
transcribed ranges are empty, so (i)-(iii) hold; `m4_p15_prop33` then yields that `H_1` has no
zero with `Im z ≥ 1`, consistent with de Bruijn (`t = 1 ≥ 1/2`).  This checks satisfiability of
the hypothesis bundle only; a non-vacuous instance with `t0 + y0²/2 < 1/2` needs numerical
verification of (i)-(iii) (milestones M5/M6), which is not done here. -/
theorem m4_p15_hyps_satisfiable : P15ZeroFreeRect 1 1 1 ∧ P15Canopy 1 1 1 ∧ P15Barrier 1 1 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y _ _ hy hy1
    exfalso
    have h3 : (1 : ℝ) < Real.sqrt (1 ^ 2 + 2 * 1) := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    linarith
  · intro x y _ hy hy'
    exfalso
    have : Real.sqrt (1 - 2 * 1 : ℝ) = 0 := Real.sqrt_eq_zero'.mpr (by norm_num)
    linarith
  · intro t x y _ _ hlo hhi _ ht1
    exfalso
    have hlt : Real.sqrt (1 - 2 * t) < Real.sqrt (1 ^ 2 + 2 * (1 - t)) := by
      rcases le_or_gt 0 (1 - 2 * t) with h | h
      · exact Real.sqrt_lt_sqrt h (by linarith)
      · rw [Real.sqrt_eq_zero'.mpr h.le]
        exact Real.sqrt_pos.mpr (by linarith)
    linarith

/-- The control instance of Prop 3.3: `H_1` has no zero with `Im z ≥ 1`. -/
theorem m4_p15_control_instance : ∀ x y : ℝ, 1 ≤ y → H 1 ((x : ℂ) + (y : ℂ) * I) ≠ 0 :=
  m4_p15_prop33 1 1 1 one_pos one_pos one_pos le_rfl m4_p15_hyps_satisfiable.1
    m4_p15_hyps_satisfiable.2.1 m4_p15_hyps_satisfiable.2.2

end DBN

/-! ### Registry-shaped forms (root namespace; proposed nodes, NOT registered by this lane)

Hypotheses inlined verbatim (character-identical to the bodies of `DBN.P15ZeroFreeRect`,
`DBN.P15Canopy`, `DBN.P15Barrier`, `DBN.M1aStep`), so a registry statement needs no new `RHDefs`
vocabulary beyond `DBN.H`. -/

/-- **Polymath15 Prop 3.3**, registry-shaped (proposed node `RH_dbn_p15_prop33`): hypotheses
(i)-(iii) inlined; conclusion: no zero `H_{t0}(x + iy) = 0` with `y ≥ y0`.  A criterion; it
verifies none of (i)-(iii).  Nothing here proves RH.  conjecture1_proved = False. -/
theorem m4_dbn_p15_prop33 :
    ∀ X t0 y0 : ℝ, 0 < X → 0 < t0 → 0 < y0 → y0 ≤ 1 →
    (∀ x y : ℝ, 0 ≤ x → x ≤ X → Real.sqrt (y0 ^ 2 + 2 * t0) ≤ y → y ≤ 1 →
      DBN.H 0 ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0) →
    (∀ x y : ℝ, X + Real.sqrt (1 - y0 ^ 2) ≤ x → y0 ≤ y → y ≤ Real.sqrt (1 - 2 * t0) →
      DBN.H t0 ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0) →
    (∀ t x y : ℝ, X ≤ x → x ≤ X + Real.sqrt (1 - y0 ^ 2) →
      Real.sqrt (y0 ^ 2 + 2 * (t0 - t)) ≤ y → y ≤ Real.sqrt (1 - 2 * t) → 0 ≤ t → t ≤ t0 →
      DBN.H t ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0) →
    ∀ x y : ℝ, y0 ≤ y → DBN.H t0 ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0 :=
  fun X t0 y0 hX ht0 hy0 hy1 hi hii hiii ↦ DBN.m4_p15_prop33 X t0 y0 hX ht0 hy0 hy1 hi hii hiii

/-- **Polymath15 Thm 1.2 conclusion from Prop 3.3's hypotheses**, registry-shaped, with the
parametric de Bruijn step (M1a, synthesis 7.2 `RH_dbn_debruijn_parametric`) as an inlined
HYPOTHESIS.  Applied to lane m1's `dbn_debruijn_parametric` it gives the synthesis statement of
`RH_dbn_p15_criterion`.  Nothing here proves RH.  conjecture1_proved = False. -/
theorem m4_dbn_p15_criterion_of_parametric :
    (∀ t0 Y : ℝ, (∀ z : ℂ, DBN.H t0 z = 0 → z.im ^ 2 ≤ Y) →
      ∀ t : ℝ, t0 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im ^ 2 ≤ max (Y - 2 * (t - t0)) 0) →
    ∀ X t0 y0 : ℝ, 0 < X → 0 < t0 → 0 < y0 → y0 ≤ 1 →
    (∀ x y : ℝ, 0 ≤ x → x ≤ X → Real.sqrt (y0 ^ 2 + 2 * t0) ≤ y → y ≤ 1 →
      DBN.H 0 ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0) →
    (∀ x y : ℝ, X + Real.sqrt (1 - y0 ^ 2) ≤ x → y0 ≤ y → y ≤ Real.sqrt (1 - 2 * t0) →
      DBN.H t0 ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0) →
    (∀ t x y : ℝ, X ≤ x → x ≤ X + Real.sqrt (1 - y0 ^ 2) →
      Real.sqrt (y0 ^ 2 + 2 * (t0 - t)) ≤ y → y ≤ Real.sqrt (1 - 2 * t) → 0 ≤ t → t ≤ t0 →
      DBN.H t ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0) →
    ∀ t : ℝ, t0 + y0 ^ 2 / 2 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im = 0 :=
  fun hM1a X t0 y0 hX ht0 hy0 hy1 hi hii hiii ↦
    DBN.m4_p15_criterion_of_M1aStep hM1a X t0 y0 hX ht0 hy0 hy1 hi hii hiii
