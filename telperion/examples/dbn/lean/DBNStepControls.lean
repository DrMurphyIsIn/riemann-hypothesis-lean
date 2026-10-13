/-
  DBNStepControls -- kernel-checked positive and negative controls for the discrete de Bruijn
  step of `DBNStep.lean` (Route C / C3 groundwork, obligation L4 of
  telperion/docs/DESIGN_RH_dbn_debruijn_real_zeros_2026-09-22.md, section 2.2 and the hand
  checks of section 8).

    * POSITIVE control (`f z = 1 + z²`, zeros `±i`, strip `Δ2 = 1`): `f` carries even Hadamard
      data (`τ 0 = i`), is real, and its zeros lie in the strip, so every hypothesis of
      `EvenHadamardData.shiftAvg_zero_im_sq_le` is met by a concrete function (the lemma is not
      vacuous); and `T_δ f = 1 − δ² + z²` has the zero `i √(1 − δ²)` for `0 < δ < 1`, where
      `(Im w)² = 1 − δ² = max (1 − δ²) 0`: the step bound is ATTAINED (it is sharp).
    * NEGATIVE control (`f z = z² − 2i`, zeros `±(1 + i)`, strip `Δ2 = 1`, NOT real): `f` carries
      even Hadamard data (`c = −2i`, `τ 0 = (1 − i)/2`) and its zeros lie in the strip, but with
      `δ = √15 / 2` the function `T_δ f = z² − δ² − 2i` vanishes at `w = 2 + i/2`, where
      `(Im w)² = 1/4 > 0 = max (1 − δ²) 0`.  So the reality hypothesis of the step lemma is
      load-bearing: the conclusion is FALSE without it (memo section 2.2 needs zeros closed
      under conjugation; the conjugate expansion in `DBNStep` is exactly where reality enters).

  Nothing here proves RH or anything about `H_t`.  conjecture1_proved = False.
-/
import DBNStep

open Complex ComplexConjugate Filter Topology

namespace DBN

/-! ### Positive control: `f z = 1 + z²` -/

/-- `1 + z² = 1 − z² τ²` with `τ = i`: even Hadamard data with exactly one nontrivial factor. -/
noncomputable def evenHadamardData_one_add_sq : EvenHadamardData (fun z : ℂ ↦ 1 + z ^ 2) where
  c := 1
  m := 0
  τ := fun k ↦ if k = 0 then I else 0
  tendsto_prod := by
    intro z
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Finset.prod_eq_single (0 : ℕ)]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h

lemma one_add_sq_conj (z : ℂ) :
    (fun z : ℂ ↦ 1 + z ^ 2) (conj z) = conj ((fun z : ℂ ↦ 1 + z ^ 2) z) := by
  simp [map_add, map_pow]

lemma one_add_sq_zero_im_sq_le (z : ℂ) (hz : (fun z : ℂ ↦ 1 + z ^ 2) z = 0) :
    z.im ^ 2 ≤ 1 := by
  have h1 := congrArg Complex.re hz
  have h2 := congrArg Complex.im hz
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re, sq, Complex.mul_re,
    Complex.add_im, Complex.one_im, Complex.zero_im, Complex.mul_im] at h1 h2
  nlinarith [sq_nonneg z.re, sq_nonneg z.im]

/-- `T_δ (1 + z²) = 1 − δ² + z²`. -/
lemma shiftAvg_one_add_sq (δ : ℝ) (z : ℂ) :
    shiftAvg δ (fun z : ℂ ↦ 1 + z ^ 2) z = 1 - (δ : ℂ) ^ 2 + z ^ 2 := by
  unfold shiftAvg
  ring_nf
  rw [I_sq]
  ring

/-- **Positive control, non-vacuity**: the step lemma applies to `1 + z²` (all hypotheses met). -/
theorem step_one_add_sq {δ : ℝ} (hδ : 0 < δ) {w : ℂ}
    (hw : shiftAvg δ (fun z : ℂ ↦ 1 + z ^ 2) w = 0) : w.im ^ 2 ≤ max (1 - δ ^ 2) 0 :=
  evenHadamardData_one_add_sq.shiftAvg_zero_im_sq_le one_add_sq_conj hδ one_add_sq_zero_im_sq_le hw

/-- **Positive control, sharpness**: for `0 < δ < 1` the bound of the step lemma is attained by
`T_δ (1 + z²)` at `w = i √(1 − δ²)`. -/
theorem step_bound_attained {δ : ℝ} (hδ1 : δ < 1) (hδ : 0 < δ) :
    ∃ w : ℂ, shiftAvg δ (fun z : ℂ ↦ 1 + z ^ 2) w = 0 ∧ w.im ^ 2 = max (1 - δ ^ 2) 0 := by
  have hpos : 0 < 1 - δ ^ 2 := by nlinarith
  refine ⟨I * (Real.sqrt (1 - δ ^ 2) : ℂ), ?_, ?_⟩
  · have hs : ((Real.sqrt (1 - δ ^ 2) : ℝ) : ℂ) ^ 2 = 1 - (δ : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hpos.le]
      push_cast
      ring
    rw [shiftAvg_one_add_sq, mul_pow, I_sq, hs]
    ring
  · rw [max_eq_left hpos.le]
    simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
      Complex.ofReal_re, one_mul, zero_add]
    exact Real.sq_sqrt hpos.le

/-! ### Negative control: reality is load-bearing -/

/-- `z² − 2i = −2i (1 − z² τ²)` with `τ = (1 − i)/2` (`τ² = −i/2`). -/
noncomputable def evenHadamardData_sq_sub_two_I : EvenHadamardData (fun z : ℂ ↦ z ^ 2 - 2 * I) where
  c := -2 * I
  m := 0
  τ := fun k ↦ if k = 0 then (1 - I) / 2 else 0
  tendsto_prod := by
    intro z
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Finset.prod_eq_single (0 : ℕ)]
    · simp only [↓reduceIte, mul_zero, pow_zero, mul_one]
      linear_combination z ^ 2 * (1 - I / 2) * I_sq
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h

lemma sq_sub_two_I_zero_im_sq_le (z : ℂ) (hz : (fun z : ℂ ↦ z ^ 2 - 2 * I) z = 0) :
    z.im ^ 2 ≤ 1 := by
  have h1 := congrArg Complex.re hz
  have h2 := congrArg Complex.im hz
  simp only [Complex.sub_re, Complex.zero_re, sq, Complex.mul_re, Complex.re_ofNat,
    Complex.I_re, Complex.im_ofNat, Complex.I_im, Complex.sub_im, Complex.zero_im,
    Complex.mul_im] at h1 h2
  -- h1 : re² − im² = 0, h2 : 2 re im = 2
  have hri : z.re * z.im = 1 := by linarith
  have h4 : z.im ^ 2 * z.im ^ 2 = 1 := by
    have : (z.re * z.im) ^ 2 = 1 := by rw [hri]; norm_num
    nlinarith
  nlinarith [sq_nonneg (z.im ^ 2 - 1), sq_nonneg z.im]

/-- `T_δ (z² − 2i) = z² − δ² − 2i`. -/
lemma shiftAvg_sq_sub_two_I (δ : ℝ) (z : ℂ) :
    shiftAvg δ (fun z : ℂ ↦ z ^ 2 - 2 * I) z = z ^ 2 - (δ : ℂ) ^ 2 - 2 * I := by
  unfold shiftAvg
  ring_nf
  rw [I_sq]
  ring

/-- **Negative control**: WITHOUT the reality hypothesis the conclusion of the step lemma fails.
`f z = z² − 2i` has even Hadamard data and all its zeros in `(Im z)² ≤ 1`, yet for
`δ = √15 / 2` the shifted function `T_δ f` vanishes at `w = 2 + i/2` with
`(Im w)² = 1/4 > 0 = max (1 − δ²) 0`. -/
theorem step_needs_reality :
    ∃ (f : ℂ → ℂ) (_ : EvenHadamardData f) (δ : ℝ), 0 < δ ∧
      (∀ z, f z = 0 → z.im ^ 2 ≤ 1) ∧
      ∃ w : ℂ, shiftAvg δ f w = 0 ∧ max (1 - δ ^ 2) 0 < w.im ^ 2 := by
  have h15 : Real.sqrt 15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)
  refine ⟨fun z : ℂ ↦ z ^ 2 - 2 * I, evenHadamardData_sq_sub_two_I, Real.sqrt 15 / 2,
    by positivity, sq_sub_two_I_zero_im_sq_le, 2 + I / 2, ?_, ?_⟩
  · rw [shiftAvg_sq_sub_two_I]
    have hδ : ((Real.sqrt 15 / 2 : ℝ) : ℂ) ^ 2 = 15 / 4 := by
      rw [← Complex.ofReal_pow, div_pow, h15]
      push_cast
      ring
    rw [hδ]
    ring_nf
    rw [I_sq]
    ring
  · have hmax : max (1 - (Real.sqrt 15 / 2) ^ 2) 0 = 0 := by
      rw [div_pow, h15]
      norm_num
    rw [hmax]
    simp only [Complex.add_im, Complex.div_ofNat_im, Complex.I_im, Complex.im_ofNat]
    norm_num

end DBN
