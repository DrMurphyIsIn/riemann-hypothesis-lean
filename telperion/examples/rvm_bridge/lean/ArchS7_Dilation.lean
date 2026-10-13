import ArchS7_Concrete

/-!
# ArchS7_Dilation: the scaling action `ϑ` on `L²(ℝ)` and on `L²(ℝ)_ev` (interface O3, first half)

CC (61): `ϑ(λ) ξ (v) = λ^{-1/2} ξ(λ⁻¹ v)`.  In the additive variable, `θ t = ϑ(e^t)`:
`(θ t f)(v) = e^{-t/2} f(e^{-t} v)`.

* `thL t : L²(ℝ) →ₗᵢ L²(ℝ)`, `coeFn_thL`, `thL_add` (group law), `thL_zero`.
* `reflect_thL`, `thL_mem_evenL2`: `θ` commutes with `f ↦ f(-·)`.
* `P1_thL_neg`: for `t ≥ 0`, `θ(-t) = ϑ(e^{-t})` maps `ran P₁` into itself (CC (82)).
* `fourier_thF`, `fourier_thL`: `𝓕 (θ t f) = θ(-t) (𝓕 f)` on `L²(ℝ)` (Fourier of a dilation).
* `continuous_thL`: strong continuity `t ↦ θ t f` (density of continuous compactly supported functions).
* `scalingEven : Scaling evenPair` and `isPointwise_scalingEven`: **the concrete `Scaling` of S7's
  `thm47_concrete` exists and acts pointwise**.

conjecture1_proved = False.
-/

open MeasureTheory Set Filter FourierTransform Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

noncomputable section

namespace ArchS7

open ArchS6 ArchS5

set_option linter.unusedSectionVars false

/-! ### The pointwise dilation -/

/-- `(θ t F)(v) = e^{-t/2} F(e^{-t} v)`. -/
def thF (t : ℝ) (F : ℝ → ℂ) (v : ℝ) : ℂ := (Real.exp (-t / 2) : ℂ) * F (Real.exp (-t) * v)

theorem thF_congr {F G : ℝ → ℂ} (h : F =ᵐ[volume] G) (t : ℝ) : thF t F =ᵐ[volume] thF t G := by
  filter_upwards [ae_comp_mul h (Real.exp_pos (-t)).ne'] with v hv
  simp only [thF] at *
  rw [hv]

theorem memLp_comp_mul {F : ℝ → ℂ} (hF : MemLp F 2 volume) {c : ℝ} (hc : c ≠ 0) :
    MemLp (fun v ↦ F (c * v)) 2 volume := by
  have h : MemLp F 2 (volume.map (fun v : ℝ ↦ c * v)) := by
    rw [Real.map_volume_mul_left hc]; exact hF.smul_measure ENNReal.ofReal_ne_top
  exact h.comp_of_map (measurable_const_mul c).aemeasurable

theorem memLp_thF {F : ℝ → ℂ} (hF : MemLp F 2 volume) (t : ℝ) : MemLp (thF t F) 2 volume :=
  (memLp_comp_mul hF (Real.exp_pos (-t)).ne').const_mul _

theorem exp_half_sq (t : ℝ) :
    (Real.exp (-t / 2) : ℂ) * (Real.exp (-t / 2) : ℂ) = (Real.exp (-t) : ℂ) := by
  rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring

/-- `θ t` preserves the pairing `∫ conj F · G`. -/
theorem integral_thF (t : ℝ) (F G : ℝ → ℂ) :
    ∫ v, conj (thF t F v) * thF t G v = ∫ v, conj (F v) * G v := by
  have key := MeasureTheory.Measure.integral_comp_mul_left
    (fun u ↦ conj (F u) * G u) (Real.exp (-t))
  have e : ∀ v, conj (thF t F v) * thF t G v
      = (Real.exp (-t) : ℂ) * (conj (F (Real.exp (-t) * v)) * G (Real.exp (-t) * v)) := by
    intro v
    simp only [thF, map_mul, Complex.conj_ofReal]
    rw [← exp_half_sq]; ring
  simp_rw [e]
  rw [integral_const_mul, key, ← Real.exp_neg, neg_neg, abs_of_pos (Real.exp_pos t),
    Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel,
    Real.exp_zero, Complex.ofReal_one, one_mul]

/-! ### The dilation on `L²(ℝ)` -/

/-- `θ t f` as an element of `L²(ℝ)`. -/
def thRaw (t : ℝ) (f : L2R) : L2R := (memLp_thF (Lp.memLp f) t).toLp _

theorem coeFn_thRaw (t : ℝ) (f : L2R) : (thRaw t f : ℝ → ℂ) =ᵐ[volume] thF t f :=
  MemLp.coeFn_toLp _

theorem inner_thRaw (t : ℝ) (f g : L2R) : ⟪thRaw t f, thRaw t g⟫_ℂ = ⟪f, g⟫_ℂ := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have h1 : (fun v ↦ ⟪(thRaw t f : ℝ → ℂ) v, (thRaw t g : ℝ → ℂ) v⟫_ℂ)
      =ᵐ[volume] fun v ↦ conj (thF t f v) * thF t g v := by
    filter_upwards [coeFn_thRaw t f, coeFn_thRaw t g] with v e1 e2
    rw [e1, e2, RCLike.inner_apply']
  rw [integral_congr_ae h1, integral_thF]
  congr 1; funext v; rw [RCLike.inner_apply']

/-- `θ t` as a linear isometry of `L²(ℝ)`. -/
def thL (t : ℝ) : L2R →ₗᵢ[ℂ] L2R where
  toFun := thRaw t
  map_add' f g := by
    apply Lp.ext
    filter_upwards [coeFn_thRaw t (f + g), thF_congr (Lp.coeFn_add f g) t,
      Lp.coeFn_add (thRaw t f) (thRaw t g), coeFn_thRaw t f, coeFn_thRaw t g] with v e1 e2 e3 e4 e5
    rw [e1, e2, e3, Pi.add_apply, e4, e5]
    simp only [thF, Pi.add_apply]; ring
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [coeFn_thRaw t (c • f), thF_congr (Lp.coeFn_smul c f) t,
      Lp.coeFn_smul c (thRaw t f), coeFn_thRaw t f] with v e1 e2 e3 e4
    rw [e1, e2, RingHom.id_apply, e3, Pi.smul_apply, e4]
    simp only [thF, Pi.smul_apply, smul_eq_mul]; ring
  norm_map' f := by
    have h := congrArg RCLike.re (inner_thRaw t f f)
    rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at h
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem thL_apply (t : ℝ) (f : L2R) : thL t f = thRaw t f := rfl

theorem coeFn_thL (t : ℝ) (f : L2R) : (thL t f : ℝ → ℂ) =ᵐ[volume] thF t f := coeFn_thRaw t f

/-- Group law `θ s θ t = θ (s + t)`. -/
theorem thL_add (s t : ℝ) (f : L2R) : thL s (thL t f) = thL (s + t) f := by
  apply Lp.ext
  filter_upwards [coeFn_thL s (thL t f), thF_congr (coeFn_thL t f) s, coeFn_thL (s + t) f]
    with v e1 e2 e3
  rw [e1, e2, e3]
  simp only [thF]
  have h1 : Real.exp (-t) * (Real.exp (-s) * v) = Real.exp (-(s + t)) * v := by
    rw [← mul_assoc, ← Real.exp_add, show -t + -s = -(s + t) by ring]
  have h2 : (Real.exp (-s / 2) : ℂ) * (Real.exp (-t / 2) : ℂ) = (Real.exp (-(s + t) / 2) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, show -s / 2 + -t / 2 = -(s + t) / 2 by ring]
  rw [h1, ← mul_assoc, h2]

theorem thL_zero (f : L2R) : thL 0 f = f := by
  apply Lp.ext
  filter_upwards [coeFn_thL 0 f] with v e1
  rw [e1]; simp [thF]

theorem thL_neg_thL (t : ℝ) (f : L2R) : thL (-t) (thL t f) = f := by
  rw [thL_add, neg_add_cancel, thL_zero]

theorem inner_thL_left (t : ℝ) (f g : L2R) : ⟪thL t f, g⟫_ℂ = ⟪f, thL (-t) g⟫_ℂ := by
  have h : g = thL t (thL (-t) g) := by rw [thL_add, add_neg_cancel, thL_zero]
  conv_lhs => rw [h]
  exact LinearIsometry.inner_map_map _ _ _

/-! ### Evenness and supports -/

theorem reflect_thL (t : ℝ) (f : L2R) : reflect (thL t f) = thL t (reflect f) := by
  apply Lp.ext
  filter_upwards [coeFn_reflect (thL t f), ae_eq_comp_neg (coeFn_thL t f),
    coeFn_thL t (reflect f), thF_congr (coeFn_reflect f) t] with v e1 e2 e3 e4
  rw [e1, e2, e3, e4]
  simp only [thF, mul_neg]

theorem thL_mem_evenL2 (t : ℝ) {f : L2R} (hf : f ∈ evenL2) : thL t f ∈ evenL2 := by
  rw [mem_evenL2] at hf ⊢
  rw [reflect_thL, hf]

/-- **CC (82)** support fact: for `t ≥ 0`, `ϑ(e^{-t}) = θ(-t)` maps `ran P₁` into itself. -/
theorem P1_thL_neg {t : ℝ} (ht : 0 ≤ t) {f : L2R} (hf : P1 f = f) :
    P1 (thL (-t) f) = thL (-t) f := by
  have hP := coeFn_P1 f
  rw [hf] at hP
  apply Lp.ext
  filter_upwards [coeFn_P1 (thL (-t) f), coeFn_thL (-t) f, thF_congr hP (-t)] with v e1 e2 e3
  rw [e1]
  by_cases hv : v ∈ Icc (-1 : ℝ) 1
  · rw [indicator_of_mem hv]
  · rw [indicator_of_notMem hv, e2, e3]
    have h1 : 1 ≤ Real.exp t := Real.one_le_exp ht
    have hm : Real.exp (-(-t)) * v ∉ Icc (-1 : ℝ) 1 := by
      rw [neg_neg]
      intro h
      apply hv
      rw [mem_Icc, not_and_or, not_le, not_le] at *
      rcases hv with h' | h'
      · exact absurd h.1 (by nlinarith)
      · exact absurd h.2 (by nlinarith)
    simp only [thF]
    rw [indicator_of_notMem hm, mul_zero]

/-! ### Fourier transform of a dilation -/

theorem fourier_congr_ae {F G : ℝ → ℂ} (h : F =ᵐ[volume] G) (w : ℝ) : 𝓕 F w = 𝓕 G w := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae ?_
  filter_upwards [h] with v hv
  rw [hv]

/-- `𝓕 (θ t F) = θ(-t) (𝓕 F)` pointwise (the change of variables `v = e^t u`). -/
theorem fourier_thF (t : ℝ) (F : ℝ → ℂ) (w : ℝ) : 𝓕 (thF t F) w = thF (-t) (𝓕 F) w := by
  rw [Real.fourier_real_eq_integral_exp_smul, thF, Real.fourier_real_eq_integral_exp_smul]
  simp only [thF, smul_eq_mul]
  have hs : ∀ v, Real.exp t * (Real.exp (-t) * v) = v := fun v ↦ by
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  have key := MeasureTheory.Measure.integral_comp_mul_left
    (fun u ↦ Complex.exp (↑(-2 * Real.pi * (Real.exp t * u) * w) * Complex.I)
      * ((Real.exp (-t / 2) : ℂ) * F u)) (Real.exp (-t))
  simp only [hs] at key
  rw [key, ← Real.exp_neg, neg_neg, abs_of_pos (Real.exp_pos t), Complex.real_smul]
  have hI : ∀ u, Complex.exp (↑(-2 * Real.pi * (Real.exp t * u) * w) * Complex.I)
      * ((Real.exp (-t / 2) : ℂ) * F u)
      = (Real.exp (-t / 2) : ℂ)
        * (Complex.exp (↑(-2 * Real.pi * u * (Real.exp (-(-t)) * w)) * Complex.I) * F u) := by
    intro u
    rw [neg_neg, show -2 * Real.pi * (Real.exp t * u) * w = -2 * Real.pi * u * (Real.exp t * w) by ring]
    ring
  simp_rw [hI]
  rw [integral_const_mul, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3
  all_goals first | (funext a; simp only [neg_neg]) | ring

theorem integrable_thF {F : ℝ → ℂ} (hF : Integrable F) (t : ℝ) : Integrable (thF t F) :=
  (hF.comp_mul_left' (Real.exp_pos (-t)).ne').const_mul _

/-- **`𝓕 θ(t) = θ(-t) 𝓕` on `L²(ℝ)`.** -/
theorem fourier_thL (t : ℝ) (f : L2R) : (𝓕 (thL t f : L2R) : L2R) = thL (-t) (𝓕 f) := by
  refine L2R_eq_of_integrable (A := fun f ↦ (𝓕 (thL t f : L2R) : L2R))
    (B := fun f ↦ thL (-t) (𝓕 f)) (continuous_fourier_L2R.comp (thL t).continuous)
    ((thL (-t)).continuous.comp continuous_fourier_L2R) (fun f hf ↦ ?_) f
  have hint : Integrable (thL t f : ℝ → ℂ) :=
    (integrable_thF hf t).congr (coeFn_thL t f).symm
  apply Lp.ext
  filter_upwards [fourier_ae_eq (thL t f) hint, coeFn_thL (-t) (𝓕 f),
    thF_congr (fourier_ae_eq f hf) (-t)] with w e1 e2 e3
  rw [e1, e2, e3, fourier_congr_ae (coeFn_thL t f), fourier_thF]

/-- On even functions: `F θ(t) F = θ(-t)` (CC: `ϑ(ρ) = F⁻¹ ϑ(ρ⁻¹) F`). -/
theorem fourier_thL_fourier {f : L2R} (hf : f ∈ evenL2) (t : ℝ) :
    (𝓕 (thL t (𝓕 f : L2R) : L2R) : L2R) = thL (-t) f := by
  rw [fourier_thL, fourier_fourier_of_even hf]

/-! ### Strong continuity -/

theorem norm_sq_eq_integral (F : L2R) : ‖F‖ ^ 2 = ∫ v, ‖(F : ℝ → ℂ) v‖ ^ 2 := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) F
  rw [MeasureTheory.L2.inner_def] at h
  have h2 : ∀ v, ⟪(F : ℝ → ℂ) v, (F : ℝ → ℂ) v⟫_ℂ = ((‖(F : ℝ → ℂ) v‖ ^ 2 : ℝ) : ℂ) := by
    intro v; rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  simp_rw [h2] at h
  rw [integral_complex_ofReal] at h
  have h3 : ((∫ x, ‖(F : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) = ((‖F‖ ^ 2 : ℝ) : ℂ) := by
    rw [h]; push_cast; rfl
  exact (Complex.ofReal_injective h3).symm

theorem continuous_thF_apply {g : ℝ → ℂ} (hg : Continuous g) (v : ℝ) :
    Continuous fun t ↦ thF t g v := by
  unfold thF; fun_prop

/-- Strong continuity on continuous compactly supported functions (dominated convergence). -/
theorem continuous_thL_of_compact {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hm : MemLp g 2 volume) : Continuous fun t ↦ thL t (hm.toLp g) := by
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  obtain ⟨R₀, hR₀⟩ := hgc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  set R := max R₀ 1
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have zero_out : ∀ u, R < |u| → g u = 0 := fun u hu ↦ image_eq_zero_of_notMem_tsupport
    fun h ↦ by
      have := hR₀ h
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
      linarith [le_max_left R₀ 1]
  have hM0 : 0 ≤ M := (norm_nonneg (g 0)).trans (hM 0)
  set G := hm.toLp g
  have hG : ∀ t, (thL t G : ℝ → ℂ) =ᵐ[volume] thF t g :=
    fun t ↦ (coeFn_thL t G).trans (thF_congr hm.coeFn_toLp t)
  rw [continuous_iff_continuousAt]
  intro t₀
  set K := |t₀| + 1
  set R' := R * Real.exp K
  set C := Real.exp (K / 2) * M
  -- pointwise bound for `|t - t₀| < 1`
  have hbd : ∀ t ∈ Ioo (t₀ - 1) (t₀ + 1), ∀ v, ‖thF t g v‖ ≤ (Icc (-R') R').indicator (fun _ ↦ C) v := by
    intro t ht v
    have htK : |t| < K := by
      rw [abs_lt]; constructor <;> linarith [ht.1, ht.2, le_abs_self t₀, neg_abs_le t₀]
    by_cases hv : v ∈ Icc (-R') R'
    · rw [indicator_of_mem hv, thF, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      refine mul_le_mul (Real.exp_le_exp.2 ?_) (hM _) (norm_nonneg _) (Real.exp_pos _).le
      linarith [neg_le_abs t]
    · rw [indicator_of_notMem hv]
      have hv' : R' < |v| := by
        rw [mem_Icc, not_and_or, not_le, not_le] at hv
        rcases hv with h | h
        · rw [abs_of_neg (by nlinarith [Real.exp_pos K])]; linarith
        · rw [abs_of_pos (by nlinarith [Real.exp_pos K])]; linarith
      have : R < |Real.exp (-t) * v| := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        have h1 : 1 ≤ Real.exp (-t) * Real.exp K := by
          rw [← Real.exp_add]; exact Real.one_le_exp (by have := (abs_lt.1 htK).2; linarith)
        calc R ≤ R * (Real.exp (-t) * Real.exp K) := le_mul_of_one_le_right hRpos.le h1
          _ = Real.exp (-t) * R' := by ring
          _ < Real.exp (-t) * |v| := mul_lt_mul_of_pos_left hv' (Real.exp_pos _)
      rw [thF, zero_out _ this, mul_zero, norm_zero]
  have key : Tendsto (fun t ↦ ‖thL t G - thL t₀ G‖ ^ 2) (𝓝 t₀) (𝓝 0) := by
    have e : ∀ t, ‖thL t G - thL t₀ G‖ ^ 2 = ∫ v, ‖thF t g v - thF t₀ g v‖ ^ 2 := by
      intro t
      rw [norm_sq_eq_integral]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (thL t G) (thL t₀ G), hG t, hG t₀] with v e1 e2 e3
      rw [e1, Pi.sub_apply, e2, e3]
    simp_rw [e]
    have h0 : (0 : ℝ) = ∫ _v : ℝ, (0 : ℝ) := by simp
    rw [h0]
    have hIoo : Ioo (t₀ - 1) (t₀ + 1) ∈ 𝓝 t₀ := Ioo_mem_nhds (by linarith) (by linarith)
    refine tendsto_integral_filter_of_dominated_convergence
      (fun v ↦ (Icc (-R') R').indicator (fun _ ↦ (2 * C) ^ 2) v) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun t ↦ (((continuous_iff_continuousAt.2 fun v ↦ by
        unfold thF; fun_prop).sub (by unfold thF; fun_prop)).norm.pow 2).aestronglyMeasurable
    · filter_upwards [hIoo] with t ht
      refine Eventually.of_forall fun v ↦ ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 := hbd t ht v
      have h2 := hbd t₀ ⟨by linarith, by linarith⟩ v
      by_cases hv : v ∈ Icc (-R') R'
      · rw [indicator_of_mem hv] at h1 h2 ⊢
        have h3 : ‖thF t g v - thF t₀ g v‖ ≤ 2 * C := (norm_sub_le _ _).trans (by linarith)
        exact pow_le_pow_left₀ (norm_nonneg _) h3 2
      · rw [indicator_of_notMem hv] at h1 h2 ⊢
        have a1 : thF t g v = 0 := norm_le_zero_iff.1 h1
        have a2 : thF t₀ g v = 0 := norm_le_zero_iff.1 h2
        rw [a1, a2]; simp
    · exact (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
    · refine Eventually.of_forall fun v ↦ ?_
      have hc : Continuous fun t ↦ ‖thF t g v - thF t₀ g v‖ ^ 2 :=
        ((continuous_thF_apply hg v).sub continuous_const).norm.pow 2
      have := hc.tendsto t₀
      simpa using this
  have key2 : Tendsto (fun t ↦ ‖thL t G - thL t₀ G‖) (𝓝 t₀) (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp key
    simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at this
    exact this
  exact tendsto_iff_norm_sub_tendsto_zero.2 key2

/-- **Strong continuity of the dilation group.** -/
theorem continuous_thL (f : L2R) : Continuous fun t ↦ thL t f := by
  refine continuous_of_uniform_approx_of_continuous fun u hu ↦ ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
  obtain ⟨g, hgc, hle, hgcont, hgm⟩ := (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le
    ENNReal.ofNat_ne_top (ε := ENNReal.ofReal (ε / 2)) (by simpa using half_pos hε)
  refine ⟨fun t ↦ thL t (hgm.toLp g), continuous_thL_of_compact hgcont hgc hgm, fun t ↦ hεu ?_⟩
  rw [dist_eq_norm, ← map_sub, LinearIsometry.norm_map, Lp.norm_def]
  have : eLpNorm (⇑(f - hgm.toLp g)) 2 volume = eLpNorm (⇑f - g) 2 volume := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub f (hgm.toLp g), hgm.coeFn_toLp] with v e1 e2
    rw [e1, Pi.sub_apply, e2, Pi.sub_apply]
  rw [this]
  exact lt_of_le_of_lt (ENNReal.toReal_le_of_le_ofReal (half_pos hε).le hle) (half_lt_self hε)

/-! ### The concrete `Scaling` on `L²(ℝ)_ev` -/

/-- `θ t` restricted to `L²(ℝ)_ev`. -/
def thE (t : ℝ) : evenL2 →L[ℂ] evenL2 :=
  ((thL t).toContinuousLinearMap.comp evenL2.subtypeL).codRestrict evenL2
    fun x ↦ thL_mem_evenL2 t x.2

theorem coe_thE (t : ℝ) (x : evenL2) : ((thE t x : evenL2) : L2R) = thL t (x : L2R) := rfl

/-- **The concrete scaling action `θ t = ϑ(e^t)` on `L²(ℝ)_ev`** (interface O3, first half). -/
def scalingEven : Scaling evenPair where
  θ := thE
  norm_θ t x := by
    show ‖((thE t x : evenL2) : L2R)‖ = ‖(x : L2R)‖
    rw [coe_thE, LinearIsometry.norm_map]
  F_θ_F t x := by
    apply Subtype.ext
    show (𝓕 (thL t (𝓕 (x : L2R) : L2R) : L2R) : L2R) = thL (-t) (x : L2R)
    exact fourier_thL_fourier x.2 t
  P₁_θ t ht x hx := by
    apply Subtype.ext
    show P1 (thL (-t) (x : L2R)) = thL (-t) (x : L2R)
    exact P1_thL_neg ht (congrArg Subtype.val hx)
  cont x y := by
    have : (fun t ↦ ⟪x, thE t y⟫_ℂ) = fun t ↦ ⟪(x : L2R), thL t (y : L2R)⟫_ℂ := by
      funext t; rw [Submodule.coe_inner, coe_thE]
    rw [this]
    exact continuous_const.inner (continuous_thL _)

theorem scalingEven_θ (t : ℝ) (x : evenL2) :
    ((scalingEven.θ t x : evenL2) : L2R) = thL t (x : L2R) := rfl

/-- The concrete scaling acts pointwise (`IsPointwise`, the form used by `thm47_concrete`). -/
theorem isPointwise_scalingEven : IsPointwise scalingEven := fun t f ↦ coeFn_thL t (f : L2R)

end ArchS7

namespace ArchS7

open ArchS6 ArchS8

/-- **CC Theorem 4.7 with the concrete scaling** (`scalingEven`, so O3's scaling half is discharged):
`‖S ϑ(g)‖²_HS = archW g + Re (D.Eplus (autocorr g))`. -/
theorem thm47_even {ι : Type*} (bR : EigenBasis CopR ι) (D : ProlateDataNat) (σ : ℕ ≃ ι)
    (hDlam : ∀ n, D.lam n = bR.μ (σ n)) (hDphi : ∀ n, D.phi n = phiR bR (σ n))
    (hτ : Summable fun i ↦ |(realProlateBasis bR).τ i|)
    (g : ℝ → ℂ) (hf : MeasureTheory.Integrable (WeilExplicit.autocorr g)) (V : evenL2 →L[ℂ] evenL2)
    (hcoef : ∀ v, ((‖(ContinuousLinearMap.adjoint V) v‖ ^ 2 : ℝ) : ℂ)
      = ∫ x, WeilExplicit.autocorr g x * ⟪v, scalingEven.θ x v⟫_ℂ)
    {κ : Type*} (e : HilbertBasis κ ℂ evenL2)
    (h85 : HasSum (fun k ↦ ‖evenPair.hatP (evenPair.P (V (e k)))‖ ^ 2)
      (ArchS3.archW g + (∫ x, WeilExplicit.autocorr g x
        * ProlateBasis.δS (realProlateBasis bR) scalingEven |x|).re)) :
    HasSum (fun k ↦ ‖ArchS6.ProlateBasis.soninProj (S := evenPair) (V (e k))‖ ^ 2)
      (ArchS3.archW g + (D.Eplus (WeilExplicit.autocorr g)).re) :=
  thm47_concrete bR scalingEven isPointwise_scalingEven D σ hDlam hDphi hτ g hf V hcoef e h85

end ArchS7
