import ArchS7_LogMap

/-!
# ArchS7_Kappa: the Mellin kernel `κ_t` of `P F P` (second half of the (85) bridge)

`κ_t(v) = conj(|v|^{-z} Φ_t(|v|)) / √2` on `|v| > 1` (and `0` on `[-1,1]`), with `z = 1/2 + it` and
S3's `Φ_t(a) = Ψ(z) - ∫₀^a s^{z-1} 2cos(2πs) ds`.  Then:

* `kap t ∈ L²(ℝ)_ev`, `norm_kap_sq`: `‖κ_t‖² = ∫₁^∞ |Φ_t(a)|² da/a = Nnorm t` (S3);
* `mellin_PFP_smooth`: for even smooth compactly supported `φ` vanishing on `[-1,1]`,
  `𝓕Λ(P F φ)(w) = ⟨κ_{-2πw}, φ⟩` for every `w`.  So `κ_t` is "`P F P` applied to the generalised
  eigenvector `x^{z-1}` of `ϑ`", i.e. CC's `A e_t`.

conjecture1_proved = False.
-/

open MeasureTheory Set Filter Topology FourierTransform
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace ArchS7

open ArchS6 ArchS3

set_option linter.unusedSectionVars false

/-! ### The kernel -/

/-- `x^{-z}` with `z = 1/2 + it`, for `x > 0`. -/
def mz (t x : ℝ) : ℂ := ((x : ℝ) : ℂ) ^ (-zt t)

theorem norm_mz {t x : ℝ} (hx : 0 < x) : ‖mz t x‖ = x ^ (-1 / 2 : ℝ) := by
  rw [mz, Complex.norm_cpow_eq_rpow_re_of_pos hx]; simp [zt]; norm_num

/-- The pre-kernel `|v|^{-z} Φ_t(|v|) / √2`. -/
def kapG (t v : ℝ) : ℂ := ((1 / Real.sqrt 2 : ℝ) : ℂ) * mz t |v| * Phi t |v|

/-- `κ_t(v) = conj(kapG t v)` on `|v| > 1`, `0` otherwise. -/
def kapF (t v : ℝ) : ℂ := {v : ℝ | 1 < |v|}.indicator (fun v ↦ conj (kapG t v)) v

theorem measurableSet_one_lt_abs : MeasurableSet {v : ℝ | 1 < |v|} :=
  measurableSet_lt measurable_const measurable_abs

theorem kapF_neg (t v : ℝ) : kapF t (-v) = kapF t v := by
  simp only [kapF, kapG, abs_neg, Set.indicator, Set.mem_ofPred_eq]

/-- The density `‖κ_t‖²`. -/
def kd (t v : ℝ) : ℝ := {v : ℝ | 1 < |v|}.indicator (fun v ↦ ‖Phi t |v|‖ ^ 2 / |v| / 2) v

theorem norm_kapF_sq (t v : ℝ) : ‖kapF t v‖ ^ 2 = kd t v := by
  unfold kapF kd
  by_cases hv : 1 < |v|
  · rw [indicator_of_mem (show v ∈ {v : ℝ | 1 < |v|} from hv),
      indicator_of_mem (show v ∈ {v : ℝ | 1 < |v|} from hv), Complex.norm_conj, kapG, norm_mul,
      norm_mul, Complex.norm_real, norm_mz (by linarith), Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    have hx : 0 < |v| := by linarith
    have h1 : (|v| ^ (-1 / 2 : ℝ)) ^ 2 = |v|⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num; rw [Real.rpow_neg_one]
    have h2 : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
    rw [mul_pow, mul_pow, h1, h2]
    field_simp
  · rw [indicator_of_notMem (show v ∉ {v : ℝ | 1 < |v|} from hv),
      indicator_of_notMem (show v ∉ {v : ℝ | 1 < |v|} from hv)]
    simp

theorem kd_neg (t v : ℝ) : kd t (-v) = kd t v := by
  simp only [kd, abs_neg, Set.indicator, Set.mem_ofPred_eq]

theorem continuousOn_kapG (t : ℝ) : ContinuousOn (fun v ↦ conj (kapG t v)) {v : ℝ | 1 < |v|} := by
  have hpos : ∀ v ∈ {v : ℝ | 1 < |v|}, |v| ∈ Ioi (0 : ℝ) := fun v hv ↦
    show (0 : ℝ) < |v| by linarith [show 1 < |v| from hv]
  have hPhi : ContinuousOn (fun v : ℝ ↦ Phi t |v|) {v : ℝ | 1 < |v|} :=
    (continuousOn_Phi t).comp continuous_abs.continuousOn hpos
  have hmz : ContinuousOn (fun v : ℝ ↦ mz t |v|) {v : ℝ | 1 < |v|} := by
    intro v hv
    refine ContinuousAt.continuousWithinAt ?_
    unfold mz
    exact ContinuousAt.cpow (Complex.continuous_ofReal.comp continuous_abs).continuousAt
      continuousAt_const (Complex.ofReal_mem_slitPlane.2 (hpos v hv))
  exact Complex.continuous_conj.comp_continuousOn ((continuousOn_const.mul hmz).mul hPhi)

theorem aestronglyMeasurable_kapF (t : ℝ) : AEStronglyMeasurable (kapF t) volume := by
  unfold kapF
  rw [aestronglyMeasurable_indicator_iff measurableSet_one_lt_abs]
  exact (continuousOn_kapG t).aestronglyMeasurable measurableSet_one_lt_abs

theorem integrableOn_kd_Ioi (t : ℝ) : IntegrableOn (kd t) (Ioi 1) := by
  have h := (integrableOn_normSq_Phi t).div_const 2
  refine IntegrableOn.congr_fun h (fun v hv ↦ ?_) measurableSet_Ioi
  have hv' : (1 : ℝ) < v := hv
  simp only [kd, indicator_of_mem (show v ∈ {v : ℝ | 1 < |v|} by
    show 1 < |v|; rw [abs_of_pos (by linarith)]; exact hv'), abs_of_pos (by linarith : (0:ℝ) < v)]

theorem integrable_kd (t : ℝ) : Integrable (kd t) := by
  have hI : IntegrableOn (kd t) (Iio (-1) ∪ Ioi 1) := by
    refine IntegrableOn.union ?_ (integrableOn_kd_Ioi t)
    have hmp := (Measure.measurePreserving_neg (volume : Measure ℝ))
    have := (hmp.integrableOn_comp_preimage (Homeomorph.neg ℝ).measurableEmbedding
      (f := kd t) (s := Ioi 1)).2 (integrableOn_kd_Ioi t)
    rw [show (fun x : ℝ ↦ -x) ⁻¹' Ioi 1 = Iio (-1) by ext x; simp [lt_neg]] at this
    refine IntegrableOn.congr_fun this (fun v _ ↦ ?_) measurableSet_Iio
    simp only [Function.comp, kd_neg]
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 hI
  intro v hv
  by_contra h
  apply hv
  simp only [mem_union, mem_Iio, mem_Ioi, not_or, not_lt] at h
  have : ¬ 1 < |v| := by rw [not_lt, abs_le]; constructor <;> linarith [h.1, h.2]
  simp [kd, indicator_of_notMem (show v ∉ {v : ℝ | 1 < |v|} from this)]

theorem memLp_kapF (t : ℝ) : MemLp (kapF t) 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_kapF t)).2 ?_
  simp_rw [norm_kapF_sq]; exact integrable_kd t

/-- `κ_t ∈ L²(ℝ)`. -/
def kap (t : ℝ) : L2R := (memLp_kapF t).toLp _

theorem coeFn_kap (t : ℝ) : (kap t : ℝ → ℂ) =ᵐ[volume] kapF t := MemLp.coeFn_toLp _

theorem kap_mem_evenL2 (t : ℝ) : kap t ∈ evenL2 := by
  rw [mem_evenL2]
  apply Lp.ext
  filter_upwards [coeFn_reflect (kap t), ae_eq_comp_neg (coeFn_kap t), coeFn_kap t] with v e1 e2 e3
  rw [e1, e2, e3, kapF_neg]

theorem integral_even_eq_real {h : ℝ → ℝ} (hi : Integrable h) (he : ∀ x, h (-x) = h x) :
    ∫ x, h x = 2 * ∫ x in Ioi 0, h x := by
  rw [← integral_add_compl measurableSet_Ioi hi, compl_Ioi]
  have : ∫ x in Iic 0, h x = ∫ x in Ioi 0, h x := by
    have hn := integral_comp_neg_Ioi (c := (0 : ℝ)) (f := h)
    rw [neg_zero] at hn
    rw [← hn]
    simp only [he]
  rw [this]; ring

/-- **`‖κ_t‖² = Nnorm t = ∫₁^∞ |Φ_t(a)|² da/a`.** -/
theorem norm_kap_sq (t : ℝ) : ‖kap t‖ ^ 2 = Nnorm t := by
  rw [norm_sq_eq_integral]
  have h1 : ∫ v, ‖(kap t : ℝ → ℂ) v‖ ^ 2 = ∫ v, kd t v := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_kap t] with v hv
    rw [hv, norm_kapF_sq]
  rw [h1, integral_even_eq_real (integrable_kd t) (kd_neg t)]
  have h2 : ∫ v in Ioi 0, kd t v = ∫ v in Ioi 1, ‖Phi t v‖ ^ 2 / v / 2 := by
    have e : ∀ v ∈ Ioi (0 : ℝ), kd t v = (Ioi 1).indicator (fun v ↦ ‖Phi t v‖ ^ 2 / v / 2) v := by
      intro v hv
      have hv0 : (0 : ℝ) < v := hv
      simp only [kd, Set.indicator, Set.mem_ofPred_eq, mem_Ioi, abs_of_pos hv0]
    rw [setIntegral_congr_fun measurableSet_Ioi e, setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.2 (Ioi_subset_Ioi zero_le_one)]
  rw [h2, integral_div, Nnorm]
  ring

end ArchS7
