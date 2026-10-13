import ArchS7_PFP

/-!
# ArchS7_Density: `𝓕Λ(P F P c) = ⟨κ_{-2πw}, c⟩` a.e., for every `c ∈ L²(ℝ)_ev`

* `mellin_PFP_smooth`: the identity on the smooth class (from `ArchS7_PFP`), as an a.e. identity in `L²`.
* `exists_smooth_near`: even smooth compactly supported functions vanishing on `[-1, 1]` are dense in
  `{a ∈ L²(ℝ)_ev : P₁ a = 0}` (smooth cutoff `χ_m` times the even part of a smooth approximant).
* `mellin_PFP`: the identity for every `c ∈ L²(ℝ)_ev`, by `L²` convergence of the left side, an a.e.
  convergent subsequence, and pointwise convergence of the right side.

conjecture1_proved = False.
-/

open MeasureTheory Set Filter Topology FourierTransform
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace ArchS7

open ArchS6 ArchS3

set_option linter.unusedSectionVars false

/-- The class `𝒮`: even, `C¹`, compactly supported, vanishing on `[-1, 1]`. -/
structure SmoothClass (φ : ℝ → ℂ) : Prop where
  smooth : ContDiff ℝ 1 φ
  compact : HasCompactSupport φ
  even : ∀ x, φ (-x) = φ x
  vanish : ∀ x, |x| ≤ 1 → φ x = 0

theorem SmoothClass.memLp {φ : ℝ → ℂ} (h : SmoothClass φ) : MemLp φ 2 volume :=
  h.smooth.continuous.memLp_of_hasCompactSupport h.compact

/-- `P F` on `L²(ℝ)`, followed by the Mellin transform: `T a = 𝓕Λ(𝓕 a - P₁ 𝓕 a)`. -/
def Tpf : L2R →L[ℂ] L2R := mellinL ∘L (1 - P1) ∘L fourierL

theorem Tpf_apply (a : L2R) : Tpf a = mellinL ((𝓕 a : L2R) - P1 (𝓕 a : L2R)) := rfl

/-- **The identity on the smooth class.** -/
theorem mellin_PFP_smooth {φ : ℝ → ℂ} (h : SmoothClass φ) :
    (Tpf (h.memLp.toLp φ) : ℝ → ℂ) =ᵐ[volume]
      fun w ↦ ⟪kap (-2 * Real.pi * w), h.memLp.toLp φ⟫_ℂ := by
  set c := h.memLp.toLp φ
  have hφi := integrable_phi h.smooth h.compact
  have hci : Integrable (c : ℝ → ℂ) := hφi.congr h.memLp.coeFn_toLp.symm
  have hFc : ((𝓕 c : L2R) : ℝ → ℂ) =ᵐ[volume] 𝓕 φ := by
    filter_upwards [fourier_ae_eq c hci] with w hw
    rw [hw, fourier_congr_ae h.memLp.coeFn_toLp]
  set d : L2R := (𝓕 c : L2R) - P1 (𝓕 c : L2R)
  have hd : (d : ℝ → ℂ) =ᵐ[volume] fun y ↦ (Icc (-1 : ℝ) 1)ᶜ.indicator (𝓕 φ) y := by
    filter_upwards [Lp.coeFn_sub (𝓕 c : L2R) (P1 (𝓕 c : L2R)), coeFn_P1 (𝓕 c : L2R), hFc]
      with y e1 e2 e3
    rw [e1, Pi.sub_apply, e2]
    by_cases hy : y ∈ Icc (-1 : ℝ) 1
    · rw [indicator_of_mem hy, indicator_of_notMem (show y ∉ (Icc (-1 : ℝ) 1)ᶜ from fun h ↦ h hy),
        sub_self]
    · rw [indicator_of_notMem hy, indicator_of_mem (show y ∈ (Icc (-1 : ℝ) 1)ᶜ from hy), sub_zero, e3]
  have hl : (logL d : ℝ → ℂ) =ᵐ[volume] betaF φ := by
    filter_upwards [coeFn_logL d, logF_congr hd] with u e1 e2
    rw [e1, e2, logF, betaF]
    by_cases hu : 0 < u
    · have : Real.exp u ∉ Icc (-1 : ℝ) 1 := fun h ↦ by
        have := Real.exp_le_one_iff.1 h.2; linarith
      rw [indicator_of_mem (show Real.exp u ∈ (Icc (-1 : ℝ) 1)ᶜ from this),
        indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu)]
    · have : Real.exp u ∈ Icc (-1 : ℝ) 1 :=
        ⟨by linarith [Real.exp_pos u], Real.exp_le_one_iff.2 (le_of_not_gt hu)⟩
      rw [indicator_of_notMem (show Real.exp u ∉ (Icc (-1 : ℝ) 1)ᶜ from fun h ↦ h this),
        indicator_of_notMem (show u ∉ Ioi (0 : ℝ) from hu), mul_zero]
  have hli : Integrable (logL d : ℝ → ℂ) :=
    (integrable_betaF h.smooth h.compact).congr hl.symm
  rw [Tpf_apply]
  filter_upwards [fourier_ae_eq (logL d) hli] with w hw
  rw [mellinL_apply, hw, fourier_congr_ae hl,
    fourier_betaF_eq_inner h.smooth h.compact h.even h.vanish h.memLp w]

/-! ### Density of the smooth class -/

/-- The smooth cutoff `χ_m(x) = s((m+1)(x² - 1) - 1)`: `0` on `[-1,1]`, `→ 1` on `|x| > 1`. -/
def chi (m : ℕ) (x : ℝ) : ℝ := Real.smoothTransition ((m + 1) * (x ^ 2 - 1) - 1)

theorem chi_nonneg (m : ℕ) (x : ℝ) : 0 ≤ chi m x := Real.smoothTransition.nonneg _
theorem chi_le_one (m : ℕ) (x : ℝ) : chi m x ≤ 1 := Real.smoothTransition.le_one _

theorem chi_zero {m : ℕ} {x : ℝ} (hx : |x| ≤ 1) : chi m x = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  have : x ^ 2 ≤ 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg x]
  have : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  nlinarith

theorem chi_neg (m : ℕ) (x : ℝ) : chi m (-x) = chi m x := by simp [chi]

theorem contDiff_chi (m : ℕ) : ContDiff ℝ 1 (chi m) :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

theorem tendsto_chi {x : ℝ} (hx : 1 < |x|) : Tendsto (fun m : ℕ ↦ chi m x) atTop (𝓝 1) := by
  have hx2 : 0 < x ^ 2 - 1 := by
    have : 1 < x ^ 2 := by rw [← sq_abs]; nlinarith
    linarith
  refine tendsto_const_nhds.congr' ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / (x ^ 2 - 1))
  filter_upwards [eventually_ge_atTop N] with m hm
  symm
  refine Real.smoothTransition.one_of_one_le ?_
  have hm' : (2 / (x ^ 2 - 1)) < (m : ℝ) + 1 := by
    have : (N : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  rw [div_lt_iff₀ hx2] at hm'
  linarith

/-- `‖g‖ ≤ ‖f‖` when `g = χ f` a.e. with `|χ| ≤ 1`. -/
theorem norm_le_of_ae_mul {f g : L2R} {χ : ℝ → ℝ} (hχ : ∀ x, |χ x| ≤ 1)
    (h : (g : ℝ → ℂ) =ᵐ[volume] fun x ↦ (χ x : ℂ) * (f : ℝ → ℂ) x) : ‖g‖ ≤ ‖f‖ := by
  have h1 : ‖g‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [norm_sq_eq_integral, norm_sq_eq_integral]
    refine integral_mono_ae ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).1
      (Lp.memLp g)) ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).1
      (Lp.memLp f)) ?_
    filter_upwards [h] with x hx
    rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
    have := hχ x
    have h0 : |χ x| ^ 2 ≤ 1 := by nlinarith [abs_nonneg (χ x)]
    nlinarith [sq_nonneg ‖(f : ℝ → ℂ) x‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1

theorem memLp_chi_mul (m : ℕ) (f : L2R) :
    MemLp (fun x ↦ (chi m x : ℂ) * (f : ℝ → ℂ) x) 2 volume :=
  (Lp.memLp f).of_le
    ((Complex.continuous_ofReal.comp (contDiff_chi m).continuous).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f))
    (Eventually.of_forall fun x ↦ by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (chi_nonneg m x)]
      exact mul_le_of_le_one_left (norm_nonneg _) (chi_le_one m x))

/-- `χ_m a → a` in `L²` when `a = 0` on `[-1, 1]`. -/
theorem tendsto_chi_mul {a : L2R} (ha : P1 a = 0) :
    Tendsto (fun m : ℕ ↦ (memLp_chi_mul m a).toLp _) atTop (𝓝 a) := by
  have hP := coeFn_P1 a
  rw [ha] at hP
  have hz : ∀ᵐ x ∂volume, |x| ≤ 1 → (a : ℝ → ℂ) x = 0 := by
    filter_upwards [hP, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x e1 e2 hx
    have hm : x ∈ Icc (-1 : ℝ) 1 := abs_le.1 hx
    rw [indicator_of_mem hm] at e1
    rw [← e1, e2]; rfl
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have key : Tendsto (fun m : ℕ ↦ ‖(memLp_chi_mul m a).toLp _ - a‖ ^ 2) atTop (𝓝 0) := by
    have e : ∀ m : ℕ, ‖(memLp_chi_mul m a).toLp _ - a‖ ^ 2
        = ∫ x, ‖((chi m x : ℂ) - 1) * (a : ℝ → ℂ) x‖ ^ 2 := by
      intro m
      rw [norm_sq_eq_integral]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub ((memLp_chi_mul m a).toLp _) a,
        (memLp_chi_mul m a).coeFn_toLp] with x e1 e2
      rw [e1, Pi.sub_apply, e2, sub_mul, one_mul]
    simp_rw [e]
    have h0 : (0 : ℝ) = ∫ _x : ℝ, (0 : ℝ) := by simp
    rw [h0]
    refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖(a : ℝ → ℂ) x‖ ^ 2) ?_
      ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable a)).1 (Lp.memLp a)) ?_ ?_
    · intro m
      exact (((Complex.continuous_ofReal.comp (contDiff_chi m).continuous).sub
        continuous_const).aestronglyMeasurable.mul (Lp.aestronglyMeasurable a)).norm.pow 2
    · intro m
      refine Eventually.of_forall fun x ↦ ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul, mul_pow]
      have h1 : ‖(chi m x : ℂ) - 1‖ ≤ 1 := by
        rw [show (chi m x : ℂ) - 1 = ((chi m x - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_le]
        constructor <;> linarith [chi_nonneg m x, chi_le_one m x]
      have h2 : ‖(chi m x : ℂ) - 1‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg ((chi m x : ℂ) - 1)]
      nlinarith [sq_nonneg ‖(a : ℝ → ℂ) x‖]
    · filter_upwards [hz] with x hx
      by_cases h1 : |x| ≤ 1
      · rw [hx h1]; simp
      · have hc := tendsto_chi (not_le.1 h1)
        have := (((Complex.continuous_ofReal.tendsto 1).comp hc).sub_const 1).mul_const
          ((a : ℝ → ℂ) x)
        have := (this.norm).pow 2
        simpa using this
  have := (Real.continuous_sqrt.tendsto 0).comp key
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this

instance fact_one_le_two : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩

/-- **Density**: every `a ∈ L²(ℝ)_ev` with `P₁ a = 0` is an `L²` limit of the smooth class. -/
theorem exists_smooth_near {a : L2R} (hae : a ∈ evenL2) (ha : P1 a = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : ℝ → ℂ, ∃ h : SmoothClass φ, ‖h.memLp.toLp φ - a‖ < ε := by
  -- the cutoff
  obtain ⟨m, hm⟩ := ((tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_chi_mul ha)).eventually
    (gt_mem_nhds (half_pos hε))).exists
  -- a smooth approximant
  obtain ⟨f, ⟨ψ, hfψ, hψc, hψs⟩, hf⟩ :=
    (Lp.dense_hasCompactSupport_contDiff (p := 2) (μ := volume) (F := ℂ) (E := ℝ)
      ENNReal.ofNat_ne_top).exists_dist_lt a (half_pos hε)
  rw [dist_comm, dist_eq_norm] at hf
  set φ : ℝ → ℂ := fun x ↦ (chi m x : ℂ) * ((ψ x + ψ (-x)) / 2)
  have hsm : SmoothClass φ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (Complex.ofRealCLM.contDiff.comp (contDiff_chi m)).mul
        (((hψs.of_le (WithTop.coe_le_coe.2 le_top)).add
          ((hψs.of_le (WithTop.coe_le_coe.2 le_top)).comp contDiff_neg)).div_const 2)
    · refine (hψc.add (hψc.comp_homeomorph (Homeomorph.neg ℝ))).mono' ?_
      intro x hx
      refine subset_tsupport _ ?_
      intro h0
      apply hx
      have h0' : ψ x + ψ (-x) = 0 := by simpa using h0
      simp only [φ, h0', zero_div, mul_zero]
    · intro x; simp only [φ, chi_neg, neg_neg, add_comm]
    · intro x hx; simp only [φ, chi_zero hx, Complex.ofReal_zero, zero_mul]
  refine ⟨φ, hsm, ?_⟩
  -- `φ - χ a = χ (even ψ - a)` and `‖even ψ - a‖ ≤ ‖ψ - a‖`
  set E : L2R := (1 / 2 : ℂ) • ((f - a) + reflect (f - a))
  have hE : ‖E‖ ≤ ‖f - a‖ := by
    rw [norm_smul]
    calc ‖(1 / 2 : ℂ)‖ * ‖(f - a) + reflect (f - a)‖ ≤ ‖(1 / 2 : ℂ)‖ * (‖f - a‖ + ‖reflect (f - a)‖) :=
          by gcongr; exact norm_add_le _ _
      _ = ‖f - a‖ := by rw [LinearIsometry.norm_map]; norm_num; ring
  have hEa : (E : ℝ → ℂ) =ᵐ[volume] fun x ↦ (ψ x + ψ (-x)) / 2 - (a : ℝ → ℂ) x := by
    have hev := even_ae hae
    filter_upwards [Lp.coeFn_smul (1 / 2 : ℂ) ((f - a) + reflect (f - a)),
      Lp.coeFn_add (f - a) (reflect (f - a)), Lp.coeFn_sub f a, coeFn_reflect (f - a),
      ae_eq_comp_neg (Lp.coeFn_sub f a), hfψ, ae_eq_comp_neg hfψ, hev] with x e1 e2 e3 e4 e5 e6 e7 e8
    rw [e1, Pi.smul_apply, e2, Pi.add_apply, e3, e4, e5]
    simp only [Pi.sub_apply]
    rw [e6, e7, ← e8, smul_eq_mul]; ring
  have h1 : ‖hsm.memLp.toLp φ - (memLp_chi_mul m a).toLp _‖ ≤ ‖E‖ := by
    refine norm_le_of_ae_mul (χ := chi m) (fun x ↦ by
      rw [abs_of_nonneg (chi_nonneg m x)]; exact chi_le_one m x) ?_
    filter_upwards [Lp.coeFn_sub (hsm.memLp.toLp φ) ((memLp_chi_mul m a).toLp _),
      hsm.memLp.coeFn_toLp, (memLp_chi_mul m a).coeFn_toLp, hEa] with x e1 e2 e3 e4
    rw [e1, Pi.sub_apply, e2, e3, e4]
    simp only [φ]; ring
  calc ‖hsm.memLp.toLp φ - a‖
      ≤ ‖hsm.memLp.toLp φ - (memLp_chi_mul m a).toLp _‖ + ‖(memLp_chi_mul m a).toLp _ - a‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := by
        have : ‖f - a‖ < ε / 2 := hf
        exact add_lt_add_of_le_of_lt (h1.trans (hE.trans this.le)) hm
    _ = ε := add_halves ε

/-! ### The identity for every `c` -/

theorem inner_kap_P1 (t : ℝ) (c : L2R) : ⟪kap t, P1 c⟫_ℂ = 0 := by
  rw [← inner_P1]
  have : P1 (kap t) = 0 := by
    apply Lp.ext
    filter_upwards [coeFn_P1 (kap t), coeFn_kap t, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)]
      with x e1 e2 e3
    rw [e1, e3]
    by_cases hx : x ∈ Icc (-1 : ℝ) 1
    · rw [indicator_of_mem hx, e2, kapF, indicator_of_notMem]
      · rfl
      · show ¬ 1 < |x|
        exact not_lt.2 (abs_le.2 hx)
    · rw [indicator_of_notMem hx]; rfl
  rw [this, inner_zero_left]

/-- **`𝓕Λ(P F P c)(w) = ⟨κ_{-2πw}, c⟩` for a.e. `w`**, every `a ∈ L²(ℝ)_ev` with `P₁ a = 0`. -/
theorem mellin_PFP_of_P1 {a : L2R} (hae : a ∈ evenL2) (ha : P1 a = 0) :
    (Tpf a : ℝ → ℂ) =ᵐ[volume] fun w ↦ ⟪kap (-2 * Real.pi * w), a⟫_ℂ := by
  have hseq : ∀ n : ℕ, ∃ φ : ℝ → ℂ, ∃ h : SmoothClass φ, ‖h.memLp.toLp φ - a‖ < 1 / (n + 1) :=
    fun n ↦ exists_smooth_near hae ha (by positivity)
  choose φ hφ hφa using hseq
  set c : ℕ → L2R := fun n ↦ (hφ n).memLp.toLp (φ n)
  have hc : Tendsto c atTop (𝓝 a) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ (hφa n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hT : Tendsto (fun n ↦ Tpf (c n)) atTop (𝓝 (Tpf a)) := (Tpf.continuous.tendsto a).comp hc
  obtain ⟨ns, hmono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hT).exists_seq_tendsto_ae
  have hall : ∀ᵐ w ∂volume, ∀ n, (Tpf (c n) : ℝ → ℂ) w = ⟪kap (-2 * Real.pi * w), c n⟫_ℂ :=
    ae_all_iff.2 fun n ↦ mellin_PFP_smooth (hφ n)
  filter_upwards [hns, hall] with w h1 h2
  have h3 : Tendsto (fun i ↦ ⟪kap (-2 * Real.pi * w), c (ns i)⟫_ℂ) atTop
      (𝓝 ⟪kap (-2 * Real.pi * w), a⟫_ℂ) :=
    (tendsto_const_nhds.inner (hc.comp (StrictMono.tendsto_atTop ‹StrictMono ns›)))
  simp only [h2] at h1
  exact tendsto_nhds_unique h1 h3

end ArchS7
