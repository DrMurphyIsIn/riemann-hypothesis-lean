import ArchS5_Spectral
import ArchS6_Abstract
import ArchS6_Fourier

/-!
# ArchS6_Proj: `P₁`, extension/restriction to `[a, b]`, and the concrete pair on `L²(ℝ)_ev`

* `extendIcc a b : L²([a,b]) →ₗᵢ L²(ℝ)` (extension by zero) and `restrictIcc a b : L²(ℝ) →L L²([a,b])`,
  with `restrictIcc ∘ extendIcc = 1`, `extendIcc ∘ restrictIcc = 1_{[a,b]} ·`, and
  `⟪extendIcc h, f⟫ = ⟪h, restrictIcc f⟫`.  `L²([a,b])` is S5's `Lp ℂ 2 (volI a b)`.
* `P1 = extendIcc (-1) 1 ∘ restrictIcc (-1) 1`: multiplication by `1_{[-1,1]}` (CC's `P₁`), an
  orthogonal projection commuting with the reflection.
* `evenPair : ProjPair evenL2`: CC's pair `(P₁, F_{e_ℝ})` on `L²(ℝ)_ev`, so every result of
  `ArchS6_Abstract` applies to it.
* `mem_sonin_evenPair`: its Sonin space is CC's `S(1,1)` (Def 4.4): even `ξ` with `ξ = 0` and
  `F_{e_ℝ} ξ = 0` a.e. on `[-1, 1]`.

conjecture1_proved = False.
-/

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal InnerProductSpace

noncomputable section

namespace ArchS6

open ArchS5

set_option linter.unusedSectionVars false

/-- `L²([a, b])`, S5's space. -/
abbrev L2I (a b : ℝ) : Type := Lp ℂ 2 (volI a b)

/-! ### Extension by zero and restriction -/

section Icc

variable (a b : ℝ)

theorem memLp_indicator_L2I (h : L2I a b) : MemLp ((Icc a b).indicator (h : ℝ → ℂ)) 2 volume :=
  (memLp_indicator_iff_restrict measurableSet_Icc).2 (Lp.memLp h)

/-- Extension by zero, as a raw map. -/
def extendFun (h : L2I a b) : L2R := (memLp_indicator_L2I a b h).toLp _

theorem coeFn_extendFun (h : L2I a b) :
    (extendFun a b h : ℝ → ℂ) =ᵐ[volume] (Icc a b).indicator (h : ℝ → ℂ) :=
  MemLp.coeFn_toLp _

theorem indicator_ae_eq_of_L2I {h k : L2I a b} {F G : ℝ → ℂ} (hF : (h : ℝ → ℂ) =ᵐ[volI a b] F)
    (hG : (k : ℝ → ℂ) =ᵐ[volI a b] G) (hFG : ∀ x, F x = G x) :
    (Icc a b).indicator (h : ℝ → ℂ) =ᵐ[volume] (Icc a b).indicator (k : ℝ → ℂ) := by
  have : (h : ℝ → ℂ) =ᵐ[volI a b] (k : ℝ → ℂ) := by
    filter_upwards [hF, hG] with x h1 h2; rw [h1, h2, hFG]
  exact (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Icc).1 this

/-- Extension by zero `L²([a,b]) → L²(ℝ)`, a linear isometry. -/
def extendIcc : L2I a b →ₗᵢ[ℂ] L2R where
  toFun := extendFun a b
  map_add' h k := by
    apply Lp.ext
    have hi := (ae_eq_restrict_iff_indicator_ae_eq (μ := volume) measurableSet_Icc).1
      (Lp.coeFn_add h k)
    filter_upwards [coeFn_extendFun a b (h + k), coeFn_extendFun a b h, coeFn_extendFun a b k,
      Lp.coeFn_add (extendFun a b h) (extendFun a b k), hi] with x e1 e2 e3 e4 e5
    rw [e4, Pi.add_apply, e1, e2, e3, e5]
    by_cases hm : x ∈ Icc a b <;> simp [hm]
  map_smul' c h := by
    apply Lp.ext
    have hi := (ae_eq_restrict_iff_indicator_ae_eq (μ := volume) measurableSet_Icc).1
      (Lp.coeFn_smul c h)
    filter_upwards [coeFn_extendFun a b (c • h), coeFn_extendFun a b h,
      Lp.coeFn_smul c (extendFun a b h), hi] with x e1 e2 e3 e4
    rw [RingHom.id_apply, e3, Pi.smul_apply, e1, e2, e4]
    by_cases hm : x ∈ Icc a b <;> simp [hm]
  norm_map' h := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, extendFun, Lp.norm_toLp]
    rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc, Lp.norm_def]

theorem coeFn_extendIcc (h : L2I a b) :
    (extendIcc a b h : ℝ → ℂ) =ᵐ[volume] (Icc a b).indicator (h : ℝ → ℂ) :=
  coeFn_extendFun a b h

/-- Restriction `L²(ℝ) → L²([a,b])`. -/
def restrictFun (f : L2R) : L2I a b := ((Lp.memLp f).restrict (Icc a b)).toLp _

theorem coeFn_restrictFun (f : L2R) : (restrictFun a b f : ℝ → ℂ) =ᵐ[volI a b] (f : ℝ → ℂ) :=
  MemLp.coeFn_toLp _

/-- Restriction as a linear map. -/
def restrictₗ : L2R →ₗ[ℂ] L2I a b where
  toFun := restrictFun a b
  map_add' f g := by
    apply Lp.ext
    filter_upwards [coeFn_restrictFun a b (f + g), coeFn_restrictFun a b f,
      coeFn_restrictFun a b g, Lp.coeFn_add (restrictFun a b f) (restrictFun a b g),
      ae_restrict_of_ae (Lp.coeFn_add f g)] with x e1 e2 e3 e4 e5
    rw [e4, Pi.add_apply, e1, e2, e3, e5, Pi.add_apply]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [coeFn_restrictFun a b (c • f), coeFn_restrictFun a b f,
      Lp.coeFn_smul c (restrictFun a b f), ae_restrict_of_ae (Lp.coeFn_smul c f)]
      with x e1 e2 e3 e4
    rw [RingHom.id_apply, e3, Pi.smul_apply, e1, e2, e4, Pi.smul_apply]

theorem norm_restrictFun_le (f : L2R) : ‖restrictFun a b f‖ ≤ ‖f‖ := by
  rw [restrictFun, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_restrict_le _ _ _ _)

/-- Restriction `L²(ℝ) → L²([a,b])` as a continuous linear map. -/
def restrictIcc : L2R →L[ℂ] L2I a b :=
  (restrictₗ a b).mkContinuous 1 fun f ↦ by
    rw [one_mul]; exact norm_restrictFun_le a b f

theorem coeFn_restrictIcc (f : L2R) :
    (restrictIcc a b f : ℝ → ℂ) =ᵐ[volI a b] (f : ℝ → ℂ) :=
  coeFn_restrictFun a b f

theorem restrictIcc_extendIcc (h : L2I a b) : restrictIcc a b (extendIcc a b h) = h := by
  apply Lp.ext
  filter_upwards [coeFn_restrictIcc a b (extendIcc a b h),
    ae_restrict_of_ae (coeFn_extendIcc a b h),
    indicator_ae_eq_restrict (f := (h : ℝ → ℂ)) (μ := volume) measurableSet_Icc] with x e1 e2 e3
  rw [e1, e2, e3]

theorem coeFn_extendIcc_restrictIcc (f : L2R) :
    (extendIcc a b (restrictIcc a b f) : ℝ → ℂ) =ᵐ[volume] (Icc a b).indicator (f : ℝ → ℂ) := by
  filter_upwards [coeFn_extendIcc a b (restrictIcc a b f),
    (ae_eq_restrict_iff_indicator_ae_eq (μ := volume) measurableSet_Icc).1
      (coeFn_restrictIcc a b f)] with x e1 e2
  rw [e1, e2]

/-- `⟪E h, f⟫ = ⟪h, R f⟫`: restriction is the adjoint of extension by zero. -/
theorem inner_extendIcc_left (h : L2I a b) (f : L2R) :
    ⟪extendIcc a b h, f⟫_ℂ = ⟪h, restrictIcc a b f⟫_ℂ := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have e1 : (fun x ↦ ⟪(extendIcc a b h : ℝ → ℂ) x, (f : ℝ → ℂ) x⟫_ℂ) =ᵐ[volume]
      (Icc a b).indicator fun x ↦ ⟪(h : ℝ → ℂ) x, (f : ℝ → ℂ) x⟫_ℂ := by
    filter_upwards [coeFn_extendIcc a b h] with x hx
    rw [hx]
    by_cases hm : x ∈ Icc a b
    · simp [indicator_of_mem hm]
    · simp [indicator_of_notMem hm]
  rw [integral_congr_ae e1, integral_indicator measurableSet_Icc]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_restrictIcc a b f] with x hx
  rw [hx]

theorem inner_extendIcc_right (h : L2I a b) (f : L2R) :
    ⟪f, extendIcc a b h⟫_ℂ = ⟪restrictIcc a b f, h⟫_ℂ := by
  rw [← inner_conj_symm, inner_extendIcc_left, inner_conj_symm]

/-- An `L²` function on a bounded interval, extended by zero, is integrable. -/
theorem integrable_extendIcc (h : L2I a b) : Integrable (extendIcc a b h : ℝ → ℂ) := by
  have h1 : Integrable (h : ℝ → ℂ) (volI a b) :=
    (Lp.memLp h).integrable (by norm_num)
  have h2 : Integrable ((Icc a b).indicator (h : ℝ → ℂ)) volume :=
    (integrable_indicator_iff measurableSet_Icc).2 h1
  exact h2.congr (coeFn_extendIcc a b h).symm

end Icc

/-! ### CC's `P₁` -/

/-- CC's `P₁`: multiplication by `1_{[-1,1]}` on `L²(ℝ)`. -/
def P1 : L2R →L[ℂ] L2R := (extendIcc (-1) 1).toContinuousLinearMap ∘L restrictIcc (-1) 1

theorem P1_apply (f : L2R) : P1 f = extendIcc (-1) 1 (restrictIcc (-1) 1 f) := rfl

theorem coeFn_P1 (f : L2R) : (P1 f : ℝ → ℂ) =ᵐ[volume] (Icc (-1 : ℝ) 1).indicator (f : ℝ → ℂ) :=
  coeFn_extendIcc_restrictIcc _ _ f

theorem P1_P1 (f : L2R) : P1 (P1 f) = P1 f := by
  rw [P1_apply, P1_apply, restrictIcc_extendIcc]

theorem inner_P1 (f g : L2R) : ⟪P1 f, g⟫_ℂ = ⟪f, P1 g⟫_ℂ := by
  rw [P1_apply, P1_apply, inner_extendIcc_left, inner_extendIcc_right]

theorem isOrthProj_P1 : IsOrthProj P1 := ⟨P1_P1, inner_P1⟩

theorem P1_extendIcc (h : L2I (-1) 1) : P1 (extendIcc (-1) 1 h) = extendIcc (-1) 1 h := by
  rw [P1_apply, restrictIcc_extendIcc]

theorem neg_mem_Icc_neg_one_one {x : ℝ} : -x ∈ Icc (-1 : ℝ) 1 ↔ x ∈ Icc (-1 : ℝ) 1 := by
  simp only [mem_Icc]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- `P₁` commutes with the reflection. -/
theorem P1_reflect (f : L2R) : P1 (reflect f) = reflect (P1 f) := by
  apply Lp.ext
  filter_upwards [coeFn_P1 (reflect f), coeFn_reflect f, coeFn_reflect (P1 f),
    ae_eq_comp_neg (coeFn_P1 f)] with x e1 e2 e3 e4
  rw [e1, e3, e4]
  by_cases hm : x ∈ Icc (-1 : ℝ) 1
  · rw [indicator_of_mem hm, indicator_of_mem (neg_mem_Icc_neg_one_one.2 hm), e2]
  · rw [indicator_of_notMem hm, indicator_of_notMem (fun h ↦ hm (neg_mem_Icc_neg_one_one.1 h))]

theorem P1_mem_evenL2 {f : L2R} (hf : f ∈ evenL2) : P1 f ∈ evenL2 := by
  rw [mem_evenL2] at hf ⊢
  rw [← P1_reflect, hf]

/-- `P₁ f = 0` iff `f = 0` a.e. on `[-1, 1]`. -/
theorem P1_eq_zero_iff (f : L2R) : P1 f = 0 ↔ (f : ℝ → ℂ) =ᵐ[volI (-1) 1] 0 := by
  rw [ae_eq_restrict_iff_indicator_ae_eq measurableSet_Icc, Set.indicator_zero']
  constructor
  · intro h
    have := coeFn_P1 f
    rw [h] at this
    exact this.symm.trans (Lp.coeFn_zero ℂ 2 volume)
  · intro h
    apply Lp.ext
    filter_upwards [coeFn_P1 f, h, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x e1 e2 e3
    rw [e1, e2, e3]

/-! ### The concrete pair on `L²(ℝ)_ev` -/

/-- `P₁` on `L²(ℝ)_ev`. -/
def P1even : evenL2 →L[ℂ] evenL2 :=
  (P1.comp evenL2.subtypeL).codRestrict evenL2 fun f ↦ P1_mem_evenL2 f.2

theorem coe_P1even (f : evenL2) : (P1even f : L2R) = P1 (f : L2R) := rfl

/-- **CC's pair `(P₁, F_{e_ℝ})` on `L²(ℝ)_ev`** (CC §4, (61)-(62)). -/
def evenPair : ProjPair evenL2 where
  P₁ := P1even
  F := fourierEven
  P₁_P₁ f := Subtype.ext (by rw [coe_P1even, coe_P1even, P1_P1])
  inner_P₁ f g := by
    rw [Submodule.coe_inner, Submodule.coe_inner, coe_P1even, coe_P1even, inner_P1]
  F_F := fourierEven_fourierEven
  inner_F := inner_fourierEven

theorem evenPair_P₁ (f : evenL2) : (evenPair.P₁ f : L2R) = P1 f := rfl

theorem evenPair_F (f : evenL2) : (evenPair.F f : L2R) = 𝓕 (f : L2R) := rfl

/-- `P̂₁ = F P₁ F` on `L²(ℝ)_ev` is CC's `F⁻¹ P₁ F` (and `F P₁ F⁻¹`). -/
theorem evenPair_hatP₁ (f : evenL2) :
    (evenPair.hatP₁ f : L2R) = 𝓕⁻ (P1 (𝓕 (f : L2R) : L2R)) := by
  rw [ProjPair.hatP₁_apply, evenPair_F, evenPair_P₁, evenPair_F,
    fourierInv_eq_fourier_of_even (P1_mem_evenL2 (fourier_mem_evenL2 f.2))]

/-- **Sonin's space `S(1,1)`** (CC Def 4.4): even `ξ ∈ L²(ℝ)` with `ξ = 0` and `F_{e_ℝ} ξ = 0`
a.e. on `[-1, 1]`. -/
theorem mem_sonin_evenPair (f : evenL2) :
    f ∈ evenPair.sonin ↔
      (f : ℝ → ℂ) =ᵐ[volI (-1) 1] 0 ∧ ((𝓕 (f : L2R) : L2R) : ℝ → ℂ) =ᵐ[volI (-1) 1] 0 := by
  rw [ProjPair.mem_sonin]
  have h1 : evenPair.P₁ f = 0 ↔ P1 (f : L2R) = 0 := by
    rw [← evenPair_P₁]; exact ⟨fun h ↦ by rw [h]; rfl, fun h ↦ Subtype.ext h⟩
  have h2 : evenPair.P₁ (evenPair.F f) = 0 ↔ P1 (𝓕 (f : L2R)) = 0 := by
    rw [← evenPair_F, ← evenPair_P₁]; exact ⟨fun h ↦ by rw [h]; rfl, fun h ↦ Subtype.ext h⟩
  rw [h1, h2, P1_eq_zero_iff, P1_eq_zero_iff]

end ArchS6
