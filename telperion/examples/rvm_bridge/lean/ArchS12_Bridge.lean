/-
  ArchS12_Bridge -- STAGE S12, shared bridges A1 + A2 (rvm_bridge island, 2026-10-11).
  conjecture1_proved = False.  Nothing here is RH progress.

  S11's spectral certificate is a statement about `Lp ℂ 2 (volI 0 ℓ)` and the operator
  `KI ℓ (chiK D) _` with kernel χ(y - x) on `[0, ℓ]²`.  S8's `prop55_lift` is a function-level double
  integral over `ℝ²`, with test functions supported in `[-L, L]`.  This module connects the two.

  A2 (Lp → functions): for continuous `F` vanishing off `[0, ℓ]` and `f = F` in `L²([0, ℓ])`,
    re ⟪T_κ f, f⟫ = re ∫∫ conj F(x) κ(x, y) F(y),  ‖f‖² = re ∫ conj F · F,  ⟪1, f⟫ = ∫ F.
  A1 (translation): x ↦ x - L is an isometry; translation-invariant kernels k(y - x) give the same
    double integral for `h` and `F = h(· - L)`.
  Then CC's χ: on tsupport h × tsupport h ⊆ [-L, L]², |y - x| ≤ 2L ≤ log 2, so S11's clamped kernel
  `chiK D` agrees with S8's `D.chi (y - x)`.  Results (namespace `ArchS12`):
    * `form_chi_half`:  re ∫∫ conj h(x) h(y) χ(y - x) ≤ 0.95921 · re ∫ conj h · h   (tsupport h ⊆ [-1/4, 1/4]);
    * `form_chi_log2`:  re ∫∫ … ≤ 0.9995 · re ∫ conj h · h + 0.058 ‖∫ h‖² / log 2  (tsupport h ⊆ [-log2/2, log2/2]).
  No `sorry`.
-/
import ArchS11_KI
import ArchS12_Index

open MeasureTheory Set
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace ArchS12

open ArchS5 ArchS8 ArchS11

/-! ## A2. From `L²([0, ℓ])` to function-level integrals. -/

section A2

variable {ℓ : ℝ} {F : ℝ → ℂ}

/-- `F` as an element of `L²([0, ℓ])`. -/
def toLpI (ℓ : ℝ) (hF : Continuous F) : Lp ℂ 2 (volI 0 ℓ) := (memLp_volI (a := ℓ) hF).toLp F

theorem toLpI_ae (hF : Continuous F) : (toLpI ℓ hF : ℝ → ℂ) =ᵐ[volI 0 ℓ] F := MemLp.coeFn_toLp _

theorem integral_volI_of_vanish {G : ℝ → ℂ} (hG : ∀ x, x ∉ Icc (0 : ℝ) ℓ → G x = 0) :
    ∫ x, G x ∂(volI 0 ℓ) = ∫ x, G x :=
  setIntegral_eq_integral_of_forall_compl_eq_zero hG

theorem inner_one_toLpI (hF : Continuous F) (hFs : ∀ x, x ∉ Icc (0 : ℝ) ℓ → F x = 0) :
    ⟪(polyLp ℓ [1] : Lp ℂ 2 (volI 0 ℓ)), toLpI ℓ hF⟫_ℂ = ∫ x, F x := by
  rw [inner_one_eq_integral, integral_congr_ae (toLpI_ae hF), integral_volI_of_vanish hFs]

theorem norm_sq_toLpI (hF : Continuous F) (hFs : ∀ x, x ∉ Icc (0 : ℝ) ℓ → F x = 0) :
    ((‖toLpI ℓ hF‖ ^ 2 : ℝ) : ℂ) = ∫ x, conj (F x) * F x := by
  rw [show ((‖toLpI ℓ hF‖ ^ 2 : ℝ) : ℂ) = ⟪toLpI ℓ hF, toLpI ℓ hF⟫_ℂ from by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast, MeasureTheory.L2.inner_def]
  have h1 : (fun x => ⟪(toLpI ℓ hF : ℝ → ℂ) x, (toLpI ℓ hF : ℝ → ℂ) x⟫_ℂ) =ᵐ[volI 0 ℓ]
      fun x => conj (F x) * F x := by
    filter_upwards [toLpI_ae hF] with x hx
    rw [hx, RCLike.inner_apply']
  rw [integral_congr_ae h1]
  exact integral_volI_of_vanish fun x hx => by rw [hFs x hx]; simp

theorem integrable_double {κ : ℝ × ℝ → ℂ} (hκ : Continuous κ) (hF : Continuous F)
    (hFs : ∀ x, x ∉ Icc (0 : ℝ) ℓ → F x = 0) :
    Integrable (fun p : ℝ × ℝ => conj (F p.1) * κ p * F p.2) (volume.prod volume) := by
  have hc : Continuous (fun p : ℝ × ℝ => conj (F p.1) * κ p * F p.2) := by fun_prop
  refine hc.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro ((isCompact_Icc (a := (0 : ℝ)) (b := ℓ)).prod
    (isCompact_Icc (a := (0 : ℝ)) (b := ℓ)))
    fun p hp => ?_
  rw [Set.mem_prod, not_and_or] at hp
  rcases hp with hp | hp
  · rw [hFs _ hp]; simp
  · rw [hFs _ hp]; simp

/-- **A2.**  The `L²([0, ℓ])` form of a continuous kernel is the whole-line double integral. -/
theorem re_inner_toLpI {κ : ℝ × ℝ → ℂ} (hκ : Continuous κ) (hF : Continuous F)
    (hFs : ∀ x, x ∉ Icc (0 : ℝ) ℓ → F x = 0) :
    RCLike.re ⟪intOp (kernelOfContinuous 0 ℓ κ hκ) (toLpI ℓ hF), toLpI ℓ hF⟫_ℂ
      = (∫ x, ∫ y, conj (F x) * κ (x, y) * F y).re := by
  rw [re_inner_intOp_swap, inner_intOp_eq_integral]
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := volI 0 ℓ) (ν := volI 0 ℓ)).ae_eq_comp
    (toLpI_ae hF)
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := volI 0 ℓ) (ν := volI 0 ℓ)).ae_eq_comp
    (toLpI_ae hF)
  have hL : (fun p : ℝ × ℝ => conj ((toLpI ℓ hF : ℝ → ℂ) p.1) *
      (kernelOfContinuous 0 ℓ κ hκ : ℝ × ℝ → ℂ) p * (toLpI ℓ hF : ℝ → ℂ) p.2)
      =ᵐ[(volI 0 ℓ).prod (volI 0 ℓ)] fun p => conj (F p.1) * κ p * F p.2 := by
    filter_upwards [h1, h2, kernelOfContinuous_ae_eq (a := 0) (b := ℓ) hκ] with p hp1 hp2 hp3
    simp only [Function.comp_apply] at hp1 hp2
    rw [hp1, hp2, hp3]
  rw [integral_congr_ae hL, volI_prod, setIntegral_eq_integral_of_forall_compl_eq_zero,
    Measure.volume_eq_prod,
    integral_prod _ (integrable_double hκ hF hFs)]
  · rfl
  intro p hp
  rw [Set.mem_prod, not_and_or] at hp
  rcases hp with hp | hp
  · rw [hFs _ hp]; simp
  · rw [hFs _ hp]; simp

end A2

/-! ## A1. Translation. -/

section A1

/-- Translation `x ↦ x - L` of a translation-invariant double integral. -/
theorem double_integral_translate (h : ℝ → ℂ) (k : ℝ → ℂ) (L : ℝ) :
    (∫ x, ∫ y, conj (h (x - L)) * k (y - x) * h (y - L))
      = ∫ x, ∫ y, conj (h x) * k (y - x) * h y := by
  have inner : ∀ x, (∫ y, conj (h (x - L)) * k (y - x) * h (y - L))
      = ∫ y, conj (h (x - L)) * k (y - (x - L)) * h y := by
    intro x
    have := integral_sub_right_eq_self (μ := volume)
      (fun y => conj (h (x - L)) * k (y - (x - L)) * h y) L
    rw [← this]
    congr 1; funext y; congr 3; ring
  simp_rw [inner]
  exact integral_sub_right_eq_self (μ := volume)
    (fun x => ∫ y, conj (h x) * k (y - x) * h y) L

theorem integral_translate (h : ℝ → ℂ) (L : ℝ) : (∫ x, h (x - L)) = ∫ x, h x :=
  integral_sub_right_eq_self (μ := volume) h L

theorem integral_conj_mul_translate (h : ℝ → ℂ) (L : ℝ) :
    (∫ x, conj (h (x - L)) * h (x - L)) = ∫ x, conj (h x) * h x :=
  integral_sub_right_eq_self (μ := volume) (fun x => conj (h x) * h x) L

end A1

/-! ## CC's kernel on `[-L, L]`. -/

section Chi

variable {D : ProlateDataNat}

/-- S11's clamped kernel as a function of `y - x`. -/
def chiT (D : ProlateDataNat) (v : ℝ) : ℂ :=
  ((D.Qeps (min |v| (Real.log 2)) / (2 * D.eps1 0) : ℝ) : ℂ)

theorem chiK_eq_chiT (p : ℝ × ℝ) : (chiK D p : ℂ) = chiT D (p.2 - p.1) := rfl

theorem vanish_of_tsupport {h : ℝ → ℂ} {a b : ℝ} (hs : tsupport h ⊆ Icc a b) :
    ∀ x, x ∉ Icc a b → h x = 0 :=
  fun _ hx => image_eq_zero_of_notMem_tsupport (fun h' => hx (hs h'))

/-- On the support, S8's `D.chi (y - x)` is S11's clamped kernel. -/
theorem double_chi_eq_chiT {h : ℝ → ℂ} {L : ℝ} (hs : tsupport h ⊆ Icc (-L) L)
    (hL : 2 * L ≤ Real.log 2) :
    (∫ x, ∫ y, conj (h x) * h y * (D.chi (y - x) : ℂ))
      = ∫ x, ∫ y, conj (h x) * chiT D (y - x) * h y := by
  have hv := vanish_of_tsupport hs
  congr 1; funext x; congr 1; funext y
  by_cases hx : x ∈ Icc (-L) L
  · by_cases hy : y ∈ Icc (-L) L
    · have hm : |y - x| ≤ Real.log 2 := by
        rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
      unfold chiT ProlateData.chi
      rw [min_eq_left hm]; ring
    · rw [hv y hy]; simp
  · rw [hv x hx]; simp

/-- The translated function `F = h(· - L)` vanishes off `[0, 2L]`. -/
theorem vanish_translate {h : ℝ → ℂ} {L ℓ : ℝ} (hs : tsupport h ⊆ Icc (-L) L) (hℓ : 2 * L ≤ ℓ) :
    ∀ x, x ∉ Icc (0 : ℝ) ℓ → h (x - L) = 0 := by
  intro x hx
  refine vanish_of_tsupport hs _ fun hm => hx ⟨by linarith [hm.1], by linarith [hm.2]⟩

/-- The CC form on `[-L, L]` as S11's `L²([0, ℓ])` form. -/
theorem re_double_chi_eq_inner {h : ℝ → ℂ} (hc : Continuous h) {L ℓ : ℝ}
    (hs : tsupport h ⊆ Icc (-L) L) (hℓ : 2 * L ≤ ℓ) (hℓ2 : ℓ ≤ Real.log 2)
    (hκ : Continuous (chiK (𝕜 := ℂ) D)) :
    (∫ x, ∫ y, conj (h x) * h y * (D.chi (y - x) : ℂ)).re
      = RCLike.re ⟪KI ℓ (chiK D) hκ (toLpI ℓ (hc.comp (continuous_sub_right L))),
          toLpI ℓ (hc.comp (continuous_sub_right L))⟫_ℂ := by
  rw [KI, re_inner_toLpI hκ _ (vanish_translate hs hℓ), double_chi_eq_chiT hs (hℓ.trans hℓ2)]
  simp only [chiK_eq_chiT]
  rw [double_integral_translate h (chiT D) L]

theorem norm_sq_translate {h : ℝ → ℂ} (hc : Continuous h) {L ℓ : ℝ}
    (hs : tsupport h ⊆ Icc (-L) L) (hℓ : 2 * L ≤ ℓ) :
    ‖toLpI ℓ (hc.comp (continuous_sub_right L))‖ ^ 2 = (∫ x, conj (h x) * h x).re := by
  have := norm_sq_toLpI (ℓ := ℓ) (hc.comp (continuous_sub_right L)) (vanish_translate hs hℓ)
  simp only [Function.comp_apply] at this
  rw [integral_conj_mul_translate] at this
  rw [← this, Complex.ofReal_re]

theorem inner_one_translate {h : ℝ → ℂ} (hc : Continuous h) {L ℓ : ℝ}
    (hs : tsupport h ⊆ Icc (-L) L) (hℓ : 2 * L ≤ ℓ) :
    ⟪(polyLp ℓ [1] : Lp ℂ 2 (volI 0 ℓ)), toLpI ℓ (hc.comp (continuous_sub_right L))⟫_ℂ
      = ∫ x, h x := by
  rw [inner_one_toLpI _ (vanish_translate hs hℓ)]
  exact integral_translate h L

/-- **A1 + A2 + S11 T1.**  For `tsupport h ⊆ [-1/4, 1/4]` (|I| = 1/2), CC's K_I form is at most
`0.95921 ‖h‖²`. -/
theorem form_chi_half (hB : ArchS10.CertBasis D) {h : ℝ → ℂ} (hc : Continuous h)
    (hs : tsupport h ⊆ Icc (-(1 / 4)) (1 / 4)) :
    (∫ x, ∫ y, conj (h x) * h y * (D.chi (y - x) : ℂ)).re
      ≤ 0.95921 * (∫ x, conj (h x) * h x).re := by
  have hl : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hκ := chiK_approx (𝕜 := ℂ) hB hl
  have hd : (0 : ℝ) ≤ ArchS10.Data.deltaChi := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h19, -⟩ := final_facts
    exact_mod_cast h19
  have h2 : 2 * (1 / 4 : ℝ) ≤ 1 / 2 := by norm_num
  rw [re_double_chi_eq_inner hc hs h2 hl hκ.cont, ← norm_sq_translate hc hs h2]
  exact KI_half_form hκ hd le_rfl _

/-- **A1 + A2 + S11 T2.**  For `tsupport h ⊆ [-log2/2, log2/2]` (|I| = log 2), CC's K_I form is at most
`0.9995 ‖h‖² + 0.058 |∫ h|² / log 2` (CC Lemma 6.9 form). -/
theorem form_chi_log2 (hB : ArchS10.CertBasis D) {h : ℝ → ℂ} (hc : Continuous h)
    (hs : tsupport h ⊆ Icc (-(Real.log 2 / 2)) (Real.log 2 / 2)) :
    (∫ x, ∫ y, conj (h x) * h y * (D.chi (y - x) : ℂ)).re
      ≤ 0.9995 * (∫ x, conj (h x) * h x).re + 0.058 * ‖∫ x, h x‖ ^ 2 / Real.log 2 := by
  have hκ := chiK_approx (𝕜 := ℂ) hB (le_refl (Real.log 2))
  have hd : (0 : ℝ) ≤ ArchS10.Data.deltaChi := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h19, -⟩ := final_facts
    exact_mod_cast h19
  have h2 : 2 * (Real.log 2 / 2) ≤ Real.log 2 := by linarith
  rw [re_double_chi_eq_inner hc hs h2 le_rfl hκ.cont, ← norm_sq_translate hc hs h2,
    ← inner_one_translate hc hs h2]
  exact KI_log2_form_gamma hκ hd le_rfl _

end Chi

end ArchS12
