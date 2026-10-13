import ArchS6_Real

/-!
# ArchS6_Functions: `ξ_n`, `η_n`, `ψ_n`, `ζ_n` as explicit functions

For the prolate basis `prolateBasisOf b` (and its real version), with `φ_n = λ_n⁻¹ C e_n` the analytic
continuation (`phi`, even and continuous on `ℝ`), and `c₂ = 1/√2`:

* `coeFn_ξ`: `ξ_n = c₂ · 1_{[-1,1]} · φ_n`  a.e. on `ℝ`;
* `coeFn_η`: `η_n = F ξ_n = c₂ λ_n φ_n`  a.e. on `ℝ`;
* `coeFn_ψ`: `ψ_n = P η_n = c₂ λ_n · 1_{ℝ∖[-1,1]} · φ_n`;
* `coeFn_ζ`: `ζ_n = c₂ (λ_n/√(1-λ_n²)) · 1_{ℝ∖[-1,1]} · φ_n`.

In CC's normalisation (multiply by `√2`, see `ArchS6_Even`): `ξ_n = 1_{[-1,1]} ξ_n^an` and
`ζ_n = (λ_n/√(1-λ_n²)) 1_{|x|>1} ξ_n^an`, which is the form S8's `cc84_term` assumes.

conjecture1_proved = False.
-/

open MeasureTheory Set Filter FourierTransform Complex
open scoped InnerProductSpace Real

noncomputable section

namespace ArchS6

open ArchS5

set_option linter.unusedSectionVars false

variable {ι : Type*} (b : EigenBasis Cop ι)

theorem phi_neg (i : ι) (w : ℝ) : phi b i (-w) = phi b i w := by
  rw [phi, phi, cosTrans_neg]

/-- `ξ_n = c₂ · 1_{[-1,1]} · φ_n`. -/
theorem coeFn_ξ (i : ι) :
    (((prolateBasisOf b).ξ i : L2R) : ℝ → ℂ) =ᵐ[volume]
      fun w ↦ c2 * (Icc (-1 : ℝ) 1).indicator (phi b i) w := by
  rw [prolateBasisOf_ξ]
  filter_upwards [coeFn_J_of (b.e i) (ae_eq_phi b i), ae_ne_zero_real] with w e1 hw
  rw [e1]
  congr 1
  rcases lt_or_gt_of_ne hw with hneg | hpos
  · have h1 : w ∉ Icc (0 : ℝ) 1 := fun h' ↦ by linarith [h'.1]
    rw [indicator_of_notMem h1, zero_add]
    by_cases h2 : -w ∈ Icc (0 : ℝ) 1
    · have hw1 : w ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [h2.2], by linarith⟩
      rw [indicator_of_mem h2, indicator_of_mem hw1, phi_neg]
    · rw [indicator_of_notMem h2, indicator_of_notMem]
      intro h'; exact h2 ⟨by linarith, by linarith [h'.1]⟩
  · have h2 : -w ∉ Icc (0 : ℝ) 1 := fun h' ↦ by linarith [h'.1]
    rw [indicator_of_notMem h2, add_zero]
    by_cases h1 : w ∈ Icc (0 : ℝ) 1
    · rw [indicator_of_mem h1, indicator_of_mem (show w ∈ Icc (-1 : ℝ) 1 from ⟨by linarith, h1.2⟩)]
    · rw [indicator_of_notMem h1, indicator_of_notMem]
      intro h'; exact h1 ⟨by linarith, h'.2⟩

/-- `η_n = F ξ_n = c₂ λ_n φ_n`. -/
theorem coeFn_η (i : ι) :
    (((prolateBasisOf b).η i : L2R) : ℝ → ℂ) =ᵐ[volume] fun w ↦ c2 * (b.μ i : ℂ) * phi b i w :=
  fourier_ξ_ae b i

theorem coe_ψ (i : ι) :
    ((prolateBasisOf b).ψ i : L2R) =
      ((prolateBasisOf b).η i : L2R) - P1 ((prolateBasisOf b).η i : L2R) := rfl

/-- `ψ_n = c₂ λ_n · 1_{ℝ∖[-1,1]} · φ_n`. -/
theorem coeFn_ψ (i : ι) :
    (((prolateBasisOf b).ψ i : L2R) : ℝ → ℂ) =ᵐ[volume]
      fun w ↦ (Icc (-1 : ℝ) 1)ᶜ.indicator (fun w ↦ c2 * (b.μ i : ℂ) * phi b i w) w := by
  rw [coe_ψ]
  filter_upwards [Lp.coeFn_sub ((prolateBasisOf b).η i : L2R) (P1 ((prolateBasisOf b).η i : L2R)),
    coeFn_P1 ((prolateBasisOf b).η i : L2R), coeFn_η b i] with w e1 e2 e3
  rw [e1, Pi.sub_apply, e2, e3]
  by_cases hm : w ∈ Icc (-1 : ℝ) 1
  · rw [indicator_of_mem hm, e3, sub_self,
      indicator_of_notMem (show w ∉ (Icc (-1 : ℝ) 1)ᶜ from fun h ↦ h hm)]
  · rw [indicator_of_notMem hm, sub_zero, indicator_of_mem (show w ∈ (Icc (-1 : ℝ) 1)ᶜ from hm)]

/-- `ζ_n = c₂ (λ_n/√(1-λ_n²)) · 1_{ℝ∖[-1,1]} · φ_n` (CC: `ζ_n = λ/√(1-λ²) ξ_n^an` on `|x| > 1`). -/
theorem coeFn_ζ (i : ι) :
    (((prolateBasisOf b).ζ i : L2R) : ℝ → ℂ) =ᵐ[volume]
      fun w ↦ (Icc (-1 : ℝ) 1)ᶜ.indicator
        (fun w ↦ c2 * ((b.μ i / (prolateBasisOf b).s i : ℝ) : ℂ) * phi b i w) w := by
  have hs : ((prolateBasisOf b).ζ i : L2R) =
      (((prolateBasisOf b).s i)⁻¹ : ℂ) • ((prolateBasisOf b).ψ i : L2R) := rfl
  rw [hs]
  filter_upwards [Lp.coeFn_smul ((((prolateBasisOf b).s i)⁻¹ : ℂ)) ((prolateBasisOf b).ψ i : L2R),
    coeFn_ψ b i] with w e1 e2
  rw [e1, Pi.smul_apply, e2, smul_eq_mul]
  by_cases hm : w ∈ (Icc (-1 : ℝ) 1)ᶜ
  · rw [indicator_of_mem hm, indicator_of_mem hm]; push_cast; ring
  · rw [indicator_of_notMem hm, indicator_of_notMem hm, mul_zero]

/-! ### Real version -/

theorem phiR_neg (bR : EigenBasis CopR ι) (i : ι) (w : ℝ) : phiR bR i (-w) = phiR bR i w := by
  have := phi_neg (complexify bR) i w
  rw [phi_complexify, phi_complexify] at this
  exact_mod_cast this

/-- `ξ_n = c₂ · 1_{[-1,1]} · φ_n` with `φ_n` real. -/
theorem coeFn_ξ_real (bR : EigenBasis CopR ι) (i : ι) :
    (((realProlateBasis bR).ξ i : L2R) : ℝ → ℂ) =ᵐ[volume]
      fun w ↦ c2 * (((Icc (-1 : ℝ) 1).indicator (phiR bR i) w : ℝ) : ℂ) := by
  filter_upwards [coeFn_ξ (complexify bR) i] with w hw
  rw [realProlateBasis, hw]
  congr 1
  by_cases hm : w ∈ Icc (-1 : ℝ) 1
  · rw [indicator_of_mem hm, indicator_of_mem hm, phi_complexify]
  · rw [indicator_of_notMem hm, indicator_of_notMem hm, Complex.ofReal_zero]

/-- `ζ_n = c₂ (λ_n/√(1-λ_n²)) · 1_{ℝ∖[-1,1]} · φ_n` with `φ_n` real. -/
theorem coeFn_ζ_real (bR : EigenBasis CopR ι) (i : ι) :
    (((realProlateBasis bR).ζ i : L2R) : ℝ → ℂ) =ᵐ[volume]
      fun w ↦ c2 * (((Icc (-1 : ℝ) 1)ᶜ.indicator
        (fun w ↦ bR.μ i / (realProlateBasis bR).s i * phiR bR i w) w : ℝ) : ℂ) := by
  filter_upwards [coeFn_ζ (complexify bR) i] with w hw
  rw [realProlateBasis, hw]
  by_cases hm : w ∈ (Icc (-1 : ℝ) 1)ᶜ
  · rw [indicator_of_mem hm, indicator_of_mem hm, phi_complexify, complexify_μ]
    push_cast; ring
  · rw [indicator_of_notMem hm, indicator_of_notMem hm, Complex.ofReal_zero, mul_zero]

/-! ### Smoothness of `φ_n` (S8's `phi_contDiff`) -/

theorem cosTrans_eq_fourier (h : L2I 0 1) :
    cosTrans h = fun w ↦ 𝓕 (Eplus h : ℝ → ℂ) w + 𝓕 (Eplus h : ℝ → ℂ) (-w) := by
  funext w
  rw [fourier_extendIcc_eq, fourier_extendIcc_eq,
    ← integral_add (integrable_fourierK_mul 0 1 w h) (integrable_fourierK_mul 0 1 (-w) h)]
  unfold cosTrans
  congr 1; funext v
  rw [← add_mul, fourierK_add_neg]

/-- All moments of `E₊ h` are finite (compact support). -/
theorem integrable_moment_Eplus (h : L2I 0 1) (n : ℕ) :
    Integrable (fun v : ℝ ↦ ‖v‖ ^ n * ‖(Eplus h : ℝ → ℂ) v‖) := by
  refine (integrable_extendIcc 0 1 h).norm.mono' ?_ ?_
  · exact (continuous_norm.pow n).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable _).norm
  · filter_upwards [coeFn_extendIcc 0 1 h] with v hv
    rw [norm_mul, norm_norm, norm_pow, norm_norm, hv]
    by_cases hm : v ∈ Icc (0 : ℝ) 1
    · rw [indicator_of_mem hm]
      have h1 : ‖v‖ ^ n ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg hm.1]; exact pow_le_one₀ hm.1 hm.2
      calc ‖v‖ ^ n * ‖(h : ℝ → ℂ) v‖ ≤ 1 * ‖(h : ℝ → ℂ) v‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = _ := one_mul _
    · rw [indicator_of_notMem hm, norm_zero, mul_zero]

/-- `C h` (as a function on `ℝ`) is `C^∞`. -/
theorem contDiff_cosTrans (h : L2I 0 1) (N : ℕ∞) : ContDiff ℝ N (cosTrans h) := by
  have hG : ContDiff ℝ N (𝓕 (Eplus h : ℝ → ℂ)) :=
    Real.contDiff_fourier fun n _ ↦ integrable_moment_Eplus h n
  rw [cosTrans_eq_fourier]
  exact hG.add (hG.comp contDiff_neg)

theorem contDiff_phi (i : ι) (N : ℕ∞) : ContDiff ℝ N (phi b i) :=
  contDiff_const.mul (contDiff_cosTrans _ N)

/-- **`φ_n` is `C^∞` on `ℝ`** (S8's `ProlateData.phi_contDiff`, for every `n`). -/
theorem contDiff_phiR (bR : EigenBasis CopR ι) (i : ι) (N : ℕ∞) : ContDiff ℝ N (phiR bR i) := by
  have h := Complex.reCLM.contDiff.comp (contDiff_phi (complexify bR) i N)
  have : phiR bR i = Complex.reCLM ∘ phi (complexify bR) i := by
    funext w; simp [phi_complexify]
  rw [this]; exact h

end ArchS6
