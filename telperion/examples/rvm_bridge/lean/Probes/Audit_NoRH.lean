/- Audit probe: term_re_nonneg WITHOUT the RH hypothesis. Every example is EXPECTED TO FAIL. -/
import E6Bridge5
open Zeta23 Complex MeasureTheory WeilExplicit
open scoped ComplexConjugate

/- 1. The author's proof text with hRH deleted (the rewrite step has nothing to feed it). -/
example {g : ℝ → ℂ} (hg : IsWeilTest g) (ρ : ℂ) :
    0 ≤ ((WeilExplicit.zeroMult ρ : ℂ) * weilKernel (autocorr g) ρ).re := by
  by_cases hz : IsNontrivialZero ρ
  · have hk : weilKernel (autocorr g) ρ = weilKernel (autocorr g) (1 / 2 + (ρ.im : ℂ) * I) := by
      rw [← RvMBridge5.eq_half_add_im_of_rh _ hz]
    rw [hk, RvMBridge5.weilKernel_autocorr_line hg]
    positivity
  · rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial hz]
    simp

/- 2. Automation on the hypothesis-free summand sentence. -/
example {g : ℝ → ℂ} (hg : IsWeilTest g) (ρ : ℂ) :
    0 ≤ ((WeilExplicit.zeroMult ρ : ℂ) * weilKernel (autocorr g) ρ).re := by
  positivity

example {g : ℝ → ℂ} (hg : IsWeilTest g) (ρ : ℂ) :
    0 ≤ ((WeilExplicit.zeroMult ρ : ℂ) * weilKernel (autocorr g) ρ).re := by
  simp [WeilExplicit.zeroMult, weilKernel, autocorr]

example {g : ℝ → ℂ} (hg : IsWeilTest g) (ρ : ℂ) :
    0 ≤ ((WeilExplicit.zeroMult ρ : ℂ) * weilKernel (autocorr g) ρ).re := by
  aesop

/- 3. What IS true off the line without RH: the summand is h(z) conj(h(conj z)) for z = gammaOf ρ,
   which is a square modulus only when conj z = z, i.e. ρ on the line. (Expected to SUCCEED.) -/
example {g : ℝ → ℂ} (hg : IsWeilTest g) (ρ : ℂ) :
    weilKernel (autocorr g) ρ = paperFT g (gammaOf ρ) * conj (paperFT g (conj (gammaOf ρ))) := by
  rw [RvMBridge4.weilKernel_eq_paperFT_gammaOf, RvMBridge5.autocorr_eq_weilTest,
    Zeta23.EF.paperFT_weilTest hg.1.continuous hg.1.continuous hg.2 hg.2]

/- 4. The on-line lemma really needs the on-line hypothesis: weilKernel_autocorr_line at an
   off-line point is not a square modulus of anything by rewriting (expected to FAIL). -/
example {g : ℝ → ℂ} (hg : IsWeilTest g) (σ r : ℝ) :
    weilKernel (autocorr g) ((σ : ℂ) + (r : ℂ) * I) = ((‖paperFT g r‖ : ℂ)) ^ 2 := by
  rw [RvMBridge4.weilKernel_eq_paperFT_gammaOf, RvMBridge5.autocorr_eq_weilTest,
    Zeta23.EF.paperFT_weilTest hg.1.continuous hg.1.continuous hg.2 hg.2]
  simp [gammaOf]
