/- Audit probes for E6Bridge10. -/
import E6Bridge10
open Zeta23 Complex MeasureTheory Filter Topology RvMBridge6 RvMBridge8 RvMBridge10 WeilExplicit
open scoped ComplexConjugate

/- 1. Non-vacuity: an off-line nontrivial zero refutes GaussianPositivity (expected SUCCESS). -/
theorem audit_offline_refutes (ρ₀ : ℂ) (h₀ : IsNontrivialZero ρ₀) (hre : ρ₀.re ≠ 1 / 2) :
    ¬ GaussianPositivity := by
  intro hGP
  obtain ⟨c, lam, hlam, hneg⟩ := RvMBridge7.gaussian_dominance ρ₀ h₀ hre
  linarith [hGP c lam hlam]
#print axioms audit_offline_refutes

/- 2. Honest values on the NON-compactly-supported limit test f = autocorr (gaussPhi c lam):
   the autocorr integrand, the kernel integrand, the archimedean integrand are integrable and the
   prime-side family is summable (expected SUCCESS, from the same majorants). -/
theorem audit_norm_autocorr_gaussPhi_le {c lam : ℝ} (hlam : 0 < lam) (u : ℝ) :
    ‖autocorr (gaussPhi c lam) u‖ ≤ autocorrMaj lam u := by
  unfold autocorr
  rw [← integral_vMaj hlam u]
  refine norm_integral_le_of_norm_le (integrable_vMaj hlam u)
    (Filter.Eventually.of_forall fun v => ?_)
  rw [norm_mul, Complex.norm_conj]
  exact norm_phi_mul_phi_le c lam u v

theorem audit_integrable_autocorr_integrand {c lam : ℝ} (hlam : 0 < lam) (u : ℝ) :
    Integrable (fun v : ℝ => gaussPhi c lam v * conj (gaussPhi c lam (v - u))) := by
  refine (integrable_vMaj hlam u).mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
  · exact ((continuous_gaussPhi c lam).mul (Complex.continuous_conj.comp
      ((continuous_gaussPhi c lam).comp (continuous_id.sub continuous_const)))).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_conj]; exact norm_phi_mul_phi_le c lam u v

theorem audit_aesm_autocorr_gaussPhi {c lam : ℝ} (hlam : 0 < lam) :
    AEStronglyMeasurable (autocorr (gaussPhi c lam)) volume :=
  aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (continuous_autocorr_gaussTests c lam n).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun u => autocorr_gaussTests_tendsto hlam u)

theorem audit_integrable_kernel_integrand {c lam : ℝ} (hlam : 0 < lam) {s : ℂ}
    (hs : |s.re - 1 / 2| ≤ 1 / 2) :
    Integrable (fun u : ℝ => autocorr (gaussPhi c lam) u * Complex.exp ((s - 1 / 2) * (u : ℂ))) := by
  refine (integrable_kernelMaj hlam).mono' ?_ (Filter.Eventually.of_forall fun u => ?_)
  · exact ((audit_aesm_autocorr_gaussPhi hlam).mul (by fun_prop : Continuous fun u : ℝ => Complex.exp ((s - 1 / 2) * (u : ℂ))).aestronglyMeasurable)
  · rw [norm_mul, Complex.norm_exp]
    have hre : ((s - 1 / 2) * (u : ℂ)).re = (s.re - 1 / 2) * u := by
      simp [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [hre]
    unfold kernelMaj
    have hexp : (s.re - 1 / 2) * u ≤ 1 / 2 * |u| := by
      calc (s.re - 1 / 2) * u ≤ |(s.re - 1 / 2) * u| := le_abs_self _
        _ = |s.re - 1 / 2| * |u| := abs_mul _ _
        _ ≤ 1 / 2 * |u| := mul_le_mul_of_nonneg_right hs (abs_nonneg u)
    exact mul_le_mul (audit_norm_autocorr_gaussPhi_le hlam u) (Real.exp_le_exp.mpr hexp)
      (Real.exp_pos _).le (autocorrMaj_nonneg lam u)

theorem audit_summable_primeSide_gaussPhi {c lam : ℝ} (hlam : 0 < lam) :
    Summable (fun k : ℕ => ((ArithmeticFunction.vonMangoldt k / Real.sqrt k : ℝ) : ℂ)
      * (autocorr (gaussPhi c lam) (Real.log k) + autocorr (gaussPhi c lam) (-Real.log k))) := by
  refine Summable.of_norm_bounded (summable_primeBound hlam) fun k => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))]
  unfold primeBound
  gcongr
  calc _ ≤ ‖autocorr (gaussPhi c lam) (Real.log k)‖ + ‖autocorr (gaussPhi c lam) (-Real.log k)‖ :=
        norm_add_le _ _
    _ ≤ autocorrMaj lam (Real.log k) + autocorrMaj lam (-Real.log k) :=
        add_le_add (audit_norm_autocorr_gaussPhi_le hlam _) (audit_norm_autocorr_gaussPhi_le hlam _)
    _ = 2 * autocorrMaj lam (Real.log k) := by rw [autocorrMaj_neg]; ring

/- The archimedean integrand of the limit test is integrable: it is the DCT limit of the
   truncations' integrands under the n-uniform majorant archBound (expected SUCCESS). -/
theorem audit_integrable_archIntegrand_gaussPhi {c lam : ℝ} (hlam : 0 < lam) :
    Integrable (archIntegrand (autocorr (gaussPhi c lam))) := by
  obtain ⟨C, hC0, hC⟩ := exists_paperFT_autocorr_gaussTests_bound c lam hlam
  have hlim : ∀ r : ℝ, Tendsto (fun n => archIntegrand (autocorr (gaussTests c lam n)) r) atTop
      (𝓝 (archIntegrand (autocorr (gaussPhi c lam)) r)) := fun r => by
    unfold archIntegrand
    refine (weilKernel_gaussTests_tendsto hlam (s := 1 / 2 + (r : ℂ) * I) ?_).mul_const _
    simp [Complex.add_re, Complex.mul_re]
  refine (integrable_archBound hC0).mono' ?_ (Filter.Eventually.of_forall fun r => ?_)
  · exact aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (RvMBridge4.integrable_archIntegrand
        (RvMBridge5.isWeilTest_autocorr (isWeilTest_gaussTests c lam n))).aestronglyMeasurable)
      (Filter.Eventually.of_forall hlim)
  · exact le_of_tendsto ((continuous_norm.tendsto _).comp (hlim r))
      (Filter.Eventually.of_forall fun n => norm_archIntegrand_le hC n r)

#print axioms audit_norm_autocorr_gaussPhi_le
#print axioms audit_integrable_autocorr_integrand
#print axioms audit_summable_primeSide_gaussPhi
#print axioms audit_integrable_archIntegrand_gaussPhi
#print axioms audit_integrable_kernel_integrand
#print axioms audit_aesm_autocorr_gaussPhi

/- 3. Automation cannot close the prime-side inequality (expected FAIL). -/
example (c lam : ℝ) (hlam : 0 < lam) :
    (primeSide (autocorr (gaussPhi c lam))).re ≤ (archSide (autocorr (gaussPhi c lam))).re := by
  simp [primeSide, archSide]

example (c lam : ℝ) (hlam : 0 < lam) :
    (primeSide (autocorr (gaussPhi c lam))).re ≤ (archSide (autocorr (gaussPhi c lam))).re := by
  rw [← sub_nonneg, ← Complex.sub_re, ← zeroSide_gaussTest_eq c lam hlam]
  positivity

/- 4. The inequality is not a triviality of its shape: neither "prime ≤ 0" nor "0 ≤ arch" nor the
   doubled-Λ variant follows from the same rewrite (expected FAIL each). -/
example (c lam : ℝ) (hlam : 0 < lam) (hGP : GaussianPositivity) :
    (primeSide (autocorr (gaussPhi c lam))).re ≤ 0 := by
  have := hGP c lam hlam
  rw [zeroSide_gaussTest_eq c lam hlam, Complex.sub_re] at this
  linarith

example (c lam : ℝ) (hlam : 0 < lam) (hGP : GaussianPositivity) :
    2 * (primeSide (autocorr (gaussPhi c lam))).re ≤ (archSide (autocorr (gaussPhi c lam))).re := by
  have := hGP c lam hlam
  rw [zeroSide_gaussTest_eq c lam hlam, Complex.sub_re] at this
  linarith

/- 5. Forward and converse consume exactly the named inputs (expected SUCCESS). -/
example : RiemannHypothesis ↔ GaussianPositivity :=
  ⟨rh_implies_gaussian_positivity, gaussian_positivity_implies_rh⟩
