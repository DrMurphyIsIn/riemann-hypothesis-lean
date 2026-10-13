import ArchS6_Real

/-!
# ArchS6_Bridge: S6's eigenbasis in S9's terms (continuous functions, `ip`, `T`)

Stage S9 (`ArchS9_Analysis`, branch `mm/arch-s9`) works with continuous real functions on `[0, 1]`:
`ip f g = ∫ x in 0..1, f x * g x` and `T f ω = ∫ x in 0..1, 2cos(2πxω) f x`.  Its completeness theorem
`prolate_spectrum_complete` needs "an orthonormal family of continuous eigenfunctions `(e_k, λ_k)` in
which `ψ_n` satisfies Parseval".  This file supplies that family, stated with Mathlib integrals only
(S9's definitions are reproduced verbatim as `ipS9` and `TS9`, so no cross-branch import is needed):

* `continuous_phiR`: `e_k := phiR bR k` is continuous on `ℝ` (from `ArchS6_Real`);
* `ip_phiR`: `ip e_j e_k = if j = k then 1 else 0`;
* `T_phiR`: `T e_k ω = λ_k e_k ω` for **every** `ω ∈ ℝ`, with `λ_k ≠ 0`, `|λ_k| < 1`;
* `parseval_ip`: for every continuous `ψ`, `HasSum (fun k ↦ ip ψ e_k ^ 2) (ip ψ ψ)`;
* `exists_S9_family`: all of the above, packaged as one existence statement.

conjecture1_proved = False.
-/

open MeasureTheory Set Filter
open scoped InnerProductSpace Real Interval

noncomputable section

namespace ArchS6

open ArchS5

set_option linter.unusedSectionVars false

/-- S9's inner product `ip f g = ∫₀¹ f g` (`ArchS9_Analysis.ip`, verbatim). -/
def ipS9 (f g : ℝ → ℝ) : ℝ := ∫ x in (0 : ℝ)..1, f x * g x

/-- S9's operator `T f ω = ∫₀¹ 2cos(2πxω) f x dx` (`ArchS9_Analysis.T`, verbatim). -/
def TS9 (f : ℝ → ℝ) (ω : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, 2 * Real.cos (2 * π * x * ω) * f x

theorem intervalIntegral_eq_Icc (F : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..1, F x = ∫ x in Icc (0 : ℝ) 1, F x := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]

/-- A continuous function as an element of real `L²([0, 1])`. -/
theorem memLp_continuous {ψ : ℝ → ℝ} (hψ : Continuous ψ) : MemLp ψ 2 (volI 0 1) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 1)
    hψ.continuousOn
  refine MemLp.of_bound hψ.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with x hx
  exact hC x hx

/-- `ψ` as an element of `L²([0,1]; ℝ)`. -/
def toL2 {ψ : ℝ → ℝ} (hψ : Continuous ψ) : L2IR 0 1 := (memLp_continuous hψ).toLp ψ

theorem coeFn_toL2 {ψ : ℝ → ℝ} (hψ : Continuous ψ) : (toL2 hψ : ℝ → ℝ) =ᵐ[volI 0 1] ψ :=
  MemLp.coeFn_toLp _

/-- `⟪f, g⟫_{L²} = ∫_{[0,1]} f g` for real `L²([0, 1])`. -/
theorem inner_L2IR (f g : L2IR 0 1) : ⟪f, g⟫_ℝ = ∫ x in Icc (0 : ℝ) 1, f x * g x := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp [mul_comm]

/-- `⟪e, toL2 ψ⟫ = ip e ψ` when `e` is a.e. a continuous `φ`. -/
theorem inner_eq_ipS9 {f : L2IR 0 1} {φ : ℝ → ℝ} (hf : (f : ℝ → ℝ) =ᵐ[volI 0 1] φ)
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) : ⟪f, toL2 hψ⟫_ℝ = ipS9 φ ψ := by
  rw [inner_L2IR, ipS9, intervalIntegral_eq_Icc]
  refine integral_congr_ae ?_
  filter_upwards [hf, coeFn_toL2 hψ] with x e1 e2
  rw [e1, e2]

variable {ι : Type*} (bR : EigenBasis CopR ι)

/-- Orthonormality in S9's `ip`. -/
theorem ip_phiR [DecidableEq ι] (j k : ι) :
    ipS9 (phiR bR j) (phiR bR k) = if j = k then 1 else 0 := by
  have h := orthonormal_iff_ite.1 bR.orthonormal j k
  rw [inner_L2IR] at h
  rw [ipS9, intervalIntegral_eq_Icc, ← h]
  refine integral_congr_ae ?_
  filter_upwards [ae_eq_phiR bR j, ae_eq_phiR bR k] with x e1 e2
  rw [e1, e2]

theorem ne_zero_μ (k : ι) : bR.μ k ≠ 0 := prolateBasisOf_lam_ne_zero (complexify bR) k

theorem abs_μ_lt_one (k : ι) : |bR.μ k| < 1 := (realProlateBasis bR).abs_lam_lt_one k

/-- The eigen-relation for the continuous representative, at **every** `ω`. -/
theorem T_phiR (k : ι) (ω : ℝ) : TS9 (phiR bR k) ω = bR.μ k * phiR bR k ω := by
  have hT : TS9 (phiR bR k) ω = cosTransR (bR.e k) ω := by
    rw [TS9, intervalIntegral_eq_Icc, cosTransR]
    refine integral_congr_ae ?_
    filter_upwards [ae_eq_phiR bR k] with x hx
    rw [hx, cosKR]; congr 3; ring
  rw [hT, phiR, ← mul_assoc, mul_inv_cancel₀ (ne_zero_μ bR k), one_mul]

/-- **Parseval in S9's form**: for every continuous `ψ`, `Σ_k ip ψ e_k ² = ip ψ ψ`. -/
theorem parseval_ip {ψ : ℝ → ℝ} (hψ : Continuous ψ) :
    HasSum (fun k ↦ ipS9 ψ (phiR bR k) ^ 2) (ipS9 ψ ψ) := by
  have h := bR.hasSum_inner_mul_inner (toL2 hψ) (toL2 hψ)
  have e1 : ∀ k, ⟪toL2 hψ, bR.e k⟫_ℝ * ⟪bR.e k, toL2 hψ⟫_ℝ = ipS9 ψ (phiR bR k) ^ 2 := by
    intro k
    rw [real_inner_comm (bR.e k), inner_eq_ipS9 (ae_eq_phiR bR k) hψ, sq]
    unfold ipS9; congr 1 <;> (congr 1; funext x; ring)
  have e2 : ⟪toL2 hψ, toL2 hψ⟫_ℝ = ipS9 ψ ψ := inner_eq_ipS9 (coeFn_toL2 hψ) hψ
  simp only [e1, e2] at h
  exact h

open Classical in
/-- **The family S9's `prolate_spectrum_complete` needs.**  There is an orthonormal (in `ip`) family
of continuous functions `e_k` with `T e_k = λ_k e_k` everywhere, `0 < |λ_k| < 1`, satisfying Parseval
for every continuous `ψ`. -/
theorem exists_S9_family :
    ∃ (ι : Type) (e : ι → ℝ → ℝ) (lam : ι → ℝ),
      (∀ k, Continuous (e k)) ∧
      (∀ j k, ipS9 (e j) (e k) = if j = k then 1 else 0) ∧
      (∀ k ω, TS9 (e k) ω = lam k * e k ω) ∧
      (∀ k, lam k ≠ 0 ∧ |lam k| < 1) ∧
      (∀ ψ : ℝ → ℝ, Continuous ψ → HasSum (fun k ↦ ipS9 ψ (e k) ^ 2) (ipS9 ψ ψ)) := by
  obtain ⟨ι, bR, -⟩ := exists_eigenBasis_CopR
  exact ⟨ι, phiR bR, bR.μ, continuous_phiR bR, ip_phiR bR, T_phiR bR,
    fun k ↦ ⟨ne_zero_μ bR k, abs_μ_lt_one bR k⟩, fun ψ hψ ↦ parseval_ip bR hψ⟩

end ArchS6
