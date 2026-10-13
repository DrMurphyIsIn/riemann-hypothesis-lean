import ArchS6_Bounds
import ArchS6_Enum
import ArchS5_HS
import ArchS8_ProlateData

/-!
# ArchS6_ProlateData: S6's prolate basis as an instance of S8's `ProlateData`

`prolateData bR σ` for a real eigenbasis `bR` of `C_ℝ` (S9's operator `2cos(2πxω)` on `[0,1]`) and an
enumeration `σ : ℕ ≃ ι` (`exists_equiv_nat`):

* `lam n = μ_{σ n}` (CC's signed `λ(n)`), `lam² < 1` (`abs_μ_lt_one`);
* `phi n = phiR bR (σ n)` = CC's `ξ_n^an` in CC's normalisation (16) (`∫₀¹ phi² = 1`; equals the unit
  eigenfunction `e_n` on `[0,1]`, `ae_eq_phiR`), `C^∞` (`contDiff_phiR`);
* `T = log 3`, so `[e^{-T}, e^T] = [1/3, 3]`;
* `M n = N n = Q_{σ n}` from `ArchS6_Bounds` (pointwise Bessel + Sobolev, no prolate ODE);
* `summable_wMN` from `Σ μ² S < ∞` and `μ_n → 0` (S5's `tsum_real_eigenvalue_sq_le`).

`exists_prolateData` packages the existence, with `D.lam = μ ∘ σ` and `D.phi = phiR ∘ σ`, which are
exactly the hypotheses `hDlam`, `hDphi` of S7's `thm47_concrete`.

conjecture1_proved = False.
-/

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

namespace ArchS6

open ArchS5

set_option linter.unusedSectionVars false

variable {ι : Type*} (bR : EigenBasis CopR ι)

theorem exp_neg_log_three : Real.exp (-Real.log 3) = 1 / 3 := by
  rw [Real.exp_neg, Real.exp_log (by norm_num), one_div]

theorem exp_log_three : Real.exp (Real.log 3) = 3 := Real.exp_log (by norm_num)

/-- The eigenvalues are square-summable (Hilbert–Schmidt, S5). -/
theorem summable_mu_sq : Summable fun i ↦ bR.μ i ^ 2 :=
  (tsum_real_eigenvalue_sq_le (kernelOfContinuous 0 1 cosKR continuous_cosKR) bR.orthonormal
    (lam := bR.μ) fun i ↦ bR.eigen i).1

theorem mu_sq_lt_one (i : ι) : bR.μ i ^ 2 < 1 := by
  have := abs_μ_lt_one bR i
  nlinarith [abs_nonneg (bR.μ i), sq_abs (bR.μ i)]

theorem summable_wMN_aux (σ : ℕ ≃ ι) :
    Summable fun n ↦ bR.μ (σ n) ^ 2 / (1 - bR.μ (σ n) ^ 2) * (Qb bR (σ n) * Qb bR (σ n)) := by
  have hS := ((summable_mu_sq_mul_S bR).comp_injective σ.injective).mul_left (2 * cW)
  have hl := ((summable_mu_sq bR).comp_injective σ.injective).tendsto_atTop_zero
  have hev : ∀ᶠ n in atTop, bR.μ (σ n) ^ 2 < 1 / 2 :=
    hl.eventually (gt_mem_nhds (by norm_num))
  refine Summable.of_norm_bounded_eventually_nat hS ?_
  filter_upwards [hev] with n hn
  simp only [Function.comp_apply, Qb_sq]
  have hS0 := Sint_nonneg bR (σ n)
  have hc := cW_pos
  have h1 : 0 < 1 - bR.μ (σ n) ^ 2 := by linarith
  have hfrac : bR.μ (σ n) ^ 2 / (1 - bR.μ (σ n) ^ 2) ≤ 2 * bR.μ (σ n) ^ 2 := by
    rw [div_le_iff₀ h1]; nlinarith [sq_nonneg (bR.μ (σ n))]
  have hnn : 0 ≤ bR.μ (σ n) ^ 2 / (1 - bR.μ (σ n) ^ 2) * (cW * Sint bR (σ n)) :=
    mul_nonneg (div_nonneg (sq_nonneg _) h1.le) (mul_nonneg hc.le hS0)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  calc bR.μ (σ n) ^ 2 / (1 - bR.μ (σ n) ^ 2) * (cW * Sint bR (σ n))
      ≤ 2 * bR.μ (σ n) ^ 2 * (cW * Sint bR (σ n)) :=
        mul_le_mul_of_nonneg_right hfrac (mul_nonneg hc.le hS0)
    _ = 2 * cW * (bR.μ (σ n) ^ 2 * Sint bR (σ n)) := by ring

/-- **S6's prolates as S8's `ProlateData`.** -/
def prolateData (σ : ℕ ≃ ι) : ArchS8.ProlateDataNat where
  lam n := bR.μ (σ n)
  lam_sq_lt_one n := mu_sq_lt_one bR (σ n)
  phi n := phiR bR (σ n)
  phi_contDiff n := contDiff_phiR bR (σ n) 1
  T := Real.log 3
  T_pos := Real.log_pos (by norm_num)
  M n := Qb bR (σ n)
  N n := Qb bR (σ n)
  bound_inner n x hx := by
    rw [exp_neg_log_three] at hx
    have hx' : x ∈ Icc aW bW := ⟨hx.1, by linarith [hx.2]⟩
    exact ⟨abs_phiR_le_Q bR (σ n) hx', abs_deriv_phiR_le_Q bR (σ n) hx'⟩
  bound_outer n x hx := by
    rw [exp_log_three] at hx
    have hx' : x ∈ Icc aW bW := ⟨by simp only [aW]; linarith [hx.1], hx.2⟩
    exact ⟨abs_phiR_le_Q bR (σ n) hx', abs_deriv_phiR_le_Q bR (σ n) hx'⟩
  summable_wMN := summable_wMN_aux bR σ

theorem prolateData_lam (σ : ℕ ≃ ι) (n : ℕ) : (prolateData bR σ).lam n = bR.μ (σ n) := rfl
theorem prolateData_phi (σ : ℕ ≃ ι) (n : ℕ) : (prolateData bR σ).phi n = phiR bR (σ n) := rfl
theorem prolateData_T (σ : ℕ ≃ ι) : (prolateData bR σ).T = Real.log 3 := rfl

/-- **Existence**: a real eigenbasis of `C_ℝ`, an enumeration `σ : ℕ ≃ ι`, and S8's `ProlateData`
with `D.lam = μ ∘ σ` and `D.phi = phiR ∘ σ` (the hypotheses `hDlam`, `hDphi` of S7's
`thm47_concrete`). -/
theorem exists_prolateData :
    ∃ (ι : Type) (bR : EigenBasis CopR ι) (σ : ℕ ≃ ι) (D : ArchS8.ProlateDataNat),
      (∀ n, D.lam n = bR.μ (σ n)) ∧ (∀ n, D.phi n = phiR bR (σ n)) := by
  obtain ⟨ι, bR, -⟩ := exists_eigenBasis_CopR
  obtain ⟨σ⟩ := exists_equiv_nat bR
  exact ⟨ι, bR, σ, prolateData bR σ, fun _ ↦ rfl, fun _ ↦ rfl⟩

end ArchS6
