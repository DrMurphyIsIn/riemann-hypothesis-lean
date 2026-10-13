import ArchS6_Bridge

/-!
# ArchS6_L1: `L¹` facts for the eigenfunctions (requested by S8/S10)

For a real eigenbasis `bR` of `C_ℝ` (S9's `T` on `[0,1]`):
* `integrableOn_e`, `integrableOn_phiR`: `e_i` and its continuous representative `phiR` are integrable
  on `[0,1]`;
* `integral_abs_e_le_one`, `integral_abs_phiR_le_one`: `∫_{[0,1]} |e_i| ≤ 1` (from `|e| ≤ (e² + 1)/2`
  and `∫ e² = ‖e‖² = 1`; no Cauchy-Schwarz needed).

conjecture1_proved = False.
-/

open MeasureTheory Set
open scoped InnerProductSpace

noncomputable section

namespace ArchS6

open ArchS5

variable {ι : Type*} (bR : EigenBasis CopR ι)

theorem integrableOn_e (i : ι) : IntegrableOn (bR.e i : ℝ → ℝ) (Icc 0 1) :=
  (Lp.memLp _).integrable (by norm_num)

theorem integrableOn_phiR (i : ι) : IntegrableOn (phiR bR i) (Icc 0 1) :=
  (integrableOn_e bR i).congr_fun_ae (ae_eq_phiR bR i)

theorem integral_sq_e (i : ι) : ∫ x in Icc (0 : ℝ) 1, bR.e i x * bR.e i x = 1 := by
  rw [← inner_L2IR, real_inner_self_eq_norm_sq, bR.orthonormal.1 i, one_pow]

/-- **`∫_{[0,1]} |e_i| ≤ 1`.** -/
theorem integral_abs_e_le_one (i : ι) : ∫ x in Icc (0 : ℝ) 1, |bR.e i x| ≤ 1 := by
  have hsq : Integrable (fun x ↦ bR.e i x * bR.e i x) (volI 0 1) :=
    (Lp.memLp (bR.e i)).integrable_mul (Lp.memLp (bR.e i))
  have h1 : ∫ x in Icc (0 : ℝ) 1, |bR.e i x| ≤
      ∫ x in Icc (0 : ℝ) 1, (bR.e i x * bR.e i x + 1) / 2 := by
    refine integral_mono (integrableOn_e bR i).abs ((hsq.add (integrable_const 1)).div_const 2)
      fun x ↦ ?_
    nlinarith [sq_nonneg (|bR.e i x| - 1), sq_abs (bR.e i x)]
  have h2 : ∫ x in Icc (0 : ℝ) 1, (bR.e i x * bR.e i x + 1) / 2 = 1 := by
    rw [integral_div, integral_add hsq (integrable_const 1), integral_sq_e]
    simp
  linarith

theorem integral_abs_phiR_le_one (i : ι) : ∫ x in Icc (0 : ℝ) 1, |phiR bR i x| ≤ 1 := by
  have : ∫ x in Icc (0 : ℝ) 1, |phiR bR i x| = ∫ x in Icc (0 : ℝ) 1, |bR.e i x| := by
    refine integral_congr_ae ?_
    filter_upwards [ae_eq_phiR bR i] with x hx
    rw [hx]
  rw [this]; exact integral_abs_e_le_one bR i

end ArchS6
