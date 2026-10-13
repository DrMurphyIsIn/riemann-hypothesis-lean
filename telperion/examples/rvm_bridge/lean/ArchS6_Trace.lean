import ArchS6_ProlateData

/-!
# ArchS6_Trace: the prolate eigenvalues are absolutely summable (`Σ |λ_n| ≤ 2 cosh 2π`)

This is the summability CC's series (84)/(97) and S7's `thm47_concrete` (hypothesis `hτ`) need, i.e.
bypass B3 in its unordered form.  The proof is elementary and does not order the spectrum:

* `2cos(2πxy) = Σ_j a_j x^{2j} y^{2j}` with `a_j = 2(-1)^j (2π)^{2j}/(2j)!` (`hasSum_cosKR`);
* `λ_i = ⟪e_i, C e_i⟫ = Σ_j a_j c_{ij}²` with `c_{ij} = ∫₀¹ x^{2j} e_i(x) dx` (`mu_eq_tsum`,
  Fubini + dominated exchange of `∫` and `Σ`);
* Bessel `Σ_i c_{ij}² ≤ ‖x^{2j}‖² ≤ 1`, hence `Σ_i |λ_i| ≤ Σ_j |a_j| = 2 cosh 2π`
  (`summable_abs_mu`, `tsum_abs_mu_le`);
* `|τ_i| = |λ_i|/√(1-λ_i²) ≤ 2|λ_i|` for all but finitely many `i`, so `Σ |τ_i| < ∞`
  (`summable_abs_tau`), which is S7's hypothesis `hτ`.

conjecture1_proved = False.
-/

open MeasureTheory Set Filter
open scoped InnerProductSpace Real

noncomputable section

namespace ArchS6

open ArchS5

set_option linter.unusedSectionVars false

/-- The Taylor coefficients of `2cos(2πt)` in `t²`. -/
def aC (j : ℕ) : ℝ := 2 * ((-1) ^ j * (2 * π) ^ (2 * j) / ((2 * j).factorial : ℝ))

theorem abs_aC (j : ℕ) : |aC j| = 2 * ((2 * π) ^ (2 * j) / ((2 * j).factorial : ℝ)) := by
  rw [aC, abs_mul, abs_two, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * π) ^ (2 * j)),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 * j).factorial : ℝ))]

theorem hasSum_abs_aC : HasSum (fun j ↦ |aC j|) (2 * Real.cosh (2 * π)) := by
  simp only [abs_aC]
  exact (Real.hasSum_cosh (2 * π)).mul_left 2

theorem summable_abs_aC : Summable fun j ↦ |aC j| := hasSum_abs_aC.summable

theorem hasSum_cosKR (x y : ℝ) : HasSum (fun j ↦ aC j * (x * y) ^ (2 * j)) (cosKR (x, y)) := by
  have h := (Real.hasSum_cos (2 * π * x * y)).mul_left 2
  rw [cosKR]
  have e : (fun j ↦ aC j * (x * y) ^ (2 * j)) =
      fun i ↦ 2 * ((-1) ^ i * (2 * π * x * y) ^ (2 * i) / ((2 * i).factorial : ℝ)) := by
    funext j
    rw [aC, show 2 * π * x * y = (2 * π) * (x * y) by ring, mul_pow]
    ring
  rw [e]; exact h

variable {ι : Type*} (bR : EigenBasis CopR ι)

/-- `c_{ij} = ∫₀¹ x^{2j} e_i(x) dx`. -/
def cMom (i : ι) (j : ℕ) : ℝ := ∫ x in Icc (0 : ℝ) 1, x ^ (2 * j) * bR.e i x

theorem integrable_e (i : ι) : Integrable (bR.e i : ℝ → ℝ) (volI 0 1) :=
  (Lp.memLp _).integrable (by norm_num)

theorem integrable_mom (i : ι) (j : ℕ) :
    Integrable (fun x ↦ x ^ (2 * j) * bR.e i x) (volI 0 1) := by
  refine (integrable_e bR i).bdd_mul (c := 1) (by fun_prop) ?_
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with x hx
  rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg hx.1]
  exact pow_le_one₀ hx.1 hx.2

theorem abs_cMom_le (i : ι) (j : ℕ) : |cMom bR i j| ≤ ∫ x in Icc (0 : ℝ) 1, |bR.e i x| := by
  rw [cMom]
  refine (abs_integral_le_integral_abs).trans (integral_mono_ae (integrable_mom bR i j).abs
    (integrable_e bR i).abs ?_)
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with x hx
  rw [abs_mul, abs_pow, abs_of_nonneg hx.1]
  exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hx.1 hx.2)

/-- The `j`-th term of the double integral `∫∫ e(x) 2cos(2πxy) e(y)`. -/
def Fterm (i : ι) (j : ℕ) (p : ℝ × ℝ) : ℝ :=
  aC j * ((p.1 ^ (2 * j) * bR.e i p.1) * (p.2 ^ (2 * j) * bR.e i p.2))

theorem integrable_Fterm (i : ι) (j : ℕ) :
    Integrable (Fterm bR i j) ((volI 0 1).prod (volI 0 1)) :=
  ((integrable_mom bR i j).mul_prod (integrable_mom bR i j)).const_mul (aC j)

theorem integral_Fterm (i : ι) (j : ℕ) :
    ∫ p, Fterm bR i j p ∂((volI 0 1).prod (volI 0 1)) = aC j * cMom bR i j ^ 2 := by
  simp only [Fterm]
  rw [integral_const_mul, integral_prod_mul (fun x ↦ x ^ (2 * j) * bR.e i x)
    (fun x ↦ x ^ (2 * j) * bR.e i x), cMom, sq]

theorem integral_norm_Fterm (i : ι) (j : ℕ) :
    ∫ p, ‖Fterm bR i j p‖ ∂((volI 0 1).prod (volI 0 1)) =
      |aC j| * (∫ x in Icc (0 : ℝ) 1, |x ^ (2 * j)| * |bR.e i x|) ^ 2 := by
  simp only [Fterm, Real.norm_eq_abs, abs_mul]
  rw [integral_const_mul, integral_prod_mul (fun x ↦ |x ^ (2 * j)| * |bR.e i x|)
    (fun x ↦ |x ^ (2 * j)| * |bR.e i x|), sq]

theorem integral_abs_mom_le (i : ι) (j : ℕ) :
    ∫ x in Icc (0 : ℝ) 1, |x ^ (2 * j)| * |bR.e i x| ≤ ∫ x in Icc (0 : ℝ) 1, |bR.e i x| := by
  refine integral_mono_ae ((integrable_mom bR i j).abs.congr (ae_of_all _ fun x ↦ abs_mul _ _))
    (integrable_e bR i).abs ?_
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with x hx
  rw [abs_pow, abs_of_nonneg hx.1]
  exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hx.1 hx.2)

theorem summable_integral_norm_Fterm (i : ι) :
    Summable fun j ↦ ∫ p, ‖Fterm bR i j p‖ ∂((volI 0 1).prod (volI 0 1)) := by
  set A := ∫ x in Icc (0 : ℝ) 1, |bR.e i x|
  refine Summable.of_nonneg_of_le (fun j ↦ integral_nonneg fun _ ↦ norm_nonneg _)
    (fun j ↦ ?_) (summable_abs_aC.mul_right (A ^ 2))
  rw [integral_norm_Fterm]
  have h0 : 0 ≤ ∫ x in Icc (0 : ℝ) 1, |x ^ (2 * j)| * |bR.e i x| :=
    integral_nonneg fun _ ↦ mul_nonneg (abs_nonneg _) (abs_nonneg _)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (integral_abs_mom_le bR i j) 2)
    (abs_nonneg _)

/-- `λ_i = ⟪e_i, C e_i⟫ = ∫∫ e_i(x) 2cos(2πxy) e_i(y)`. -/
theorem mu_eq_integral (i : ι) :
    bR.μ i = ∫ p, bR.e i p.1 * cosKR p * bR.e i p.2 ∂((volI 0 1).prod (volI 0 1)) := by
  have h := bR.μ_eq_inner i
  have h2 := inner_intOp_eq_integral (kernelOfContinuous 0 1 cosKR continuous_cosKR) (bR.e i)
    (bR.e i)
  simp only [conj_trivial] at h2
  have h3 : bR.μ i = ⟪bR.e i, CopR (bR.e i)⟫_ℝ := h
  rw [h3]
  refine h2.trans (integral_congr_ae ?_)
  filter_upwards [kernelOfContinuous_ae_eq (a := 0) (b := 1) continuous_cosKR] with p hp
  rw [hp]

/-- **`λ_i = Σ_j a_j c_{ij}²`.** -/
theorem hasSum_mu (i : ι) : HasSum (fun j ↦ aC j * cMom bR i j ^ 2) (bR.μ i) := by
  have hsum := summable_integral_norm_Fterm bR i
  have hex := integral_tsum_of_summable_integral_norm (integrable_Fterm bR i) hsum
  have hpt : ∀ p : ℝ × ℝ, ∑' j, Fterm bR i j p = bR.e i p.1 * cosKR p * bR.e i p.2 := by
    intro p
    have := ((hasSum_cosKR p.1 p.2).mul_left (bR.e i p.1 * bR.e i p.2)).tsum_eq
    rw [show (p.1, p.2) = p from rfl] at this
    rw [← show bR.e i p.1 * bR.e i p.2 * cosKR p = bR.e i p.1 * cosKR p * bR.e i p.2 by ring,
      ← this]
    congr 1; funext j
    simp only [Fterm]; rw [mul_pow]; ring
  simp only [hpt, integral_Fterm] at hex
  rw [mu_eq_integral, ← hex]
  refine (Summable.of_norm_bounded (summable_abs_aC.mul_right
    ((∫ x in Icc (0 : ℝ) 1, |bR.e i x|) ^ 2)) fun j ↦ ?_).hasSum
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (abs_cMom_le bR i j) 2)
    (abs_nonneg _)

/-- Bessel for the moments: `Σ_{i ∈ s} c_{ij}² ≤ 1`. -/
theorem sum_cMom_sq_le (j : ℕ) (s : Finset ι) : ∑ i ∈ s, cMom bR i j ^ 2 ≤ 1 := by
  have hg : Continuous (Function.uncurry fun (_ y : ℝ) ↦ y ^ (2 * j)) := by fun_prop
  have h := sum_sq_kInt_le bR hg (B := 1) (fun _ y hy ↦ by
    rw [abs_pow, abs_of_nonneg hy.1]; exact pow_le_one₀ hy.1 hy.2) 0 s
  simpa [kInt, cMom] using h

/-- **Trace class**: `Σ_{i ∈ s} |λ_i| ≤ 2 cosh 2π` for every finite `s`. -/
theorem sum_abs_mu_le (s : Finset ι) : ∑ i ∈ s, |bR.μ i| ≤ 2 * Real.cosh (2 * π) := by
  have hsm : ∀ i, Summable fun j ↦ |aC j| * cMom bR i j ^ 2 := fun i ↦
    Summable.of_nonneg_of_le (fun j ↦ mul_nonneg (abs_nonneg _) (sq_nonneg _))
      (fun j ↦ mul_le_mul_of_nonneg_left
        (by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_cMom_le bR i j) 2)
        (abs_nonneg _))
      (summable_abs_aC.mul_right ((∫ x in Icc (0 : ℝ) 1, |bR.e i x|) ^ 2))
  have h1 : ∀ i, |bR.μ i| ≤ ∑' j, |aC j| * cMom bR i j ^ 2 := fun i ↦ by
    have hn : Summable fun j ↦ ‖aC j * cMom bR i j ^ 2‖ := by
      refine (hsm i).congr fun j ↦ ?_
      rw [Real.norm_eq_abs, abs_mul, abs_pow, sq_abs]
    rw [← (hasSum_mu bR i).tsum_eq, ← Real.norm_eq_abs]
    refine (norm_tsum_le_tsum_norm hn).trans_eq ?_
    congr 1; funext j; rw [Real.norm_eq_abs, abs_mul, abs_pow, sq_abs]
  calc ∑ i ∈ s, |bR.μ i| ≤ ∑ i ∈ s, ∑' j, |aC j| * cMom bR i j ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ h1 i
    _ = ∑' j, ∑ i ∈ s, |aC j| * cMom bR i j ^ 2 :=
        (Summable.tsum_finsetSum fun i _ ↦ hsm i).symm
    _ ≤ ∑' j, |aC j| := by
        refine Summable.tsum_le_tsum (fun j ↦ ?_) (summable_sum fun i _ ↦ hsm i) summable_abs_aC
        rw [← Finset.mul_sum]
        exact mul_le_of_le_one_right (abs_nonneg _) (sum_cMom_sq_le bR j s)
    _ = 2 * Real.cosh (2 * π) := hasSum_abs_aC.tsum_eq

theorem summable_abs_mu : Summable fun i ↦ |bR.μ i| :=
  summable_of_sum_le (fun _ ↦ abs_nonneg _) (sum_abs_mu_le bR)

theorem tsum_abs_mu_le : ∑' i, |bR.μ i| ≤ 2 * Real.cosh (2 * π) :=
  (summable_abs_mu bR).tsum_le_of_sum_le (sum_abs_mu_le bR)

/-- **S7's hypothesis `hτ`**: `Σ |τ_i| < ∞`, `τ_i = λ_i/√(1 - λ_i²)`. -/
theorem summable_abs_tau : Summable fun i ↦ |(realProlateBasis bR).τ i| := by
  have hz := (summable_abs_mu bR).tendsto_cofinite_zero
  have hev : ∀ᶠ i in cofinite, |bR.μ i| < 1 / 2 := hz.eventually (gt_mem_nhds (by norm_num))
  refine Summable.of_norm_bounded_eventually ((summable_abs_mu bR).mul_left 2) ?_
  filter_upwards [hev] with i hi
  have hs : 1 / 2 ≤ (realProlateBasis bR).s i := by
    rw [ProlateBasis.s, realProlateBasis_lam]
    apply Real.le_sqrt_of_sq_le
    nlinarith [abs_nonneg (bR.μ i), sq_abs (bR.μ i)]
  have hs0 : 0 < (realProlateBasis bR).s i := by linarith
  rw [Real.norm_eq_abs, abs_abs, ProlateBasis.τ, realProlateBasis_lam, abs_div,
    abs_of_pos hs0, div_le_iff₀ hs0]
  nlinarith [abs_nonneg (bR.μ i)]

end ArchS6
