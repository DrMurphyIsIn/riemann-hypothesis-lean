/-
  M6gapImAxis -- lane m6gap, gap (1) of the M6 row (ROUTE_C_SYNTHESIS_2026-09-23 section 5.2):
  the T = 0 case of Polymath15 Thm 1.2(i), by the Polymath15 p.15 argument (positivity of Φ).

  On the imaginary axis the heat-flow integrand is `e^{tu²} Φ(u) cosh(yu) > 0`, so

      H_t(iy) = ∫_0^∞ e^{tu²} Φ(u) cosh(yu) du > 0          (every real t, y)

  (`H_ofReal_mul_I_re_pos`, from `Φ_pos` of DBNHeatApprox).  Through the C2 identity
  `H_0(z) = (1/8) ξ(1/2 + iz/2)` (`dbn_H0_eq_xi`) at `z = (1 - 2σ) i` this says `ξ(σ) ≠ 0` for every
  real `σ`, and through the C4 unpacking `ξ(s) = 0 ↔ ζ(s) = 0 ∧ 0 < Re s < 1` it says
  `ζ(σ) ≠ 0` for real `0 < σ < 1` (`riemannZeta_ofReal_ne_zero_of_mem_Ioo`).  No Euler-Maclaurin,
  no Dirichlet eta, no summation by parts: the only analytic input is `Φ > 0`.

  Also here: `H_conj` (Schwarz reflection for `H_t`, the `Gδ_conj` argument), used by the
  M6gap assembly to move between the four symmetric copies of a zero; and the root-namespace,
  registry-shaped forms `m6gap_dbn_H_imag_axis_ne_zero`, `m6gap_dbn_no_real_zero_in_unit_interval`.

  conjecture1_proved = False.  Real zeros of ζ in (0,1) are classically absent; nothing here
  bears on the Riemann Hypothesis or on the de Bruijn-Newman constant.
-/
import DBNHeatApprox
import DBNRealZerosIffFinal

open Real MeasureTheory Set Filter ComplexConjugate

namespace M6gap

open DBN

/-- **`H_t` is real** (Schwarz reflection): `H t (conj z) = conj (H t z)`. -/
theorem H_conj (t : ℝ) (z : ℂ) : H t (conj z) = conj (H t z) := by
  unfold H
  rw [← integral_conj]
  congr 1
  funext u
  unfold HIntegrand
  rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, ← Complex.cos_conj, map_mul,
    Complex.conj_ofReal]

/-- The integrand on the imaginary axis: `cos((y i) u) = cosh(y u)`. -/
lemma cos_ofReal_mul_I_mul (y u : ℝ) :
    Complex.cos ((y : ℂ) * Complex.I * (u : ℂ)) = ((Real.cosh (y * u) : ℝ) : ℂ) := by
  rw [show (y : ℂ) * Complex.I * (u : ℂ) = ((y * u : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.cos_mul_I, Complex.ofReal_cosh]

/-- On the imaginary axis `H_t` is the real integral `∫_0^∞ e^{tu²} Φ(u) cosh(yu) du`. -/
theorem H_ofReal_mul_I (t y : ℝ) :
    H t ((y : ℂ) * Complex.I)
      = ((∫ u in Ioi (0 : ℝ), Real.exp (t * u ^ 2) * Real.cosh (y * u) * Φ u : ℝ) : ℂ) := by
  have hfun : (fun u ↦ HIntegrand t ((y : ℂ) * Complex.I) u)
      = fun u ↦ ((Real.exp (t * u ^ 2) * Real.cosh (y * u) * Φ u : ℝ) : ℂ) := by
    funext u
    unfold HIntegrand
    rw [cos_ofReal_mul_I_mul]
    push_cast
    ring
  unfold H
  rw [hfun]
  exact integral_ofReal

/-- Integrability of the imaginary-axis integrand `e^{tu²} cosh(yu) Φ(u)` on `(0, ∞)`. -/
lemma integrableOn_imAxis (t y : ℝ) :
    IntegrableOn (fun u ↦ (Real.exp (t * u ^ 2) * Real.cosh (y * u)) * Φ u) (Ioi 0) := by
  have hcont : Continuous (fun u : ℝ ↦ (Real.exp (t * u ^ 2) * Real.cosh (y * u)) * Φ u) := by
    fun_prop
  refine (integrableOn_exp_mul_abs_Φ t |y|).mono' hcont.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu ↦ ?_
  have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
  have hch : Real.cosh (y * u) ≤ Real.exp (|y| * u) := by
    refine (cosh_le_exp_abs (y * u)).trans (le_of_eq ?_)
    rw [abs_mul, abs_of_nonneg hu0]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (mul_pos (Real.exp_pos _) (Real.cosh_pos _)),
    Real.exp_add]
  have hΦ := abs_nonneg (Φ u)
  have he := Real.exp_pos (t * u ^ 2)
  calc Real.exp (t * u ^ 2) * Real.cosh (y * u) * |Φ u|
      ≤ Real.exp (t * u ^ 2) * Real.exp (|y| * u) * |Φ u| := by gcongr

/-- `H_t(iy)` is real for every real `t` and `y` (with `H_ofReal_mul_I_re_pos`: `H_t(iy) > 0`,
the Polymath15 p.15 statement "H_t(iy) > 0 for all y ∈ ℝ"). -/
theorem H_ofReal_mul_I_im (t y : ℝ) : (H t ((y : ℂ) * Complex.I)).im = 0 := by
  rw [H_ofReal_mul_I, Complex.ofReal_im]

/-- **`H_t(iy) > 0`** (real part) for every real `t` and `y`: the imaginary-axis integrand
`e^{tu²} cosh(yu) Φ(u)` is positive (`Φ_pos`).  Polymath15 p.15. -/
theorem H_ofReal_mul_I_re_pos (t y : ℝ) : 0 < (H t ((y : ℂ) * Complex.I)).re := by
  rw [H_ofReal_mul_I, Complex.ofReal_re]
  exact setIntegral_weight_mul_Φ_pos
    (fun u ↦ mul_pos (Real.exp_pos _) (Real.cosh_pos _)) (integrableOn_imAxis t y)

/-- **`H_t` has no zero on the imaginary axis**, for every real `t`. -/
theorem H_ofReal_mul_I_ne_zero (t y : ℝ) : H t ((y : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have := H_ofReal_mul_I_re_pos t y
  rw [h, Complex.zero_re] at this
  exact lt_irrefl _ this

/-- A zero of `H_t` with real part `0` does not exist. -/
theorem H_ne_zero_of_re_eq_zero (t : ℝ) {z : ℂ} (hz : z.re = 0) : H t z ≠ 0 := by
  have : z = ((z.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hz]
  rw [this]
  exact H_ofReal_mul_I_ne_zero t z.im

/-- The C4 point of the imaginary axis: `1/2 + i ((1 - 2σ) i)/2 = σ`. -/
lemma xiArg_imAxis (σ : ℝ) :
    (1 / 2 + Complex.I * (((1 - 2 * σ : ℝ) : ℂ) * Complex.I) / 2 : ℂ) = (σ : ℂ) := by
  push_cast
  linear_combination ((1 - 2 * (σ : ℂ)) / 2) * Complex.I_mul_I

/-- **`ξ(σ) ≠ 0` for every real `σ`** (C2 at `z = (1 - 2σ) i`, plus `H_0(iy) > 0`). -/
theorem riemannXi_ofReal_ne_zero (σ : ℝ) : LiCriterion.riemannXi (σ : ℂ) ≠ 0 := by
  intro h
  have hH := dbn_H0_eq_xi (((1 - 2 * σ : ℝ) : ℂ) * Complex.I)
  rw [xiArg_imAxis, h, mul_zero] at hH
  exact H_ofReal_mul_I_ne_zero 0 (1 - 2 * σ) hH

/-- **`ζ(σ) ≠ 0` for real `0 < σ < 1`** (the T = 0 slice of Polymath15 Thm 1.2(i)), via
`ξ(σ) ≠ 0` and the C4 unpacking `ξ(s) = 0 ↔ ζ(s) = 0 ∧ 0 < Re s < 1`. -/
theorem riemannZeta_ofReal_ne_zero_of_mem_Ioo {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta (σ : ℂ) ≠ 0 := by
  intro hz
  refine riemannXi_ofReal_ne_zero σ ((riemannXi_eq_zero_iff_strip_zero (σ : ℂ)).mpr ⟨hz, ?_, ?_⟩)
  · simpa using h0
  · simpa using h1

/-- `ζ(σ) ≠ 0` for every real `σ ≥ 1/2` (the interval `(0,1)` above; `σ ≥ 1` from Mathlib's
`riemannZeta_ne_zero_of_one_le_re`, which includes Mathlib's junk value at the pole `σ = 1`). -/
theorem riemannZeta_ofReal_ne_zero_of_half_le {σ : ℝ} (h : 1 / 2 ≤ σ) :
    riemannZeta (σ : ℂ) ≠ 0 := by
  rcases lt_or_ge σ 1 with h1 | h1
  · exact riemannZeta_ofReal_ne_zero_of_mem_Ioo (by linarith) h1
  · exact riemannZeta_ne_zero_of_one_le_re (by simpa using h1)

end M6gap

/-! ### Registry-shaped forms (root namespace; proposed nodes, NOT registered by this lane) -/

/-- `H_t` has no zero on the imaginary axis, for every real `t` (Polymath15 p.15, from `Φ > 0`). -/
theorem m6gap_dbn_H_imag_axis_ne_zero :
    ∀ t y : ℝ, DBN.H t ((y : ℂ) * Complex.I) ≠ 0 :=
  M6gap.H_ofReal_mul_I_ne_zero

/-- `ζ(σ) ≠ 0` for real `0 < σ < 1` (the statement of `RvMBridge19.NoRealZeroInUnitInterval`), on
the dbn island, from `Φ > 0` through C2 and the C4 unpacking. -/
theorem m6gap_dbn_no_real_zero_in_unit_interval :
    ∀ σ : ℝ, 0 < σ → σ < 1 → riemannZeta (σ : ℂ) ≠ 0 :=
  fun _ h0 h1 ↦ M6gap.riemannZeta_ofReal_ne_zero_of_mem_Ioo h0 h1
