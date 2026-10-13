import ArchS8_ProlateData

/-!
# ArchS7_Term: the termwise identification of CC (84) with S8's `ε` (closes S8 open item 1)

Connes–Consani, arXiv:2006.13771, Thm 4.7 and (84):
`ε(ρ) = Σ λ(n)/√(1-λ(n)²) ⟨ξ_n | ϑ(ρ⁻¹) ζ_n⟩` for `ρ ≥ 1`.

We work in the additive variable `t = log ρ ≥ 0` and in S6's normalisation (`L²(ℝ)` with the full-line
inner product).  The even prolate `ξ_n` is `phi_n(|v|)/√2` on `[-1, 1]` and `0` outside (so that
`∫_ℝ |ξ_n|² = ∫_0^1 phi_n² = 1`, CC's normalisation (16) for `phi_n`), and CC's
`ζ_n = (η_n - λ ξ_n)/√(1-λ²)` vanishes on `(-1, 1)` and equals `τ_n phi_n(|v|)/√2` on `|v| ≥ 1`,
where `phi_n = ξ_n^an` (CC, after (98)) and `τ_n = λ/√(1-λ²)`.

`ϑ(ρ⁻¹) ζ (v) = ρ^{1/2} ζ(ρ v)`, i.e. `dil t ζ v = e^{t/2} ζ(e^t v)`.

* `integral_coeff`: `∫_ℝ conj(ξ(v)) e^{t/2} ζ(e^t v) dv = kM phi (c • phi) t` for `t ≥ 0`.
* `cc84_coeff`: `τ_n ⟨ξ_n | ϑ(e^{-t}) ζ_n⟩ = w_n · kn_n(t)`, i.e. CC's n-th term of (84) is S8's.
* `eps_eq_tsum`: S8's `D.eps t` is CC's series (84) for `t ≥ 0`.

conjecture1_proved = False.
-/

open MeasureTheory Set Real
open scoped ComplexConjugate

noncomputable section

namespace ArchS7

open ArchS8

/-- The even representative of `ξ_n` in S6's normalisation: `phi(|v|)/√2` on `[-1,1]`, else `0`. -/
def xiRep (phi : ℝ → ℝ) (v : ℝ) : ℂ :=
  if |v| ≤ 1 then ((phi |v| / Real.sqrt 2 : ℝ) : ℂ) else 0

/-- The even representative of `ζ_n`: `c · phi(|v|)/√2` on `|v| ≥ 1`, `0` on `(-1, 1)`. -/
def zetaRep (c : ℝ) (phi : ℝ → ℝ) (v : ℝ) : ℂ :=
  if 1 ≤ |v| then ((c * phi |v| / Real.sqrt 2 : ℝ) : ℂ) else 0

/-- `ϑ(e^{-t})` pointwise: `ζ ↦ e^{t/2} ζ(e^t ·)` (CC (61) with `λ = ρ⁻¹ = e^{-t}`). -/
def dil (t : ℝ) (z : ℝ → ℂ) (v : ℝ) : ℂ := (Real.exp (t / 2) : ℂ) * z (Real.exp t * v)

/-- The real integrand on `[e^{-t}, 1]`. -/
def coeffDensity (phi : ℝ → ℝ) (c t x : ℝ) : ℝ :=
  Real.exp (t / 2) * (phi x * (c * phi (Real.exp t * x))) / 2

theorem integrand_eq (phi : ℝ → ℝ) (c t v : ℝ) :
    conj (xiRep phi v) * dil t (zetaRep c phi) v
      = (((Icc (Real.exp (-t)) 1).indicator (coeffDensity phi c t) |v| : ℝ) : ℂ) := by
  have he : 0 < Real.exp t := Real.exp_pos t
  have habs : |Real.exp t * v| = Real.exp t * |v| := by
    rw [abs_mul, abs_of_pos he]
  have hiff : Real.exp (-t) ≤ |v| ↔ 1 ≤ Real.exp t * |v| := by
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀' he]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  unfold xiRep dil zetaRep
  rw [habs]
  by_cases h1 : |v| ≤ 1
  · by_cases h3 : 1 ≤ Real.exp t * |v|
    · rw [if_pos h1, if_pos h3, indicator_of_mem (show |v| ∈ Icc (Real.exp (-t)) 1 from ⟨hiff.2 h3, h1⟩), Complex.conj_ofReal]
      unfold coeffDensity
      push_cast
      field_simp
      have h2c : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring
      rw [h2c]
    · rw [if_pos h1, if_neg h3, indicator_of_notMem (fun h => h3 (hiff.1 h.1))]
      simp
  · rw [if_neg h1, indicator_of_notMem (fun h => h1 h.2)]
    simp

/-- **The matrix coefficient `⟨ξ | ϑ(e^{-t}) ζ⟩` is S8's Volterra coefficient `kM`** (`t ≥ 0`). -/
theorem integral_coeff (phi : ℝ → ℝ) (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ v, conj (xiRep phi v) * dil t (zetaRep c phi) v = (kM phi (fun x => c * phi x) t : ℂ) := by
  simp_rw [integrand_eq]
  rw [integral_complex_ofReal]
  congr 1
  rw [integral_comp_abs (f := (Icc (Real.exp (-t)) 1).indicator (coeffDensity phi c t)),
    setIntegral_indicator measurableSet_Icc]
  have hsub : Ioi (0 : ℝ) ∩ Icc (Real.exp (-t)) 1 = Icc (Real.exp (-t)) 1 :=
    inter_eq_right.2 fun x hx => lt_of_lt_of_le (Real.exp_pos _) hx.1
  have hle : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  rw [hsub, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  unfold kM coeffDensity
  rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul]
  ring

/-- **CC (84) termwise = S8.**  With CC's `ζ_n = τ_n ξ_n^an` on `[1,∞)`, the n-th term of (84),
`τ_n ⟨ξ_n | ϑ(e^{-t}) ζ_n⟩`, is `w_n · kn_n(t)`. -/
theorem cc84_coeff (D : ProlateDataNat) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ((D.lam n / Real.sqrt (1 - D.lam n ^ 2) : ℝ) : ℂ)
        * ∫ v, conj (xiRep (D.phi n) v)
            * dil t (zetaRep (D.lam n / Real.sqrt (1 - D.lam n ^ 2)) (D.phi n)) v
      = ((D.w n * D.kn n t : ℝ) : ℂ) := by
  rw [integral_coeff _ _ ht, ← Complex.ofReal_mul, D.cc84_term n t]

/-- **S8's `ε` is CC's series (84)** on `t ≥ 0`, with the matrix coefficients written as integrals
over `ℝ` in S6's normalisation. -/
theorem eps_eq_tsum (D : ProlateDataNat) {t : ℝ} (ht : 0 ≤ t) :
    ((D.eps t : ℝ) : ℂ) = ∑' n, ((D.lam n / Real.sqrt (1 - D.lam n ^ 2) : ℝ) : ℂ)
        * ∫ v, conj (xiRep (D.phi n) v)
            * dil t (zetaRep (D.lam n / Real.sqrt (1 - D.lam n ^ 2)) (D.phi n)) v := by
  simp_rw [cc84_coeff D _ ht]
  rw [ProlateData.eps, Complex.ofReal_tsum]

/-- Even form used by `Eplus`: for every real `v`, `ε(|v|)` is CC's (84) at `ρ = e^{|v|}`. -/
theorem eps_abs_eq_tsum (D : ProlateDataNat) (v : ℝ) :
    ((D.eps |v| : ℝ) : ℂ) = ∑' n, ((D.lam n / Real.sqrt (1 - D.lam n ^ 2) : ℝ) : ℂ)
        * ∫ x, conj (xiRep (D.phi n) x)
            * dil |v| (zetaRep (D.lam n / Real.sqrt (1 - D.lam n ^ 2)) (D.phi n)) x :=
  eps_eq_tsum D (abs_nonneg v)

end ArchS7
