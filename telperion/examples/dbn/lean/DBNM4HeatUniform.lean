/-
  DBNM4HeatUniform -- lane m4 (Route C milestone M4): two analytic facts about the heat flow
  `H t z = ∫_0^∞ e^{tu²} Φ(u) cos(zu) du` and its de Bruijn approximants
  `Gδ δ n = T_δ^n H_0` (`DBNHeatApprox`), used by the discrete barrier proof of Polymath15
  Prop 3.3 (`DBNM4P15Criterion`).

  * `m4_continuous_H_uncurry`: `(t, z) ↦ H t z` is jointly continuous on `ℝ × ℂ` (dominated
    convergence, locally uniform majorant `e^{(t₀+1)u² + (10 + ‖z₀‖)u} |Φ(u)|`).
  * `m4_exp_sub_cosh_pow_le`: `e^{n v²/2} − cosh(v)^n ≤ e^{n v²/2} · n v⁴/4` for every real `v`
    (Bernoulli's inequality applied to `g = cosh(v) e^{−v²/2} ∈ [1 − v⁴/4, 1]`).
  * `m4_norm_H_sub_Gδ_le`: the uniform approximation bound along the discrete heat path,
    `‖H (n δ²/2) z − Gδ δ n z‖ ≤ (n δ⁴/4) · m4ApproxConst T R` whenever `|Im z| ≤ R` and
    `n δ²/2 ≤ T`, with the fourth-moment constant
    `m4ApproxConst T R = ∫_0^∞ u⁴ e^{T u² + R u} |Φ(u)| du`.  On the path `δ² = 2t0/N`,
    `n ≤ N` this is `≤ (t0²/N) · m4ApproxConst t0 R`, uniformly in `n` -- the island's
    `norm_H_sub_G_le` is for a fixed time `t` and gives no rate.

  Nothing here proves RH.  conjecture1_proved = False.
-/
import DBNHeatApprox

open Real MeasureTheory Set Filter Topology

namespace DBN

/-! ### Joint continuity of the heat flow -/

/-- **`(t, z) ↦ H t z` is jointly continuous.** -/
theorem m4_continuous_H_uncurry : Continuous (fun p : ℝ × ℂ ↦ H p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t₀, z₀⟩
  unfold H
  have hC := ΦBoundConst_nonneg
  have hint : Integrable (fun u : ℝ ↦ ΦBoundConst * (Real.exp ((t₀ + 1) * u ^ 2 + (10 + ‖z₀‖) * u)
      * Real.exp (-(π / 2) * Real.exp (4 * u)))) (volume.restrict (Ioi (0 : ℝ))) :=
    (integrableOn_exp_quad_mul_exp_neg_exp (t₀ + 1) (10 + ‖z₀‖)).const_mul ΦBoundConst
  have h1 : ∀ᶠ p : ℝ × ℂ in 𝓝 (t₀, z₀), p.1 < t₀ + 1 :=
    (continuous_fst.tendsto (t₀, z₀)).eventually (gt_mem_nhds (by linarith))
  have h2 : ∀ᶠ p : ℝ × ℂ in 𝓝 (t₀, z₀), ‖p.2‖ < ‖z₀‖ + 1 :=
    ((continuous_norm.comp continuous_snd).tendsto (t₀, z₀)).eventually
      (gt_mem_nhds (by simp))
  have hmeas : ∀ᶠ p : ℝ × ℂ in 𝓝 (t₀, z₀),
      AEStronglyMeasurable (fun u ↦ HIntegrand p.1 p.2 u) (volume.restrict (Ioi (0 : ℝ))) :=
    Eventually.of_forall fun p ↦ (continuous_HIntegrand p.1 p.2).aestronglyMeasurable
  have hb : ∀ᶠ p : ℝ × ℂ in 𝓝 (t₀, z₀), ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖HIntegrand p.1 p.2 u‖ ≤ ΦBoundConst * (Real.exp ((t₀ + 1) * u ^ 2 + (10 + ‖z₀‖) * u)
        * Real.exp (-(π / 2) * Real.exp (4 * u))) := by
    filter_upwards [h1, h2] with p hp1 hp2
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun u hu ↦ ?_
    have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
    have hcos : ‖Complex.cos (p.2 * u)‖ ≤ Real.exp ((‖z₀‖ + 1) * u) := by
      refine (norm_cos_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
      exact mul_le_mul_of_nonneg_right hp2.le hu0
    have hexp : Real.exp (p.1 * u ^ 2) ≤ Real.exp ((t₀ + 1) * u ^ 2) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hp1.le (sq_nonneg u))
    have hΦ := abs_Φ_le hu0
    unfold HIntegrand
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (p.1 * u ^ 2) * |Φ u| * ‖Complex.cos (p.2 * u)‖
        ≤ Real.exp ((t₀ + 1) * u ^ 2)
            * (ΦBoundConst * (Real.exp (9 * u) * Real.exp (-(π / 2) * Real.exp (4 * u))))
            * Real.exp ((‖z₀‖ + 1) * u) := by gcongr
      _ = ΦBoundConst * (Real.exp ((t₀ + 1) * u ^ 2 + (10 + ‖z₀‖) * u)
            * Real.exp (-(π / 2) * Real.exp (4 * u))) := by
          have e : Real.exp ((t₀ + 1) * u ^ 2 + (10 + ‖z₀‖) * u)
              = Real.exp ((t₀ + 1) * u ^ 2) * Real.exp (9 * u) * Real.exp ((‖z₀‖ + 1) * u) := by
            rw [← Real.exp_add, ← Real.exp_add]; ring_nf
          rw [e]; ring
  have hc : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))),
      ContinuousAt (fun p : ℝ × ℂ ↦ HIntegrand p.1 p.2 u) (t₀, z₀) := by
    refine Eventually.of_forall fun u ↦ ?_
    have : Continuous (fun p : ℝ × ℂ ↦ HIntegrand p.1 p.2 u) := by
      unfold HIntegrand
      fun_prop
    exact this.continuousAt
  exact continuousAt_of_dominated hmeas hb hint hc

/-! ### The kernel error `e^{n v²/2} − cosh(v)^n` -/

/-- **`e^{n v²/2} − cosh(v)^n ≤ e^{n v²/2} · n v⁴/4`** for every real `v` and `n : ℕ`. -/
lemma m4_exp_sub_cosh_pow_le (v : ℝ) (n : ℕ) :
    Real.exp (n * v ^ 2 / 2) - Real.cosh v ^ n ≤ Real.exp (n * v ^ 2 / 2) * (n * v ^ 4 / 4) := by
  set g : ℝ := Real.cosh v * Real.exp (-(v ^ 2 / 2)) with hg
  have hE : Real.exp (-(v ^ 2 / 2)) * Real.exp (v ^ 2 / 2) = 1 := by
    rw [← Real.exp_add]; simp
  have hcosh : Real.cosh v = g * Real.exp (v ^ 2 / 2) := by
    rw [hg, mul_assoc, hE, mul_one]
  have hg0 : 0 ≤ g := by
    rw [hg]; exact mul_nonneg (Real.cosh_pos v).le (Real.exp_pos _).le
  have hglow : 1 - v ^ 4 / 4 ≤ g := by
    have hc := one_add_sq_div_two_le_cosh v
    have he := Real.add_one_le_exp (-(v ^ 2 / 2))
    rcases le_total (v ^ 2) 2 with h | h
    · calc 1 - v ^ 4 / 4 = (1 + v ^ 2 / 2) * (-(v ^ 2 / 2) + 1) := by ring
        _ ≤ Real.cosh v * Real.exp (-(v ^ 2 / 2)) :=
            mul_le_mul hc he (by linarith) (Real.cosh_pos v).le
    · have : 1 - v ^ 4 / 4 ≤ 0 := by nlinarith
      linarith
  have hbern : 1 + (n : ℝ) * (g - 1) ≤ g ^ n := by
    have := one_add_mul_le_pow (a := g - 1) (by linarith) n
    simpa using this
  have hpow : Real.cosh v ^ n = g ^ n * Real.exp (n * v ^ 2 / 2) := by
    rw [hcosh, mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  rw [hpow]
  have hEpos : 0 < Real.exp (n * v ^ 2 / 2) := Real.exp_pos _
  have h1 : 1 - g ^ n ≤ n * v ^ 4 / 4 := by
    have : (n : ℝ) * (1 - g) ≤ n * (v ^ 4 / 4) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n)
    linarith
  calc Real.exp (n * v ^ 2 / 2) - g ^ n * Real.exp (n * v ^ 2 / 2)
      = Real.exp (n * v ^ 2 / 2) * (1 - g ^ n) := by ring
    _ ≤ Real.exp (n * v ^ 2 / 2) * (n * v ^ 4 / 4) := mul_le_mul_of_nonneg_left h1 hEpos.le

/-! ### Uniform approximation along the discrete heat path -/

/-- The fourth-moment majorant integrand `u⁴ e^{T u² + R u} |Φ(u)|`. -/
noncomputable def m4ApproxIntegrand (T R : ℝ) (u : ℝ) : ℝ :=
  u ^ 4 * Real.exp (T * u ^ 2 + R * u) * |Φ u|

/-- The fourth-moment constant `∫_0^∞ u⁴ e^{T u² + R u} |Φ(u)| du`. -/
noncomputable def m4ApproxConst (T R : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), m4ApproxIntegrand T R u

lemma m4_integrableOn_approxIntegrand (T R : ℝ) :
    IntegrableOn (m4ApproxIntegrand T R) (Ioi 0) := by
  have hg := (integrableOn_exp_mul_abs_Φ T (R + 1)).const_mul 24
  have hcont : Continuous (m4ApproxIntegrand T R) := by
    unfold m4ApproxIntegrand
    fun_prop
  refine hg.mono' hcont.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu ↦ ?_
  have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
  have h4 : u ^ 4 ≤ 24 * Real.exp u := by
    have := Real.pow_div_factorial_le_exp u hu0 4
    norm_num [Nat.factorial] at this
    linarith
  unfold m4ApproxIntegrand
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc u ^ 4 * Real.exp (T * u ^ 2 + R * u) * |Φ u|
      ≤ (24 * Real.exp u) * Real.exp (T * u ^ 2 + R * u) * |Φ u| := by gcongr
    _ = 24 * (Real.exp (T * u ^ 2 + (R + 1) * u) * |Φ u|) := by
        have e : Real.exp (T * u ^ 2 + (R + 1) * u) = Real.exp u * Real.exp (T * u ^ 2 + R * u) := by
          rw [← Real.exp_add]; ring_nf
        rw [e]; ring

lemma m4ApproxConst_nonneg (T R : ℝ) : 0 ≤ m4ApproxConst T R := by
  unfold m4ApproxConst
  refine setIntegral_nonneg measurableSet_Ioi fun u _ ↦ ?_
  unfold m4ApproxIntegrand
  have : 0 ≤ u ^ 4 := by positivity
  positivity

/-- **Uniform approximation along the discrete heat path.**  For `|Im z| ≤ R` and
`n δ²/2 ≤ T`: `‖H (n δ²/2) z − Gδ δ n z‖ ≤ (n δ⁴/4) · m4ApproxConst T R`. -/
theorem m4_norm_H_sub_Gδ_le (δ : ℝ) (n : ℕ) {z : ℂ} {R T : ℝ} (hR : |z.im| ≤ R)
    (hT : n * δ ^ 2 / 2 ≤ T) :
    ‖H (n * δ ^ 2 / 2) z - Gδ δ n z‖ ≤ n * δ ^ 4 / 4 * m4ApproxConst T R := by
  unfold Gδ H m4ApproxConst
  rw [← integral_sub (integrableOn_HIntegrand _ z) (integrableOn_GδIntegrand δ n z),
    ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((m4_integrableOn_approxIntegrand T R).const_mul _) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu ↦ ?_
  have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
  have hsu : (n : ℝ) * δ ^ 2 / 2 * u ^ 2 = n * (δ * u) ^ 2 / 2 := by ring
  have hker := m4_exp_sub_cosh_pow_le (δ * u) n
  rw [← hsu] at hker
  have hle : Real.cosh (δ * u) ^ n ≤ Real.exp (n * δ ^ 2 / 2 * u ^ 2) := cosh_pow_le_exp δ u n
  have h2 : 0 ≤ Real.exp (n * δ ^ 2 / 2 * u ^ 2) - Real.cosh (δ * u) ^ n := by linarith
  have hexpT : Real.exp (n * δ ^ 2 / 2 * u ^ 2) ≤ Real.exp (T * u ^ 2) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hT (sq_nonneg u))
  have hdiff : HIntegrand (n * δ ^ 2 / 2) z u - GδIntegrand δ n z u
      = (((Real.exp (n * δ ^ 2 / 2 * u ^ 2) - Real.cosh (δ * u) ^ n : ℝ)) : ℂ)
        * ((Φ u : ℝ) : ℂ) * Complex.cos (z * u) := by
    unfold HIntegrand GδIntegrand
    push_cast
    ring
  rw [hdiff, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg h2]
  have hcos : ‖Complex.cos (z * u)‖ ≤ Real.exp (R * u) :=
    (norm_cos_mul_le hu0 z).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hR hu0))
  have hkerT : Real.exp (n * δ ^ 2 / 2 * u ^ 2) - Real.cosh (δ * u) ^ n
      ≤ Real.exp (T * u ^ 2) * (n * (δ * u) ^ 4 / 4) := by
    refine hker.trans ?_
    gcongr
  unfold m4ApproxIntegrand
  calc (Real.exp (n * δ ^ 2 / 2 * u ^ 2) - Real.cosh (δ * u) ^ n) * |Φ u|
        * ‖Complex.cos (z * u)‖
      ≤ (Real.exp (T * u ^ 2) * (n * (δ * u) ^ 4 / 4)) * |Φ u| * Real.exp (R * u) := by
        gcongr
    _ = n * δ ^ 4 / 4 * (u ^ 4 * Real.exp (T * u ^ 2 + R * u) * |Φ u|) := by
        rw [Real.exp_add]; ring

end DBN
