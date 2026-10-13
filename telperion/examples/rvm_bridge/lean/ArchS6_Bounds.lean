import ArchS6_Bridge
import ArchS6_Functions
import ArchS6_Sobolev

/-!
# ArchS6_Bounds: sup bounds for the prolates without the ODE (S8's `M n`, `N n`)

For a real eigenbasis `bR` of `C_ℝ` (eigenvalue `μ_i`, eigenvector `e_i`) and
`F_k^i(x) = ∫₀¹ k(x, y) e_i(y) dy` with the kernels

  `k₀ = 2cos(2πxy)`, `k₁ = ∂ₓk₀ = -4πy sin(2πxy)`, `k₂ = ∂ₓk₁ = -8π²y² cos(2πxy)`,

we have `μ_i φ_i = F₀^i`, `μ_i φ_i' = F₁^i`, `μ_i φ_i'' = F₂^i` on all of `ℝ` (`hasDerivAt_kInt`).

* **Pointwise Bessel** (`sum_sq_kInt_le`): `F_k^i(x) = ⟪e_i, k(x, ·)⟫`, so for every `x` and every
  finite set of indices `Σ_i F_k^i(x)² ≤ ‖k(x, ·)‖² ≤ B_k²` with `B = 2, 4π, 8π²`.
* **Sobolev** (`ArchS6_Sobolev`) on `[a, b] = [1/3, 3]` turns this into sup bounds:
  `|φ_i(x)|, |φ_i'(x)| ≤ Q_i` on `[1/3, 3]` (`abs_phiR_le_Q`, `abs_deriv_phiR_le_Q`), where
  `Q_i² = C · ∫_{1/3}^{3} (φ_i² + φ_i'² + φ_i''²)`, `C = 1/(b-a) + 2`.
* **Summability** (`summable_mu_sq_mul_S`): `Σ_i μ_i² ∫(φ_i² + φ_i'² + φ_i''²) < ∞`, because it equals
  `Σ_i ∫(F₀² + F₁² + F₂²) ≤ (b - a)(4 + 16π² + 64π⁴)`.

This is S8's "one substantive analytic obligation" (the bound `M n` beating `1/|λ_n|`), discharged
with `M n = N n = Q_n`: then `λ²/(1-λ²)·M·N = C λ² S/(1-λ²)`, which is summable.

conjecture1_proved = False.
-/

open MeasureTheory Set Filter
open scoped InnerProductSpace Real

noncomputable section

namespace ArchS6

open ArchS5

set_option linter.unusedSectionVars false

/-! ### Differentiation under the integral sign -/

/-- `F(x) = ∫₀¹ g(x, y) e(y) dy`. -/
def kInt (g : ℝ → ℝ → ℝ) (e : L2IR 0 1) (x : ℝ) : ℝ := ∫ y in Icc (0 : ℝ) 1, g x y * e y

theorem exists_bound_compact {g : ℝ → ℝ → ℝ} (hg : Continuous (Function.uncurry g)) (x₀ : ℝ) :
    ∃ B, ∀ x ∈ Metric.closedBall x₀ 1, ∀ y ∈ Icc (0 : ℝ) 1, |g x y| ≤ B := by
  obtain ⟨B, hB⟩ := ((isCompact_closedBall x₀ 1).prod isCompact_Icc).exists_bound_of_continuousOn
    hg.continuousOn
  exact ⟨B, fun x hx y hy ↦ by simpa using hB (x, y) ⟨hx, hy⟩⟩

theorem integrable_kernel_mul {g : ℝ → ℝ → ℝ} (hg : Continuous (Function.uncurry g)) (x : ℝ)
    (e : L2IR 0 1) : Integrable (fun y ↦ g x y * e y) (volI 0 1) := by
  obtain ⟨B, hB⟩ := exists_bound_compact hg x
  refine ((Lp.memLp e).integrable (by norm_num)).bdd_mul (c := B)
    (hg.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with y hy
  exact hB x (Metric.mem_closedBall_self zero_le_one) y hy

/-- **Differentiation under the integral sign** for `∫₀¹ g(x, y) e(y) dy`. -/
theorem hasDerivAt_kInt {g g' : ℝ → ℝ → ℝ} (hg : Continuous (Function.uncurry g))
    (hg' : Continuous (Function.uncurry g')) (hd : ∀ x y, HasDerivAt (fun x ↦ g x y) (g' x y) x)
    (e : L2IR 0 1) (x₀ : ℝ) : HasDerivAt (kInt g e) (kInt g' e x₀) x₀ := by
  obtain ⟨B, hB⟩ := exists_bound_compact hg' x₀
  have hei : Integrable (e : ℝ → ℝ) (volI 0 1) := (Lp.memLp e).integrable (by norm_num)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volI 0 1)
    (F := fun x y ↦ g x y * e y) (F' := fun x y ↦ g' x y * e y)
    (bound := fun y ↦ B * ‖e y‖) (x₀ := x₀) (s := Metric.ball x₀ 1)
    (Metric.ball_mem_nhds x₀ one_pos)
    (Eventually.of_forall fun x ↦ (integrable_kernel_mul hg x e).aestronglyMeasurable)
    (integrable_kernel_mul hg x₀ e) (integrable_kernel_mul hg' x₀ e).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with y hy x hx
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hB x (Metric.ball_subset_closedBall hx) y hy)
        (norm_nonneg _))
    (hei.norm.const_mul B)
    (ae_of_all _ fun y x _ ↦ (hd x y).mul_const (e y))
  exact key.2

/-! ### The kernels -/

/-- `k₀(x, y) = 2cos(2πxy)` (S9's `K`). -/
def k0 (x y : ℝ) : ℝ := 2 * Real.cos (2 * π * x * y)
/-- `k₁ = ∂ₓ k₀`. -/
def k1 (x y : ℝ) : ℝ := -(4 * π * y * Real.sin (2 * π * x * y))
/-- `k₂ = ∂ₓ k₁`. -/
def k2 (x y : ℝ) : ℝ := -(8 * π ^ 2 * y ^ 2 * Real.cos (2 * π * x * y))
/-- `k₃ = ∂ₓ k₂`. -/
def k3 (x y : ℝ) : ℝ := 16 * π ^ 3 * y ^ 3 * Real.sin (2 * π * x * y)

theorem continuous_k0 : Continuous (Function.uncurry k0) := by
  unfold k0; fun_prop
theorem continuous_k1 : Continuous (Function.uncurry k1) := by
  unfold k1; fun_prop
theorem continuous_k2 : Continuous (Function.uncurry k2) := by
  unfold k2; fun_prop
theorem continuous_k3 : Continuous (Function.uncurry k3) := by
  unfold k3; fun_prop

theorem hasDerivAt_arg (x y : ℝ) : HasDerivAt (fun x ↦ 2 * π * x * y) (2 * π * y) x := by
  have := ((hasDerivAt_id x).const_mul (2 * π)).mul_const y
  simpa using this

theorem hasDerivAt_k0 (x y : ℝ) : HasDerivAt (fun x ↦ k0 x y) (k1 x y) x := by
  have := ((hasDerivAt_arg x y).cos).const_mul 2
  unfold k0 k1
  exact this.congr_deriv (by ring)

theorem hasDerivAt_k1 (x y : ℝ) : HasDerivAt (fun x ↦ k1 x y) (k2 x y) x := by
  have := (((hasDerivAt_arg x y).sin).const_mul (4 * π * y)).neg
  unfold k1 k2
  refine (this.congr_deriv (by ring)).congr_of_eventuallyEq
    (Eventually.of_forall fun s ↦ ?_)
  simp only [Pi.neg_apply]

theorem hasDerivAt_k2 (x y : ℝ) : HasDerivAt (fun x ↦ k2 x y) (k3 x y) x := by
  have := (((hasDerivAt_arg x y).cos).const_mul (8 * π ^ 2 * y ^ 2)).neg
  unfold k2 k3
  refine (this.congr_deriv (by ring)).congr_of_eventuallyEq
    (Eventually.of_forall fun s ↦ ?_)
  simp only [Pi.neg_apply]

theorem abs_k0_le (x : ℝ) {y : ℝ} (_hy : y ∈ Icc (0 : ℝ) 1) : |k0 x y| ≤ 2 := by
  unfold k0
  rw [abs_mul, abs_two]
  nlinarith [Real.abs_cos_le_one (2 * π * x * y)]

theorem abs_k1_le (x : ℝ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : |k1 x y| ≤ 4 * π := by
  unfold k1
  rw [abs_neg, abs_mul, abs_of_nonneg (by have := Real.pi_pos; nlinarith [hy.1] : 0 ≤ 4 * π * y)]
  have h1 := Real.abs_sin_le_one (2 * π * x * y)
  have h2 : 4 * π * y ≤ 4 * π := by nlinarith [Real.pi_pos, hy.2]
  have h3 : 0 ≤ 4 * π * y := by nlinarith [Real.pi_pos, hy.1]
  nlinarith [abs_nonneg (Real.sin (2 * π * x * y))]

theorem abs_k2_le (x : ℝ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : |k2 x y| ≤ 8 * π ^ 2 := by
  unfold k2
  have h0 : 0 ≤ 8 * π ^ 2 * y ^ 2 := by positivity
  rw [abs_neg, abs_mul, abs_of_nonneg h0]
  have h1 := Real.abs_cos_le_one (2 * π * x * y)
  have hy2 : y ^ 2 ≤ 1 := by nlinarith [hy.1, hy.2]
  have h2 : 8 * π ^ 2 * y ^ 2 ≤ 8 * π ^ 2 := by nlinarith [sq_nonneg π]
  nlinarith [abs_nonneg (Real.cos (2 * π * x * y))]

/-! ### `φ_i` and its derivatives -/

variable {ι : Type*} (bR : EigenBasis CopR ι)

theorem cosTransR_eq_kInt (e : L2IR 0 1) : cosTransR e = kInt k0 e := by
  funext w; rfl

theorem phiR_eq (i : ι) : phiR bR i = fun x ↦ (bR.μ i)⁻¹ * kInt k0 (bR.e i) x := by
  funext x; rw [phiR, cosTransR_eq_kInt]

/-- `φ_i' = μ_i⁻¹ F₁^i`. -/
theorem hasDerivAt_phiR (i : ι) (x : ℝ) :
    HasDerivAt (phiR bR i) ((bR.μ i)⁻¹ * kInt k1 (bR.e i) x) x := by
  rw [phiR_eq]
  exact (hasDerivAt_kInt continuous_k0 continuous_k1 hasDerivAt_k0 (bR.e i) x).const_mul _

/-- `φ_i'' = μ_i⁻¹ F₂^i`. -/
theorem hasDerivAt_dphiR (i : ι) (x : ℝ) :
    HasDerivAt (fun x ↦ (bR.μ i)⁻¹ * kInt k1 (bR.e i) x) ((bR.μ i)⁻¹ * kInt k2 (bR.e i) x) x :=
  (hasDerivAt_kInt continuous_k1 continuous_k2 hasDerivAt_k1 (bR.e i) x).const_mul _

theorem continuous_kInt_k2 (e : L2IR 0 1) : Continuous (kInt k2 e) :=
  continuous_iff_continuousAt.2 fun x ↦
    (hasDerivAt_kInt continuous_k2 continuous_k3 hasDerivAt_k2 e x).continuousAt

theorem continuous_kInt_k1 (e : L2IR 0 1) : Continuous (kInt k1 e) :=
  continuous_iff_continuousAt.2 fun x ↦
    (hasDerivAt_kInt continuous_k1 continuous_k2 hasDerivAt_k1 e x).continuousAt

theorem continuous_kInt_k0 (e : L2IR 0 1) : Continuous (kInt k0 e) :=
  continuous_iff_continuousAt.2 fun x ↦
    (hasDerivAt_kInt continuous_k0 continuous_k1 hasDerivAt_k0 e x).continuousAt

theorem deriv_phiR (i : ι) (x : ℝ) : deriv (phiR bR i) x = (bR.μ i)⁻¹ * kInt k1 (bR.e i) x :=
  (hasDerivAt_phiR bR i x).deriv

/-! ### Pointwise Bessel -/

theorem continuous_section {g : ℝ → ℝ → ℝ} (hg : Continuous (Function.uncurry g)) (x : ℝ) :
    Continuous (fun y ↦ g x y) :=
  hg.comp (Continuous.prodMk continuous_const continuous_id)

/-- `F(x) = ⟪e, g(x, ·)⟫`. -/
theorem kInt_eq_inner {g : ℝ → ℝ → ℝ} (hg : Continuous (Function.uncurry g)) (e : L2IR 0 1)
    (x : ℝ) : kInt g e x = ⟪e, toL2 (continuous_section hg x)⟫_ℝ := by
  rw [inner_L2IR, kInt]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2 (continuous_section hg x)] with y hy
  rw [hy, mul_comm]

theorem norm_toL2_sq_le {ψ : ℝ → ℝ} (hψ : Continuous ψ) {B : ℝ}
    (hB : ∀ y ∈ Icc (0 : ℝ) 1, |ψ y| ≤ B) : ‖toL2 hψ‖ ^ 2 ≤ B ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_L2IR]
  have h1 : ∫ x in Icc (0 : ℝ) 1, (toL2 hψ : ℝ → ℝ) x * (toL2 hψ : ℝ → ℝ) x =
      ∫ x in Icc (0 : ℝ) 1, ψ x ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_toL2 hψ] with y hy
    rw [hy, sq]
  rw [h1]
  calc ∫ x in Icc (0 : ℝ) 1, ψ x ^ 2 ≤ ∫ _ in Icc (0 : ℝ) 1, B ^ 2 := by
        refine setIntegral_mono_on ((hψ.pow 2).integrableOn_Icc) (integrableOn_const (by simp))
          measurableSet_Icc fun y hy ↦ ?_
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hB y hy) 2
    _ = B ^ 2 := by simp

/-- **Pointwise Bessel**: `Σ_{i ∈ s} F_g^i(x)² ≤ B²` whenever `|g(x, y)| ≤ B` on `[0,1]`. -/
theorem sum_sq_kInt_le {g : ℝ → ℝ → ℝ} (hg : Continuous (Function.uncurry g)) {B : ℝ}
    (hB : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, |g x y| ≤ B) (x : ℝ) (s : Finset ι) :
    ∑ i ∈ s, kInt g (bR.e i) x ^ 2 ≤ B ^ 2 := by
  have h := bR.orthonormal.sum_inner_products_le (toL2 (continuous_section hg x)) (s := s)
  simp only [Real.norm_eq_abs, sq_abs] at h
  simp only [kInt_eq_inner hg]
  exact h.trans (norm_toL2_sq_le _ (hB x))

/-! ### Sup bounds on `[1/3, 3]` via Sobolev -/

/-- The window `[a, b] = [1/3, 3] ⊇ [e^{-T}, e^T]` for `T = log 3`. -/
abbrev aW : ℝ := 1 / 3
abbrev bW : ℝ := 3

theorem aW_lt_bW : aW < bW := by norm_num

/-- The Sobolev constant `C = 1/(b - a) + 2`. -/
def cW : ℝ := 1 / (bW - aW) + 2

theorem cW_pos : 0 < cW := by unfold cW; norm_num

/-- `φ_i'` and `φ_i''`. -/
def dphi (i : ι) (x : ℝ) : ℝ := (bR.μ i)⁻¹ * kInt k1 (bR.e i) x
def ddphi (i : ι) (x : ℝ) : ℝ := (bR.μ i)⁻¹ * kInt k2 (bR.e i) x

theorem continuous_dphi (i : ι) : Continuous (dphi bR i) :=
  continuous_const.mul (continuous_kInt_k1 _)
theorem continuous_ddphi (i : ι) : Continuous (ddphi bR i) :=
  continuous_const.mul (continuous_kInt_k2 _)
theorem continuous_phiR' (i : ι) : Continuous (phiR bR i) := by
  rw [phiR_eq]; exact continuous_const.mul (continuous_kInt_k0 _)

/-- `S_i = ∫_a^b (φ_i² + φ_i'² + φ_i''²)`. -/
def Sint (i : ι) : ℝ :=
  ∫ t in aW..bW, (phiR bR i t ^ 2 + dphi bR i t ^ 2 + ddphi bR i t ^ 2)

/-- `Q_i = √(C S_i)`: the sup bound for `|φ_i|` and `|φ_i'|` on `[1/3, 3]`. -/
def Qb (i : ι) : ℝ := Real.sqrt (cW * Sint bR i)

theorem intervalIntegrable_sq {f : ℝ → ℝ} (hf : Continuous f) :
    IntervalIntegrable (fun t ↦ f t ^ 2) volume aW bW := (hf.pow 2).intervalIntegrable _ _

theorem Sint_nonneg (i : ι) : 0 ≤ Sint bR i :=
  intervalIntegral.integral_nonneg aW_lt_bW.le fun _ _ ↦ by positivity

theorem continuous_Sint_integrand (i : ι) :
    Continuous fun t ↦ phiR bR i t ^ 2 + dphi bR i t ^ 2 + ddphi bR i t ^ 2 :=
  (((continuous_phiR' bR i).pow 2).add ((continuous_dphi bR i).pow 2)).add
    ((continuous_ddphi bR i).pow 2)

theorem le_Sint {f : ℝ → ℝ} (i : ι) (hf : Continuous fun t ↦ f t)
    (h : ∀ t, f t ≤ phiR bR i t ^ 2 + dphi bR i t ^ 2 + ddphi bR i t ^ 2) :
    ∫ t in aW..bW, f t ≤ Sint bR i :=
  intervalIntegral.integral_mono_on aW_lt_bW.le (hf.intervalIntegrable _ _)
    ((continuous_Sint_integrand bR i).intervalIntegrable _ _) fun t _ ↦ h t

theorem sobolev_to_Q (i : ι) {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Continuous f')
    (h1 : ∫ t in aW..bW, f t ^ 2 ≤ Sint bR i)
    (h2 : ∫ t in aW..bW, (f t ^ 2 + f' t ^ 2) ≤ Sint bR i) {x : ℝ} (hx : x ∈ Icc aW bW) :
    |f x| ≤ Qb bR i := by
  apply Real.abs_le_sqrt
  have hs := sq_le_sobolev aW_lt_bW hf hf' hx
  have hba : (0 : ℝ) < bW - aW := by norm_num
  have : (∫ t in aW..bW, f t ^ 2) / (bW - aW) ≤ Sint bR i / (bW - aW) :=
    div_le_div_of_nonneg_right h1 hba.le
  unfold cW
  rw [add_mul, div_mul_eq_mul_div, one_mul]
  linarith

/-- **`|φ_i(x)| ≤ Q_i` on `[1/3, 3]`.** -/
theorem abs_phiR_le_Q (i : ι) {x : ℝ} (hx : x ∈ Icc aW bW) : |phiR bR i x| ≤ Qb bR i := by
  have hc := continuous_phiR' bR i
  have hd := continuous_dphi bR i
  have hdd := continuous_ddphi bR i
  have h1 : ∫ t in aW..bW, phiR bR i t ^ 2 ≤ Sint bR i := by
    refine le_Sint bR i (hc.pow 2) fun t ↦ ?_
    nlinarith [sq_nonneg (dphi bR i t), sq_nonneg (ddphi bR i t)]
  have h2 : ∫ t in aW..bW, (phiR bR i t ^ 2 + dphi bR i t ^ 2) ≤ Sint bR i := by
    refine le_Sint bR i ((hc.pow 2).add (hd.pow 2)) fun t ↦ ?_
    nlinarith [sq_nonneg (ddphi bR i t)]
  exact sobolev_to_Q bR i (f' := dphi bR i) (fun x ↦ hasDerivAt_phiR bR i x) hd h1 h2 hx

/-- **`|φ_i'(x)| ≤ Q_i` on `[1/3, 3]`.** -/
theorem abs_deriv_phiR_le_Q (i : ι) {x : ℝ} (hx : x ∈ Icc aW bW) :
    |deriv (phiR bR i) x| ≤ Qb bR i := by
  have hc := continuous_phiR' bR i
  have hd := continuous_dphi bR i
  have hdd := continuous_ddphi bR i
  have h1 : ∫ t in aW..bW, dphi bR i t ^ 2 ≤ Sint bR i := by
    refine le_Sint bR i (hd.pow 2) fun t ↦ ?_
    nlinarith [sq_nonneg (phiR bR i t), sq_nonneg (ddphi bR i t)]
  have h2 : ∫ t in aW..bW, (dphi bR i t ^ 2 + ddphi bR i t ^ 2) ≤ Sint bR i := by
    refine le_Sint bR i ((hd.pow 2).add (hdd.pow 2)) fun t ↦ ?_
    nlinarith [sq_nonneg (phiR bR i t)]
  rw [deriv_phiR]
  exact sobolev_to_Q bR i (f := dphi bR i) (f' := ddphi bR i)
    (fun x ↦ hasDerivAt_dphiR bR i x) hdd h1 h2 hx

/-! ### Summability of `μ_i² S_i` -/

theorem mu_sq_mul_Sint (i : ι) :
    bR.μ i ^ 2 * Sint bR i = ∫ t in aW..bW,
      (kInt k0 (bR.e i) t ^ 2 + kInt k1 (bR.e i) t ^ 2 + kInt k2 (bR.e i) t ^ 2) := by
  have hne := ne_zero_μ bR i
  rw [Sint, ← intervalIntegral.integral_const_mul]
  congr 1; funext t
  rw [phiR_eq]; simp only [dphi, ddphi]
  field_simp

/-- **`Σ_i μ_i² S_i < ∞`**, with `Σ ≤ (b - a)(4 + 16π² + 64π⁴)`. -/
theorem summable_mu_sq_mul_S : Summable fun i ↦ bR.μ i ^ 2 * Sint bR i := by
  refine summable_of_sum_le (c := (bW - aW) * (2 ^ 2 + (4 * π) ^ 2 + (8 * π ^ 2) ^ 2))
    (fun i ↦ mul_nonneg (sq_nonneg _) (Sint_nonneg bR i)) fun s ↦ ?_
  simp only [mu_sq_mul_Sint]
  have hcont : ∀ i : ι, Continuous fun t ↦
      kInt k0 (bR.e i) t ^ 2 + kInt k1 (bR.e i) t ^ 2 + kInt k2 (bR.e i) t ^ 2 := fun i ↦
    (((continuous_kInt_k0 _).pow 2).add ((continuous_kInt_k1 _).pow 2)).add
      ((continuous_kInt_k2 _).pow 2)
  rw [← intervalIntegral.integral_finsetSum (μ := volume) (a := aW) (b := bW) (s := s)
    (f := fun i t ↦ kInt k0 (bR.e i) t ^ 2 + kInt k1 (bR.e i) t ^ 2 + kInt k2 (bR.e i) t ^ 2)
    fun i _ ↦ (hcont i).intervalIntegrable _ _]
  have hb : ∀ t, ∑ i ∈ s, (kInt k0 (bR.e i) t ^ 2 + kInt k1 (bR.e i) t ^ 2 +
      kInt k2 (bR.e i) t ^ 2) ≤ 2 ^ 2 + (4 * π) ^ 2 + (8 * π ^ 2) ^ 2 := by
    intro t
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have h0 := sum_sq_kInt_le bR continuous_k0 (fun x y hy ↦ abs_k0_le x hy) t s
    have h1 := sum_sq_kInt_le bR continuous_k1 (fun x y hy ↦ abs_k1_le x hy) t s
    have h2 := sum_sq_kInt_le bR continuous_k2 (fun x y hy ↦ abs_k2_le x hy) t s
    linarith
  calc ∫ t in aW..bW, ∑ i ∈ s, (kInt k0 (bR.e i) t ^ 2 + kInt k1 (bR.e i) t ^ 2 +
        kInt k2 (bR.e i) t ^ 2)
      ≤ ∫ _ in aW..bW, (2 ^ 2 + (4 * π) ^ 2 + (8 * π ^ 2) ^ 2 : ℝ) :=
        intervalIntegral.integral_mono_on aW_lt_bW.le
          ((continuous_finsetSum _ fun i _ ↦ hcont i).intervalIntegrable _ _)
          intervalIntegrable_const fun t _ ↦ hb t
    _ = (bW - aW) * (2 ^ 2 + (4 * π) ^ 2 + (8 * π ^ 2) ^ 2) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]

theorem Qb_sq (i : ι) : Qb bR i * Qb bR i = cW * Sint bR i :=
  Real.mul_self_sqrt (mul_nonneg cW_pos.le (Sint_nonneg bR i))

end ArchS6
