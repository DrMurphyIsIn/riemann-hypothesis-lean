/-
  ArchS8_Kernel -- stage S8 of the archimedean conceptual blueprint (2026-10-11), part 3:
  the functional E∘Q and the operator K_I (Connes-Consani arXiv:2006.13771, (101)-(104),
  Proposition 5.5, Remark 5.6), over an abstract `ProlateData`.

  CONVENTIONS.  Additive variable x = log ρ.  CC's E₊(f) = ∫ f(x) ε(exp|x|) dx (101) is
  `Eplus D f = ∫ f v · eps |v| dv`, and Q₊ = -∂² + 1/4.  For η, ξ on an interval I the
  correlation is CC's f = η* ∗ ξ (103):
      corr η ξ v = ∫ conj(η x) ξ(x + v) dx,
  and `corr h h` is the island's `WeilExplicit.autocorr h` (corr_self_eq_autocorr).

  THEOREMS.
    eq102          : CC (102) (Remark 3.7 without distributions): for C² f vanishing for |v| ≥ R,
                     R < T,  E₊(Q₊ f) = -2 ε'(1⁺) f(0) + ∫_0^R (f(x) + f(-x)) (Qε)(e^x) dx.
    lemma51_corr   : CC Lemma 5.1, additive integrated form: Q₊ (η* ∗ ξ) = η* ∗ (Q₊ ξ).
    prop55         : CC Proposition 5.5 as an identity of sesquilinear forms: for η continuous and
                     ξ smooth, both supported in an interval of length ℓ < T,
                       E₊(Q₊(η* ∗ ξ)) = -2 ε'(1⁺) ⟨η|ξ⟩ + ∫∫ conj η(x) ξ(y) (Qε)(e^{|y-x|}) dx dy.
    prop55_KI      : the same as  -2 ε'(1⁺) (⟨η|ξ⟩ - ⟨η|K_I ξ⟩),  K_I with kernel χ(y - x),
                     χ(v) = (Qε)(e^{|v|}) / (2 ε'(1⁺)), when ε'(1⁺) ≠ 0.
    chi_zero       : χ(0) = 0, the diagonal of K_I vanishes (CC Rem 5.6, "Tr K_I = 0").
    prop55_autocorr: the quadratic form for an `IsWeilTest` h, written with `autocorr`.
    corr_lift      : for S2's lift g = h' - h/2:  g ∗ g* = Q₊ (h ∗ h*)   (CC Lemma 3.3 / Prop 3.5).
    prop55_lift    : E₊(g ∗ g*) = ⟨h | N_I h⟩ for pole-free g = h' - h/2 (the S12-facing statement).
  CC's restriction |I| ≤ log 2 becomes ℓ < T, where T is the range of the prolate bounds.
  No sorry, no axiom.  conjecture1_proved = False.  Nothing here is RH progress.
-/
import ArchS8_ProlateData
import E6Bridge5

open MeasureTheory Set Filter Topology Complex
open scoped Interval ComplexConjugate

noncomputable section

namespace ArchS8

/-! ## Correlations -/

/-- CC's `f = η* ∗ ξ`, `f(v) = ∫ conj(η x) ξ(x + v) dx` (103). -/
def corr (η ξ : ℝ → ℂ) (v : ℝ) : ℂ := ∫ x, conj (η x) * ξ (x + v)

theorem corr_self_eq_autocorr (h : ℝ → ℂ) : corr h h = WeilExplicit.autocorr h := by
  funext u
  unfold corr WeilExplicit.autocorr
  rw [← integral_add_right_eq_self (fun v => h v * (starRingEnd ℂ) (h (v - u))) u]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [add_sub_cancel_right]
  ring

theorem integrable_corr_integrand {η ξ : ℝ → ℂ} (hη : Continuous η) (hηc : HasCompactSupport η)
    (hξ : Continuous ξ) {C : ℝ} (hC : ∀ y, ‖ξ y‖ ≤ C) (v : ℝ) :
    Integrable (fun x => conj (η x) * ξ (x + v)) := by
  have hηi : Integrable η := hη.integrable_of_hasCompactSupport hηc
  refine Integrable.mono' (hηi.norm.mul_const C)
    ((continuous_conj.comp hη).mul (hξ.comp (continuous_id.add continuous_const))).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)

/-- Differentiation of a correlation in the shift. -/
theorem hasDerivAt_corr {η ξ ξ' : ℝ → ℂ} (hη : Continuous η) (hηc : HasCompactSupport η)
    (hξ : ∀ y, HasDerivAt ξ (ξ' y) y) (hξb : ∃ C, ∀ y, ‖ξ y‖ ≤ C) (hξ' : Continuous ξ')
    (hξ'b : ∃ C, ∀ y, ‖ξ' y‖ ≤ C) (v : ℝ) :
    HasDerivAt (corr η ξ) (corr η ξ' v) v := by
  obtain ⟨C, hC⟩ := hξ'b
  obtain ⟨C0, hC0⟩ := hξb
  have hξc : Continuous ξ := continuous_iff_continuousAt.2 fun x => (hξ x).continuousAt
  have hηi : Integrable η := hη.integrable_of_hasCompactSupport hηc
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun v x => conj (η x) * ξ (x + v)) (F' := fun v x => conj (η x) * ξ' (x + v))
    (x₀ := v) (bound := fun x => ‖η x‖ * C) Filter.univ_mem
    (Eventually.of_forall fun v =>
      ((continuous_conj.comp hη).mul (hξc.comp (continuous_id.add continuous_const))).aestronglyMeasurable)
    (integrable_corr_integrand hη hηc hξc hC0 v)
    ((continuous_conj.comp hη).mul (hξ'.comp (continuous_id.add continuous_const))).aestronglyMeasurable
    (Eventually.of_forall fun x y _ => by
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _))
    (hηi.norm.mul_const C)
    (Eventually.of_forall fun x y _ => ((hξ (x + y)).comp_const_add x y).const_mul (conj (η x)))
  exact key.2

theorem corr_eq_zero {η ξ : ℝ → ℂ} {α ℓ v : ℝ} (hηs : tsupport η ⊆ Icc α (α + ℓ))
    (hξs : tsupport ξ ⊆ Icc α (α + ℓ)) (hv : ℓ < |v|) : corr η ξ v = 0 := by
  unfold corr
  have : (fun x => conj (η x) * ξ (x + v)) = fun _ => 0 := by
    funext x
    by_cases h1 : η x = 0
    · simp [h1]
    by_cases h2 : ξ (x + v) = 0
    · simp [h2]
    exfalso
    have m1 := hηs (subset_tsupport _ h1)
    have m2 := hξs (subset_tsupport _ h2)
    have : |v| ≤ ℓ := abs_le.2 ⟨by linarith [m1.1, m1.2, m2.1, m2.2],
      by linarith [m1.1, m1.2, m2.1, m2.2]⟩
    linarith
  rw [this, integral_zero]

/-- Smooth test function supported in `Icc α (α + ℓ)`: its first three derivatives, all
continuous, bounded and supported in the same interval. -/
structure SmoothOn (ξ : ℝ → ℂ) (α ℓ : ℝ) : Prop where
  d0 : ∀ y, HasDerivAt ξ (deriv ξ y) y
  d1 : ∀ y, HasDerivAt (deriv ξ) (deriv (deriv ξ) y) y
  d2 : ∀ y, HasDerivAt (deriv (deriv ξ)) (deriv (deriv (deriv ξ)) y) y
  c3 : Continuous (deriv (deriv (deriv ξ)))
  b0 : ∃ C, ∀ y, ‖ξ y‖ ≤ C
  b1 : ∃ C, ∀ y, ‖deriv ξ y‖ ≤ C
  b2 : ∃ C, ∀ y, ‖deriv (deriv ξ) y‖ ≤ C
  b3 : ∃ C, ∀ y, ‖deriv (deriv (deriv ξ)) y‖ ≤ C
  s0 : tsupport ξ ⊆ Icc α (α + ℓ)
  s1 : tsupport (deriv ξ) ⊆ Icc α (α + ℓ)
  s2 : tsupport (deriv (deriv ξ)) ⊆ Icc α (α + ℓ)

theorem smoothOn_of_contDiff {ξ : ℝ → ℂ} {α ℓ : ℝ} (hξ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ξ)
    (hs : tsupport ξ ⊆ Icc α (α + ℓ)) : SmoothOn ξ α ℓ := by
  have e0 := contDiff_infty_iff_deriv.1 hξ
  have e1 := contDiff_infty_iff_deriv.1 e0.2
  have e2 := contDiff_infty_iff_deriv.1 e1.2
  have hc0 : HasCompactSupport ξ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hs
  have hc1 : HasCompactSupport (deriv ξ) := hc0.deriv
  have hc2 : HasCompactSupport (deriv (deriv ξ)) := hc1.deriv
  have hc3 : HasCompactSupport (deriv (deriv (deriv ξ))) := hc2.deriv
  exact
    { d0 := fun y => (e0.1 y).hasDerivAt
      d1 := fun y => (e1.1 y).hasDerivAt
      d2 := fun y => (e2.1 y).hasDerivAt
      c3 := e2.2.continuous
      b0 := hξ.continuous.bounded_above_of_compact_support hc0
      b1 := e0.2.continuous.bounded_above_of_compact_support hc1
      b2 := e1.2.continuous.bounded_above_of_compact_support hc2
      b3 := e2.2.continuous.bounded_above_of_compact_support hc3
      s0 := hs
      s1 := (tsupport_deriv_subset).trans hs
      s2 := (tsupport_deriv_subset).trans ((tsupport_deriv_subset).trans hs) }

/-- The first and second derivatives of `η* ∗ ξ`. -/
theorem deriv_corr {η ξ : ℝ → ℂ} {α ℓ : ℝ} (hη : Continuous η) (hηc : HasCompactSupport η)
    (hξ : SmoothOn ξ α ℓ) :
    (∀ v, HasDerivAt (corr η ξ) (corr η (deriv ξ) v) v) ∧
      (∀ v, HasDerivAt (corr η (deriv ξ)) (corr η (deriv (deriv ξ)) v) v) ∧
      (∀ v, HasDerivAt (corr η (deriv (deriv ξ))) (corr η (deriv (deriv (deriv ξ))) v) v) := by
  have c1 : Continuous (deriv ξ) := continuous_iff_continuousAt.2 fun x => (hξ.d1 x).continuousAt
  have c2 : Continuous (deriv (deriv ξ)) :=
    continuous_iff_continuousAt.2 fun x => (hξ.d2 x).continuousAt
  exact ⟨fun v => hasDerivAt_corr hη hηc hξ.d0 hξ.b0 c1 hξ.b1 v,
    fun v => hasDerivAt_corr hη hηc hξ.d1 hξ.b1 c2 hξ.b2 v,
    fun v => hasDerivAt_corr hη hηc hξ.d2 hξ.b2 hξ.c3 hξ.b3 v⟩

/-- **CC Lemma 5.1, additive integrated form.**  `Q₊` commutes with correlation against a
smooth vector: `-(η* ∗ ξ)'' + (η* ∗ ξ)/4 = η* ∗ (-ξ'' + ξ/4)`.  (CC's `-⟨η|ϑ(ρ⁻¹)Dξ⟩` is the
image of the right side: `D = D_u² + D_u` becomes `∂² - 1/4` under `ξ ↦ e^{u/2} ξ(e^u)`.) -/
theorem lemma51_corr {η ξ : ℝ → ℂ} {α ℓ : ℝ} (hη : Continuous η) (hηc : HasCompactSupport η)
    (hξ : SmoothOn ξ α ℓ) (v : ℝ) :
    -(deriv (deriv (corr η ξ)) v) + corr η ξ v / 4
      = corr η (fun x => -(deriv (deriv ξ) x) + ξ x / 4) v := by
  obtain ⟨h1, h2, -⟩ := deriv_corr hη hηc hξ
  have hd1 : deriv (corr η ξ) = corr η (deriv ξ) := funext fun v => (h1 v).deriv
  rw [hd1, (h2 v).deriv]
  have c0 : Continuous ξ := continuous_iff_continuousAt.2 fun x => (hξ.d0 x).continuousAt
  have c2 : Continuous (deriv (deriv ξ)) :=
    continuous_iff_continuousAt.2 fun x => (hξ.d2 x).continuousAt
  obtain ⟨C0, hC0⟩ := hξ.b0
  obtain ⟨C2, hC2⟩ := hξ.b2
  have i0 := integrable_corr_integrand hη hηc c0 hC0 v
  have i2 := integrable_corr_integrand hη hηc c2 hC2 v
  unfold corr
  rw [← integral_neg, ← integral_div, ← integral_add]
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring
  · exact i2.neg
  · exact i0.div_const 4

/-! ## E₊, χ and K_I -/

namespace ProlateData

variable {ι : Type*} (D : ProlateData ι)

/-- CC (101): `E₊(f) = ∫ f(x) ε(exp|x|) dx`. -/
def Eplus (f : ℝ → ℂ) : ℂ := ∫ v, f v * (D.eps |v| : ℂ)

/-- The kernel of `K_I`: `χ(v) = (Qε)(e^{|v|}) / (2 ε'(1⁺))` (CC (104)). -/
def chi (v : ℝ) : ℝ := D.Qeps |v| / (2 * D.eps1 0)

/-- **CC Remark 5.6**: the diagonal of the kernel of `K_I` vanishes ("Tr K_I = 0"). -/
theorem chi_zero : D.chi 0 = 0 := by simp [chi]

theorem mem_Ioo_of_le {R : ℝ} (hRT : R < D.T) {x : ℝ} (h0 : 0 ≤ x) (hx : x ≤ R) :
    x ∈ Ioo (-D.T) D.T :=
  ⟨by linarith [D.T_pos], by linarith⟩

/-- Remark 3.7 on the half line `[0, R]`: two integrations by parts against `ε`. -/
theorem halfline {f f1 f2 : ℝ → ℂ} {R : ℝ} (hR0 : 0 ≤ R) (hRT : R < D.T)
    (hf : ∀ x, HasDerivAt f (f1 x) x) (hf1 : ∀ x, HasDerivAt f1 (f2 x) x)
    (hf2 : Continuous f2) (hfR : f R = 0) (hf1R : f1 R = 0) :
    ∫ v in (0 : ℝ)..R, (-(f2 v) + f v / 4) * (D.eps v : ℂ)
      = -(D.eps1 0 : ℂ) * f 0 + ∫ v in (0 : ℝ)..R, f v * (D.Qeps v : ℂ) := by
  have hmem : ∀ x ∈ uIcc 0 R, x ∈ Ioo (-D.T) D.T := fun x hx => by
    rw [uIcc_of_le hR0] at hx; exact D.mem_Ioo_of_le hRT hx.1 hx.2
  have he : ∀ x ∈ uIcc 0 R, HasDerivAt (fun v => (D.eps v : ℂ)) (D.eps1 x : ℂ) x :=
    fun x hx => (D.hasDerivAt_eps (hmem x hx)).ofReal_comp
  have he1 : ∀ x ∈ uIcc 0 R, HasDerivAt (fun v => (D.eps1 v : ℂ)) (D.eps2 x : ℂ) x :=
    fun x hx => (D.hasDerivAt_eps1 (hmem x hx)).ofReal_comp
  have hf0 : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hf1c : Continuous f1 := continuous_iff_continuousAt.2 fun x => (hf1 x).continuousAt
  have cE : ContinuousOn (fun v => (D.eps v : ℂ)) (uIcc 0 R) :=
    continuous_ofReal.comp_continuousOn (D.continuousOn_eps.mono hmem)
  have cE1 : ContinuousOn (fun v => (D.eps1 v : ℂ)) (uIcc 0 R) :=
    continuous_ofReal.comp_continuousOn (D.continuousOn_eps1.mono hmem)
  have cE2 : ContinuousOn (fun v => (D.eps2 v : ℂ)) (uIcc 0 R) :=
    continuous_ofReal.comp_continuousOn (D.continuousOn_eps2.mono hmem)
  have I1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := R)
    (u := fun v => (D.eps v : ℂ)) (v := f1) (u' := fun v => (D.eps1 v : ℂ)) (v' := f2)
    he (fun x _ => hf1 x) cE1.intervalIntegrable (hf2.intervalIntegrable _ _)
  have I2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := R)
    (u := fun v => (D.eps1 v : ℂ)) (v := f) (u' := fun v => (D.eps2 v : ℂ)) (v' := f1)
    he1 (fun x _ => hf x) cE2.intervalIntegrable (hf1c.intervalIntegrable _ _)
  simp only [hf1R, hfR, D.eps_zero, ofReal_zero, mul_zero, zero_mul] at I1 I2
  have i_ef : IntervalIntegrable (fun v => (D.eps v : ℂ) * f v) volume 0 R :=
    (cE.mul hf0.continuousOn).intervalIntegrable
  have i_ef2 : IntervalIntegrable (fun v => (D.eps v : ℂ) * f2 v) volume 0 R :=
    (cE.mul hf2.continuousOn).intervalIntegrable
  have i_e2f : IntervalIntegrable (fun v => (D.eps2 v : ℂ) * f v) volume 0 R :=
    (cE2.mul hf0.continuousOn).intervalIntegrable
  have L : ∫ v in (0 : ℝ)..R, (-(f2 v) + f v / 4) * (D.eps v : ℂ)
      = -(∫ v in (0 : ℝ)..R, (D.eps v : ℂ) * f2 v)
        + (1 / 4) * ∫ v in (0 : ℝ)..R, (D.eps v : ℂ) * f v := by
    have hc : ∫ v in (0 : ℝ)..R, (-(f2 v) + f v / 4) * (D.eps v : ℂ)
        = ∫ v in (0 : ℝ)..R, (-((D.eps v : ℂ) * f2 v) + 1 / 4 * ((D.eps v : ℂ) * f v)) :=
      intervalIntegral.integral_congr fun v _ => by ring
    rw [hc, intervalIntegral.integral_add, intervalIntegral.integral_neg,
      intervalIntegral.integral_const_mul]
    · exact i_ef2.neg
    · exact i_ef.const_mul _
  have Rr : ∫ v in (0 : ℝ)..R, f v * (D.Qeps v : ℂ)
      = -(∫ v in (0 : ℝ)..R, (D.eps2 v : ℂ) * f v)
        + (1 / 4) * ∫ v in (0 : ℝ)..R, (D.eps v : ℂ) * f v := by
    have hc : ∫ v in (0 : ℝ)..R, f v * (D.Qeps v : ℂ)
        = ∫ v in (0 : ℝ)..R, (-((D.eps2 v : ℂ) * f v) + 1 / 4 * ((D.eps v : ℂ) * f v)) :=
      intervalIntegral.integral_congr fun v _ => by simp only [Qeps]; push_cast; ring
    rw [hc, intervalIntegral.integral_add, intervalIntegral.integral_neg,
      intervalIntegral.integral_const_mul]
    · exact i_e2f.neg
    · exact i_ef.const_mul _
  rw [L, Rr]
  linear_combination (-1 : ℂ) * I1 + I2

/-- Splitting a full-line integral of a function vanishing for `|v| ≥ R` into the half line. -/
theorem integral_eq_halfline {g : ℝ → ℂ} {R : ℝ} (hR0 : 0 ≤ R)
    (hg : ContinuousOn g (Icc (-R) R)) (hvan : ∀ v, R ≤ |v| → g v = 0) :
    ∫ v, g v = ∫ v in (0 : ℝ)..R, (g v + g (-v)) := by
  have h1 : ∫ v in (-R)..R, g v = ∫ v, g v := by
    rw [intervalIntegral.integral_of_le (by linarith),
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    apply hvan
    simp only [mem_Ioc, not_and_or, not_lt, not_le] at hx
    rcases hx with hx | hx
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; exact hx.le
  have i1 : IntervalIntegrable g volume (-R) 0 :=
    (hg.mono (by rw [uIcc_of_le (by linarith)]; exact Icc_subset_Icc le_rfl hR0)).intervalIntegrable
  have i2 : IntervalIntegrable g volume 0 R :=
    (hg.mono (by rw [uIcc_of_le hR0]; exact Icc_subset_Icc (by linarith) le_rfl)).intervalIntegrable
  have i3 : IntervalIntegrable (fun v => g (-v)) volume 0 R := by
    refine (hg.comp continuous_neg.continuousOn fun x hx => ?_).intervalIntegrable
    rw [uIcc_of_le hR0] at hx
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have h2 := intervalIntegral.integral_comp_neg (a := 0) (b := R) g
  rw [neg_zero] at h2
  rw [← h1, ← intervalIntegral.integral_add_adjacent_intervals i1 i2, ← h2,
    intervalIntegral.integral_add i2 i3, add_comm]

/-- **CC (102)** (Remark 3.7, the jump of `ε'` at `ρ = 1`): for `f ∈ C²` vanishing with `f'`, `f''`
for `|v| ≥ R`, `R < T`,
`E₊(Q₊ f) = -2 ε'(1⁺) f(0) + ∫_0^R (f(x) + f(-x)) (Qε)(e^x) dx`. -/
theorem eq102 {f f1 f2 : ℝ → ℂ} {R : ℝ} (hR0 : 0 ≤ R) (hRT : R < D.T)
    (hf : ∀ x, HasDerivAt f (f1 x) x) (hf1 : ∀ x, HasDerivAt f1 (f2 x) x) (hf2 : Continuous f2)
    (hvan : ∀ v, R ≤ |v| → f v = 0 ∧ f1 v = 0 ∧ f2 v = 0) :
    D.Eplus (fun v => -(f2 v) + f v / 4)
      = -2 * (D.eps1 0 : ℂ) * f 0 + ∫ v in (0 : ℝ)..R, (f v + f (-v)) * (D.Qeps v : ℂ) := by
  have hf0 : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hf1c : Continuous f1 := continuous_iff_continuousAt.2 fun x => (hf1 x).continuousAt
  have cE : ContinuousOn (fun v => (D.eps |v| : ℂ)) (Icc (-R) R) := by
    refine continuous_ofReal.comp_continuousOn
      (D.continuousOn_eps.comp continuous_abs.continuousOn fun x hx => ?_)
    exact D.mem_Ioo_of_le hRT (abs_nonneg x) (abs_le.2 ⟨hx.1, hx.2⟩)
  unfold Eplus
  show ∫ v, (-(f2 v) + f v / 4) * (D.eps |v| : ℂ) = _
  rw [integral_eq_halfline (g := fun v => (-(f2 v) + f v / 4) * (D.eps |v| : ℂ)) hR0
    (((hf2.neg.add (hf0.div_const 4)).continuousOn).mul cE)
    (fun v hv => by simp [(hvan v hv).1, (hvan v hv).2.2])]
  -- the two half lines
  have hR : ∫ v in (0 : ℝ)..R, (-(f2 v) + f v / 4) * (D.eps |v| : ℂ)
      = -(D.eps1 0 : ℂ) * f 0 + ∫ v in (0 : ℝ)..R, f v * (D.Qeps v : ℂ) := by
    rw [← D.halfline hR0 hRT hf hf1 hf2 (hvan R (le_abs_self R)).1 (hvan R (le_abs_self R)).2.1]
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le hR0] at hv
    simp only [abs_of_nonneg hv.1]
  have hfm : ∀ x, HasDerivAt (fun x => f (-x)) (-f1 (-x)) x := fun x =>
    ((hf (-x)).scomp x (hasDerivAt_neg x)).congr_deriv (by simp)
  have hf1m : ∀ x, HasDerivAt (fun x => -f1 (-x)) (f2 (-x)) x := fun x =>
    ((hf1 (-x)).scomp x (hasDerivAt_neg x)).neg.congr_deriv (by simp)
  have hRm := (hvan (-R) (by rw [abs_neg]; exact le_abs_self R))
  have hL : ∫ v in (0 : ℝ)..R, (-(f2 (-v)) + f (-v) / 4) * (D.eps |-v| : ℂ)
      = -(D.eps1 0 : ℂ) * f 0 + ∫ v in (0 : ℝ)..R, f (-v) * (D.Qeps v : ℂ) := by
    have := D.halfline hR0 hRT hfm hf1m (hf2.comp continuous_neg) hRm.1 (by simp [hRm.2.1])
    simp only [neg_zero] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le hR0] at hv
    simp only [abs_neg, abs_of_nonneg hv.1]
  have cQ : ContinuousOn (fun v => (D.Qeps v : ℂ)) (uIcc 0 R) := by
    refine continuous_ofReal.comp_continuousOn (D.continuousOn_Qeps.mono fun x hx => ?_)
    rw [uIcc_of_le hR0] at hx; exact D.mem_Ioo_of_le hRT hx.1 hx.2
  have j1 : IntervalIntegrable (fun v => f v * (D.Qeps v : ℂ)) volume 0 R :=
    (hf0.continuousOn.mul cQ).intervalIntegrable
  have j2 : IntervalIntegrable (fun v => f (-v) * (D.Qeps v : ℂ)) volume 0 R :=
    ((hf0.comp continuous_neg).continuousOn.mul cQ).intervalIntegrable
  have j3 : IntervalIntegrable (fun v => (-(f2 v) + f v / 4) * (D.eps |v| : ℂ)) volume 0 R := by
    refine ((hf2.neg.add (hf0.div_const 4)).continuousOn.mul (cE.mono ?_)).intervalIntegrable
    rw [uIcc_of_le hR0]; exact Icc_subset_Icc (by linarith) le_rfl
  have j4 : IntervalIntegrable (fun v => (-(f2 (-v)) + f (-v) / 4) * (D.eps |-v| : ℂ))
      volume 0 R := by
    refine (((hf2.comp continuous_neg).neg.add ((hf0.comp continuous_neg).div_const 4)).continuousOn.mul
      (cE.comp continuous_neg.continuousOn fun x hx => ?_)).intervalIntegrable
    rw [uIcc_of_le hR0] at hx
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  rw [intervalIntegral.integral_add j3 j4, hR, hL]
  have : ∫ v in (0 : ℝ)..R, (f v + f (-v)) * (D.Qeps v : ℂ)
      = (∫ v in (0 : ℝ)..R, f v * (D.Qeps v : ℂ)) + ∫ v in (0 : ℝ)..R, f (-v) * (D.Qeps v : ℂ) := by
    rw [← intervalIntegral.integral_add j1 j2]
    exact intervalIntegral.integral_congr fun v _ => by ring
  rw [this]
  ring

/-- The clamped kernel `v ↦ (Qε)(min |v| R)`: continuous on ℝ, equal to `(Qε)(|v|)` for `|v| ≤ R`. -/
theorem continuous_Qeps_clamp {R : ℝ} (hR0 : 0 ≤ R) (hRT : R < D.T) :
    Continuous fun v : ℝ => (D.Qeps (min |v| R) : ℂ) := by
  refine continuous_ofReal.comp
    (D.continuousOn_Qeps.comp_continuous (continuous_abs.min continuous_const) fun v => ?_)
  exact D.mem_Ioo_of_le hRT (le_min (abs_nonneg v) hR0) (min_le_right _ _)

end ProlateData

/-- Fubini for the correlation pairing against a continuous kernel. -/
theorem integral_corr_mul {η ξ q : ℝ → ℂ} {α ℓ : ℝ} (hη : Continuous η) (hξ : Continuous ξ)
    (hq : Continuous q) (hηs : tsupport η ⊆ Icc α (α + ℓ)) (hξs : tsupport ξ ⊆ Icc α (α + ℓ)) :
    ∫ v, corr η ξ v * q v = ∫ x, ∫ y, conj (η x) * ξ y * q (y - x) := by
  have hint : Integrable (Function.uncurry fun v x => conj (η x) * ξ (x + v) * q v)
      (volume.prod volume) := by
    have hc : Continuous (Function.uncurry fun v x => conj (η x) * ξ (x + v) * q v) := by
      show Continuous fun p : ℝ × ℝ => conj (η p.2) * ξ (p.2 + p.1) * q p.1
      exact ((continuous_conj.comp (hη.comp continuous_snd)).mul
        (hξ.comp (continuous_snd.add continuous_fst))).mul (hq.comp continuous_fst)
    refine hc.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_Icc.prod (isCompact_Icc (a := α) (b := α + ℓ)))
        (K := Icc (-ℓ) ℓ ×ˢ Icc α (α + ℓ)) fun p hp => ?_)
    obtain ⟨v, x⟩ := p
    show conj (η x) * ξ (x + v) * q v = 0
    by_cases h1 : η x = 0
    · simp [h1]
    by_cases h2 : ξ (x + v) = 0
    · simp [h2]
    exfalso
    have m1 := hηs (subset_tsupport _ h1)
    have m2 := hξs (subset_tsupport _ h2)
    exact hp ⟨⟨by linarith [m1.1, m1.2, m2.1, m2.2], by linarith [m1.1, m1.2, m2.1, m2.2]⟩, m1⟩
  calc ∫ v, corr η ξ v * q v = ∫ v, ∫ x, conj (η x) * ξ (x + v) * q v := by
        refine integral_congr_ae (Eventually.of_forall fun v => ?_)
        simp only [corr]
        rw [integral_mul_const]
    _ = ∫ x, ∫ v, conj (η x) * ξ (x + v) * q v := integral_integral_swap hint
    _ = ∫ x, ∫ y, conj (η x) * ξ y * q (y - x) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        dsimp only
        rw [← integral_add_left_eq_self (fun y => conj (η x) * ξ y * q (y - x)) x]
        refine integral_congr_ae (Eventually.of_forall fun v => ?_)
        simp only [add_sub_cancel_left]

namespace ProlateData

variable {ι : Type*} (D : ProlateData ι)

/-- **CC Proposition 5.5**, as an identity of sesquilinear forms.  Let `η` be continuous and `ξ`
smooth, both supported in an interval `I = [α, α + ℓ]` with `ℓ < T` (CC: `|I| ≤ log 2`).  Then

  E₊(Q₊(η* ∗ ξ)) = -2 ε'(1⁺) ∫ conj η ξ + ∫∫ conj η(x) ξ(y) (Qε)(e^{|y - x|}) dx dy,

i.e. `⟨η | N_I ξ⟩ = -2ε'(1⁺)⟨η|ξ⟩ + ⟨η | (Qε)(e^{|y-x|}) ξ⟩` (CC (103)-(104)). -/
theorem prop55 {η ξ : ℝ → ℂ} {α ℓ : ℝ} (hℓ : ℓ < D.T) (hη : Continuous η)
    (hξ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ξ)
    (hηs : tsupport η ⊆ Icc α (α + ℓ)) (hξs : tsupport ξ ⊆ Icc α (α + ℓ)) :
    D.Eplus (fun v => -(deriv (deriv (corr η ξ)) v) + corr η ξ v / 4)
      = -2 * (D.eps1 0 : ℂ) * (∫ x, conj (η x) * ξ x)
        + ∫ x, ∫ y, conj (η x) * ξ y * (D.Qeps |y - x| : ℂ) := by
  set R : ℝ := (max ℓ 0 + D.T) / 2 with hRdef
  have hR0 : 0 ≤ R := by have := le_max_right ℓ 0; have := D.T_pos; rw [hRdef]; linarith
  have hℓR : ℓ < R := by have := le_max_left ℓ 0; rw [hRdef]; linarith
  have hRT : R < D.T := by
    have : max ℓ 0 < D.T := max_lt hℓ D.T_pos
    rw [hRdef]; linarith
  have hηc : HasCompactSupport η := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hηs
  have hS := smoothOn_of_contDiff hξ hξs
  obtain ⟨h1, h2, h3⟩ := deriv_corr hη hηc hS
  have hd1 : deriv (corr η ξ) = corr η (deriv ξ) := funext fun v => (h1 v).deriv
  have hd2 : deriv (corr η (deriv ξ)) = corr η (deriv (deriv ξ)) := funext fun v => (h2 v).deriv
  rw [hd1, hd2]
  have hc2 : Continuous (corr η (deriv (deriv ξ))) :=
    continuous_iff_continuousAt.2 fun x => (h3 x).continuousAt
  have hvan : ∀ v, R ≤ |v| → corr η ξ v = 0 ∧ corr η (deriv ξ) v = 0 ∧
      corr η (deriv (deriv ξ)) v = 0 := fun v hv => by
    have : ℓ < |v| := by linarith
    exact ⟨corr_eq_zero hηs hS.s0 this, corr_eq_zero hηs hS.s1 this, corr_eq_zero hηs hS.s2 this⟩
  rw [D.eq102 hR0 hRT h1 h2 hc2 hvan]
  have hf0 : corr η ξ 0 = ∫ x, conj (η x) * ξ x := by simp [corr]
  rw [hf0]
  congr 1
  -- the kernel term
  have hcorr : Continuous (corr η ξ) := continuous_iff_continuousAt.2 fun x => (h1 x).continuousAt
  have hq := D.continuous_Qeps_clamp hR0 hRT
  have hξc : Continuous ξ := continuous_iff_continuousAt.2 fun x => (hS.d0 x).continuousAt
  have step1 : ∫ v in (0 : ℝ)..R, (corr η ξ v + corr η ξ (-v)) * (D.Qeps v : ℂ)
      = ∫ v, corr η ξ v * (D.Qeps (min |v| R) : ℂ) := by
    rw [integral_eq_halfline (g := fun v => corr η ξ v * (D.Qeps (min |v| R) : ℂ)) hR0
      (hcorr.mul hq).continuousOn (fun v hv => by simp [(hvan v hv).1])]
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le hR0] at hv
    simp only [abs_neg, abs_of_nonneg hv.1, min_eq_left hv.2]
    ring
  rw [step1, integral_corr_mul hη hξc hq hηs hξs]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  try dsimp only
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  try dsimp only
  by_cases hx : η x = 0
  · simp [hx]
  by_cases hy : ξ y = 0
  · simp [hy]
  have m1 := hηs (subset_tsupport _ hx)
  have m2 := hξs (subset_tsupport _ hy)
  have : |y - x| ≤ R := by
    rw [abs_le]; constructor <;> linarith [m1.1, m1.2, m2.1, m2.2]
  simp only [min_eq_left this]

/-- **CC Proposition 5.5 (ii)**: `N_I = -2 ε'(1⁺)(Id - K_I)` as sesquilinear forms, where `K_I`
has kernel `χ(y - x)`, `χ(v) = (Qε)(e^{|v|}) / (2 ε'(1⁺))`.  Needs `ε'(1⁺) ≠ 0` (it is
`Σ λ²/(1-λ²) ξ_n(1)² ≥ 0`, numerically 22.9965). -/
theorem prop55_KI {η ξ : ℝ → ℂ} {α ℓ : ℝ} (hℓ : ℓ < D.T) (hη : Continuous η)
    (hξ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ξ)
    (hηs : tsupport η ⊆ Icc α (α + ℓ)) (hξs : tsupport ξ ⊆ Icc α (α + ℓ))
    (hε : D.eps1 0 ≠ 0) :
    D.Eplus (fun v => -(deriv (deriv (corr η ξ)) v) + corr η ξ v / 4)
      = -2 * (D.eps1 0 : ℂ) * ((∫ x, conj (η x) * ξ x)
          - ∫ x, ∫ y, conj (η x) * ξ y * (D.chi (y - x) : ℂ)) := by
  rw [D.prop55 hℓ hη hξ hηs hξs]
  have hε' : (D.eps1 0 : ℂ) ≠ 0 := ofReal_ne_zero.2 hε
  have : ∫ x, ∫ y, conj (η x) * ξ y * (D.Qeps |y - x| : ℂ)
      = 2 * (D.eps1 0 : ℂ) * ∫ x, ∫ y, conj (η x) * ξ y * (D.chi (y - x) : ℂ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    try dsimp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    try dsimp only
    simp only [chi]
    push_cast
    field_simp
  rw [this]
  ring

/-- The quadratic form `⟨h | N_I h⟩` for an island test function `h` (`WeilExplicit.IsWeilTest`)
supported in an interval of length `ℓ < T`, written with the island's `autocorr`. -/
theorem prop55_autocorr {h : ℝ → ℂ} (hh : WeilExplicit.IsWeilTest h) {α ℓ : ℝ} (hℓ : ℓ < D.T)
    (hs : tsupport h ⊆ Icc α (α + ℓ)) :
    D.Eplus (fun v => -(deriv (deriv (WeilExplicit.autocorr h)) v) + WeilExplicit.autocorr h v / 4)
      = -2 * (D.eps1 0 : ℂ) * (∫ x, conj (h x) * h x)
        + ∫ x, ∫ y, conj (h x) * h y * (D.Qeps |y - x| : ℂ) := by
  rw [← corr_self_eq_autocorr]
  exact D.prop55 hℓ hh.1.continuous hh.1 hs hs

end ProlateData

/-! ## The bridge to S2: `autocorr (h' - h/2) = Q₊ (autocorr h)` -/

/-- For the S2 lift `g = h' - h/2` (`ArchS2.poleFree_iff_exists_lift`), the autocorrelation of `g`
is `Q₊` applied to that of `h`: `g ∗ g* = -(h ∗ h*)'' + (h ∗ h*)/4` (CC Lemma 3.3 / Prop 3.5:
the pole-free `f = g ∗ g*` are exactly the `Q f₀` with `f₀ = h ∗ h*`).  Two integrations by parts. -/
theorem corr_lift {h : ℝ → ℂ} {α ℓ : ℝ} (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    (hs : tsupport h ⊆ Icc α (α + ℓ)) (v : ℝ) :
    corr (fun u => deriv h u - h u / 2) (fun u => deriv h u - h u / 2) v
      = -corr h (deriv (deriv h)) v + corr h h v / 4 := by
  have hS := smoothOn_of_contDiff hh hs
  have hc0 : HasCompactSupport h := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hs
  have hc1 : HasCompactSupport (deriv h) := hc0.deriv
  have ch : Continuous h := continuous_iff_continuousAt.2 fun x => (hS.d0 x).continuousAt
  have c1 : Continuous (deriv h) := continuous_iff_continuousAt.2 fun x => (hS.d1 x).continuousAt
  have c2 : Continuous (deriv (deriv h)) :=
    continuous_iff_continuousAt.2 fun x => (hS.d2 x).continuousAt
  obtain ⟨C0, hC0⟩ := hS.b0
  obtain ⟨C1, hC1⟩ := hS.b1
  obtain ⟨C2, hC2⟩ := hS.b2
  have iA := integrable_corr_integrand ch hc0 c1 hC1 v
  have iB := integrable_corr_integrand c1 hc1 ch hC0 v
  have iC := integrable_corr_integrand ch hc0 ch hC0 v
  have iD := integrable_corr_integrand c1 hc1 c1 hC1 v
  have iE := integrable_corr_integrand ch hc0 c2 hC2 v
  have hconj : ∀ x, HasDerivAt (fun x => conj (h x)) (conj (deriv h x)) x :=
    fun x => (hS.d0 x).star
  have hconj1 : ∀ x, HasDerivAt (fun x => conj (deriv h x)) (conj (deriv (deriv h) x)) x :=
    fun x => (hS.d1 x).star
  have IBP1 : ∫ x, conj (h x) * deriv h (x + v) = -∫ x, conj (deriv h x) * h (x + v) :=
    integral_mul_deriv_eq_deriv_mul_of_integrable (u := fun x => conj (h x))
      (u' := fun x => conj (deriv h x)) (v := fun x => h (x + v)) (v' := fun x => deriv h (x + v))
      (fun x _ => hconj x) (fun x _ => (hS.d0 (x + v)).comp_add_const x v) iA iB iC
  have IBP2 : ∫ x, conj (deriv h x) * deriv h (x + v)
      = -∫ x, conj (h x) * deriv (deriv h) (x + v) := by
    have := integral_mul_deriv_eq_deriv_mul_of_integrable (u := fun x => conj (h x))
      (u' := fun x => conj (deriv h x)) (v := fun x => deriv h (x + v))
      (v' := fun x => deriv (deriv h) (x + v))
      (fun x _ => hconj x) (fun x _ => (hS.d1 (x + v)).comp_add_const x v) iE iD iA
    rw [this, neg_neg]
  have hexp : corr (fun u => deriv h u - h u / 2) (fun u => deriv h u - h u / 2) v
      = (∫ x, conj (deriv h x) * deriv h (x + v)) - (1 / 2) * (∫ x, conj (deriv h x) * h (x + v))
        - (1 / 2) * (∫ x, conj (h x) * deriv h (x + v)) + (1 / 4) * ∫ x, conj (h x) * h (x + v) := by
    have hc : corr (fun u => deriv h u - h u / 2) (fun u => deriv h u - h u / 2) v
        = ∫ x, (((conj (deriv h x) * deriv h (x + v)) - (1 / 2) * (conj (deriv h x) * h (x + v)))
            - (1 / 2) * (conj (h x) * deriv h (x + v))) + (1 / 4) * (conj (h x) * h (x + v)) := by
      simp only [corr]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [map_sub, map_div₀, map_ofNat]
      ring
    rw [hc, integral_add, integral_sub, integral_sub, integral_const_mul, integral_const_mul,
      integral_const_mul]
    · exact iD
    · exact iB.const_mul _
    · exact iD.sub (iB.const_mul _)
    · exact iA.const_mul _
    · exact (iD.sub (iB.const_mul _)).sub (iA.const_mul _)
    · exact iC.const_mul _
  rw [hexp]
  unfold corr
  linear_combination IBP2 - (1 / 2 : ℂ) * IBP1

namespace ProlateData

variable {ι : Type*} (D : ProlateData ι)

/-- **E∘Q on the pole-free class** (CC Prop 3.5 + Prop 5.5 in the island's variables).  If `h` is
an island test function supported in an interval of length `ℓ < T` and `g = h' - h/2` is its
S2 image (so `g` is pole-free), then

  E₊(g ∗ g*) = -2 ε'(1⁺) ‖h‖² + ∫∫ conj h(x) h(y) (Qε)(e^{|y-x|}) dx dy = ⟨h | N_I h⟩. -/
theorem prop55_lift {h : ℝ → ℂ} (hh : WeilExplicit.IsWeilTest h) {α ℓ : ℝ} (hℓ : ℓ < D.T)
    (hs : tsupport h ⊆ Icc α (α + ℓ)) :
    D.Eplus (WeilExplicit.autocorr fun u => deriv h u - h u / 2)
      = -2 * (D.eps1 0 : ℂ) * (∫ x, conj (h x) * h x)
        + ∫ x, ∫ y, conj (h x) * h y * (D.Qeps |y - x| : ℂ) := by
  have hc0 : HasCompactSupport h := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hs
  obtain ⟨h1, h2, -⟩ := deriv_corr hh.1.continuous hc0 (smoothOn_of_contDiff hh.1 hs)
  have hd1 : deriv (corr h h) = corr h (deriv h) := funext fun v => (h1 v).deriv
  have e : WeilExplicit.autocorr (fun u => deriv h u - h u / 2)
      = fun v => -(deriv (deriv (corr h h)) v) + corr h h v / 4 := by
    rw [← corr_self_eq_autocorr]
    funext v
    rw [corr_lift hh.1 hs v, hd1, (h2 v).deriv]
  rw [e]
  exact D.prop55 hℓ hh.1.continuous hh.1 hs hs

end ProlateData

end ArchS8
