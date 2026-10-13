/-
  ArchS8_Volterra -- stage S8 of the archimedean conceptual blueprint (2026-10-11), part 1:
  CC Lemmas 5.1 and 5.2 (arXiv:2006.13771, section 5) in the additive variable t = log ρ.

  THE DICTIONARY.  CC's matrix coefficient on L²(ℝ)_ev (normalisation (16)) is, for ρ ≥ 1,
      k(ρ) = ⟨ξ | ϑ(ρ⁻¹) ζ⟩ = ρ^{1/2} ∫_{ρ⁻¹}^{1} ξ(x) ζ(ρ x) dx        (ξ on (0,1], ζ on [1,∞)).
  With ρ = e^t and the unitary images
      aOf ξ s = e^{-s/2} ξ(e^{-s}),     bOf ζ u = e^{u/2} ζ(e^u),
  the substitution x = e^{-s} turns it into a truncated (Volterra) convolution
      kM ξ ζ t = volt (aOf ξ) (bOf ζ) t = ∫_0^t aOf ξ (s) · bOf ζ (t - s) ds      (volt_aOf_bOf).
  ρ∂_ρ is ∂_t, so CC's Q = -(ρ∂_ρ)² + 1/4 is Q₊ = -∂_t² + 1/4.
  The scaling Hamiltonian D_u f (x) = x f'(x) becomes  -(a' + a/2)  on the a-side and  b' - b/2  on
  the b-side (aOf_Du, bOf_Du).

  THEOREMS.
    hasDerivAt_volt        : the Volterra rule (volt F G)' = F t · G 0 + volt F G' t.
    lemma52_additive       : Q₊ (volt a b) = volt ã b̃ + ã(t) b(0) - a(0) b̃(t), ã = -(a'+a/2), b̃ = b'-b/2.
    lemma52                : CC (96) verbatim at ρ = e^t (with the explicit first and second derivatives
                             kM1, kM2 of kM): -kM2 + kM/4 = ρ^{1/2}∫(D_uξ)(x)(D_uζ)(ρx)dx
                             + ρ^{-1/2}(D_uξ)(ρ⁻¹)ζ(1) - ρ^{1/2}ξ(1)(D_uζ)(ρ).
    lemma51_scaling        : the core of CC Lemma 5.1: (-(∂_t)² + 1/4)(e^{t/2} ξ(e^t x)) = -e^{t/2}(Dξ)(e^t x),
                             D = D_u² + D_u, (Dξ)(y) = y² ξ''(y) + 2 y ξ'(y).
  No sorry, no axiom.  conjecture1_proved = False.  Nothing here is RH progress.
-/
import Mathlib

open MeasureTheory Set Filter Topology Asymptotics
open scoped Interval

noncomputable section

namespace ArchS8

/-! ## The Volterra convolution -/

/-- The truncated (Volterra) convolution `∫_0^t F(s) G(t - s) ds`. -/
def volt (F G : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, F s * G (t - s)

theorem volt_comm (F G : ℝ → ℝ) (t : ℝ) : volt F G t = volt G F t := by
  unfold volt
  have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := t)
    (fun s => F s * G (t - s)) t
  simp only [sub_sub_cancel, sub_self, sub_zero] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun s _ => ?_
  ring

@[simp] theorem volt_zero (F G : ℝ → ℝ) : volt F G 0 = 0 := by
  simp [volt]

theorem continuous_volt {F G : ℝ → ℝ} (hF : Continuous F) (hG : Continuous G) :
    Continuous (volt F G) := by
  have hc : Continuous (Function.uncurry fun (t s : ℝ) => F s * G (t - s)) := by
    show Continuous fun p : ℝ × ℝ => F p.2 * G (p.1 - p.2)
    fun_prop
  have h := intervalIntegral.continuous_parametric_primitive_of_continuous (μ := volume) (a₀ := (0 : ℝ)) hc
  exact h.comp (continuous_id.prodMk continuous_id)

theorem abs_volt_le {F G : ℝ → ℝ} {t C : ℝ}
    (h : ∀ s ∈ uIcc 0 t, |F s * G (t - s)| ≤ C) : |volt F G t| ≤ C * |t| := by
  unfold volt
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := C)
    (f := fun s => F s * G (t - s))
    (fun s hs => by simpa [Real.norm_eq_abs] using h s (uIoc_subset_uIcc hs))
  simpa [Real.norm_eq_abs] using this

/-- The Volterra rule: differentiation with a moving upper limit and a moving argument. -/
theorem hasDerivAt_volt {F G G' : ℝ → ℝ} (hF : Continuous F)
    (hG : ∀ x, HasDerivAt G (G' x) x) (hG' : Continuous G') (t₀ : ℝ) :
    HasDerivAt (volt F G) (F t₀ * G 0 + volt F G' t₀) t₀ := by
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun x => (hG x).continuousAt
  have hcont : ∀ y : ℝ, Continuous fun s => F s * G (y - s) := fun y => by fun_prop
  have hcont' : ∀ y : ℝ, Continuous fun s => F s * G' (y - s) := fun y => by fun_prop
  -- (1) fixed upper limit, moving argument
  have hΦ : HasDerivAt (fun y => ∫ s in (0 : ℝ)..t₀, F s * G (y - s)) (volt F G' t₀) t₀ := by
    obtain ⟨C, hC⟩ := (isCompact_uIcc.prod (isCompact_closedBall t₀ 1)).exists_bound_of_continuousOn
      (f := fun p : ℝ × ℝ => F p.1 * G' (p.2 - p.1)) (by fun_prop)
    have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := 0) (b := t₀) (F := fun y s => F s * G (y - s))
      (F' := fun y s => F s * G' (y - s)) (x₀ := t₀) (bound := fun _ => C)
      (Metric.ball_mem_nhds t₀ one_pos)
      (Eventually.of_forall fun y => (hcont y).aestronglyMeasurable)
      ((hcont t₀).intervalIntegrable _ _)
      ((hcont' t₀).aestronglyMeasurable)
      (Eventually.of_forall fun s hs y hy =>
        hC (s, y) ⟨uIoc_subset_uIcc hs, Metric.ball_subset_closedBall hy⟩)
      intervalIntegrable_const
      (Eventually.of_forall fun s _ y _ => by
        have h1 : HasDerivAt (fun y => y - s) 1 y := (hasDerivAt_id y).sub_const s
        have := ((hG (y - s)).comp y h1).const_mul (F s)
        simpa using this)
    exact key.2
  -- (2) moving upper limit, argument frozen at t₀
  have hP : HasDerivAt (fun y => ∫ s in t₀..y, F s * G (t₀ - s)) (F t₀ * G 0) t₀ := by
    have := ((hcont t₀).integral_hasStrictDerivAt t₀ t₀).hasDerivAt
    simpa using this
  -- (3) the cross term is O((y - t₀)²)
  obtain ⟨CF, hCF⟩ := (isCompact_closedBall t₀ 1).exists_bound_of_continuousOn hF.continuousOn
  obtain ⟨CG, hCG⟩ := (isCompact_closedBall (0 : ℝ) 1).exists_bound_of_continuousOn
    hG'.continuousOn
  have hmem : ∀ y ∈ Metric.closedBall t₀ 1, ∀ s ∈ uIcc t₀ y,
      s ∈ Metric.closedBall t₀ 1 ∧ y - s ∈ Metric.closedBall (0 : ℝ) 1 ∧
        t₀ - s ∈ Metric.closedBall (0 : ℝ) 1 := by
    intro y hy s hs
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hy
    simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]
    rcases mem_uIcc.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    · exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hS : HasDerivAt (fun y => ∫ s in t₀..y, F s * (G (y - s) - G (t₀ - s))) 0 t₀ := by
    have hbig : (fun y => ∫ s in t₀..y, F s * (G (y - s) - G (t₀ - s))) =O[𝓝 t₀]
        fun y => ‖y - t₀‖ ^ 2 := by
      refine IsBigO.of_bound (CF * CG) ?_
      filter_upwards [Metric.closedBall_mem_nhds t₀ one_pos] with y hy
      have hb : ∀ s ∈ Ι t₀ y, ‖F s * (G (y - s) - G (t₀ - s))‖ ≤ CF * CG * ‖y - t₀‖ := by
        intro s hs
        obtain ⟨m1, m2, m3⟩ := hmem y hy s (uIoc_subset_uIcc hs)
        have hmv : ‖G (y - s) - G (t₀ - s)‖ ≤ CG * ‖(y - s) - (t₀ - s)‖ :=
          (convex_closedBall (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
            (fun x _ => (hG x).hasDerivWithinAt) (fun x hx => hCG x hx) m3 m2
        have e : (y - s) - (t₀ - s) = y - t₀ := by ring
        rw [e] at hmv
        rw [norm_mul]
        have hCG0 : 0 ≤ CG := (norm_nonneg _).trans (hCG 0 (Metric.mem_closedBall_self zero_le_one))
        calc ‖F s‖ * ‖G (y - s) - G (t₀ - s)‖ ≤ CF * (CG * ‖y - t₀‖) :=
              mul_le_mul (hCF s m1) hmv (norm_nonneg _)
                ((norm_nonneg _).trans (hCF s m1))
          _ = CF * CG * ‖y - t₀‖ := by ring
      have := intervalIntegral.norm_integral_le_of_norm_le_const hb
      calc ‖∫ s in t₀..y, F s * (G (y - s) - G (t₀ - s))‖ ≤ CF * CG * ‖y - t₀‖ * |y - t₀| := this
        _ = CF * CG * ‖‖y - t₀‖ ^ 2‖ := by
          simp only [norm_pow, Real.norm_eq_abs, abs_abs]; ring
    have hlit := hbig.trans_isLittleO (isLittleO_pow_sub_sub t₀ one_lt_two)
    refine hasDerivAt_iff_isLittleO.2 (hlit.congr_left fun y => ?_)
    simp
  -- (4) assemble
  have hsum := (hΦ.add hP).add hS
  refine (hsum.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv (by ring)
  show volt F G y = (∫ s in (0 : ℝ)..t₀, F s * G (y - s)) + (∫ s in t₀..y, F s * G (t₀ - s))
      + ∫ s in t₀..y, F s * (G (y - s) - G (t₀ - s))
  unfold volt
  rw [← intervalIntegral.integral_add_adjacent_intervals ((hcont y).intervalIntegrable 0 t₀)
    ((hcont y).intervalIntegrable t₀ y), add_assoc, ← intervalIntegral.integral_add
      ((hcont t₀).intervalIntegrable _ _) (by apply Continuous.intervalIntegrable; fun_prop)]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  ring

/-- First derivative of `volt a b` when `a` is `C¹` (differentiate on the `a` side). -/
theorem hasDerivAt_volt_left {a a' b : ℝ → ℝ} (ha : ∀ x, HasDerivAt a (a' x) x)
    (ha' : Continuous a') (hb : Continuous b) (t : ℝ) :
    HasDerivAt (volt a b) (a 0 * b t + volt a' b t) t := by
  have h := hasDerivAt_volt hb ha ha' t
  have e1 : volt b a = volt a b := funext fun t => volt_comm b a t
  rw [e1] at h
  refine h.congr_deriv ?_
  rw [volt_comm b a']
  ring

/-- Second derivative: derivative of `a 0 * b t + volt a' b t` when `b` is `C¹`. -/
theorem hasDerivAt_volt_left' {a a' b b' : ℝ → ℝ} (ha' : Continuous a')
    (hb : ∀ x, HasDerivAt b (b' x) x) (hb' : Continuous b') (t : ℝ) :
    HasDerivAt (fun t => a 0 * b t + volt a' b t)
      (a 0 * b' t + (a' t * b 0 + volt a' b' t)) t :=
  ((hb t).const_mul (a 0)).add (hasDerivAt_volt ha' hb hb' t)

/-- The two ways of differentiating `volt a b` agree: this is the integration-by-parts identity
that produces CC's boundary terms. -/
theorem volt_deriv_swap {a a' b b' : ℝ → ℝ} (ha : ∀ x, HasDerivAt a (a' x) x)
    (ha' : Continuous a') (hb : ∀ x, HasDerivAt b (b' x) x) (hb' : Continuous b') (t : ℝ) :
    volt a' b t - volt a b' t = a t * b 0 - a 0 * b t := by
  have hac : Continuous a := continuous_iff_continuousAt.2 fun x => (ha x).continuousAt
  have hbc : Continuous b := continuous_iff_continuousAt.2 fun x => (hb x).continuousAt
  have h1 := hasDerivAt_volt hac hb hb' t
  have h2 := hasDerivAt_volt_left ha ha' hbc t
  have := h1.unique h2
  linarith

/-- **CC Lemma 5.2, additive form.**  For `C¹` functions `a, b` on ℝ, the second derivative of the
truncated convolution `k = volt a b` is `a 0 * b' t + a' t * b 0 + volt a' b' t`
(`hasDerivAt_volt_left`, `hasDerivAt_volt_left'`), and `Q₊ k = -k'' + k/4` is

    volt ã b̃ t + ã t * b 0 - a 0 * b̃ t,     ã = -(a' + a/2),  b̃ = b' - b/2,

the images of `D_u ξ` and `D_u ζ`. -/
theorem lemma52_additive {a a' b b' : ℝ → ℝ} (ha : ∀ x, HasDerivAt a (a' x) x)
    (ha' : Continuous a') (hb : ∀ x, HasDerivAt b (b' x) x) (hb' : Continuous b') (t : ℝ) :
    -(a 0 * b' t + (a' t * b 0 + volt a' b' t)) + volt a b t / 4
      = volt (fun s => -(a' s + a s / 2)) (fun u => b' u - b u / 2) t
        + (-(a' t + a t / 2)) * b 0 - a 0 * (b' t - b t / 2) := by
  have hac : Continuous a := continuous_iff_continuousAt.2 fun x => (ha x).continuousAt
  have hbc : Continuous b := continuous_iff_continuousAt.2 fun x => (hb x).continuousAt
  have hsw := volt_deriv_swap ha ha' hb hb' t
  have hexp : volt (fun s => -(a' s + a s / 2)) (fun u => b' u - b u / 2) t
      = -volt a' b' t + (1 / 2) * volt a' b t - (1 / 2) * volt a b' t + (1 / 4) * volt a b t := by
    unfold volt
    have c1 : IntervalIntegrable (fun s => a' s * b' (t - s)) volume 0 t := by
      apply Continuous.intervalIntegrable; fun_prop
    have c2 : IntervalIntegrable (fun s => a' s * b (t - s)) volume 0 t := by
      apply Continuous.intervalIntegrable; fun_prop
    have c3 : IntervalIntegrable (fun s => a s * b' (t - s)) volume 0 t := by
      apply Continuous.intervalIntegrable; fun_prop
    have c4 : IntervalIntegrable (fun s => a s * b (t - s)) volume 0 t := by
      apply Continuous.intervalIntegrable; fun_prop
    have hc : ∫ s in (0 : ℝ)..t, (fun s => -(a' s + a s / 2)) s * (fun u => b' u - b u / 2) (t - s)
        = ∫ s in (0 : ℝ)..t, ((-(a' s * b' (t - s)) + 1 / 2 * (a' s * b (t - s)))
            - 1 / 2 * (a s * b' (t - s))) + 1 / 4 * (a s * b (t - s)) :=
      intervalIntegral.integral_congr fun s _ => by simp only; ring
    rw [hc, intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_add, intervalIntegral.integral_neg,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    all_goals first
      | exact c1.neg
      | exact c2.const_mul _
      | exact c3.const_mul _
      | exact c4.const_mul _
      | (apply Continuous.intervalIntegrable; fun_prop)
  rw [hexp]
  linear_combination (-1 / 2 : ℝ) * hsw

/-! ## Multiplicative form: CC's matrix coefficients -/

/-- The a-side image `s ↦ e^{-s/2} ξ(e^{-s})` (ξ restricted to (0,1] corresponds to s ≥ 0). -/
def aOf (ξ : ℝ → ℝ) (s : ℝ) : ℝ := Real.exp (-s / 2) * ξ (Real.exp (-s))

/-- The b-side image `u ↦ e^{u/2} ζ(e^u)` (ζ restricted to [1,∞) corresponds to u ≥ 0). -/
def bOf (ζ : ℝ → ℝ) (u : ℝ) : ℝ := Real.exp (u / 2) * ζ (Real.exp u)

/-- Derivative of `aOf ξ`. -/
def aOf' (ξ : ℝ → ℝ) (s : ℝ) : ℝ :=
  -(Real.exp (-s / 2) * (ξ (Real.exp (-s)) / 2 + Real.exp (-s) * deriv ξ (Real.exp (-s))))

/-- Derivative of `bOf ζ`. -/
def bOf' (ζ : ℝ → ℝ) (u : ℝ) : ℝ :=
  Real.exp (u / 2) * (ζ (Real.exp u) / 2 + Real.exp u * deriv ζ (Real.exp u))

/-- CC's scaling Hamiltonian `D_u f (x) = x f'(x)`. -/
def Du (f : ℝ → ℝ) (x : ℝ) : ℝ := x * deriv f x

/-- CC's matrix coefficient `ρ^{1/2} ∫_{ρ⁻¹}^1 ξ(x) ζ(ρ x) dx` at `ρ = e^t`
(this is `⟨ξ | ϑ(ρ⁻¹) ζ⟩` for ξ supported in [0,1], ζ in [1,∞), with the normalisation (16)). -/
def kM (ξ ζ : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (t / 2) * ∫ x in (Real.exp (-t))..1, ξ x * ζ (Real.exp t * x)

/-- The first derivative of `kM ξ ζ` (in `t = log ρ`, i.e. `ρ ∂_ρ`). -/
def kM1 (ξ ζ : ℝ → ℝ) (t : ℝ) : ℝ := aOf ξ 0 * bOf ζ t + volt (aOf' ξ) (bOf ζ) t

/-- The second derivative of `kM ξ ζ` (i.e. `(ρ ∂_ρ)² k`). -/
def kM2 (ξ ζ : ℝ → ℝ) (t : ℝ) : ℝ :=
  aOf ξ 0 * bOf' ζ t + (aOf' ξ t * bOf ζ 0 + volt (aOf' ξ) (bOf' ζ) t)

@[simp] theorem aOf_zero (ξ : ℝ → ℝ) : aOf ξ 0 = ξ 1 := by simp [aOf]
@[simp] theorem bOf_zero (ζ : ℝ → ℝ) : bOf ζ 0 = ζ 1 := by simp [bOf]

theorem aOf_Du (ξ : ℝ → ℝ) (s : ℝ) : -(aOf' ξ s + aOf ξ s / 2) = aOf (Du ξ) s := by
  unfold aOf' aOf Du; ring

theorem bOf_Du (ζ : ℝ → ℝ) (u : ℝ) : bOf' ζ u - bOf ζ u / 2 = bOf (Du ζ) u := by
  unfold bOf' bOf Du; ring

theorem hasDerivAt_aOf {ξ : ℝ → ℝ} (hξ : Differentiable ℝ ξ) (s : ℝ) :
    HasDerivAt (aOf ξ) (aOf' ξ s) s := by
  have h1 : HasDerivAt (fun s : ℝ => -s / 2) (-1 / 2) s := by
    simpa using ((hasDerivAt_id s).neg.div_const 2)
  have h2 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (Real.exp (-s) * (-1)) s :=
    (hasDerivAt_neg s).exp
  have h3 := (hξ (Real.exp (-s))).hasDerivAt.comp s h2
  exact (h1.exp.mul h3).congr_deriv (by unfold aOf'; simp only [Function.comp_apply]; ring)

theorem hasDerivAt_bOf {ζ : ℝ → ℝ} (hζ : Differentiable ℝ ζ) (u : ℝ) :
    HasDerivAt (bOf ζ) (bOf' ζ u) u := by
  have h1 : HasDerivAt (fun u : ℝ => u / 2) (1 / 2) u := by
    simpa using ((hasDerivAt_id u).div_const 2)
  have h2 : HasDerivAt (fun u : ℝ => Real.exp u) (Real.exp u) u := Real.hasDerivAt_exp u
  have h3 := (hζ (Real.exp u)).hasDerivAt.comp u h2
  exact (h1.exp.mul h3).congr_deriv (by unfold bOf'; simp only [Function.comp_apply]; ring)

theorem continuous_aOf {ξ : ℝ → ℝ} (hξ : Continuous ξ) : Continuous (aOf ξ) := by
  unfold aOf; fun_prop

theorem continuous_bOf {ζ : ℝ → ℝ} (hζ : Continuous ζ) : Continuous (bOf ζ) := by
  unfold bOf; fun_prop

theorem continuous_aOf' {ξ : ℝ → ℝ} (hξ : Continuous ξ) (hξ' : Continuous (deriv ξ)) :
    Continuous (aOf' ξ) := by
  unfold aOf'; fun_prop

theorem continuous_bOf' {ζ : ℝ → ℝ} (hζ : Continuous ζ) (hζ' : Continuous (deriv ζ)) :
    Continuous (bOf' ζ) := by
  unfold bOf'; fun_prop

/-- The substitution `x = e^{-s}`: CC's multiplicative matrix coefficient is the Volterra
convolution of the additive images. -/
theorem volt_aOf_bOf {ξ ζ : ℝ → ℝ} (hξ : Continuous ξ) (hζ : Continuous ζ) (t : ℝ) :
    volt (aOf ξ) (bOf ζ) t = kM ξ ζ t := by
  unfold volt kM aOf bOf
  have hsub := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := t)
    (f := fun s => Real.exp (-s)) (f' := fun s => -Real.exp (-s))
    (g := fun x => ξ x * ζ (Real.exp t * x))
    (fun x _ => by simpa using (hasDerivAt_neg x).exp)
    (by fun_prop) (by fun_prop)
  simp only [Function.comp_apply, neg_zero, Real.exp_zero] at hsub
  calc ∫ s in (0 : ℝ)..t, Real.exp (-s / 2) * ξ (Real.exp (-s))
          * (Real.exp ((t - s) / 2) * ζ (Real.exp (t - s)))
        = ∫ s in (0 : ℝ)..t, Real.exp (t / 2)
            * -(ξ (Real.exp (-s)) * ζ (Real.exp t * Real.exp (-s)) * -Real.exp (-s)) := by
          refine intervalIntegral.integral_congr fun s _ => ?_
          have e1 : Real.exp (t - s) = Real.exp t * Real.exp (-s) := by
            rw [← Real.exp_add]; ring_nf
          have e2 : Real.exp (-s / 2) * Real.exp ((t - s) / 2) = Real.exp (t / 2) * Real.exp (-s) := by
            rw [← Real.exp_add, ← Real.exp_add]; ring_nf
          rw [e1]
          linear_combination (ξ (Real.exp (-s)) * ζ (Real.exp t * Real.exp (-s))) * e2
      _ = Real.exp (t / 2)
            * -(∫ s in (0 : ℝ)..t, ξ (Real.exp (-s)) * ζ (Real.exp t * Real.exp (-s))
                * -Real.exp (-s)) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_neg]
      _ = Real.exp (t / 2) * ∫ x in (Real.exp (-t))..1, ξ x * ζ (Real.exp t * x) := by
          rw [hsub, ← intervalIntegral.integral_symm]

/-- **CC Lemma 5.2 ((96)), at ρ = e^t.**  For `C¹` real functions ξ, ζ, the matrix coefficient
`k = kM ξ ζ` has `ρ∂_ρ k = kM1`, `(ρ∂_ρ)² k = kM2`, and

  (Qk)(ρ) = ρ^{1/2} ∫_{ρ⁻¹}^1 (D_uξ)(x)(D_uζ)(ρx) dx + ρ^{-1/2}(D_uξ)(ρ⁻¹) ζ(1) - ρ^{1/2} ξ(1)(D_uζ)(ρ).

The identity holds for every real t (for t < 0 the integral is oriented). -/
theorem lemma52 {ξ ζ : ℝ → ℝ} (hξ : ContDiff ℝ 1 ξ) (hζ : ContDiff ℝ 1 ζ) (t : ℝ) :
    HasDerivAt (kM ξ ζ) (kM1 ξ ζ t) t ∧ HasDerivAt (kM1 ξ ζ) (kM2 ξ ζ t) t ∧
      -(kM2 ξ ζ t) + kM ξ ζ t / 4
        = kM (Du ξ) (Du ζ) t + Real.exp (-t / 2) * Du ξ (Real.exp (-t)) * ζ 1
          - Real.exp (t / 2) * ξ 1 * Du ζ (Real.exp t) := by
  have dξ : Differentiable ℝ ξ := hξ.differentiable (by norm_num)
  have dζ : Differentiable ℝ ζ := hζ.differentiable (by norm_num)
  have cξ : Continuous ξ := hξ.continuous
  have cζ : Continuous ζ := hζ.continuous
  have cξ' : Continuous (deriv ξ) := hξ.continuous_deriv le_rfl
  have cζ' : Continuous (deriv ζ) := hζ.continuous_deriv le_rfl
  have ha := hasDerivAt_aOf dξ
  have hb := hasDerivAt_bOf dζ
  have ha' := continuous_aOf' cξ cξ'
  have hb' := continuous_bOf' cζ cζ'
  have hkM : kM ξ ζ = volt (aOf ξ) (bOf ζ) := funext fun t => (volt_aOf_bOf cξ cζ t).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [hkM]; exact hasDerivAt_volt_left ha ha' (continuous_bOf cζ) t
  · exact hasDerivAt_volt_left' ha' hb hb' t
  · have h := lemma52_additive ha ha' hb hb' t
    have eA : (fun s => -(aOf' ξ s + aOf ξ s / 2)) = aOf (Du ξ) := funext (aOf_Du ξ)
    have eB : (fun u => bOf' ζ u - bOf ζ u / 2) = bOf (Du ζ) := funext (bOf_Du ζ)
    have cDξ : Continuous (Du ξ) := by unfold Du; fun_prop
    have cDζ : Continuous (Du ζ) := by unfold Du; fun_prop
    rw [eA, eB, volt_aOf_bOf cDξ cDζ, aOf_Du, bOf_Du] at h
    unfold kM2
    rw [hkM, h]
    simp only [aOf, bOf, neg_zero, zero_div, Real.exp_zero, one_mul]
    ring

/-! ## CC Lemma 5.1: the scaling computation -/

/-- CC's operator `D = D_u² + D_u`, `(D ξ)(y) = y² ξ''(y) + 2 y ξ'(y)`, from explicit derivatives. -/
def Dop (ξ1 ξ2 : ℝ → ℝ) (y : ℝ) : ℝ := y ^ 2 * ξ2 y + 2 * y * ξ1 y

/-- **Core of CC Lemma 5.1.**  For fixed `x`, the function `t ↦ e^{t/2} ξ(e^t x)`
(i.e. `ρ ↦ ρ^{1/2} ξ(ρ x)` at `ρ = e^t`) satisfies

    (-(∂_t)² + 1/4)(e^{t/2} ξ(e^t x)) = -e^{t/2} (D ξ)(e^t x),

so `Q` acting on a matrix coefficient of smooth vectors is `-⟨η | ϑ(ρ⁻¹) D ξ⟩`. -/
theorem lemma51_scaling {ξ ξ1 ξ2 : ℝ → ℝ} (h1 : ∀ y, HasDerivAt ξ (ξ1 y) y)
    (h2 : ∀ y, HasDerivAt ξ1 (ξ2 y) y) (x t : ℝ) :
    HasDerivAt (fun t => Real.exp (t / 2) * ξ (Real.exp t * x))
        (Real.exp (t / 2) * (ξ (Real.exp t * x) / 2 + Real.exp t * x * ξ1 (Real.exp t * x))) t ∧
      HasDerivAt
        (fun t => Real.exp (t / 2) * (ξ (Real.exp t * x) / 2 + Real.exp t * x * ξ1 (Real.exp t * x)))
        (Real.exp (t / 2) * (ξ (Real.exp t * x) / 4 + 2 * (Real.exp t * x) * ξ1 (Real.exp t * x)
          + (Real.exp t * x) ^ 2 * ξ2 (Real.exp t * x))) t ∧
      -(Real.exp (t / 2) * (ξ (Real.exp t * x) / 4 + 2 * (Real.exp t * x) * ξ1 (Real.exp t * x)
          + (Real.exp t * x) ^ 2 * ξ2 (Real.exp t * x)))
        + Real.exp (t / 2) * ξ (Real.exp t * x) / 4
        = -(Real.exp (t / 2) * Dop ξ1 ξ2 (Real.exp t * x)) := by
  have hh : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) t := by
    simpa using ((hasDerivAt_id t).div_const 2)
  have he : HasDerivAt (fun t : ℝ => Real.exp (t / 2)) (Real.exp (t / 2) * (1 / 2)) t := hh.exp
  have hy : HasDerivAt (fun t : ℝ => Real.exp t * x) (Real.exp t * x) t :=
    (Real.hasDerivAt_exp t).mul_const x
  have hξy := (h1 (Real.exp t * x)).comp t hy
  have hξ1y := (h2 (Real.exp t * x)).comp t hy
  refine ⟨(he.mul hξy).congr_deriv (by simp only [Function.comp_apply]; ring), ?_,
    by unfold Dop; ring⟩
  have hin := ((hξy.div_const 2).add (hy.mul hξ1y))
  exact (he.mul hin).congr_deriv (by simp only [Function.comp_apply, Pi.add_apply, Pi.mul_apply]; ring)

end ArchS8
