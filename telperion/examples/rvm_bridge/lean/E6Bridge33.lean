/-
  E6Bridge33 -- the archimedean integral in u-space, part 2 (2026-09-23): the Dirichlet form of
  one exponential kernel and its lower bound from the support of g.

  For f = autocorr g, M = f(0) = ||g||_2^2, K_b(u) = e^{-b|u|} (b > 0) and L with
  tsupport g ⊆ Icc (-L) L, the quantity

      E_b := M ∫ K_b - Re ∫ f K_b = (1/2) ∫∫ |g(v) - g(w)|^2 K_b(v - w) dv dw          (Eb_eq_half)

  (∫ f K_b = ∫∫ g(v) conj g(w) K_b(v - w) by Fubini, then symmetrisation) is bounded below by
  splitting the plane into the square Icc^2 and its complement:

      E_b >= (2 e^{-bL} / b) M + e^{-2bL} (2 L M - |∫ g|^2)                            (Eb_ge)

  the first term from the cross regions (for v in the square, ∫_{w outside} K_b(v - w) dw
  = (e^{-b(L-v)} + e^{-b(L+v)})/b >= 2 e^{-bL}/b by AM-GM), the second from K_b >= e^{-2bL} on
  the square and (1/2) ∫∫_{square} |g(v) - g(w)|^2 = 2 L M - |∫ g|^2.

  Consumed by E6Bridge34 (the assembly at L <= 1/10).  No zeros, no RH progress.
  conjecture1_proved = False.
-/
import E6Bridge32

open Zeta23 Complex MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace RvMBridge33
open WeilExplicit RvMBridge11 RvMBridge30 RvMBridge31 RvMBridge32

/-! ## A. One-dimensional exponential integrals and the outer mass. -/

/-- ∫_{w > c} e^{-b w} dw = e^{-b c} / b. -/
lemma integral_Ioi_exp_neg_mul {b : ℝ} (hb : 0 < b) (c : ℝ) :
    ∫ w in Set.Ioi c, Real.exp (-b * w) = Real.exp (-b * c) / b := by
  have h := integral_exp_mul_complex_Ioi (a := (-b : ℂ)) (by simp; linarith) c
  have hc : ∫ w in Set.Ioi c, ((Real.exp (-b * w) : ℝ) : ℂ)
      = ∫ w in Set.Ioi c, cexp ((-b : ℂ) * w) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun w _ => ?_
    rw [Complex.ofReal_exp]
    push_cast
    ring_nf
  rw [integral_complex_ofReal] at hc
  rw [← hc] at h
  have h2 : ((Real.exp (-b * c) / b : ℝ) : ℂ) = -cexp ((-b : ℂ) * c) / (-b : ℂ) := by
    push_cast
    rw [neg_div_neg_eq]
  exact Complex.ofReal_inj.mp (h.trans h2.symm)

/-- ∫_{w < c} e^{b w} dw = e^{b c} / b. -/
lemma integral_Iio_exp_mul {b : ℝ} (hb : 0 < b) (c : ℝ) :
    ∫ w in Set.Iio c, Real.exp (b * w) = Real.exp (b * c) / b := by
  rw [← integral_Iic_eq_integral_Iio]
  have h := integral_comp_neg_Iic c (fun y : ℝ => Real.exp (-b * y))
  have e : (fun x : ℝ => Real.exp (-b * -x)) = fun x => Real.exp (b * x) := by
    funext x
    ring_nf
  rw [e] at h
  rw [h, integral_Ioi_exp_neg_mul hb (-c)]
  ring_nf

/-- ∫ e^{-b|u|} du = 2/b (the Lorentzian pair at ω = 0). -/
lemma integral_expK {b : ℝ} (hb : 0 < b) : ∫ u : ℝ, expK b u = 2 / b := by
  have h := integral_expK_mul_cexp hb 0
  have e : (fun x : ℝ => (expK b x : ℂ) * cexp (I * (0 : ℝ) * x)) = fun x => (expK b x : ℂ) := by
    funext x
    simp
  rw [e, integral_complex_ofReal] at h
  have h2 : lor b 0 = 2 / b := by
    unfold lor
    rw [zero_pow two_ne_zero, add_zero, sq]
    field_simp
  rw [h2] at h
  exact Complex.ofReal_inj.mp h

/-- The outer mass: for v in [-L, L], ∫_{w outside [-L, L]} e^{-b|v-w|} dw >= 2 e^{-bL} / b. -/
theorem integral_compl_Icc_expK_ge {b : ℝ} (hb : 0 < b) {L : ℝ} {v : ℝ}
    (hv : v ∈ Set.Icc (-L) L) :
    2 * Real.exp (-b * L) / b ≤ ∫ w in (Set.Icc (-L) L)ᶜ, expK b (v - w) := by
  have hL : 0 ≤ L := by linarith [hv.1, hv.2]
  have hint : Integrable (fun w : ℝ => expK b (v - w)) := (integrable_expK hb).comp_sub_left v
  -- the two half-lines, with the exponential rewritten
  have hright : ∫ w in Set.Ioi L, expK b (v - w) = Real.exp (b * v) * (Real.exp (-b * L) / b) := by
    rw [← integral_Ioi_exp_neg_mul hb L, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
    unfold expK
    rw [abs_of_nonpos (by linarith [hv.2, Set.mem_Ioi.mp hw]), ← Real.exp_add]
    ring_nf
  have hleft : ∫ w in Set.Iio (-L), expK b (v - w)
      = Real.exp (-b * v) * (Real.exp (-b * L) / b) := by
    rw [show Real.exp (-b * L) = Real.exp (b * (-L)) by ring_nf, ← integral_Iio_exp_mul hb (-L),
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Iio fun w hw => ?_
    unfold expK
    rw [abs_of_nonneg (by linarith [hv.1, Set.mem_Iio.mp hw]), ← Real.exp_add]
    ring_nf
  -- (Icc)ᶜ ⊇ Ioi L ∪ Iio (-L) pointwise on indicators
  have hmono : ∫ w, (Set.Ioi L).indicator (fun w => expK b (v - w)) w
        + (Set.Iio (-L)).indicator (fun w => expK b (v - w)) w
      ≤ ∫ w, ((Set.Icc (-L) L)ᶜ).indicator (fun w => expK b (v - w)) w := by
    refine integral_mono ((hint.indicator measurableSet_Ioi).add (hint.indicator measurableSet_Iio))
      (hint.indicator measurableSet_Icc.compl) fun w => ?_
    by_cases h1 : w ∈ Set.Ioi L
    · have h2 : w ∉ Set.Iio (-L) := by
        rw [Set.mem_Ioi] at h1
        rw [Set.mem_Iio]
        linarith
      have h3 : w ∈ (Set.Icc (-L) L)ᶜ := by
        rw [Set.mem_compl_iff, Set.mem_Icc]
        rw [Set.mem_Ioi] at h1
        intro h
        linarith [h.2]
      rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, Set.indicator_of_mem h3, add_zero]
    · rw [Set.indicator_of_notMem h1, zero_add]
      by_cases h2 : w ∈ Set.Iio (-L)
      · have h3 : w ∈ (Set.Icc (-L) L)ᶜ := by
          rw [Set.mem_compl_iff, Set.mem_Icc]
          rw [Set.mem_Iio] at h2
          intro h
          linarith [h.1]
        rw [Set.indicator_of_mem h2, Set.indicator_of_mem h3]
      · rw [Set.indicator_of_notMem h2]
        exact Set.indicator_nonneg (fun w _ => expK_nonneg b (v - w)) w
  rw [integral_add (hint.indicator measurableSet_Ioi) (hint.indicator measurableSet_Iio),
    integral_indicator measurableSet_Ioi, integral_indicator measurableSet_Iio,
    integral_indicator measurableSet_Icc.compl, hright, hleft] at hmono
  -- AM-GM: e^{bv} + e^{-bv} >= 2
  have hpos := Real.exp_pos (b * v)
  have hinv : Real.exp (-b * v) = (Real.exp (b * v))⁻¹ := by rw [← Real.exp_neg]; ring_nf
  have hamgm : 2 ≤ Real.exp (b * v) + Real.exp (-b * v) := by
    rw [hinv]
    have : Real.exp (b * v) + (Real.exp (b * v))⁻¹ - 2
        = (Real.exp (b * v) - 1) ^ 2 / Real.exp (b * v) := by
      field_simp
      ring
    have h2 : 0 ≤ (Real.exp (b * v) - 1) ^ 2 / Real.exp (b * v) := by positivity
    linarith
  have hE : 0 ≤ Real.exp (-b * L) / b := by positivity
  calc 2 * Real.exp (-b * L) / b = 2 * (Real.exp (-b * L) / b) := by ring
    _ ≤ (Real.exp (b * v) + Real.exp (-b * v)) * (Real.exp (-b * L) / b) :=
        mul_le_mul_of_nonneg_right hamgm hE
    _ = Real.exp (b * v) * (Real.exp (-b * L) / b) + Real.exp (-b * v) * (Real.exp (-b * L) / b) := by
        ring
    _ ≤ _ := hmono

/-! ## B. The plane functions and their integrability. -/

/-- The square [-L, L]^2 as a set of pairs. -/
def sq (L : ℝ) : Set (ℝ × ℝ) := Set.Icc (-L) L ×ˢ Set.Icc (-L) L

lemma measurableSet_sq (L : ℝ) : MeasurableSet (sq L) := measurableSet_Icc.prod measurableSet_Icc

/-- H(v, w) = |g(v)|^2 e^{-b|v-w|}. -/
def Hfun (g : ℝ → ℂ) (b : ℝ) (z : ℝ × ℝ) : ℝ := ‖g z.1‖ ^ 2 * expK b (z.1 - z.2)

/-- H'(v, w) = |g(w)|^2 e^{-b|v-w|}. -/
def Hfun' (g : ℝ → ℂ) (b : ℝ) (z : ℝ × ℝ) : ℝ := ‖g z.2‖ ^ 2 * expK b (z.1 - z.2)

/-- F(v, w) = g(v) conj g(w) e^{-b|v-w|}. -/
def Ffun (g : ℝ → ℂ) (b : ℝ) (z : ℝ × ℝ) : ℂ :=
  g z.1 * (starRingEnd ℂ) (g z.2) * (expK b (z.1 - z.2) : ℂ)

/-- R(v, w) = |g(v) - g(w)|^2 e^{-b|v-w|}. -/
def Rfun (g : ℝ → ℂ) (b : ℝ) (z : ℝ × ℝ) : ℝ := ‖g z.1 - g z.2‖ ^ 2 * expK b (z.1 - z.2)

lemma expK_sub_eq (b : ℝ) (v w : ℝ) : expK b (w - v) = expK b (v - w) := by
  unfold expK
  rw [abs_sub_comm]

lemma continuous_expK_sub (b : ℝ) : Continuous fun z : ℝ × ℝ => expK b (z.1 - z.2) :=
  (continuous_expK b).comp (continuous_fst.sub continuous_snd)

lemma integrable_Hfun {g : ℝ → ℂ} (hg : IsWeilTest g) {b : ℝ} (hb : 0 < b) :
    Integrable (Hfun g b) (volume.prod volume) := by
  have hc : Continuous (Hfun g b) := by
    unfold Hfun
    have := hg.1.continuous
    exact ((this.comp continuous_fst).norm.pow 2).mul (continuous_expK_sub b)
  rw [integrable_prod_iff hc.aestronglyMeasurable]
  constructor
  · filter_upwards with v
    show Integrable (fun w : ℝ => ‖g v‖ ^ 2 * expK b (v - w))
    exact ((integrable_expK hb).comp_sub_left v).const_mul _
  · have e : (fun v : ℝ => ∫ w : ℝ, ‖Hfun g b (v, w)‖) = fun v => ‖g v‖ ^ 2 * (2 / b) := by
      funext v
      unfold Hfun
      simp only
      rw [← integral_expK hb, ← integral_sub_left_eq_self (expK b) volume v, ← integral_const_mul]
      congr 1
      funext w
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (expK_nonneg b _))]
    rw [e]
    exact (integrable_normSq hg).mul_const _

lemma integrable_Hfun' {g : ℝ → ℂ} (hg : IsWeilTest g) {b : ℝ} (hb : 0 < b) :
    Integrable (Hfun' g b) (volume.prod volume) := by
  have h := (integrable_Hfun hg hb).swap
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [Function.comp, Hfun, Hfun', Prod.swap, expK_sub_eq]

lemma continuous_Ffun {g : ℝ → ℂ} (hg : IsWeilTest g) (b : ℝ) : Continuous (Ffun g b) := by
  unfold Ffun
  have := hg.1.continuous
  exact ((this.comp continuous_fst).mul (Complex.continuous_conj.comp (this.comp continuous_snd))).mul
    (Complex.continuous_ofReal.comp (continuous_expK_sub b))

lemma hasCompactSupport_Ffun {g : ℝ → ℂ} {L : ℝ} (hsupp : tsupport g ⊆ Set.Icc (-L) L) (b : ℝ) :
    HasCompactSupport (Ffun g b) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (-L) L ×ˢ Set.Icc (-L) L) (isCompact_Icc.prod isCompact_Icc) fun z hz => ?_
  rw [Function.mem_support] at hz
  unfold Ffun at hz
  have h1 : g z.1 ≠ 0 := fun h => hz (by rw [h]; ring)
  have h2 : g z.2 ≠ 0 := fun h => hz (by rw [h, map_zero]; ring)
  exact Set.mk_mem_prod (hsupp (subset_tsupport g h1)) (hsupp (subset_tsupport g h2))

lemma integrable_Ffun {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) (b : ℝ) : Integrable (Ffun g b) (volume.prod volume) :=
  (continuous_Ffun hg b).integrable_of_hasCompactSupport (hasCompactSupport_Ffun hsupp b)

/-- |g(v) - g(w)|^2 K = H + H' - 2 Re F pointwise. -/
lemma Rfun_eq (g : ℝ → ℂ) (b : ℝ) (z : ℝ × ℝ) :
    Rfun g b z = Hfun g b z + Hfun' g b z - 2 * (Ffun g b z).re := by
  unfold Rfun Hfun Hfun' Ffun
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq]
  rw [show (g z.1 * (starRingEnd ℂ) (g z.2) * (expK b (z.1 - z.2) : ℂ)).re
      = (g z.1 * (starRingEnd ℂ) (g z.2)).re * expK b (z.1 - z.2) by
      rw [mul_comm, Complex.re_ofReal_mul, mul_comm]]
  ring

lemma integrable_Rfun {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) {b : ℝ} (hb : 0 < b) :
    Integrable (Rfun g b) (volume.prod volume) := by
  have h := ((integrable_Hfun hg hb).add (integrable_Hfun' hg hb)).sub
    ((integrable_Ffun hg hsupp b).re.const_mul 2)
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [Rfun_eq]
  rfl

/-! ## C. The identities: ∫ f K = ∫∫ F, M ∫ K = ∫∫ H = ∫∫ H', E_b = (1/2) ∫∫ R. -/

/-- The convolution integrand in the (u, v) variables, for Fubini. -/
lemma integrable_conv_integrand {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) (b : ℝ) :
    Integrable (Function.uncurry fun (u v : ℝ) =>
      g v * (starRingEnd ℂ) (g (v - u)) * (expK b u : ℂ)) (volume.prod volume) := by
  have hL : ∀ x ∈ tsupport g, -L ≤ x ∧ x ≤ L := fun x hx => Set.mem_Icc.mp (hsupp hx)
  have hc : Continuous (Function.uncurry fun (u v : ℝ) =>
      g v * (starRingEnd ℂ) (g (v - u)) * (expK b u : ℂ)) := by
    have := hg.1.continuous
    exact ((this.comp continuous_snd).mul
      (Complex.continuous_conj.comp (this.comp (continuous_snd.sub continuous_fst)))).mul
      (Complex.continuous_ofReal.comp ((continuous_expK b).comp continuous_fst))
  refine hc.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (-(2 * L)) (2 * L) ×ˢ Set.Icc (-L) L)
      (isCompact_Icc.prod isCompact_Icc) fun z hz => ?_)
  rw [Function.mem_support] at hz
  simp only [Function.uncurry] at hz
  have h1 : g z.2 ≠ 0 := fun h => hz (by rw [h]; ring)
  have h2 : g (z.2 - z.1) ≠ 0 := fun h => hz (by rw [h, map_zero]; ring)
  have hv := hL _ (subset_tsupport g h1)
  have hvu := hL _ (subset_tsupport g h2)
  refine Set.mk_mem_prod ?_ ?_
  · rw [Set.mem_Icc]
    constructor <;> linarith [hv.1, hv.2, hvu.1, hvu.2]
  · exact Set.mem_Icc.mpr hv

/-- ∫ f K = ∫∫ F: Fubini and the substitution w = v - u. -/
theorem integral_autocorr_mul_expK {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) (b : ℝ) :
    ∫ u : ℝ, autocorr g u * (expK b u : ℂ) = ∫ z : ℝ × ℝ, Ffun g b z ∂(volume.prod volume) := by
  have hF := integrable_conv_integrand hg hsupp b
  calc ∫ u : ℝ, autocorr g u * (expK b u : ℂ)
      = ∫ u : ℝ, ∫ v : ℝ, g v * (starRingEnd ℂ) (g (v - u)) * (expK b u : ℂ) := by
        congr 1
        funext u
        unfold autocorr
        rw [← integral_mul_const]
    _ = ∫ v : ℝ, ∫ u : ℝ, g v * (starRingEnd ℂ) (g (v - u)) * (expK b u : ℂ) := by
        rw [integral_integral_swap hF]
    _ = ∫ v : ℝ, ∫ w : ℝ, Ffun g b (v, w) := by
        congr 1
        funext v
        rw [← integral_sub_left_eq_self (fun w : ℝ => Ffun g b (v, w)) volume v]
        congr 1
        funext u
        unfold Ffun
        simp only [sub_sub_cancel]
    _ = ∫ z : ℝ × ℝ, Ffun g b z ∂(volume.prod volume) := by
        rw [integral_prod _ (integrable_Ffun hg hsupp b)]

/-- M ∫ K = ∫∫ H. -/
theorem mass_mul_eq_integral_Hfun {g : ℝ → ℂ} (hg : IsWeilTest g) {b : ℝ} (hb : 0 < b) :
    mass g * (2 / b) = ∫ z : ℝ × ℝ, Hfun g b z ∂(volume.prod volume) := by
  rw [integral_prod _ (integrable_Hfun hg hb)]
  unfold mass
  rw [← integral_mul_const]
  congr 1
  funext v
  unfold Hfun
  simp only
  rw [← integral_expK hb, ← integral_sub_left_eq_self (expK b) volume v, ← integral_const_mul]

/-- ∫∫ H = ∫∫ H' (swap the variables; K is even). -/
theorem integral_Hfun_eq_Hfun' (g : ℝ → ℂ) (b : ℝ) :
    ∫ z : ℝ × ℝ, Hfun g b z ∂(volume.prod volume)
      = ∫ z : ℝ × ℝ, Hfun' g b z ∂(volume.prod volume) := by
  rw [← integral_prod_swap (Hfun g b)]
  congr 1
  funext z
  simp only [Hfun, Hfun', Prod.swap, expK_sub_eq]

/-- E_b := M ∫ K - Re ∫ f K. -/
def Eb (g : ℝ → ℂ) (b : ℝ) : ℝ :=
  mass g * (2 / b) - (∫ u : ℝ, autocorr g u * (expK b u : ℂ)).re

/-- E_b = (1/2) ∫∫ |g(v) - g(w)|^2 K_b(v - w). -/
theorem Eb_eq_half {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) {b : ℝ} (hb : 0 < b) :
    Eb g b = (1 / 2) * ∫ z : ℝ × ℝ, Rfun g b z ∂(volume.prod volume) := by
  unfold Eb
  rw [integral_autocorr_mul_expK hg hsupp b, mass_mul_eq_integral_Hfun hg hb]
  have hre : (∫ z : ℝ × ℝ, Ffun g b z ∂(volume.prod volume)).re
      = ∫ z : ℝ × ℝ, (Ffun g b z).re ∂(volume.prod volume) := by
    have := Complex.reCLM.integral_comp_comm (integrable_Ffun hg hsupp b)
    simp only [Complex.reCLM_apply] at this
    exact this.symm
  rw [hre]
  have hR : (fun z : ℝ × ℝ => Rfun g b z)
      = fun z => Hfun g b z + Hfun' g b z - 2 * (Ffun g b z).re := funext (Rfun_eq g b)
  have hHH : Integrable (fun z : ℝ × ℝ => Hfun g b z + Hfun' g b z) (volume.prod volume) :=
    (integrable_Hfun hg hb).add (integrable_Hfun' hg hb)
  have hF2 : Integrable (fun z : ℝ × ℝ => 2 * (Ffun g b z).re) (volume.prod volume) := by
    have := (integrable_Ffun hg hsupp b).re.const_mul 2
    simpa using this
  rw [hR, integral_sub hHH hF2, integral_add (integrable_Hfun hg hb) (integrable_Hfun' hg hb),
    integral_const_mul, ← integral_Hfun_eq_Hfun' g b]
  ring

/-! ## D. The pointwise lower bound on the plane and the theorem. -/

/-- The indicator of [-L, L]. -/
def cIn (L : ℝ) : ℝ → ℝ := (Set.Icc (-L) L).indicator (fun _ => (1 : ℝ))

/-- The indicator of the complement of [-L, L]. -/
def cOut (L : ℝ) : ℝ → ℝ := (Set.Icc (-L) L)ᶜ.indicator (fun _ => (1 : ℝ))

lemma integrable_cIn (L : ℝ) : Integrable (cIn L) :=
  (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integrable_indicator
    measurableSet_Icc

lemma integral_cIn {L : ℝ} (hL : 0 ≤ L) : ∫ x : ℝ, cIn L x = 2 * L := by
  unfold cIn
  rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc, smul_eq_mul,
    max_eq_left (by linarith)]
  ring

lemma cOut_le_one (L : ℝ) (x : ℝ) : ‖cOut L x‖ ≤ 1 := by
  unfold cOut
  by_cases hx : x ∈ (Set.Icc (-L) L)ᶜ
  · rw [Set.indicator_of_mem hx]; simp
  · rw [Set.indicator_of_notMem hx]; simp

lemma measurable_cOut (L : ℝ) : Measurable (cOut L) :=
  measurable_const.indicator measurableSet_Icc.compl

/-- P1: the square part, written without the square's indicator (g vanishes off [-L, L]). -/
def P1 (g : ℝ → ℂ) (b L : ℝ) (z : ℝ × ℝ) : ℝ :=
  Real.exp (-2 * b * L) * (‖g z.1‖ ^ 2 * cIn L z.2 + cIn L z.1 * ‖g z.2‖ ^ 2
    - 2 * (g z.1 * (starRingEnd ℂ) (g z.2)).re)

/-- P2: v inside, w outside. -/
def P2 (g : ℝ → ℂ) (b L : ℝ) (z : ℝ × ℝ) : ℝ := Hfun g b z * cOut L z.2

/-- P3: w inside, v outside. -/
def P3 (g : ℝ → ℂ) (b L : ℝ) (z : ℝ × ℝ) : ℝ := Hfun' g b z * cOut L z.1

/-- THE POINTWISE INEQUALITY: P1 + P2 + P3 <= |g(v) - g(w)|^2 K_b(v - w). -/
lemma Rfun_ge {g : ℝ → ℂ} {L : ℝ} (hsupp : tsupport g ⊆ Set.Icc (-L) L) {b : ℝ} (hb : 0 < b)
    (z : ℝ × ℝ) : P1 g b L z + P2 g b L z + P3 g b L z ≤ Rfun g b z := by
  unfold P1 P2 P3 Rfun Hfun Hfun' cIn cOut
  have hK0 := expK_nonneg b (z.1 - z.2)
  have hnorm : ‖g z.1 - g z.2‖ ^ 2
      = ‖g z.1‖ ^ 2 + ‖g z.2‖ ^ 2 - 2 * (g z.1 * (starRingEnd ℂ) (g z.2)).re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq]
  by_cases h1 : z.1 ∈ Set.Icc (-L) L <;> by_cases h2 : z.2 ∈ Set.Icc (-L) L
  · have hc1 : z.1 ∉ (Set.Icc (-L) L)ᶜ := fun h => h h1
    have hc2 : z.2 ∉ (Set.Icc (-L) L)ᶜ := fun h => h h2
    rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, Set.indicator_of_notMem hc1,
      Set.indicator_of_notMem hc2, hnorm]
    have hexp : Real.exp (-2 * b * L) ≤ expK b (z.1 - z.2) := by
      unfold expK
      apply Real.exp_le_exp.mpr
      have : |z.1 - z.2| ≤ 2 * L := by
        rw [abs_le]
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      nlinarith
    have hsq : 0 ≤ ‖g z.1‖ ^ 2 + ‖g z.2‖ ^ 2 - 2 * (g z.1 * (starRingEnd ℂ) (g z.2)).re := by
      rw [← hnorm]
      positivity
    nlinarith [mul_le_mul_of_nonneg_left hexp hsq]
  · have hg2 : g z.2 = 0 := image_eq_zero_of_notMem_tsupport (fun h => h2 (hsupp h))
    have hc1 : z.1 ∉ (Set.Icc (-L) L)ᶜ := fun h => h h1
    rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, Set.indicator_of_notMem hc1,
      Set.indicator_of_mem (s := (Set.Icc (-L) L)ᶜ) h2, hg2]
    simp
  · have hg1 : g z.1 = 0 := image_eq_zero_of_notMem_tsupport (fun h => h1 (hsupp h))
    have hc2 : z.2 ∉ (Set.Icc (-L) L)ᶜ := fun h => h h2
    rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2, Set.indicator_of_notMem hc2,
      Set.indicator_of_mem (s := (Set.Icc (-L) L)ᶜ) h1, hg1]
    simp
  · have hg1 : g z.1 = 0 := image_eq_zero_of_notMem_tsupport (fun h => h1 (hsupp h))
    have hg2 : g z.2 = 0 := image_eq_zero_of_notMem_tsupport (fun h => h2 (hsupp h))
    rw [hg1, hg2]
    simp

lemma integrable_g {g : ℝ → ℂ} (hg : IsWeilTest g) : Integrable g :=
  hg.1.continuous.integrable_of_hasCompactSupport hg.2

lemma integrable_conj_g {g : ℝ → ℂ} (hg : IsWeilTest g) :
    Integrable (fun u : ℝ => (starRingEnd ℂ) (g u)) :=
  (Complex.continuous_conj.comp hg.1.continuous).integrable_of_hasCompactSupport
    (hg.2.comp_left (map_zero _))

lemma integrable_P1 {g : ℝ → ℂ} (hg : IsWeilTest g) (b L : ℝ) :
    Integrable (P1 g b L) (volume.prod volume) := by
  have hA : Integrable (fun z : ℝ × ℝ => ‖g z.1‖ ^ 2 * cIn L z.2) (volume.prod volume) :=
    (integrable_normSq hg).mul_prod (integrable_cIn L)
  have hB : Integrable (fun z : ℝ × ℝ => cIn L z.1 * ‖g z.2‖ ^ 2) (volume.prod volume) :=
    (integrable_cIn L).mul_prod (integrable_normSq hg)
  have hC : Integrable (fun z : ℝ × ℝ => 2 * (g z.1 * (starRingEnd ℂ) (g z.2)).re)
      (volume.prod volume) := by
    have := ((integrable_g hg).mul_prod (integrable_conj_g hg)).re.const_mul 2
    simpa using this
  exact (((hA.add hB).sub hC).const_mul _)

lemma integrable_P2 {g : ℝ → ℂ} (hg : IsWeilTest g) {b : ℝ} (hb : 0 < b) (L : ℝ) :
    Integrable (P2 g b L) (volume.prod volume) := by
  unfold P2
  refine (integrable_Hfun hg hb).mul_bdd (c := 1)
    ((measurable_cOut L).comp measurable_snd).aestronglyMeasurable ?_
  filter_upwards with z
  exact cOut_le_one L z.2

/-- P3 = P2 ∘ swap. -/
lemma P3_eq_P2_swap (g : ℝ → ℂ) (b L : ℝ) (z : ℝ × ℝ) : P3 g b L z = P2 g b L z.swap := by
  simp only [P3, P2, Hfun, Hfun', Prod.swap, expK_sub_eq]

lemma integrable_P3 {g : ℝ → ℂ} (hg : IsWeilTest g) {b : ℝ} (hb : 0 < b) (L : ℝ) :
    Integrable (P3 g b L) (volume.prod volume) := by
  refine (integrable_P2 hg hb L).swap.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [Function.comp]
  exact (P3_eq_P2_swap g b L z).symm

lemma integral_P3_eq_P2 (g : ℝ → ℂ) (b L : ℝ) :
    ∫ z : ℝ × ℝ, P3 g b L z ∂(volume.prod volume)
      = ∫ z : ℝ × ℝ, P2 g b L z ∂(volume.prod volume) := by
  rw [← integral_prod_swap (P2 g b L)]
  congr 1
  funext z
  exact P3_eq_P2_swap g b L z

/-- ∫∫ P1 = e^{-2bL} (4 L M - 2 |∫ g|^2). -/
lemma integral_P1 {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ} (hL : 0 ≤ L) (b : ℝ) :
    ∫ z : ℝ × ℝ, P1 g b L z ∂(volume.prod volume)
      = Real.exp (-2 * b * L) * (4 * L * mass g - 2 * ‖∫ u : ℝ, g u‖ ^ 2) := by
  unfold P1
  rw [integral_const_mul]
  congr 1
  have hA : Integrable (fun z : ℝ × ℝ => ‖g z.1‖ ^ 2 * cIn L z.2) (volume.prod volume) :=
    (integrable_normSq hg).mul_prod (integrable_cIn L)
  have hB : Integrable (fun z : ℝ × ℝ => cIn L z.1 * ‖g z.2‖ ^ 2) (volume.prod volume) :=
    (integrable_cIn L).mul_prod (integrable_normSq hg)
  have hC : Integrable (fun z : ℝ × ℝ => 2 * (g z.1 * (starRingEnd ℂ) (g z.2)).re)
      (volume.prod volume) := by
    have := ((integrable_g hg).mul_prod (integrable_conj_g hg)).re.const_mul 2
    simpa using this
  have hAB : Integrable (fun z : ℝ × ℝ => ‖g z.1‖ ^ 2 * cIn L z.2 + cIn L z.1 * ‖g z.2‖ ^ 2)
      (volume.prod volume) := hA.add hB
  rw [integral_sub hAB hC, integral_add hA hB, integral_const_mul,
    integral_prod_mul (fun x : ℝ => ‖g x‖ ^ 2) (cIn L),
    integral_prod_mul (cIn L) (fun x : ℝ => ‖g x‖ ^ 2), integral_cIn hL]
  have hre : ∫ z : ℝ × ℝ, (g z.1 * (starRingEnd ℂ) (g z.2)).re ∂(volume.prod volume)
      = ‖∫ u : ℝ, g u‖ ^ 2 := by
    have hint : Integrable (fun z : ℝ × ℝ => g z.1 * (starRingEnd ℂ) (g z.2))
        (volume.prod volume) := (integrable_g hg).mul_prod (integrable_conj_g hg)
    have := Complex.reCLM.integral_comp_comm hint
    simp only [Complex.reCLM_apply] at this
    rw [this, integral_prod_mul g (fun u : ℝ => (starRingEnd ℂ) (g u)), integral_conj,
      Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [hre]
  unfold mass
  ring

/-- ∫∫ P2 >= (2 e^{-bL} / b) M. -/
lemma integral_P2_ge {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) {b : ℝ} (hb : 0 < b) :
    2 * Real.exp (-b * L) / b * mass g ≤ ∫ z : ℝ × ℝ, P2 g b L z ∂(volume.prod volume) := by
  rw [integral_prod _ (integrable_P2 hg hb L)]
  have hinner : ∀ v : ℝ, ∫ w : ℝ, P2 g b L (v, w)
      = ‖g v‖ ^ 2 * ∫ w in (Set.Icc (-L) L)ᶜ, expK b (v - w) := by
    intro v
    unfold P2 Hfun cOut
    rw [← integral_indicator measurableSet_Icc.compl, ← integral_const_mul]
    congr 1
    funext w
    by_cases hw : w ∈ (Set.Icc (-L) L)ᶜ
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw]
      ring
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw]
      ring
  have hint : Integrable (fun v : ℝ => ∫ w : ℝ, P2 g b L (v, w)) :=
    (integrable_P2 hg hb L).integral_prod_left
  calc 2 * Real.exp (-b * L) / b * mass g
      = ∫ v : ℝ, ‖g v‖ ^ 2 * (2 * Real.exp (-b * L) / b) := by
        unfold mass
        rw [integral_mul_const]
        ring
    _ ≤ ∫ v : ℝ, ∫ w : ℝ, P2 g b L (v, w) := by
        apply integral_mono ((integrable_normSq hg).mul_const _) hint
        intro v
        show ‖g v‖ ^ 2 * (2 * Real.exp (-b * L) / b) ≤ ∫ w : ℝ, P2 g b L (v, w)
        rw [hinner v]
        by_cases hv : v ∈ Set.Icc (-L) L
        · exact mul_le_mul_of_nonneg_left (integral_compl_Icc_expK_ge hb hv) (by positivity)
        · rw [image_eq_zero_of_notMem_tsupport (fun h => hv (hsupp h))]
          simp

/-- THE DIRICHLET LOWER BOUND for one exponential kernel. -/
theorem Eb_ge {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ} (hL : 0 ≤ L)
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) {b : ℝ} (hb : 0 < b) :
    2 * Real.exp (-b * L) / b * mass g
      + Real.exp (-2 * b * L) * (2 * L * mass g - ‖∫ u : ℝ, g u‖ ^ 2) ≤ Eb g b := by
  rw [Eb_eq_half hg hsupp hb]
  have hP1 := integrable_P1 hg b L
  have hP2 := integrable_P2 hg hb L
  have hP3 := integrable_P3 hg hb L
  have hP12 : Integrable (fun z : ℝ × ℝ => P1 g b L z + P2 g b L z) (volume.prod volume) :=
    hP1.add hP2
  have hP123 : Integrable (fun z : ℝ × ℝ => P1 g b L z + P2 g b L z + P3 g b L z)
      (volume.prod volume) := hP12.add hP3
  have hmono : ∫ z : ℝ × ℝ, (P1 g b L z + P2 g b L z + P3 g b L z) ∂(volume.prod volume)
      ≤ ∫ z : ℝ × ℝ, Rfun g b z ∂(volume.prod volume) :=
    integral_mono hP123 (integrable_Rfun hg hsupp hb) fun z => Rfun_ge hsupp hb z
  rw [integral_add hP12 hP3, integral_add hP1 hP2, integral_P1 hg hL b,
    integral_P3_eq_P2] at hmono
  have h2 := integral_P2_ge hg hsupp hb
  linarith

end RvMBridge33
