/-
  ZhuParity -- Zhu Lemma 6.1 (arXiv:2608.24827 v2), parity decoupling of the Weil form, PROVED on
  the rvm_bridge island (2026-09-23).

  Zhu Theorem 1.1 and the certified even-mode Legendre block cover REAL EVEN test functions; the
  odd sector has its own block with the pole sign reversed (Section 6, eq. 14).  The registry's
  `WeilWindow.WindowFloor` quantifies over ALL complex smooth compactly supported f.  Lemma 6.1
  closes the gap:  Q(f) = Q(Re f) + Q(Im f), and for real a, Q(a) = Q(a_even) + Q(a_odd).
  Both follow from ONE fact proved here: the Weil functional archSide - primeSide VANISHES on every
  odd test function (pole terms cancel, g(0) = 0, the archimedean integrand is odd in r because
  Re psi(1/4 + ir/2) is even, the prime terms cancel), because every cross term of the
  sesquilinear autocorrelation in these decompositions is an odd function.

  `windowFloor_of_sectors`: EvenSectorFloor L lam -> OddSectorFloor L lam -> WindowFloor L lam,
  the theorem that lets the re-specified node carry the odd sector as one explicit hypothesis and
  still conclude the full WindowFloor.  Nothing about zeros.  No `sorry`.
  conjecture1_proved = False.
-/
import ZhuEnvelope
import ZhuSymbol

open MeasureTheory Zeta23
open scoped ComplexConjugate

/-! ## A. Registry-facing definitions (namespace WeilWindow, mirrored verbatim into RHDefs). -/

namespace WeilWindow
open MeasureTheory Complex WeilExplicit WeilForm

/-- Zhu eq. (1): the window floor.  `WindowFloor L lam` says the Weil form of every smooth
    compactly supported test function supported in `[-L, L]` is at least `lam ‖f‖₂²`.  Zhu's
    `λ*(L)` is the largest such `lam`; `WindowFloor L lam` with `lam > 0` is a finite fragment
    of RH, and `∀ L, WindowFloor L 0` is RH-equivalent. -/
def WindowFloor (L lam : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, WeilExplicit.IsWeilTest f → tsupport f ⊆ Set.Icc (-L) L →
    lam * (∫ x : ℝ, ‖f x‖ ^ 2) ≤ (WeilForm.weilForm (WeilForm.autocorr f)).re

/-- The ODD-sector window floor (Zhu Section 6, eq. (14)): the Weil form of every real ODD smooth
    test function supported in `[-L, L]` is at least `lam ‖f‖₂²`.  Together with the real even
    sector this yields `WindowFloor L lam` for complex `f` (Zhu Lemma 6.1, Corollary 6.3). -/
def OddSectorFloor (L lam : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, WeilExplicit.IsWeilTest f → (∀ x, (f x).im = 0) → (∀ x, f (-x) = -f x) →
    tsupport f ⊆ Set.Icc (-L) L →
    lam * (∫ x : ℝ, ‖f x‖ ^ 2) ≤ (WeilForm.weilForm (WeilForm.autocorr f)).re

/-- The real EVEN-sector window floor, the sector Zhu Theorem 1.1 certifies. -/
def EvenSectorFloor (L lam : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, WeilExplicit.IsWeilTest f → (∀ x, (f x).im = 0) → (∀ x, f (-x) = f x) →
    tsupport f ⊆ Set.Icc (-L) L →
    lam * (∫ x : ℝ, ‖f x‖ ^ 2) ≤ (WeilForm.weilForm (WeilForm.autocorr f)).re

end WeilWindow

/-! ## B. The proof. -/

noncomputable section

namespace RvMBridgeZhu
open WeilExplicit RvMBridge4 RvMBridge5

/-! ### B.1 Closure properties of the test class. -/

lemma isWeilTest_add {f h : ℝ → ℂ} (hf : IsWeilTest f) (hh : IsWeilTest h) : IsWeilTest (f + h) :=
  ⟨hf.1.add hh.1, hf.2.add hh.2⟩

lemma isWeilTest_comp_neg {f : ℝ → ℂ} (hf : IsWeilTest f) : IsWeilTest (fun x => f (-x)) :=
  ⟨hf.1.comp contDiff_neg, hf.2.comp_homeomorph (Homeomorph.neg ℝ)⟩

lemma isWeilTest_const_mul (c : ℂ) {f : ℝ → ℂ} (hf : IsWeilTest f) :
    IsWeilTest (fun x => c * f x) :=
  ⟨contDiff_const.mul hf.1, hf.2.mul_left⟩

lemma isWeilTest_re {f : ℝ → ℂ} (hf : IsWeilTest f) : IsWeilTest (fun x => ((f x).re : ℂ)) :=
  ⟨Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp hf.1),
    hf.2.comp_left (g := fun z : ℂ => ((z.re : ℝ) : ℂ)) (by simp)⟩

lemma isWeilTest_im {f : ℝ → ℂ} (hf : IsWeilTest f) : IsWeilTest (fun x => ((f x).im : ℂ)) :=
  ⟨Complex.ofRealCLM.contDiff.comp (Complex.imCLM.contDiff.comp hf.1),
    hf.2.comp_left (g := fun z : ℂ => ((z.im : ℝ) : ℂ)) (by simp)⟩

/-- The even part `(f x + f (-x)) / 2`. -/
def evenPart (f : ℝ → ℂ) : ℝ → ℂ := fun x => (f x + f (-x)) / 2
/-- The odd part `(f x - f (-x)) / 2`. -/
def oddPart (f : ℝ → ℂ) : ℝ → ℂ := fun x => (f x - f (-x)) / 2

lemma evenPart_add_oddPart (f : ℝ → ℂ) : evenPart f + oddPart f = f := by
  funext x; simp only [evenPart, oddPart, Pi.add_apply]; ring

lemma isWeilTest_evenPart {f : ℝ → ℂ} (hf : IsWeilTest f) : IsWeilTest (evenPart f) :=
  ⟨(hf.1.add (isWeilTest_comp_neg hf).1).div_const 2,
    (hf.2.add (isWeilTest_comp_neg hf).2).comp_left (g := fun z : ℂ => z / 2) (by simp)⟩

lemma isWeilTest_oddPart {f : ℝ → ℂ} (hf : IsWeilTest f) : IsWeilTest (oddPart f) :=
  ⟨(hf.1.sub (isWeilTest_comp_neg hf).1).div_const 2,
    (hf.2.sub (isWeilTest_comp_neg hf).2).comp_left (g := fun z : ℂ => z / 2) (by simp)⟩

lemma evenPart_neg (f : ℝ → ℂ) (x : ℝ) : evenPart f (-x) = evenPart f x := by
  simp only [evenPart, neg_neg]; ring

lemma oddPart_neg (f : ℝ → ℂ) (x : ℝ) : oddPart f (-x) = -oddPart f x := by
  simp only [oddPart, neg_neg]; ring

lemma evenPart_im {f : ℝ → ℂ} (hf : ∀ x, (f x).im = 0) (x : ℝ) : (evenPart f x).im = 0 := by
  simp [evenPart, Complex.div_ofNat_im, hf]

lemma oddPart_im {f : ℝ → ℂ} (hf : ∀ x, (f x).im = 0) (x : ℝ) : (oddPart f x).im = 0 := by
  simp [oddPart, Complex.div_ofNat_im, hf]

lemma tsupport_evenPart_subset {f : ℝ → ℂ} {L : ℝ} (hs : tsupport f ⊆ Set.Icc (-L) L) :
    tsupport (evenPart f) ⊆ Set.Icc (-L) L := by
  refine closure_minimal (fun x hx => ?_) isClosed_Icc
  simp only [Function.mem_support, evenPart] at hx
  by_contra hnot
  have h1 : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hnot (hs h))
  have h2 : f (-x) = 0 := image_eq_zero_of_notMem_tsupport (fun h => hnot (by
    have := hs h; simp only [Set.mem_Icc] at this ⊢; constructor <;> linarith))
  exact hx (by rw [h1, h2]; simp)

lemma tsupport_oddPart_subset {f : ℝ → ℂ} {L : ℝ} (hs : tsupport f ⊆ Set.Icc (-L) L) :
    tsupport (oddPart f) ⊆ Set.Icc (-L) L := by
  refine closure_minimal (fun x hx => ?_) isClosed_Icc
  simp only [Function.mem_support, oddPart] at hx
  by_contra hnot
  have h1 : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hnot (hs h))
  have h2 : f (-x) = 0 := image_eq_zero_of_notMem_tsupport (fun h => hnot (by
    have := hs h; simp only [Set.mem_Icc] at this ⊢; constructor <;> linarith))
  exact hx (by rw [h1, h2]; simp)

/-! ### B.2 The cross-correlation: test class, bilinearity, parity. -/

lemma crossCorr_eq_weilTest (f h : ℝ → ℂ) : WeilForm.crossCorr f h = Zeta23.EF.weilTest f h := by
  funext u
  unfold WeilForm.crossCorr Zeta23.EF.weilTest
  rw [MeasureTheory.convolution_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [ContinuousLinearMap.mul_apply', Zeta23.EF.tilde, neg_sub]

lemma isWeilTest_crossCorr {f h : ℝ → ℂ} (hf : IsWeilTest f) (hh : IsWeilTest h) :
    IsWeilTest (WeilForm.crossCorr f h) := by
  rw [crossCorr_eq_weilTest]
  refine ⟨?_, Zeta23.EF.weilTest_hasCompactSupport hf.2 hh.2⟩
  unfold Zeta23.EF.weilTest
  exact hf.2.contDiff_convolution_left _ hf.1
    (Zeta23.EF.continuous_tilde hh.1.continuous).locallyIntegrable

lemma integrable_cross_integrand {f h : ℝ → ℂ} (hf : IsWeilTest f) (hh : IsWeilTest h) (x : ℝ) :
    Integrable (fun t => f t * (starRingEnd ℂ) (h (t - x))) := by
  have hc : Continuous fun t => f t * (starRingEnd ℂ) (h (t - x)) := by
    have := hh.1.continuous
    have := hf.1.continuous
    fun_prop
  exact hc.integrable_of_hasCompactSupport hf.2.mul_right

lemma crossCorr_add_left {f₁ f₂ h : ℝ → ℂ} (hf₁ : IsWeilTest f₁) (hf₂ : IsWeilTest f₂)
    (hh : IsWeilTest h) :
    WeilForm.crossCorr (f₁ + f₂) h = WeilForm.crossCorr f₁ h + WeilForm.crossCorr f₂ h := by
  funext x
  simp only [WeilForm.crossCorr, Pi.add_apply, add_mul]
  exact integral_add (integrable_cross_integrand hf₁ hh x) (integrable_cross_integrand hf₂ hh x)

lemma crossCorr_add_right {f h₁ h₂ : ℝ → ℂ} (hf : IsWeilTest f) (hh₁ : IsWeilTest h₁)
    (hh₂ : IsWeilTest h₂) :
    WeilForm.crossCorr f (h₁ + h₂) = WeilForm.crossCorr f h₁ + WeilForm.crossCorr f h₂ := by
  funext x
  simp only [WeilForm.crossCorr, Pi.add_apply, map_add, mul_add]
  exact integral_add (integrable_cross_integrand hf hh₁ x) (integrable_cross_integrand hf hh₂ x)

lemma crossCorr_const_mul_left (c : ℂ) (f h : ℝ → ℂ) :
    WeilForm.crossCorr (fun x => c * f x) h = fun x => c * WeilForm.crossCorr f h x := by
  funext x
  simp only [WeilForm.crossCorr]
  rw [← integral_const_mul]
  congr 1; funext t; ring

lemma crossCorr_const_mul_right (c : ℂ) (f h : ℝ → ℂ) :
    WeilForm.crossCorr f (fun x => c * h x) = fun x => (starRingEnd ℂ) c * WeilForm.crossCorr f h x := by
  funext x
  simp only [WeilForm.crossCorr, map_mul]
  rw [← integral_const_mul]
  congr 1; funext t; ring

/-- For real-valued `a`, `b`: `C(b, a)(u) = C(a, b)(-u)`. -/
lemma crossCorr_swap_of_real {a b : ℝ → ℂ} (ha : ∀ x, (a x).im = 0) (hb : ∀ x, (b x).im = 0)
    (u : ℝ) : WeilForm.crossCorr b a u = WeilForm.crossCorr a b (-u) := by
  have hca : ∀ x, (starRingEnd ℂ) (a x) = a x := fun x => Complex.conj_eq_iff_im.mpr (ha x)
  have hcb : ∀ x, (starRingEnd ℂ) (b x) = b x := fun x => Complex.conj_eq_iff_im.mpr (hb x)
  simp only [WeilForm.crossCorr, hca, hcb, sub_neg_eq_add]
  rw [← integral_add_right_eq_self (fun t => b t * a (t - u)) u]
  congr 1; funext t
  rw [add_sub_cancel_right]; ring

/-- Parity of a cross-correlation: `a(-x) = εa a(x)`, `b(-x) = εb b(x)` (real signs) give
`C(a,b)(-u) = εa εb C(a,b)(u)`. -/
lemma crossCorr_neg_of_parity {a b : ℝ → ℂ} {εa εb : ℝ} (ha : ∀ x, a (-x) = (εa : ℂ) * a x)
    (hb : ∀ x, b (-x) = (εb : ℂ) * b x) (u : ℝ) :
    WeilForm.crossCorr a b (-u) = ((εa * εb : ℝ) : ℂ) * WeilForm.crossCorr a b u := by
  simp only [WeilForm.crossCorr]
  rw [← integral_neg_eq_self, ← integral_const_mul]
  congr 1; funext t
  rw [ha t, show -t - -u = -(t - u) by ring, hb (t - u), map_mul, Complex.conj_ofReal]
  push_cast; ring

/-! ### B.3 The Weil functional: additivity, and vanishing on odd functions. -/

lemma weilKernel_add {f h : ℝ → ℂ} (hf : IsWeilTest f) (hh : IsWeilTest h) (s : ℂ) :
    weilKernel (f + h) s = weilKernel f s + weilKernel h s := by
  unfold weilKernel
  simp only [Pi.add_apply, add_mul]
  have hi : ∀ g : ℝ → ℂ, IsWeilTest g →
      Integrable (fun u : ℝ => g u * Complex.exp ((s - 1 / 2) * (u : ℂ))) := fun g hg =>
    (hg.1.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hg.2.mul_right
  exact integral_add (hi f hf) (hi h hh)

lemma archSide_add {f h : ℝ → ℂ} (hf : IsWeilTest f) (hh : IsWeilTest h) :
    archSide (f + h) = archSide f + archSide h := by
  unfold archSide
  have e : archIntegrand (f + h) = archIntegrand f + archIntegrand h := by
    funext r; simp only [archIntegrand, Pi.add_apply, weilKernel_add hf hh]; ring
  rw [weilKernel_add hf hh, weilKernel_add hf hh, e]
  simp only [Pi.add_apply]
  rw [integral_add (integrable_archIntegrand hf) (integrable_archIntegrand hh)]
  ring

/-- The prime-side summand of a test function has finite support. -/
lemma primeSide_summand_eq_zero {f : ℝ → ℂ} (hf : IsWeilTest f) :
    ∃ N0 : ℕ, ∀ n : ℕ, n ∉ Finset.range N0 →
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * (f (Real.log n) + f (-Real.log n)) = 0 := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hf.2.isCompact.isBounded
  refine ⟨⌈Real.exp R⌉₊ + 1, fun n hn => ?_⟩
  have hn' : ⌈Real.exp R⌉₊ + 1 ≤ n := by simpa [Finset.mem_range] using hn
  have h1 : Real.exp R < (n : ℝ) := by
    have := Nat.le_ceil (Real.exp R)
    have h2 : ((⌈Real.exp R⌉₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'
    push_cast at h2
    linarith
  have hlog : R < Real.log n := by
    rw [← Real.log_exp R]; exact Real.log_lt_log (Real.exp_pos _) h1
  have hout : ∀ y : ℝ, R < |y| → f y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport (fun hmem => by
      have := hR hmem; rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this; linarith)
  rw [hout _ (lt_of_lt_of_le hlog (le_abs_self _)),
    hout _ (by rw [abs_neg]; exact lt_of_lt_of_le hlog (le_abs_self _))]
  simp

lemma summable_primeSide_summand {f : ℝ → ℂ} (hf : IsWeilTest f) :
    Summable (fun n : ℕ =>
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * (f (Real.log n) + f (-Real.log n))) := by
  obtain ⟨N0, h⟩ := primeSide_summand_eq_zero hf
  exact summable_of_ne_finset_zero (s := Finset.range N0) h

lemma primeSide_add {f h : ℝ → ℂ} (hf : IsWeilTest f) (hh : IsWeilTest h) :
    primeSide (f + h) = primeSide f + primeSide h := by
  unfold primeSide
  rw [← (summable_primeSide_summand hf).tsum_add (summable_primeSide_summand hh)]
  exact tsum_congr fun n => by simp only [Pi.add_apply]; ring

theorem weilForm_add {f h : ℝ → ℂ} (hf : IsWeilTest f) (hh : IsWeilTest h) :
    WeilExplicit.weilForm (f + h) = WeilExplicit.weilForm f + WeilExplicit.weilForm h := by
  unfold WeilExplicit.weilForm
  rw [archSide_add hf hh, primeSide_add hf hh]; ring

lemma integral_eq_zero_of_odd {φ : ℝ → ℂ} (h : ∀ u, φ (-u) = -φ u) : ∫ u : ℝ, φ u = 0 := by
  have h1 := integral_neg_eq_self φ volume
  have h2 : ∫ x : ℝ, φ (-x) = -∫ x : ℝ, φ x := by
    rw [← integral_neg]; exact integral_congr_ae (Filter.Eventually.of_forall h)
  rw [h2] at h1
  linear_combination (-(1 : ℂ) / 2) * h1

/-- **The Weil functional vanishes on odd test functions.** -/
theorem weilForm_eq_zero_of_odd {k : ℝ → ℂ} (hk : IsWeilTest k) (hodd : ∀ u, k (-u) = -k u) :
    WeilExplicit.weilForm k = 0 := by
  have h0 : k 0 = 0 := by
    have h := hodd 0
    rw [neg_zero] at h
    have h2 : (2 : ℂ) * k 0 = 0 := by linear_combination h
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  -- pole terms
  have hpole : weilKernel k 0 + weilKernel k 1 = 0 := by
    unfold weilKernel
    have hi : ∀ s : ℂ, Integrable (fun u : ℝ => k u * Complex.exp ((s - 1 / 2) * (u : ℂ))) :=
      fun s => (hk.1.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hk.2.mul_right
    rw [← integral_add (hi 0) (hi 1)]
    apply integral_eq_zero_of_odd
    intro u
    rw [hodd u]
    push_cast
    have e1 : ((0 : ℂ) - 1 / 2) * (-(u : ℂ)) = (1 - 1 / 2) * (u : ℂ) := by ring
    have e2 : ((1 : ℂ) - 1 / 2) * (-(u : ℂ)) = (0 - 1 / 2) * (u : ℂ) := by ring
    rw [e1, e2]; ring
  -- archimedean integral
  have harch : ∫ r : ℝ, archIntegrand k r = 0 := by
    apply integral_eq_zero_of_odd
    intro r
    unfold archIntegrand
    have hψ := RvMBridge30.psiR_neg r
    unfold RvMBridge11.psiR at hψ
    rw [hψ]
    have hker : weilKernel k (1 / 2 + ((-r : ℝ) : ℂ) * Complex.I)
        = -weilKernel k (1 / 2 + (r : ℂ) * Complex.I) := by
      unfold weilKernel
      rw [← integral_neg, ← integral_neg_eq_self]
      congr 1; funext u
      rw [hodd u]
      push_cast
      have e : ((1 : ℂ) / 2 + -(r : ℂ) * Complex.I - 1 / 2) * (-(u : ℂ))
          = (1 / 2 + (r : ℂ) * Complex.I - 1 / 2) * (u : ℂ) := by ring
      rw [e]; ring
    rw [hker]; ring
  -- prime side
  have hprime : primeSide k = 0 := by
    unfold primeSide
    rw [← tsum_zero]
    exact tsum_congr fun n => by rw [hodd]; ring
  unfold WeilExplicit.weilForm archSide
  rw [hprime, harch, h0]
  linear_combination hpole

/-! ### B.4 Decoupling of Q. -/

lemma autocorr_add {f h : ℝ → ℂ} (hf : IsWeilTest f) (hh : IsWeilTest h) :
    WeilForm.autocorr (f + h)
      = WeilForm.autocorr f + WeilForm.autocorr h + (WeilForm.crossCorr f h + WeilForm.crossCorr h f) := by
  show WeilForm.crossCorr (f + h) (f + h) = _
  rw [crossCorr_add_left hf hh (isWeilTest_add hf hh), crossCorr_add_right hf hf hh,
    crossCorr_add_right hh hf hh]
  funext x; simp only [Pi.add_apply]; ring

lemma isWeilTest_autocorr' {f : ℝ → ℂ} (hf : IsWeilTest f) : IsWeilTest (WeilForm.autocorr f) :=
  isWeilTest_autocorr hf

/-- `Q(f + h) = Q(f) + Q(h)` whenever the cross term is odd. -/
theorem Q_add_of_cross_odd {f h : ℝ → ℂ} (hf : IsWeilTest f) (hh : IsWeilTest h)
    (hodd : ∀ u, (WeilForm.crossCorr f h + WeilForm.crossCorr h f) (-u)
      = -(WeilForm.crossCorr f h + WeilForm.crossCorr h f) u) :
    (WeilForm.weilForm (WeilForm.autocorr (f + h))).re
      = (WeilForm.weilForm (WeilForm.autocorr f)).re + (WeilForm.weilForm (WeilForm.autocorr h)).re := by
  have hc : IsWeilTest (WeilForm.crossCorr f h + WeilForm.crossCorr h f) :=
    isWeilTest_add (isWeilTest_crossCorr hf hh) (isWeilTest_crossCorr hh hf)
  show (WeilExplicit.weilForm (WeilForm.autocorr (f + h))).re = _
  rw [autocorr_add hf hh,
    weilForm_add (isWeilTest_add (isWeilTest_autocorr' hf) (isWeilTest_autocorr' hh)) hc,
    weilForm_add (isWeilTest_autocorr' hf) (isWeilTest_autocorr' hh), weilForm_eq_zero_of_odd hc hodd]
  simp only [add_zero, Complex.add_re]
  rfl

/-- Reality decoupling: `Q(a + I b) = Q(a) + Q(b)` for real-valued `a`, `b`. -/
theorem Q_add_I_mul {a b : ℝ → ℂ} (ha : IsWeilTest a) (hb : IsWeilTest b)
    (hra : ∀ x, (a x).im = 0) (hrb : ∀ x, (b x).im = 0) :
    (WeilForm.weilForm (WeilForm.autocorr (a + fun x => Complex.I * b x))).re
      = (WeilForm.weilForm (WeilForm.autocorr a)).re + (WeilForm.weilForm (WeilForm.autocorr b)).re := by
  have hib : IsWeilTest (fun x => Complex.I * b x) := isWeilTest_const_mul _ hb
  rw [Q_add_of_cross_odd ha hib]
  · have hib' : WeilForm.autocorr (fun x => Complex.I * b x) = WeilForm.autocorr b := by
      show WeilForm.crossCorr (fun x => Complex.I * b x) (fun x => Complex.I * b x) = WeilForm.crossCorr b b
      rw [crossCorr_const_mul_left, crossCorr_const_mul_right]
      funext x
      rw [Complex.conj_I]
      linear_combination (-(WeilForm.crossCorr b b x)) * Complex.I_mul_I
    rw [hib']
  · intro u
    simp only [Pi.add_apply]
    rw [crossCorr_const_mul_right, crossCorr_const_mul_left]
    simp only
    have h1 := crossCorr_swap_of_real hra hrb u
    have h2 := crossCorr_swap_of_real hra hrb (-u)
    rw [neg_neg] at h2
    rw [Complex.conj_I, h1, ← h2]
    ring

/-- Parity decoupling: `Q(a) = Q(a_even) + Q(a_odd)`. -/
theorem Q_evenPart_add_oddPart {a : ℝ → ℂ} (ha : IsWeilTest a) :
    (WeilForm.weilForm (WeilForm.autocorr a)).re
      = (WeilForm.weilForm (WeilForm.autocorr (evenPart a))).re
        + (WeilForm.weilForm (WeilForm.autocorr (oddPart a))).re := by
  conv_lhs => rw [← evenPart_add_oddPart a]
  refine Q_add_of_cross_odd (isWeilTest_evenPart ha) (isWeilTest_oddPart ha) fun u => ?_
  have he : ∀ x, evenPart a (-x) = ((1 : ℝ) : ℂ) * evenPart a x := fun x => by
    rw [evenPart_neg]; simp
  have ho : ∀ x, oddPart a (-x) = ((-1 : ℝ) : ℂ) * oddPart a x := fun x => by
    rw [oddPart_neg]; simp
  simp only [Pi.add_apply]
  rw [crossCorr_neg_of_parity he ho, crossCorr_neg_of_parity ho he]
  norm_num
  ring

/-! ### B.5 The L² mass splits the same way. -/

lemma integrable_norm_sq {f : ℝ → ℂ} (hf : IsWeilTest f) : Integrable (fun x => ‖f x‖ ^ 2) := by
  have hc : Continuous fun x => ‖f x‖ ^ 2 := by
    have := hf.1.continuous
    fun_prop
  refine hc.integrable_of_hasCompactSupport (hf.2.mono' fun x hx => subset_tsupport _ ?_)
  simp only [Function.mem_support] at hx ⊢
  intro h
  exact hx (by simp [h])

lemma norm_sq_re_add_im (z : ℂ) : ‖z‖ ^ 2 = ‖((z.re : ℝ) : ℂ)‖ ^ 2 + ‖((z.im : ℝ) : ℂ)‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]; ring

lemma integral_norm_sq_eq_re_add_im {f : ℝ → ℂ} (hf : IsWeilTest f) :
    ∫ x : ℝ, ‖f x‖ ^ 2 = (∫ x : ℝ, ‖((f x).re : ℂ)‖ ^ 2) + ∫ x : ℝ, ‖((f x).im : ℂ)‖ ^ 2 := by
  rw [← integral_add (integrable_norm_sq (isWeilTest_re hf)) (integrable_norm_sq (isWeilTest_im hf))]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => norm_sq_re_add_im (f x))

lemma norm_sq_evenPart_add_oddPart (f : ℝ → ℂ) (x : ℝ) :
    ‖evenPart f x‖ ^ 2 + ‖oddPart f x‖ ^ 2 = (‖f x‖ ^ 2 + ‖f (-x)‖ ^ 2) / 2 := by
  simp only [evenPart, oddPart, Complex.sq_norm, Complex.normSq_apply, Complex.div_ofNat_re,
    Complex.div_ofNat_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  ring

lemma integral_norm_sq_evenPart_add_oddPart {f : ℝ → ℂ} (hf : IsWeilTest f) :
    (∫ x : ℝ, ‖evenPart f x‖ ^ 2) + ∫ x : ℝ, ‖oddPart f x‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  rw [← integral_add (integrable_norm_sq (isWeilTest_evenPart hf)) (integrable_norm_sq (isWeilTest_oddPart hf))]
  have e : (fun x : ℝ => ‖evenPart f x‖ ^ 2 + ‖oddPart f x‖ ^ 2)
      = fun x => (1 / 2 : ℝ) * (‖f x‖ ^ 2 + ‖f (-x)‖ ^ 2) := by
    funext x; rw [norm_sq_evenPart_add_oddPart]; ring
  rw [e, integral_const_mul, integral_add (integrable_norm_sq hf) (integrable_norm_sq (isWeilTest_comp_neg hf)),
    integral_neg_eq_self (fun x => ‖f x‖ ^ 2)]
  ring

/-! ### B.6 The assembly: both sector floors give the full window floor. -/

theorem sector_floor_of_real {L lam : ℝ} (he : WeilWindow.EvenSectorFloor L lam)
    (ho : WeilWindow.OddSectorFloor L lam) {a : ℝ → ℂ} (ha : IsWeilTest a) (hra : ∀ x, (a x).im = 0)
    (hs : tsupport a ⊆ Set.Icc (-L) L) :
    lam * (∫ x : ℝ, ‖a x‖ ^ 2) ≤ (WeilForm.weilForm (WeilForm.autocorr a)).re := by
  have h1 := he (evenPart a) (isWeilTest_evenPart ha) (evenPart_im hra) (evenPart_neg a)
    (tsupport_evenPart_subset hs)
  have h2 := ho (oddPart a) (isWeilTest_oddPart ha) (oddPart_im hra) (oddPart_neg a)
    (tsupport_oddPart_subset hs)
  rw [Q_evenPart_add_oddPart ha, ← integral_norm_sq_evenPart_add_oddPart ha, mul_add]
  linarith

/-- **Zhu Lemma 6.1, assembled**: the real even and real odd sector floors give the window floor
for every complex test function. -/
theorem windowFloor_of_sectors {L lam : ℝ} (he : WeilWindow.EvenSectorFloor L lam)
    (ho : WeilWindow.OddSectorFloor L lam) : WeilWindow.WindowFloor L lam := by
  intro f hf hs
  set a : ℝ → ℂ := fun x => ((f x).re : ℂ) with ha
  set b : ℝ → ℂ := fun x => ((f x).im : ℂ) with hb
  have hfab : f = a + fun x => Complex.I * b x := by
    funext x
    exact Complex.ext (by simp [ha, hb]) (by simp [ha, hb])
  have hta : tsupport a ⊆ Set.Icc (-L) L :=
    (tsupport_comp_subset (g := fun z : ℂ => ((z.re : ℝ) : ℂ)) (by simp) f).trans hs
  have htb : tsupport b ⊆ Set.Icc (-L) L :=
    (tsupport_comp_subset (g := fun z : ℂ => ((z.im : ℝ) : ℂ)) (by simp) f).trans hs
  have hQ : (WeilForm.weilForm (WeilForm.autocorr f)).re
      = (WeilForm.weilForm (WeilForm.autocorr a)).re + (WeilForm.weilForm (WeilForm.autocorr b)).re := by
    conv_lhs => rw [hfab]
    exact Q_add_I_mul (isWeilTest_re hf) (isWeilTest_im hf) (fun x => by simp [ha]) (fun x => by simp [hb])
  have hN : ∫ x : ℝ, ‖f x‖ ^ 2 = (∫ x : ℝ, ‖a x‖ ^ 2) + ∫ x : ℝ, ‖b x‖ ^ 2 :=
    integral_norm_sq_eq_re_add_im hf
  have h1 := sector_floor_of_real he ho (isWeilTest_re hf) (fun x => by simp [ha]) hta
  have h2 := sector_floor_of_real he ho (isWeilTest_im hf) (fun x => by simp [hb]) htb
  rw [hQ, hN, mul_add]
  linarith

end RvMBridgeZhu

end
