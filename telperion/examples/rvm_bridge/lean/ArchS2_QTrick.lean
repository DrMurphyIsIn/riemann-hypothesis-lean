/-
  ArchS2_QTrick -- stage S2 of the archimedean conceptual blueprint (2026-10-11):
  the pole-free parametrisation (Connes-Consani, arXiv:2006.13771, Lemma 3.3 / Rem. 6.12),
  written in this island's variable and Fourier convention.

  CONVENTION (verified, not assumed): the project transform is Zeta23's
      paperFT f z = ∫ f(u) e^{i z u} du        (Zeta23/Defs.lean),
  so paperFT g (I/2) = ∫ g(u) e^{-u/2} du (paperFT_I_half below), the pole-free condition of
  RvMBridge31.PrimeFreeWindowPositivityPoleFree.  The operator annihilating that functional is
      (Q h)(u) = h'(u) - h(u)/2,
  because paperFT (Q h) z = -(I z + 1/2) paperFT h z (paperFT_lift) and I (I/2) + 1/2 = 0.
  CC write g = h/2 - h' (the opposite sign); |.|^2 identities are insensitive to it.

  THEOREMS (all for IsWeilTest tests, tsupport ⊆ Icc (-L) L; statements in the module):
    (a) poleFree_iff_exists_lift : paperFT g (I/2) = 0 ↔ ∃ h, IsWeilTest h ∧
          tsupport h ⊆ Icc (-L) L ∧ ∀ u, g u = deriv h u - h u / 2.
        The witness is qLift g L u = e^{u/2} ∫_{-L}^u g(t) e^{-t/2} dt (smooth by FTC; it vanishes
        for u ≤ -L trivially and for u ≥ L exactly because ∫ g e^{-t/2} = 0).
        lift_unique: the lift is unique (h' = h/2 with compact support forces h = 0).
        isWeilTest_of_lift / tsupport_of_lift: conversely every Q h is a window test.
    (b) hsq_lift : hsq g r = (r^2 + 1/4) * hsq h r, i.e. |ĝ(r)|^2 = (r^2 + 1/4) |ĥ(r)|^2,
        integral_lift : ∫ g = -(1/2) ∫ h  (so CC's extra condition ĝ(0) = 0 is ∫ h = 0).
    (c) poles_vanish_of_lift : both pole terms weilKernel (autocorr g) 0 and 1 vanish;
        archSide_autocorr_lift : archSide (autocorr g) = -mass g · log π
          + (1/2π) ∫ (r^2 + 1/4) |ĥ(r)|^2 psiR(r) dr.

  Nothing here involves the zeros; no RH progress.  conjecture1_proved = False.
-/
import E6Bridge31

open Zeta23 Complex MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace ArchS2
open WeilExplicit RvMBridge11 RvMBridge31

/-! ## A. The tilted test and the convention check. -/

/-- The tilted test φ_g(t) = g(t) e^{-t/2}. -/
def tilt (g : ℝ → ℂ) (t : ℝ) : ℂ := g t * Complex.exp (-(t : ℂ) / 2)

/-- The pole functional in the project convention: paperFT g (I/2) = ∫ g(t) e^{-t/2} dt. -/
lemma paperFT_I_half (g : ℝ → ℂ) : paperFT g (I / 2) = ∫ t : ℝ, tilt g t := by
  unfold paperFT tilt
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  congr 2
  rw [show I * (I / 2) * (t : ℂ) = (I * I) * t / 2 by ring, I_mul_I]
  ring

/-- paperFT f 0 = ∫ f. -/
lemma paperFT_zero (f : ℝ → ℂ) : paperFT f 0 = ∫ t : ℝ, f t := by
  unfold paperFT
  simp

lemma contDiff_expHalf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun u : ℝ => Complex.exp ((u : ℂ) / 2) :=
  (Complex.ofRealCLM.contDiff.div_const (2 : ℂ)).cexp

lemma contDiff_expNegHalf :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun u : ℝ => Complex.exp (-(u : ℂ) / 2) :=
  (Complex.ofRealCLM.contDiff.neg.div_const (2 : ℂ)).cexp

lemma contDiff_tilt {g : ℝ → ℂ} (hg : IsWeilTest g) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (tilt g) :=
  hg.1.mul contDiff_expNegHalf

lemma continuous_tilt {g : ℝ → ℂ} (hg : IsWeilTest g) : Continuous (tilt g) :=
  (contDiff_tilt hg).continuous

lemma hasDerivAt_expHalf (u : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.exp ((u : ℂ) / 2)) (Complex.exp ((u : ℂ) / 2) / 2) u := by
  have h := ((hasDerivAt_id u).ofReal_comp.div_const (2 : ℂ)).cexp
  refine h.congr_deriv ?_
  simp only [id_eq, Complex.ofReal_one]
  ring

lemma expHalf_mul_expNegHalf (u : ℝ) :
    Complex.exp ((u : ℂ) / 2) * Complex.exp (-(u : ℂ) / 2) = 1 := by
  rw [← Complex.exp_add, show (u : ℂ) / 2 + -(u : ℂ) / 2 = 0 by ring, Complex.exp_zero]

/-! ## B. The lift h(u) = e^{u/2} ∫_{-L}^u g(t) e^{-t/2} dt. -/

/-- The primitive of the tilted test from -L. -/
def tiltPrim (g : ℝ → ℂ) (L : ℝ) (u : ℝ) : ℂ := ∫ t in (-L)..u, tilt g t

/-- The pole-free lift (CC Lemma 3.3 in our variable). -/
def qLift (g : ℝ → ℂ) (L : ℝ) (u : ℝ) : ℂ := Complex.exp ((u : ℂ) / 2) * tiltPrim g L u

lemma hasDerivAt_tiltPrim {g : ℝ → ℂ} (hg : IsWeilTest g) (L u : ℝ) :
    HasDerivAt (tiltPrim g L) (tilt g u) u :=
  ((continuous_tilt hg).integral_hasStrictDerivAt (-L) u).hasDerivAt

lemma deriv_tiltPrim {g : ℝ → ℂ} (hg : IsWeilTest g) (L : ℝ) : deriv (tiltPrim g L) = tilt g :=
  funext fun u => (hasDerivAt_tiltPrim hg L u).deriv

lemma contDiff_tiltPrim {g : ℝ → ℂ} (hg : IsWeilTest g) (L : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (tiltPrim g L) := by
  rw [contDiff_infty_iff_deriv, deriv_tiltPrim hg]
  exact ⟨fun u => (hasDerivAt_tiltPrim hg L u).differentiableAt, contDiff_tilt hg⟩

/-- h' = h/2 + g. -/
lemma hasDerivAt_qLift {g : ℝ → ℂ} (hg : IsWeilTest g) (L u : ℝ) :
    HasDerivAt (qLift g L) (qLift g L u / 2 + g u) u := by
  refine ((hasDerivAt_expHalf u).mul (hasDerivAt_tiltPrim hg L u)).congr_deriv ?_
  unfold qLift tilt
  have := expHalf_mul_expNegHalf u
  linear_combination (g u) * this

/-- The defining relation g = h' - h/2. -/
lemma qLift_rel {g : ℝ → ℂ} (hg : IsWeilTest g) (L u : ℝ) :
    g u = deriv (qLift g L) u - qLift g L u / 2 := by
  rw [(hasDerivAt_qLift hg L u).deriv]
  ring

/-- The tilted test vanishes off [-L, L]. -/
lemma tilt_eq_zero_of_not_mem {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) {t : ℝ} (ht : t ≤ -L ∨ L ≤ t) : tilt g t = 0 := by
  unfold tilt
  rcases ht with ht | ht
  · rw [eq_zero_of_tsupport_subset_Icc_left hg.1.continuous hsupp ht, zero_mul]
  · rw [eq_zero_of_tsupport_subset_Icc_right hg.1.continuous hsupp ht, zero_mul]

/-- Left of the window the lift vanishes (no hypothesis needed). -/
lemma qLift_eq_zero_left {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) {u : ℝ} (hu : u ≤ -L) : qLift g L u = 0 := by
  unfold qLift tiltPrim
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)), intervalIntegral.integral_zero,
    mul_zero]
  intro t ht
  rw [Set.uIcc_of_ge hu] at ht
  exact tilt_eq_zero_of_not_mem hg hsupp (Or.inl ht.2)

/-- Right of the window the primitive is the full pole integral. -/
lemma tiltPrim_eq_right {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) {u : ℝ} (hu : L ≤ u) (hu' : -L ≤ u) :
    tiltPrim g L u = paperFT g (I / 2) := by
  unfold tiltPrim
  rw [paperFT_I_half, intervalIntegral.integral_of_le hu']
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_
  rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at ht
  rcases ht with ht | ht
  · exact tilt_eq_zero_of_not_mem hg hsupp (Or.inl ht)
  · exact tilt_eq_zero_of_not_mem hg hsupp (Or.inr (hu.trans ht.le))

/-- Right of the window the lift vanishes exactly under the pole-free condition. -/
lemma qLift_eq_zero_right {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) (h0 : paperFT g (I / 2) = 0) {u : ℝ} (hu : L ≤ u) :
    qLift g L u = 0 := by
  by_cases hu' : u ≤ -L
  · exact qLift_eq_zero_left hg hsupp hu'
  · unfold qLift
    rw [tiltPrim_eq_right hg hsupp hu (le_of_lt (not_le.mp hu')), h0, mul_zero]

lemma tsupport_qLift {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) (h0 : paperFT g (I / 2) = 0) :
    tsupport (qLift g L) ⊆ Set.Icc (-L) L := by
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  rw [Function.mem_support] at hu
  constructor
  · by_contra h
    exact hu (qLift_eq_zero_left hg hsupp (le_of_lt (not_le.mp h)))
  · by_contra h
    exact hu (qLift_eq_zero_right hg hsupp h0 (le_of_lt (not_le.mp h)))

lemma isWeilTest_qLift {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) (h0 : paperFT g (I / 2) = 0) :
    IsWeilTest (qLift g L) :=
  ⟨contDiff_expHalf.mul (contDiff_tiltPrim hg L),
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (tsupport_qLift hg hsupp h0)⟩

/-! ## C. The transform of Q h, and the converse direction. -/

/-- A continuous compactly supported f times the phase e^{i z u} is integrable. -/
lemma integrable_mul_phase {f : ℝ → ℂ} (hf : Continuous f) (hcs : HasCompactSupport f) (z : ℂ) :
    Integrable (fun u : ℝ => f u * Complex.exp (I * z * (u : ℂ))) :=
  (hf.mul (continuous_const.mul Complex.continuous_ofReal).cexp).integrable_of_hasCompactSupport
    hcs.mul_right

lemma hasDerivAt_phase (z : ℂ) (u : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.exp (I * z * (u : ℂ)))
      (Complex.exp (I * z * (u : ℂ)) * (I * z)) u := by
  refine (((hasDerivAt_id u).ofReal_comp.const_mul (I * z)).cexp).congr_deriv ?_
  simp

lemma differentiable_of_test {h : ℝ → ℂ} (hh : IsWeilTest h) : Differentiable ℝ h :=
  (contDiff_infty_iff_deriv.1 hh.1).1

lemma contDiff_deriv_of_test {h : ℝ → ℂ} (hh : IsWeilTest h) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv h) :=
  (contDiff_infty_iff_deriv.1 hh.1).2

/-- Integration by parts in the project convention: paperFT h' z = -(i z) paperFT h z. -/
theorem paperFT_deriv {h : ℝ → ℂ} (hh : IsWeilTest h) (z : ℂ) :
    paperFT (deriv h) z = -(I * z) * paperFT h z := by
  have hcd := (contDiff_deriv_of_test hh).continuous
  have h1 := integrable_mul_phase hcd hh.2.deriv z
  have h2 := integrable_mul_phase hh.1.continuous hh.2 z
  have key := integral_eq_zero_of_hasDerivAt_of_integrable
    (f := fun u : ℝ => h u * Complex.exp (I * z * (u : ℂ)))
    (f' := fun u : ℝ => deriv h u * Complex.exp (I * z * (u : ℂ))
      + h u * Complex.exp (I * z * (u : ℂ)) * (I * z))
    (fun u => (((differentiable_of_test hh) u).hasDerivAt.mul (hasDerivAt_phase z u)).congr_deriv
      (by ring))
    (h1.add (h2.mul_const _)) h2
  rw [integral_add h1 (h2.mul_const _), integral_mul_const] at key
  unfold paperFT
  linear_combination key

/-- The Q-trick on the transform: if g = h' - h/2 then paperFT g z = -(i z + 1/2) paperFT h z. -/
theorem paperFT_lift {g h : ℝ → ℂ} (hh : IsWeilTest h) (hgh : ∀ u, g u = deriv h u - h u / 2)
    (z : ℂ) : paperFT g z = -(I * z + 1 / 2) * paperFT h z := by
  have hcd := (contDiff_deriv_of_test hh).continuous
  have h1 := integrable_mul_phase hcd hh.2.deriv z
  have h2 := integrable_mul_phase hh.1.continuous hh.2 z
  have hsplit : paperFT g z = paperFT (deriv h) z - paperFT h z / 2 := by
    unfold paperFT
    rw [← integral_div, ← integral_sub h1 (h2.div_const 2)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hgh u]
    ring
  rw [hsplit, paperFT_deriv hh]
  ring

/-- Q h annihilates the pole functional. -/
theorem poleFree_of_lift {g h : ℝ → ℂ} (hh : IsWeilTest h) (hgh : ∀ u, g u = deriv h u - h u / 2) :
    paperFT g (I / 2) = 0 := by
  rw [paperFT_lift hh hgh, show I * (I / 2) + 1 / 2 = (I * I + 1) / 2 by ring, I_mul_I]
  simp

/-- Q h is supported inside the closed support of h. -/
theorem tsupport_lift_subset {g h : ℝ → ℂ} (hgh : ∀ u, g u = deriv h u - h u / 2) :
    tsupport g ⊆ tsupport h := by
  refine closure_minimal (fun u hu => ?_) (isClosed_tsupport h)
  by_contra hu'
  have hd : u ∉ tsupport (deriv h) := fun hm => hu' (tsupport_deriv_subset hm)
  apply hu
  rw [hgh u, image_eq_zero_of_notMem_tsupport hd, image_eq_zero_of_notMem_tsupport hu']
  simp

/-- Q h is again a test function. -/
theorem isWeilTest_of_lift {g h : ℝ → ℂ} (hh : IsWeilTest h)
    (hgh : ∀ u, g u = deriv h u - h u / 2) : IsWeilTest g := by
  refine ⟨?_, IsCompact.of_isClosed_subset hh.2 (isClosed_tsupport _) (tsupport_lift_subset hgh)⟩
  rw [show g = fun u => deriv h u - h u / 2 from funext hgh]
  exact (contDiff_deriv_of_test hh).sub (hh.1.div_const 2)

/-- Q h is supported in the window when h is. -/
theorem tsupport_of_lift {g h : ℝ → ℂ} (hgh : ∀ u, g u = deriv h u - h u / 2) {L : ℝ}
    (hsupp : tsupport h ⊆ Set.Icc (-L) L) : tsupport g ⊆ Set.Icc (-L) L :=
  (tsupport_lift_subset hgh).trans hsupp

/-- **(a) CC Lemma 3.3 in our variable.**  A window test is pole-free iff it is Q h = h' - h/2 of a
window test h. -/
theorem poleFree_iff_exists_lift {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) :
    paperFT g (I / 2) = 0 ↔
      ∃ h : ℝ → ℂ, IsWeilTest h ∧ tsupport h ⊆ Set.Icc (-L) L ∧
        ∀ u, g u = deriv h u - h u / 2 :=
  ⟨fun h0 => ⟨qLift g L, isWeilTest_qLift hg hsupp h0, tsupport_qLift hg hsupp h0,
      qLift_rel hg L⟩,
    fun ⟨_, hh, _, hgh⟩ => poleFree_of_lift hh hgh⟩

lemma hasDerivAt_expNegHalf (u : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.exp (-(u : ℂ) / 2)) (Complex.exp (-(u : ℂ) / 2) * (-1 / 2)) u := by
  refine (((hasDerivAt_id u).ofReal_comp.neg.div_const (2 : ℂ)).cexp).congr_deriv ?_
  simp only [id_eq, Complex.ofReal_one, Pi.neg_apply]

/-- The lift is unique: Q is injective on compactly supported smooth functions. -/
theorem lift_unique {g h₁ h₂ : ℝ → ℂ} (hh₁ : IsWeilTest h₁) (hh₂ : IsWeilTest h₂)
    (hgh₁ : ∀ u, g u = deriv h₁ u - h₁ u / 2) (hgh₂ : ∀ u, g u = deriv h₂ u - h₂ u / 2) :
    h₁ = h₂ := by
  set K : ℝ → ℂ := fun u => (h₁ u - h₂ u) * Complex.exp (-(u : ℂ) / 2) with hK
  have hKd : ∀ u, HasDerivAt K 0 u := by
    intro u
    refine ((((differentiable_of_test hh₁) u).hasDerivAt.sub
      ((differentiable_of_test hh₂) u).hasDerivAt).mul (hasDerivAt_expNegHalf u)).congr_deriv ?_
    have := (hgh₁ u).symm.trans (hgh₂ u)
    simp only [Pi.sub_apply]
    linear_combination (Complex.exp (-(u : ℂ) / 2)) * this
  have hconst := is_const_of_deriv_eq_zero (fun u => (hKd u).differentiableAt)
    (fun u => (hKd u).deriv)
  obtain ⟨y, hy⟩ := (Set.ne_univ_iff_exists_notMem _).1
    (hh₁.2.isCompact.union hh₂.2.isCompact).ne_univ
  have hy₁ : h₁ y = 0 := image_eq_zero_of_notMem_tsupport fun hm => hy (Or.inl hm)
  have hy₂ : h₂ y = 0 := image_eq_zero_of_notMem_tsupport fun hm => hy (Or.inr hm)
  funext x
  have hx : K x = 0 := by rw [hconst x y, hK]; simp [hy₁, hy₂]
  rw [hK] at hx
  simp only [mul_eq_zero, Complex.exp_ne_zero, or_false] at hx
  exact sub_eq_zero.mp hx

/-! ## D. (b) the transform identities. -/

/-- **(b)** |ĝ(r)|^2 = (r^2 + 1/4) |ĥ(r)|^2 on the real line (project convention paperFT). -/
theorem hsq_lift {g h : ℝ → ℂ} (hh : IsWeilTest h) (hgh : ∀ u, g u = deriv h u - h u / 2)
    (r : ℝ) : hsq g r = (r ^ 2 + 1 / 4) * hsq h r := by
  have hn : ‖-(I * (r : ℂ) + 1 / 2)‖ ^ 2 = r ^ 2 + 1 / 4 := by
    rw [norm_neg, Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  unfold hsq
  rw [paperFT_lift hh hgh, norm_mul, mul_pow, hn]

/-- **(b)** ∫ g = -(1/2) ∫ h. -/
theorem integral_lift {g h : ℝ → ℂ} (hh : IsWeilTest h) (hgh : ∀ u, g u = deriv h u - h u / 2) :
    ∫ u : ℝ, g u = -(1 / 2) * ∫ u : ℝ, h u := by
  rw [← paperFT_zero, ← paperFT_zero, paperFT_lift hh hgh]
  simp

/-- CC's second condition ĝ(0) = 0 is ∫ h = 0 (the constant direction). -/
theorem paperFT_zero_lift_iff {g h : ℝ → ℂ} (hh : IsWeilTest h)
    (hgh : ∀ u, g u = deriv h u - h u / 2) :
    paperFT g 0 = 0 ↔ ∫ u : ℝ, h u = 0 := by
  rw [paperFT_zero, integral_lift hh hgh]
  constructor
  · intro h0
    linear_combination (-2 : ℂ) * h0
  · intro h0
    rw [h0, mul_zero]

/-! ## E. (c) both pole terms vanish; the archimedean side in terms of h. -/

/-- **(c)** One condition kills both pole terms of weilForm (autocorr g): for g = Q h,
h(i/2) = ĝ(i/2) conj ĝ(-i/2) = 0 and h(-i/2) = ĝ(-i/2) conj ĝ(i/2) = 0. -/
theorem poles_vanish_of_lift {g h : ℝ → ℂ} (hh : IsWeilTest h)
    (hgh : ∀ u, g u = deriv h u - h u / 2) :
    weilKernel (autocorr g) 0 = 0 ∧ weilKernel (autocorr g) 1 = 0 :=
  poles_vanish (isWeilTest_of_lift hh hgh) (poleFree_of_lift hh hgh)

/-- **(c)** On the pole-free class the archimedean side of the autocorrelation, written in h:
archSide (g * g~) = -‖g‖^2 log π + (1/2π) ∫ (r^2 + 1/4) |ĥ(r)|^2 psiR(r) dr. -/
theorem archSide_autocorr_lift {g h : ℝ → ℂ} (hh : IsWeilTest h)
    (hgh : ∀ u, g u = deriv h u - h u / 2) :
    archSide (autocorr g) = -(mass g : ℂ) * (Real.log Real.pi : ℂ)
      + (1 / (2 * (Real.pi : ℂ))) * ((∫ r : ℝ, (r ^ 2 + 1 / 4) * hsq h r * psiR r : ℝ) : ℂ) := by
  rw [archSide_autocorr_poleFree (isWeilTest_of_lift hh hgh) (poleFree_of_lift hh hgh)]
  congr 4
  funext r
  rw [hsq_lift hh hgh]

/-- **(c), window form.**  For a window test g, pole-free, both pole terms of
weilForm (autocorr g) vanish and the archimedean side is the lift integral. -/
theorem poleFree_window_lift {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) (h0 : paperFT g (I / 2) = 0) :
    weilKernel (autocorr g) 0 = 0 ∧ weilKernel (autocorr g) 1 = 0 ∧
      archSide (autocorr g) = -(mass g : ℂ) * (Real.log Real.pi : ℂ)
        + (1 / (2 * (Real.pi : ℂ))) *
          ((∫ r : ℝ, (r ^ 2 + 1 / 4) * hsq (qLift g L) r * psiR r : ℝ) : ℂ) :=
  ⟨(poles_vanish hg h0).1, (poles_vanish hg h0).2,
    archSide_autocorr_lift (isWeilTest_qLift hg hsupp h0) (qLift_rel hg L)⟩

end ArchS2
