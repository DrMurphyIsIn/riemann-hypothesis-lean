/-
  RvMBridgeXi -- the PRELUDE of the xi / partial-fraction cluster (E6Bridge15 .. E6Bridge24),
  2026-09-22.  The cluster was written by parallel agents against the E6Bridge18 interface and
  re-proved its shared vocabulary in several modules (telperion/docs/SHAPES_AUDIT_48H_2026-09-22.md
  section 4, rows 1-8 and 11-12, proposal P1; SHAPES_AUDIT_C section 5.2).  This module holds ONE
  copy of each such helper; E6Bridge17, 19, 20, 21, 22 and 24 import it and their copies are gone.

    A. xi facts: xi (1 - s) = xi s, xi 0 = xi 1 = 1/2, xi analytic, xi s = 0 <-> s is a nontrivial
       zero (formerly in E6Bridge19 AND E6Bridge20); the zero set is closed and a non-zero has a
       zero-free neighbourhood (formerly RvMBridge19.zeroSet_closed AND RvMBridge24.isClosed_zeros).
    B. logDeriv xi: analyticity off the zeros (the generic analyticAt_logDeriv, formerly
       E6Bridge20), the antisymmetry logDeriv xi (1 - s) = -logDeriv xi s and its derivative form
       (formerly E6Bridge19 AND E6Bridge20), the divisor involution rho -> 1 - rho (oneSubEquiv,
       zeroMult_one_sub, formerly E6Bridge19 AND E6Bridge20) and the reindexing of the double-pole
       sum (tsum_zero_series_one_sub / tsum_polTerm_one_sub, formerly E6Bridge19 / E6Bridge20),
       through the generic tsum_reindex_zeroMult.
    C. The local unit factor: on a punctured ball where f = (z - s0)^m u with u analytic and
       nonvanishing, logDeriv f z = m/(z - s0) + logDeriv u z (logDeriv_of_unit_factor; formerly
       inlined in E6Bridge20's deriv_logDeriv_xi_local AND E6Bridge24's logDeriv_xi_local).
    D. The zero-sum majorant atom: a finite-support part on a centred ordinate window
       |Im rho - a| < h plus the local-count majorant m(rho) C/(1 + |gamma_rho|^2) (zeroBoundAt,
       generalised from E6Bridge19's window |Im rho| < 1; zeroBound is that specialisation, with
       E6Bridge19's statements verbatim), and the strip inequalities
       1/|rho|^2 <= 1/(Im rho)^2 <= (9/4)/(1 + |gamma_rho|^2) on a nontrivial zero with |Im rho| >= 1
       (formerly two lemmas of E6Bridge19; E6Bridge15 proves the same bound inline).
    E. The zero set is countable (formerly RvMBridge19.zeros_countable AND
       RvMBridge17.nontrivialZeros_countable).
    F. Discipline atoms: a punctured identity plus continuity of both sides gives the identity at
       the point (eq_of_continuousAt_of_eventually_ne, hoisted from E6Bridge19); the punctured-limit
       extension across an exceptional set is locally the analytic function
       (ext_eventuallyEq_of_punctured / differentiableAt_of_punctured, the shape of E6Bridge20's
       xiDiffExt and E6Bridge24's FwinExt); a radius avoiding finitely many values
       (exists_mem_Ioo_notMem_finset); a bound of a continuous function on a closed rectangle
       (exists_bound_on_reProdIm).

  Rows 9 and 10 of the audit table (the LSeries term comparison and the termwise derivative of
  logDeriv xi on Re s > 1, real versus complex argument) are consolidated in E6Bridge21, not here:
  E6Bridge21's node xi_logDeriv_deriv_decay consumes the real form, so a prelude holding the complex
  form would need E6Bridge21's digamma / LSeries machinery and E6Bridge21 could not import it back.
  E6Bridge15 and E6Bridge18 are upstream of this module (it uses their vocabulary), so their
  hand-written majorants (liBound, polBound) and E6Bridge15's inline 9/4 inequality are not rewired;
  the atom here is the one an emitter should target.

  Every declaration here is a helper: no registry node statement lives in this module, and no node
  theorem was moved, renamed or re-stated (each stays verbatim in its own artifact file).
  Nothing here says anything about whether RH holds.  conjecture1_proved = False.
-/
import E6Bridge15
import E6Bridge18

open Zeta23 Complex MeasureTheory Filter Topology Metric
open scoped ComplexConjugate

noncomputable section

namespace RvMBridgeXi
open WeilExplicit RvMBridge18

/-! ## A. The entire function xi: the reflection, the values at 0 and 1, the zero set. -/

theorem xi_one_sub (s : ℂ) : xi (1 - s) = xi s := by
  unfold xi
  rw [completedRiemannZeta₀_one_sub]
  ring

lemma xi_zero : xi 0 = 1 / 2 := by simp [xi]
lemma xi_one : xi 1 = 1 / 2 := by simp [xi]

lemma xi_analyticAt (s : ℂ) : AnalyticAt ℂ xi s :=
  xi_differentiable.analyticAt s

/-- xi vanishes exactly at the nontrivial zeros of zeta. -/
theorem xi_eq_zero_iff (s : ℂ) : xi s = 0 ↔ IsNontrivialZero s := by
  by_cases hs0 : s = 0
  · subst hs0; simp [xi_zero, IsNontrivialZero]
  by_cases hs1 : s = 1
  · subst hs1; simp [xi_one, IsNontrivialZero]
  rw [xi_eq s hs0 hs1, mul_eq_zero, ← RvM.completedRiemannZeta_eq_zero_iff]
  have : s * (s - 1) / 2 ≠ 0 := by
    have := sub_ne_zero.mpr hs1
    simp [hs0, this]
  simp [this]

lemma xi_ne_zero_of_not_nontrivial {s : ℂ} (h : ¬ IsNontrivialZero s) : xi s ≠ 0 :=
  fun h0 => h ((xi_eq_zero_iff s).mp h0)

/-- The zero set is closed (the preimage of 0 under the entire function xi). -/
lemma isClosed_zeros : IsClosed {w : ℂ | IsNontrivialZero w} := by
  have : {w : ℂ | IsNontrivialZero w} = xi ⁻¹' {0} := by
    ext w
    simp [xi_eq_zero_iff]
  rw [this]
  exact isClosed_singleton.preimage xi_differentiable.continuous

/-- A point that is not a nontrivial zero has a zero-free neighbourhood. -/
lemma eventually_not_zero {w₀ : ℂ} (h : ¬ IsNontrivialZero w₀) :
    ∀ᶠ w in 𝓝 w₀, ¬ IsNontrivialZero w :=
  isClosed_zeros.isOpen_compl.mem_nhds (show w₀ ∈ {w : ℂ | IsNontrivialZero w}ᶜ from h)

/-! ## B. logDeriv xi: analyticity off the zeros, the antisymmetry under s -> 1 - s, the
divisor involution rho -> 1 - rho and the reindexing of the double-pole sum. -/

/-- logDeriv of an analytic nonvanishing function is analytic. -/
lemma analyticAt_logDeriv {u : ℂ → ℂ} {z : ℂ} (hu : AnalyticAt ℂ u z) (hz : u z ≠ 0) :
    AnalyticAt ℂ (logDeriv u) z := by
  have : logDeriv u = fun w => deriv u w / u w := funext fun w => logDeriv_apply u w
  rw [this]
  exact hu.deriv.div hu hz

lemma logDeriv_xi_analyticAt {s : ℂ} (h : xi s ≠ 0) : AnalyticAt ℂ (logDeriv xi) s :=
  analyticAt_logDeriv (xi_analyticAt s) h

lemma hasDerivAt_logDeriv_xi {s : ℂ} (h : xi s ≠ 0) :
    HasDerivAt (logDeriv xi) (deriv (logDeriv xi) s) s :=
  (logDeriv_xi_analyticAt h).differentiableAt.hasDerivAt

/-- The antisymmetry logDeriv xi (1 - s) = -logDeriv xi s, everywhere (xi entire, xi(1-s) = xi(s)). -/
theorem logDeriv_xi_one_sub (s : ℂ) : logDeriv xi (1 - s) = -logDeriv xi s := by
  have hcomp : xi = xi ∘ (fun u : ℂ => 1 - u) := by
    funext u; simp [Function.comp, xi_one_sub]
  have hd : DifferentiableAt ℂ xi (1 - s) := xi_differentiable _
  have hg : DifferentiableAt ℂ (fun u : ℂ => 1 - u) s :=
    (differentiableAt_const _).sub differentiableAt_id
  have key := logDeriv_comp (x := s) hd hg
  rw [← hcomp] at key
  have hderiv : deriv (fun u : ℂ => 1 - u) s = -1 := by
    rw [deriv_const_sub, deriv_id'']
  rw [key, hderiv]
  ring

/-- deriv (logDeriv xi) is symmetric under s -> 1 - s off the zeros. -/
lemma deriv_logDeriv_xi_one_sub {s : ℂ} (hz : ¬ IsNontrivialZero s) :
    deriv (logDeriv xi) (1 - s) = deriv (logDeriv xi) s := by
  have hx : xi (1 - s) ≠ 0 := by rw [xi_one_sub, Ne, xi_eq_zero_iff]; exact hz
  have hcomp : HasDerivAt (fun u => logDeriv xi (1 - u)) (deriv (logDeriv xi) (1 - s) * (0 - 1)) s :=
    (hasDerivAt_logDeriv_xi hx).comp s ((hasDerivAt_const s (1 : ℂ)).sub (hasDerivAt_id s))
  have h : HasDerivAt (logDeriv xi) (-(deriv (logDeriv xi) (1 - s) * (0 - 1))) s := by
    refine hcomp.neg.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    show logDeriv xi u = -logDeriv xi (1 - u)
    rw [logDeriv_xi_one_sub, neg_neg]
  rw [h.deriv]
  ring

/-- The map u -> 1 - u as an involutive equivalence. -/
def oneSubEquiv : ℂ ≃ ℂ where
  toFun u := 1 - u
  invFun u := 1 - u
  left_inv u := by simp
  right_inv u := by simp

/-- The divisor is symmetric under rho -> 1 - rho (reflection composed with conjugation). -/
lemma zeroMult_one_sub (ρ : ℂ) : WeilExplicit.zeroMult (1 - ρ) = WeilExplicit.zeroMult ρ := by
  have h : (1 - ρ) = reflect (conj ρ) := by
    unfold reflect; rw [Complex.conj_conj]
  rw [h, RvMBridge6.zeroMult_reflect, RvMBridge15.zeroMult_conj]

/-- Reindexing a divisor-weighted zero sum along an equivalence that preserves the divisor. -/
lemma tsum_reindex_zeroMult (e : ℂ ≃ ℂ)
    (hm : ∀ ρ, WeilExplicit.zeroMult (e ρ) = WeilExplicit.zeroMult ρ) (F : ℕ → ℂ → ℂ) :
    ∑' ρ : ℂ, F (WeilExplicit.zeroMult ρ) (e ρ) = ∑' ρ : ℂ, F (WeilExplicit.zeroMult ρ) ρ :=
  calc ∑' ρ : ℂ, F (WeilExplicit.zeroMult ρ) (e ρ)
      = ∑' ρ : ℂ, F (WeilExplicit.zeroMult (e ρ)) (e ρ) := tsum_congr fun ρ => by rw [hm]
    _ = ∑' ρ : ℂ, F (WeilExplicit.zeroMult ρ) ρ := e.tsum_eq fun ρ => F (WeilExplicit.zeroMult ρ) ρ

/-- The double-pole zero series is symmetric under s -> 1 - s. -/
lemma tsum_zero_series_one_sub (s : ℂ) :
    ∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / ((1 - s) - ρ) ^ 2
      = ∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2 := by
  have hm : ∀ ρ, WeilExplicit.zeroMult (oneSubEquiv ρ) = WeilExplicit.zeroMult ρ := fun ρ =>
    zeroMult_one_sub ρ
  refine Eq.trans (tsum_reindex_zeroMult oneSubEquiv hm
    fun m ρ => (m : ℂ) / ((1 - s) - ρ) ^ 2).symm ?_
  refine tsum_congr fun ρ => ?_
  simp only [oneSubEquiv, Equiv.coe_fn_mk]
  congr 1
  ring

/-- The same, in E6Bridge18's polTerm vocabulary. -/
lemma tsum_polTerm_one_sub (s : ℂ) : ∑' ρ : ℂ, polTerm (1 - s) ρ = ∑' ρ : ℂ, polTerm s ρ :=
  tsum_zero_series_one_sub s

/-! ## C. The local unit factor: logDeriv on a punctured ball where f = (z - s0)^m u. -/

/-- On a ball about s0 where f = (z - s0)^m u with u analytic and nonvanishing, at every z of the
ball other than s0: logDeriv f z = m/(z - s0) + logDeriv u z. -/
lemma logDeriv_of_unit_factor {f u : ℂ → ℂ} {s₀ : ℂ} {m : ℕ} {ε : ℝ}
    (hxu : ∀ z, dist z s₀ < ε → f z = (z - s₀) ^ m * u z ∧ AnalyticAt ℂ u z ∧ u z ≠ 0)
    {z : ℂ} (hz : dist z s₀ < ε) (hne : z ≠ s₀) :
    logDeriv f z = (m : ℂ) * (z - s₀)⁻¹ + logDeriv u z := by
  have hz0 : z - s₀ ≠ 0 := sub_ne_zero.mpr hne
  have hev : f =ᶠ[𝓝 z] fun y => (y - s₀) ^ m * u y := by
    have hball : ∀ᶠ y in 𝓝 z, dist y s₀ < ε :=
      isOpen_ball.mem_nhds (show z ∈ ball s₀ ε from hz)
    filter_upwards [hball] with y hy
    exact (hxu y hy).1
  rw [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds, ← logDeriv_apply]
  rw [logDeriv_mul (f := fun y => (y - s₀) ^ m) (g := u) z (pow_ne_zero _ hz0) (hxu z hz).2.2
    ((differentiableAt_id.sub_const s₀).pow m) (hxu z hz).2.1.differentiableAt]
  congr 1
  rw [logDeriv_fun_pow (f := fun y => y - s₀) (differentiableAt_id.sub_const s₀) m, logDeriv_apply]
  rw [deriv_sub_const, deriv_id'']
  ring

/-! ## D. The 9/4 strip inequalities and the zero-sum majorant atom. -/

/-- On a nontrivial zero with |Im rho| >= 1: 1/(Im rho)^2 <= (9/4)/(1 + |gamma_rho|^2). -/
lemma inv_im_sq_le_majorant {ρ : ℂ} (h : IsNontrivialZero ρ) (him : 1 ≤ |ρ.im|) :
    1 / ρ.im ^ 2 ≤ (9 / 4) / (1 + Complex.normSq (gammaOf ρ)) := by
  have hγ : Complex.normSq (gammaOf ρ) = ρ.im ^ 2 + (1 / 2 - ρ.re) ^ 2 := by
    rw [Complex.normSq_apply, Zeta23.WeilEF.gammaOf_re, Zeta23.WeilEF.gammaOf_im]; ring
  have him2 : 1 ≤ ρ.im ^ 2 := by
    have := sq_abs ρ.im
    nlinarith [abs_nonneg ρ.im]
  have hre := h.2.1
  have hre1 := h.2.2
  rw [div_le_div_iff₀ (by linarith) (by linarith [Complex.normSq_nonneg (gammaOf ρ)])]
  rw [hγ]
  nlinarith

/-- On a nontrivial zero with |Im rho| >= 1: 1/|rho|^2 <= (9/4)/(1 + |gamma_rho|^2). -/
lemma inv_normSq_le_majorant {ρ : ℂ} (h : IsNontrivialZero ρ) (him : 1 ≤ |ρ.im|) :
    1 / Complex.normSq ρ ≤ (9 / 4) / (1 + Complex.normSq (gammaOf ρ)) := by
  refine le_trans ?_ (inv_im_sq_le_majorant h him)
  have him2 : 1 ≤ ρ.im ^ 2 := by
    have := sq_abs ρ.im
    nlinarith [abs_nonneg ρ.im]
  have hns : ρ.im ^ 2 ≤ Complex.normSq ρ := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg ρ.re]
  exact one_div_le_one_div_of_le (by linarith) hns

/-- The nontrivial zeros in the centred ordinate window |Im rho - a| < h. -/
def windowZeros (a h : ℝ) : Set ℂ := {ρ : ℂ | IsNontrivialZero ρ} ∩ {ρ : ℂ | |ρ.im - a| < h}

/-- Every centred window holds finitely many zeros (Zeta23 zetaSeam.finite_window). -/
lemma windowZeros_finite (a h : ℝ) : (windowZeros a h).Finite := by
  refine (zetaSeam.finite_window (a - h - 1) (a + h)).subset ?_
  rintro ρ ⟨hnt, hw⟩
  have hw' : |ρ.im - a| < h := hw
  have hab := abs_lt.mp hw'
  exact ⟨hnt, by linarith [hab.1], by linarith [hab.2]⟩

/-- The majorant shape: a finite-support part on the window |Im rho - a| < h plus the local-count
majorant m(rho) C/(1 + |gamma_rho|^2). -/
def zeroBoundAt (a h C : ℝ) (b : ℂ → ℝ) (ρ : ℂ) : ℝ :=
  (windowZeros a h).indicator b ρ
    + (WeilExplicit.zeroMult ρ : ℝ) * (C / (1 + Complex.normSq (gammaOf ρ)))

lemma summable_zeroBoundAt (a h C : ℝ) (b : ℂ → ℝ) : Summable (zeroBoundAt a h C b) := by
  unfold zeroBoundAt
  refine Summable.add ?_ (RvMBridgeGauss.summable_mult_div_one_add_normSq C)
  refine summable_of_ne_finset_zero (s := (windowZeros_finite a h).toFinset) fun ρ hρ => ?_
  rw [Set.Finite.mem_toFinset] at hρ
  exact Set.indicator_of_notMem hρ _

/-- A family vanishing off the zeros, bounded by b on the window and by the local-count majorant
off it, is bounded by the majorant shape. -/
lemma norm_le_zeroBoundAt {f : ℂ → ℂ} {a h C : ℝ} {b : ℂ → ℝ}
    (h0 : ∀ ρ, ¬ IsNontrivialZero ρ → f ρ = 0)
    (hwin : ∀ ρ, IsNontrivialZero ρ → |ρ.im - a| < h → ‖f ρ‖ ≤ b ρ)
    (hfar : ∀ ρ, IsNontrivialZero ρ → h ≤ |ρ.im - a| →
      ‖f ρ‖ ≤ (WeilExplicit.zeroMult ρ : ℝ) * (C / (1 + Complex.normSq (gammaOf ρ))))
    (hC : 0 ≤ C) (ρ : ℂ) : ‖f ρ‖ ≤ zeroBoundAt a h C b ρ := by
  unfold zeroBoundAt
  have hpos : 0 ≤ (WeilExplicit.zeroMult ρ : ℝ) * (C / (1 + Complex.normSq (gammaOf ρ))) := by
    have := Complex.normSq_nonneg (gammaOf ρ)
    positivity
  by_cases hz : IsNontrivialZero ρ
  · by_cases him : |ρ.im - a| < h
    · rw [Set.indicator_of_mem (show ρ ∈ windowZeros a h from ⟨hz, him⟩)]
      linarith [hwin ρ hz him]
    · rw [Set.indicator_of_notMem (fun hm => him hm.2), zero_add]
      exact hfar ρ hz (not_lt.mp him)
  · rw [h0 ρ hz, norm_zero]
    have hb : 0 ≤ (windowZeros a h).indicator b ρ := by
      rw [Set.indicator_of_notMem (fun hm => hz hm.1)]
    linarith

/-- Summability of a zero family from the majorant shape. -/
lemma summable_of_zeroBoundAt {f : ℂ → ℂ} {a h C : ℝ} {b : ℂ → ℝ}
    (h0 : ∀ ρ, ¬ IsNontrivialZero ρ → f ρ = 0)
    (hwin : ∀ ρ, IsNontrivialZero ρ → |ρ.im - a| < h → ‖f ρ‖ ≤ b ρ)
    (hfar : ∀ ρ, IsNontrivialZero ρ → h ≤ |ρ.im - a| →
      ‖f ρ‖ ≤ (WeilExplicit.zeroMult ρ : ℝ) * (C / (1 + Complex.normSq (gammaOf ρ))))
    (hC : 0 ≤ C) : Summable f :=
  Summable.of_norm_bounded (summable_zeroBoundAt a h C b) (norm_le_zeroBoundAt h0 hwin hfar hC)

/-- The finitely many nontrivial zeros with |Im rho| < 1 (the window of radius 1 about 0). -/
def smallZeros : Set ℂ := {ρ : ℂ | IsNontrivialZero ρ} ∩ {ρ : ℂ | |ρ.im| < 1}

lemma smallZeros_finite : smallZeros.Finite := RvMBridge15.finite_zeros_small

lemma smallZeros_eq : smallZeros = windowZeros 0 1 := by
  ext ρ
  simp [smallZeros, windowZeros]

/-- E6Bridge19's majorant: the small zeros plus the local-count majorant (zeroBoundAt 0 1). -/
def zeroBound (C : ℝ) (b : ℂ → ℝ) (ρ : ℂ) : ℝ :=
  smallZeros.indicator b ρ + (WeilExplicit.zeroMult ρ : ℝ) * (C / (1 + Complex.normSq (gammaOf ρ)))

lemma zeroBound_eq (C : ℝ) (b : ℂ → ℝ) : zeroBound C b = zeroBoundAt 0 1 C b := by
  funext ρ
  simp only [zeroBound, zeroBoundAt, smallZeros_eq]

lemma summable_zeroBound (C : ℝ) (b : ℂ → ℝ) : Summable (zeroBound C b) := by
  rw [zeroBound_eq]
  exact summable_zeroBoundAt 0 1 C b

/-- A family vanishing off the zeros, bounded by the local-count majorant on the large zeros,
is bounded by a zeroBound (with b any bound valid on the small zeros). -/
lemma norm_le_zeroBound {f : ℂ → ℂ} {C : ℝ} {b : ℂ → ℝ}
    (h0 : ∀ ρ, ¬ IsNontrivialZero ρ → f ρ = 0)
    (hsmall : ∀ ρ, IsNontrivialZero ρ → |ρ.im| < 1 → ‖f ρ‖ ≤ b ρ)
    (hlarge : ∀ ρ, IsNontrivialZero ρ → 1 ≤ |ρ.im| →
      ‖f ρ‖ ≤ (WeilExplicit.zeroMult ρ : ℝ) * (C / (1 + Complex.normSq (gammaOf ρ))))
    (hC : 0 ≤ C) (ρ : ℂ) : ‖f ρ‖ ≤ zeroBound C b ρ := by
  rw [zeroBound_eq]
  exact norm_le_zeroBoundAt h0 (fun ρ hz him => hsmall ρ hz (by simpa using him))
    (fun ρ hz him => hlarge ρ hz (by simpa using him)) hC ρ

/-- Summability of a zero family from the majorant. -/
lemma summable_of_zeroBound {f : ℂ → ℂ} {C : ℝ} {b : ℂ → ℝ}
    (h0 : ∀ ρ, ¬ IsNontrivialZero ρ → f ρ = 0)
    (hsmall : ∀ ρ, IsNontrivialZero ρ → |ρ.im| < 1 → ‖f ρ‖ ≤ b ρ)
    (hlarge : ∀ ρ, IsNontrivialZero ρ → 1 ≤ |ρ.im| →
      ‖f ρ‖ ≤ (WeilExplicit.zeroMult ρ : ℝ) * (C / (1 + Complex.normSq (gammaOf ρ))))
    (hC : 0 ≤ C) : Summable f :=
  Summable.of_norm_bounded (summable_zeroBound C b) (norm_le_zeroBound h0 hsmall hlarge hC)

/-! ## E. The zero set is countable. -/

/-- The nontrivial zeros form a countable set (a countable union of finite windows). -/
lemma nontrivialZeros_countable : {ρ : ℂ | IsNontrivialZero ρ}.Countable := by
  have h : {ρ : ℂ | IsNontrivialZero ρ}
      = ⋃ n : ℕ, ({ρ : ℂ | IsNontrivialZero ρ} ∩ {ρ : ℂ | |ρ.im| ≤ (n : ℝ)}) := by
    ext ρ
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hρ
      obtain ⟨n, hn⟩ := exists_nat_ge |ρ.im|
      exact ⟨n, hρ, hn⟩
    · rintro ⟨n, hρ, _⟩
      exact hρ
  rw [h]
  exact Set.countable_iUnion fun n => (RvMBridge15.finite_zeros_window (n : ℝ)).countable

/-! ## F. Discipline atoms: punctured identities, punctured-limit extensions, finite avoidance,
compact bounds. -/

/-- Agreement on a punctured neighbourhood plus continuity at the point gives agreement at the point. -/
lemma eq_of_continuousAt_of_eventually_ne {f g : ℂ → ℂ} {a : ℂ} (hf : ContinuousAt f a)
    (hg : ContinuousAt g a) (h : ∀ᶠ z in 𝓝 a, z ≠ a → f z = g z) : f a = g a := by
  have h1 : Tendsto f (𝓝[≠] a) (𝓝 (f a)) := hf.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto g (𝓝[≠] a) (𝓝 (g a)) := hg.tendsto.mono_left nhdsWithin_le_nhds
  have h3 : Tendsto f (𝓝[≠] a) (𝓝 (g a)) := by
    refine h2.congr' ?_
    rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
    filter_upwards [h] with z hz hza
    exact (hz hza).symm
  exact tendsto_nhds_unique h1 h3

/-- The punctured-limit extension is locally the analytic function.  Let `ext` equal `f` off the
exceptional set `P` and `limUnder (𝓝[≠] s) f` on it.  If on a ball about `s₀` there is no other
exceptional point and `f` agrees, off `s₀`, with an `H` continuous at `s₀` (and `f s₀ = H s₀` when
`s₀` is not exceptional), then `ext = H` on a neighbourhood of `s₀`. -/
lemma ext_eventuallyEq_of_punctured {P : ℂ → Prop} {f H ext : ℂ → ℂ} {s₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hext_of : ∀ s, ¬ P s → ext s = f s) (hext_lim : ∀ s, P s → ext s = limUnder (𝓝[≠] s) f)
    (hH : ContinuousAt H s₀)
    (hball : ∀ w ∈ ball s₀ r, w ≠ s₀ → ¬ P w ∧ f w = H w)
    (hat : ¬ P s₀ → f s₀ = H s₀) : ext =ᶠ[𝓝 s₀] H := by
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with w hw
  by_cases hne : w = s₀
  · subst hne
    by_cases hz : P w
    · rw [hext_lim w hz]
      apply Filter.Tendsto.limUnder_eq
      have h1 : Tendsto H (𝓝[≠] w) (𝓝 (H w)) := hH.continuousWithinAt.tendsto
      refine h1.congr' ?_
      rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz' hzne
      exact (hball z hz' hzne).2.symm
    · rw [hext_of w hz]
      exact hat hz
  · rw [hext_of w (hball w hw hne).1]
    exact (hball w hw hne).2

/-- The punctured-limit extension is differentiable at `s₀` when the local `H` is. -/
lemma differentiableAt_of_punctured {P : ℂ → Prop} {f H ext : ℂ → ℂ} {s₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hext_of : ∀ s, ¬ P s → ext s = f s) (hext_lim : ∀ s, P s → ext s = limUnder (𝓝[≠] s) f)
    (hH : DifferentiableAt ℂ H s₀)
    (hball : ∀ w ∈ ball s₀ r, w ≠ s₀ → ¬ P w ∧ f w = H w)
    (hat : ¬ P s₀ → f s₀ = H s₀) : DifferentiableAt ℂ ext s₀ :=
  (ext_eventuallyEq_of_punctured hr hext_of hext_lim hH.continuousAt hball hat).differentiableAt_iff.mpr
    hH

/-- A value in (a, b) avoiding finitely many given values. -/
lemma exists_mem_Ioo_notMem_finset {a b : ℝ} (hab : a < b) (D : Finset ℝ) :
    ∃ r ∈ Set.Ioo a b, r ∉ D :=
  (Set.Ioo_infinite hab).exists_notMem_finset D

/-- A continuous function is bounded on a closed rectangle, by a nonnegative bound. -/
lemma exists_bound_on_reProdIm {f : ℂ → ℂ} (hf : Continuous f) (a b c d : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → c ≤ s.im → s.im ≤ d → ‖f s‖ ≤ M := by
  have hK : IsCompact ((Set.Icc a b) ×ℂ (Set.Icc c d)) := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨M, hM⟩ := hK.bddAbove_image hf.norm.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun s h1 h2 h3 h4 => ?_⟩
  refine le_trans (hM ⟨s, ?_, rfl⟩) (le_max_left _ _)
  exact Complex.mem_reProdIm.mpr ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩

end RvMBridgeXi
