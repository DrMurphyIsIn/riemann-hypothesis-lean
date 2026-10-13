/-
  KWin_Split -- the Zhu frequency split of the Weil form on the prime-free window, in the sector
  form consumed by the KWin certificate (rvm_bridge island, 2026-09-24).

  conjecture1_proved = False.  (Finite-window Weil positivity is not RH; PR #604: the 1.3e-3
  full-class margin at this window is zero content; not Connes-Consani, whose theorem is for the
  pole-free class.)

  PROVED HERE (`Q_ge_Rb`): for a real test v of parity par (v(-u) = eps v(u), eps = +1 / -1),
  smooth, compactly supported in [-L0, L0], L0 = log 2 / 2,
      Rb par v v <= Re weilForm (autocorr v)
  where Rb (KWin_Head) = 2 eps (int v poleF)^2 + beta0 int v^2 + (1/pi) int_0^20 (Psi - beta0) Tr v^2.
  Route: Zhu eq. (2) (`symbol_representation_ofReal`, PROVED in ZhuSymbol) at L = L0, where the
  comb is empty (KWin_Constants: weilSymbol L0 = Psi); the transform on the line is the sector
  transform (the other trigonometric half vanishes by parity) and the pole term is the sector
  pole functional; Plancherel (Fourier inversion of the autocorrelation at 0, as in ZhuSymbol);
  evenness in t, and Psi >= beta*(L0, 20) >= beta0 on [20, oo) (ZhuSplit + KWin_Constants).
  No `sorry`.
-/
import KWin_Head
import ZhuParity

open Real MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace KWin
open RvMBridge11 RvMBridgeZhu WeilExplicit RvMBridge4 RvMBridge5 Zeta23

/-! ## A. Support and the conversion to [-l, l]. -/

lemma v_eq_zero_of_not_mem {v : ℝ → ℝ} (hsupp : tsupport (fun u => (v u : ℂ)) ⊆ Icc (-L0) L0)
    {x : ℝ} (hx : x ∉ Icc (-L0) L0) : v x = 0 := by
  have h : (fun u => (v u : ℂ)) x = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun u => (v u : ℂ)) (fun hm => hx (hsupp hm))
  simpa using h

lemma integral_eq_interval {v : ℝ → ℝ} (hsupp : tsupport (fun u => (v u : ℂ)) ⊆ Icc (-L0) L0)
    (w : ℝ → ℝ) : ∫ x, v x * w x = ∫ x in (-ellR)..ellR, v x * w x := by
  have hlt := L0_lt_ell
  have hL0 := L0_pos
  have hle : -ellR ≤ ellR := by unfold ellR; linarith
  rw [intervalIntegral.integral_of_le hle]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
  have : x ∉ Icc (-L0) L0 := by
    intro hm
    apply hx
    rw [mem_Ioc]
    unfold ellR
    constructor
    · linarith [hm.1]
    · linarith [hm.2]
  rw [v_eq_zero_of_not_mem hsupp this, zero_mul]

lemma integral_odd_eq_zero {g : ℝ → ℝ} (h : ∀ u, g (-u) = -g u) : ∫ u, g u = 0 := by
  have h1 := integral_neg_eq_self g volume
  have h2 : ∫ x, g (-x) = -∫ x, g x := by
    rw [← integral_neg]; exact integral_congr_ae (Filter.Eventually.of_forall h)
  rw [h2] at h1
  linarith

lemma continuous_v {v : ℝ → ℝ} (hf : IsWeilTest (fun u => (v u : ℂ))) : Continuous v := by
  have h := Complex.continuous_re.comp hf.1.continuous
  have e : (Complex.re ∘ fun u => (v u : ℂ)) = v := by funext u; simp
  rwa [e] at h

lemma compact_v {v : ℝ → ℝ} (hf : IsWeilTest (fun u => (v u : ℂ))) : HasCompactSupport v := by
  have h := hf.2.comp_left (g := Complex.re) (by simp)
  have e : (Complex.re ∘ fun u => (v u : ℂ)) = v := by funext u; simp
  rwa [e] at h

lemma integrable_v_mul {v : ℝ → ℝ} (hf : IsWeilTest (fun u => (v u : ℂ))) {w : ℝ → ℝ}
    (hw : Continuous w) : Integrable (fun u => v u * w u) :=
  ((continuous_v hf).mul hw).integrable_of_hasCompactSupport (compact_v hf).mul_right

/-! ## B. The transform on the line and the pole term. -/

lemma paperFT_ofReal_line {v : ℝ → ℝ} (hf : IsWeilTest (fun u => (v u : ℂ))) (t : ℝ) :
    paperFT (fun u => (v u : ℂ)) t
      = ((∫ u, v u * Real.cos (t * u) : ℝ) : ℂ) + ((∫ u, v u * Real.sin (t * u) : ℝ) : ℂ) * Complex.I := by
  unfold paperFT
  have e : (fun u : ℝ => (v u : ℂ) * Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)))
      = fun u => ((v u * Real.cos (t * u) : ℝ) : ℂ) + ((v u * Real.sin (t * u) : ℝ) : ℂ) * Complex.I := by
    funext u
    rw [show Complex.I * (t : ℂ) * (u : ℂ) = ((t * u : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  have hc : Integrable (fun u => ((v u * Real.cos (t * u) : ℝ) : ℂ)) :=
    (integrable_v_mul hf (by fun_prop)).ofReal
  have hs : Integrable (fun u => ((v u * Real.sin (t * u) : ℝ) : ℂ) * Complex.I) :=
    ((integrable_v_mul hf (by fun_prop)).ofReal).mul_const _
  rw [e, integral_add hc hs, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal]

lemma norm_sq_line {v : ℝ → ℝ} (hf : IsWeilTest (fun u => (v u : ℂ))) (t : ℝ) :
    ‖weilKernel (fun u => (v u : ℂ)) (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2
      = (∫ u, v u * Real.cos (t * u)) ^ 2 + (∫ u, v u * Real.sin (t * u)) ^ 2 := by
  rw [weilKernel_line, paperFT_ofReal_line hf, Complex.sq_norm, Complex.normSq_add_mul_I]

/-- On the line, `|F(t)|^2` is the square of the sector transform. -/
lemma norm_sq_line_sector {v : ℝ → ℝ} {par : ℕ} (hpar : par = 0 ∨ par = 1)
    (hf : IsWeilTest (fun u => (v u : ℂ))) (hev : ∀ u, v (-u) = epsR par * v u)
    (hsupp : tsupport (fun u => (v u : ℂ)) ⊆ Icc (-L0) L0) (t : ℝ) :
    ‖weilKernel (fun u => (v u : ℂ)) (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2 = (Tr ellR par v t) ^ 2 := by
  rw [norm_sq_line hf]
  unfold Tr
  rw [← integral_eq_interval hsupp]
  rcases hpar with h | h <;> subst h
  · have hs : ∫ u, v u * Real.sin (t * u) = 0 := integral_odd_eq_zero fun u => by
      have h1 := hev u
      simp only [epsR, if_true, one_mul] at h1
      rw [h1, mul_neg, Real.sin_neg]; ring
    rw [hs]
    simp [phiF]
  · have hc : ∫ u, v u * Real.cos (t * u) = 0 := integral_odd_eq_zero fun u => by
      have h1 := hev u
      simp only [epsR, one_ne_zero, if_false] at h1
      rw [h1, mul_neg, Real.cos_neg]; ring
    rw [hc]
    simp [phiF]

lemma weilKernel_zero_ofReal (v : ℝ → ℝ) :
    weilKernel (fun u => (v u : ℂ)) 0 = ((∫ u, v u * Real.exp (-(u / 2)) : ℝ) : ℂ) := by
  unfold weilKernel
  rw [← integral_complex_ofReal]
  congr 1
  funext u
  push_cast
  congr 2
  ring

lemma exp_moment_parity {v : ℝ → ℝ} {par : ℕ} (hev : ∀ u, v (-u) = epsR par * v u) :
    ∫ u, v u * Real.exp (-(u / 2)) = epsR par * ∫ u, v u * Real.exp (u / 2) := by
  have h := integral_neg_eq_self (fun u => v u * Real.exp (-(u / 2))) volume
  rw [← h, ← integral_const_mul]
  congr 1
  funext u
  rw [hev u]
  have : -(-u / 2) = u / 2 := by ring
  rw [this]
  ring

/-- The pole term: `|F(i/2)|^2` is the square of the sector pole functional. -/
lemma K0_sq {v : ℝ → ℝ} {par : ℕ} (hpar : par = 0 ∨ par = 1)
    (hf : IsWeilTest (fun u => (v u : ℂ))) (hev : ∀ u, v (-u) = epsR par * v u)
    (hsupp : tsupport (fun u => (v u : ℂ)) ⊆ Icc (-L0) L0) :
    ‖weilKernel (fun u => (v u : ℂ)) 0‖ ^ 2 = (Pl ellR par v) ^ 2 := by
  rw [weilKernel_zero_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hE := exp_moment_parity hev
  have hPl : Pl ellR par v = ∫ u, v u * poleF par u := (integral_eq_interval hsupp _).symm
  have hi1 : Integrable (fun u => v u * Real.exp (u / 2)) := integrable_v_mul hf (by fun_prop)
  have hi2 : Integrable (fun u => v u * Real.exp (-(u / 2))) := integrable_v_mul hf (by fun_prop)
  rw [hPl]
  rcases hpar with h | h <;> subst h
  · have e : (fun u => v u * poleF 0 u)
        = fun u => (1 / 2 : ℝ) * (v u * Real.exp (u / 2) + v u * Real.exp (-(u / 2))) := by
      funext u; simp only [poleF, if_true, Real.cosh_eq]; ring
    rw [e, integral_const_mul, integral_add hi1 hi2]
    simp only [epsR, if_true, one_mul] at hE
    rw [hE]
    ring
  · have e : (fun u => v u * poleF 1 u)
        = fun u => (1 / 2 : ℝ) * (v u * Real.exp (u / 2) - v u * Real.exp (-(u / 2))) := by
      funext u; simp only [poleF, one_ne_zero, if_false, Real.sinh_eq]; ring
    rw [e, integral_const_mul, integral_sub hi1 hi2]
    simp only [epsR, one_ne_zero, if_false] at hE
    rw [hE]
    ring

/-! ## C. Plancherel and integrability. -/

theorem plancherel_ofReal {v : ℝ → ℝ} (hf : IsWeilTest (fun u => (v u : ℂ))) :
    (∫ x, v x ^ 2) = (1 / (2 * Real.pi))
      * ∫ r : ℝ, ‖weilKernel (fun u => (v u : ℂ)) (1 / 2 + (r : ℂ) * Complex.I)‖ ^ 2 := by
  set fC : ℝ → ℂ := fun u => (v u : ℂ) with hfC
  set g : ℝ → ℂ := WeilExplicit.autocorr fC with hgdef
  have hg : IsWeilTest g := isWeilTest_autocorr hf
  set F : ℝ → ℝ := fun r => ‖weilKernel fC (1 / 2 + (r : ℂ) * Complex.I)‖ ^ 2 with hF
  have hline : ∀ r : ℝ, paperFT g r = (F r : ℂ) := by
    intro r
    rw [← weilKernel_line, hgdef, weilKernel_autocorr_line hf, hF]
    simp only
    rw [weilKernel_line]
    push_cast
    ring
  have hg0 : g 0 = ((∫ x : ℝ, ‖fC x‖ ^ 2 : ℝ) : ℂ) := by
    rw [hgdef]
    unfold WeilExplicit.autocorr
    rw [← integral_complex_ofReal]
    congr 1
    funext x
    rw [sub_zero, Complex.mul_conj']
    push_cast
    ring
  have h := inversion_zero hg
  rw [hg0] at h
  have h2 : ∫ r : ℝ, paperFT g r = ((∫ r, F r : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext r
    exact hline r
  rw [h2] at h
  have h3 : ((1 / (2 * Real.pi) * ∫ r, F r : ℝ) : ℂ) = ((∫ x : ℝ, ‖fC x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact h
  have h4 := (Complex.ofReal_inj.mp h3).symm
  have e : (fun x => ‖fC x‖ ^ 2) = fun x => v x ^ 2 := by
    funext x; rw [hfC]; simp only; rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [e] at h4
  rw [h4]

theorem integrable_line_sq {v : ℝ → ℝ} (hf : IsWeilTest (fun u => (v u : ℂ))) :
    Integrable (fun r : ℝ => ‖weilKernel (fun u => (v u : ℂ)) (1 / 2 + (r : ℂ) * Complex.I)‖ ^ 2) := by
  set fC : ℝ → ℂ := fun u => (v u : ℂ)
  set g : ℝ → ℂ := WeilExplicit.autocorr fC with hgdef
  have hg : IsWeilTest g := isWeilTest_autocorr hf
  have hline : ∀ r : ℝ, paperFT g r = ((‖weilKernel fC (1 / 2 + (r : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ) := by
    intro r
    rw [← weilKernel_line, hgdef, weilKernel_autocorr_line hf]
    rw [weilKernel_line]
    push_cast
    ring
  have := (integrable_paperFT hg).re
  refine this.congr (Filter.Eventually.of_forall fun r => ?_)
  simp only [RCLike.re_to_complex]
  rw [hline r, Complex.ofReal_re]

theorem integrable_line_sq_mul_psi {v : ℝ → ℝ} (hf : IsWeilTest (fun u => (v u : ℂ))) :
    Integrable (fun r : ℝ => ‖weilKernel (fun u => (v u : ℂ)) (1 / 2 + (r : ℂ) * Complex.I)‖ ^ 2
      * psiR r) := by
  set fC : ℝ → ℂ := fun u => (v u : ℂ)
  set g : ℝ → ℂ := WeilExplicit.autocorr fC with hgdef
  have hg : IsWeilTest g := isWeilTest_autocorr hf
  have harch : ∀ r : ℝ, archIntegrand g r
      = (((‖weilKernel fC (1 / 2 + (r : ℂ) * Complex.I)‖ ^ 2) * psiR r : ℝ) : ℂ) := by
    intro r
    unfold archIntegrand
    rw [hgdef, weilKernel_autocorr_line hf]
    rw [weilKernel_line]
    unfold psiR
    push_cast
    ring
  have := (integrable_archIntegrand hg).re
  refine this.congr (Filter.Eventually.of_forall fun r => ?_)
  simp only [RCLike.re_to_complex]
  rw [harch r, Complex.ofReal_re]

/-! ## D. The split. -/

/-- The half-line split of an even integrand at `T = 20`. -/
theorem split_line {F : ℝ → ℝ} (hFi : Integrable F) (hFPi : Integrable fun t => F t * Psi t)
    (hF0 : ∀ t, 0 ≤ F t) (hFe : ∀ t, F (-t) = F t) (hFc : Continuous F) :
    (1 / Real.pi) * (∫ t in (0 : ℝ)..20, (Psi t - beta0R) * F t)
        + beta0R * ((1 / (2 * Real.pi)) * ∫ t, F t)
      ≤ (1 / (2 * Real.pi)) * ∫ t, F t * Psi t := by
  have hpi := Real.pi_pos
  have hPe : ∀ t, Psi (-t) = Psi t := fun t => by unfold Psi; rw [RvMBridge30.psiR_neg]
  have habs1 : ∫ t, F t * Psi t = 2 * ∫ t in Ioi (0 : ℝ), F t * Psi t := by
    rw [← integral_comp_abs (f := fun t => F t * Psi t)]
    congr 1; funext t
    rcases le_or_gt 0 t with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, hFe, hPe]
  have habs2 : ∫ t, F t = 2 * ∫ t in Ioi (0 : ℝ), F t := by
    rw [← integral_comp_abs (f := F)]
    congr 1; funext t
    rcases le_or_gt 0 t with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, hFe]
  have hU : Ioc (0 : ℝ) 20 ∪ Ioi 20 = Ioi 0 := Ioc_union_Ioi_eq_Ioi (by norm_num)
  have hD : Disjoint (Ioc (0 : ℝ) 20) (Ioi 20) := by
    rw [Set.disjoint_left]; intro x hx hx'; exact absurd hx.2 (not_le.mpr hx')
  have hs1 : ∫ t in Ioi (0 : ℝ), F t * Psi t
      = (∫ t in Ioc (0 : ℝ) 20, F t * Psi t) + ∫ t in Ioi (20 : ℝ), F t * Psi t := by
    rw [← hU, setIntegral_union hD measurableSet_Ioi hFPi.integrableOn hFPi.integrableOn]
  have hs2 : ∫ t in Ioi (0 : ℝ), F t
      = (∫ t in Ioc (0 : ℝ) 20, F t) + ∫ t in Ioi (20 : ℝ), F t := by
    rw [← hU, setIntegral_union hD measurableSet_Ioi hFi.integrableOn hFi.integrableOn]
  have hmono : beta0R * ∫ t in Ioi (20 : ℝ), F t ≤ ∫ t in Ioi (20 : ℝ), F t * Psi t := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hFi.integrableOn.const_mul _) hFPi.integrableOn measurableSet_Ioi
      fun t ht => ?_
    have hb := beta0_le_betaStar
    have hs := weilSymbol_ge_betaStar (L := L0) (by norm_num : (15 : ℝ) / 4 ≤ 20) (le_of_lt ht)
    rw [weilSymbol_L0] at hs
    have : beta0R ≤ Psi t := by unfold beta0R; linarith
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left this (hF0 t)
  have hIoc : ∫ t in (0 : ℝ)..20, (Psi t - beta0R) * F t
      = (∫ t in Ioc (0 : ℝ) 20, F t * Psi t) - beta0R * ∫ t in Ioc (0 : ℝ) 20, F t := by
    rw [intervalIntegral.integral_of_le (by norm_num), ← integral_const_mul,
      ← integral_sub hFPi.integrableOn (hFi.integrableOn.const_mul _)]
    congr 1; funext t; ring
  rw [hIoc, habs1, habs2, hs1, hs2]
  have e : (1 / Real.pi) = 2 * (1 / (2 * Real.pi)) := by field_simp
  rw [e]
  have hc : 0 < 1 / (2 * Real.pi) := by positivity
  nlinarith [hmono]

/-- **The split**: `Rb par v v <= Q(v)` on the window. -/
theorem Q_ge_Rb {v : ℝ → ℝ} {par : ℕ} (hpar : par = 0 ∨ par = 1)
    (hf : IsWeilTest (fun u => (v u : ℂ))) (hev : ∀ u, v (-u) = epsR par * v u)
    (hsupp : tsupport (fun u => (v u : ℂ)) ⊆ Icc (-L0) L0) :
    Rb par v v ≤ (WeilForm.weilForm (WeilForm.autocorr (fun u => (v u : ℂ)))).re := by
  have hε : epsR par * epsR par = 1 := by unfold epsR; split_ifs <;> norm_num
  rw [symbol_representation_ofReal hε hf hev hsupp]
  set F : ℝ → ℝ := fun r => ‖weilKernel (fun u => (v u : ℂ)) (1 / 2 + (r : ℂ) * Complex.I)‖ ^ 2
    with hF
  have hFT : ∀ t, F t = (Tr ellR par v t) ^ 2 := fun t => norm_sq_line_sector hpar hf hev hsupp t
  have hFc : Continuous F := by
    have : F = fun t => (Tr ellR par v t) ^ 2 := funext hFT
    rw [this]
    exact (continuous_Tr ellR par (continuous_v hf)).pow 2
  have hFi : Integrable F := integrable_line_sq hf
  have hFpsi := integrable_line_sq_mul_psi hf
  have hFPi : Integrable fun t => F t * Psi t := by
    have e : (fun t => F t * Psi t) = fun t => F t * psiR t - F t * Real.log Real.pi := by
      funext t; unfold Psi; ring
    rw [e]
    exact hFpsi.sub (hFi.mul_const _)
  have hF0 : ∀ t, 0 ≤ F t := fun t => by rw [hF]; positivity
  have hTneg : ∀ t, Tr ellR par v (-t) = (if par = 0 then (1 : ℝ) else -1) * Tr ellR par v t := by
    intro t
    unfold Tr
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    rw [show -t * x = -(t * x) by ring, phiF_neg par hpar]
    ring
  have hFe : ∀ t, F (-t) = F t := by
    intro t
    rw [hFT, hFT, hTneg, mul_pow]
    split_ifs <;> norm_num
  have hsplit := split_line hFi hFPi hF0 hFe hFc
  have e1 : (fun t : ℝ => ‖weilKernel (fun u => (v u : ℂ)) (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2
      * WeilWindow.weilSymbol L0 t) = fun t => F t * Psi t := by
    funext t; rw [weilSymbol_L0]
  rw [e1]
  have hplan := plancherel_ofReal hf
  have hip : ip ellR v v = ∫ x, v x ^ 2 := by
    unfold ip
    rw [← integral_eq_interval hsupp]
    congr 1; funext x; ring
  have hpole := K0_sq hpar hf hev hsupp
  unfold Rb
  rw [hpole, hip, hplan]
  have e2 : (fun t => (Psi t - beta0R) * (Tr ellR par v t * Tr ellR par v t))
      = fun t => (Psi t - beta0R) * F t := by funext t; rw [hFT]; ring
  rw [e2]
  have e3 : (fun r : ℝ => ‖weilKernel (fun u => (v u : ℂ)) (1 / 2 + (r : ℂ) * Complex.I)‖ ^ 2) = F := rfl
  rw [e3]
  nlinarith [hsplit]

end KWin

end
