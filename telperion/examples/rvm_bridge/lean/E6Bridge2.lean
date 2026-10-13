/-
  E6Bridge2 -- routes-roadmap critical path (2026-09-17): the RH registry node
  RH_rvm_unconditional (the CUMULATIVE Riemann--von Mangoldt formula with an O(log T)
  remainder, NO hypotheses) discharged from Anthropic's zeta-23-lean (Alpoege--Furman,
  arXiv:2608.13637; Apache-2.0; pinned in lakefile.toml).

  WHAT IS PROVED (all kernel-checked, #print axioms = [propext, Classical.choice, Quot.sound],
  see AxiomGuardRvMBridge.lean):
    * zetaZeroCount_eq_Ncount : the registry's divisor-based rectangle count equals Zeta23's
      `Ncount 0 T` (the definitional seam: `MeromorphicOn.divisor` evaluates to
      `analyticOrderAt` on the open strip, where zeta is analytic, and vanishes off zeros).
    * int_mu_cumulative : integrated Stirling on a GENERAL window `[a, b]`, `1 <= a <= b`:
      `|int_a^b mu - (M b - M a)| <= C`, `M t = (t/2pi) log(t/2pi) - t/2pi`.
    * rvm_cumulative_eventually / rvm_cumulative : `|N(0,T] - M T| <= C log T` eventually /
      for all `T >= 2` (finite range absorbed).
    * rvm_unconditional : the node statement VERBATIM.

  WHY THIS IS NOT A COROLLARY OF THE STATED UPSTREAM THEOREMS (E6 probe, Part B): zeta-23-lean
  states only the dyadic clause `|Ncount T (2T) - T/(2pi) ell1 T| <= C log T`; summing dyadic
  windows gives an O(log^2 T) cumulative remainder. The O(log T) form is re-assembled here from
  the upstream's general-window internals, as black boxes:
    Zeta23.RvM.N_eq_halfContour_completedZeta   (folded argument principle on [T1, T2])
    Zeta23.RvM.halfContour_completedZeta_split  (Lambda'/Lambda = zeta'/zeta + Gamma_R'/Gamma_R)
    Zeta23.RvM.gamma_side                       ((1/pi) Im of the Gamma_R half-contour = int mu)
    Zeta23.StirlingVert.mu_stirling             (|mu(t) - (1/2pi) log(|t|/2pi)| <= C/t^2)
    Zeta23.RvM.backlund_horizontal              (top edge, at a zero-free ordinate: O(log T))
    Zeta23.RvM.vertical_two                     (right edge: |Im| <= pi)
    Zeta23.RvM.zeta_local_zero_count            (N(t, t+1] <= A0 log(|t|+3))
    Zeta23.RvM.exists_goodHeight, Zeta23.Ncount_add, Zeta23.Ncount_mono, Zeta23.mu_smooth.
  Route: fix a zero-free ordinate T1 in [4, 5] once; for T >= T0 pick a zero-free T2 in
  [T, T+1]; N(T1,T2] = (1/pi) Im halfContour(zeta'/zeta) + int_{T1}^{T2} mu; the bottom edge at
  T1 is a fixed number, the Gamma-side is M T2 - M T1 + O(1), Backlund bounds the top edge by
  O(log T), and N(0,T2] -> N(0,T] costs one local count. The constant 7/8 of the classical
  formula is absorbed into the remainder (log T >= log 2 > 1/2).

  The definition `RvMCount.zetaZeroCount` below MIRRORS
  telperion/missions/rh/lean/Statements/RHDefs.lean (namespace RvMCount) verbatim, and the
  theorem line is the node statement of
  telperion/missions/rh/lean/Statements/RH_rvm_unconditional.lean verbatim (name and
  binder-free form), so the registry's normalized-containment grant gate matches
  (../generate.py --check).

  No RH progress is claimed: this is the classical von Mangoldt / Backlund zero-count formula
  (Titchmarsh 9.4), machine-checked. conjecture1_proved = False.
-/
import Zeta23.Unconditional

open Zeta23 Filter Complex

namespace RvMCount

-- ===== MIRROR of missions/rh/lean/Statements/RHDefs.lean (namespace RvMCount, AUTHORED) =====
noncomputable def zetaZeroCount (T : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T},
    ((MeromorphicOn.divisor riemannZeta {s : ℂ | 0 < s.re ∧ s.re < 1} : ℂ → ℤ) ρ).toNat

end RvMCount

namespace RvMBridge2

/-! ## The definitional seam: the registry's divisor count is Zeta23's `Ncount 0 T`. -/

/-- The open critical strip does not contain the pole. -/
lemma one_not_mem_strip : (1 : ℂ) ∉ {s : ℂ | 0 < s.re ∧ s.re < 1} := by
  intro h
  simp only [Set.mem_ofPred_eq, Complex.one_re] at h
  exact lt_irrefl _ h.2

/-- Pointwise: on the open strip the divisor's `toNat` is Zeta23's `zeroMult`. -/
lemma divisor_toNat_eq_zeroMult {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ((MeromorphicOn.divisor riemannZeta {s : ℂ | 0 < s.re ∧ s.re < 1} : ℂ → ℤ) ρ).toNat
      = zeroMult ρ := by
  have hA : AnalyticOnNhd ℂ riemannZeta {s : ℂ | 0 < s.re ∧ s.re < 1} :=
    Zeta23.RvM.analyticOnNhd_riemannZeta one_not_mem_strip
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hA (show ρ ∈ {s : ℂ | 0 < s.re ∧ s.re < 1} from ⟨h0, h1⟩)]
  unfold zeroMult
  induction analyticOrderAt riemannZeta ρ using ENat.recTopCoe with
  | top => simp
  | coe n => simp

/-- A strip point with nonzero `zeroMult` is a zero of zeta. -/
lemma zero_of_zeroMult_ne_zero {ρ : ℂ} (h : zeroMult ρ ≠ 0) : riemannZeta ρ = 0 := by
  by_contra hne
  apply h
  unfold zeroMult
  rw [analyticOrderAt_eq_zero.mpr (Or.inr hne)]
  rfl

/-- The registry count equals Zeta23's window count `Ncount 0 T`. -/
theorem zetaZeroCount_eq_Ncount (T : ℝ) : RvMCount.zetaZeroCount T = Ncount 0 T := by
  unfold RvMCount.zetaZeroCount Ncount
  rw [finsum_mem_congr rfl (fun ρ hρ => divisor_toNat_eq_zeroMult hρ.1 hρ.2.1)]
  apply finsum_mem_inter_support_eq
  ext ρ
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Function.mem_support, zerosIn,
    IsNontrivialZero]
  constructor
  · rintro ⟨⟨h0, h1, h2, h3⟩, hne⟩
    exact ⟨⟨⟨zero_of_zeroMult_ne_zero hne, h0, h1⟩, h2, h3⟩, hne⟩
  · rintro ⟨⟨⟨_, h0, h1⟩, h2, h3⟩, hne⟩
    exact ⟨⟨h0, h1, h2, h3⟩, hne⟩

/-! ## The main term `M(τ) = (τ/2π) log(τ/2π) − τ/2π` and its calculus. -/

/-- The cumulative main term without the constant `7/8`. -/
noncomputable def mainTerm (τ : ℝ) : ℝ :=
  τ / (2 * Real.pi) * Real.log (τ / (2 * Real.pi)) - τ / (2 * Real.pi)

lemma hasDerivAt_mainTerm {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt mainTerm ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) τ := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have h1 : HasDerivAt (fun x : ℝ => x / (2 * Real.pi)) (1 / (2 * Real.pi)) τ :=
    (hasDerivAt_id τ).div_const _
  have h2 : HasDerivAt (fun x : ℝ => Real.log (x / (2 * Real.pi)))
      ((τ / (2 * Real.pi))⁻¹ * (1 / (2 * Real.pi))) τ := by
    have h3 := (Real.hasDerivAt_log (by positivity : τ / (2 * Real.pi) ≠ 0)).comp τ h1
    exact h3
  have h3 : HasDerivAt (fun x : ℝ => x / (2 * Real.pi) * Real.log (x / (2 * Real.pi))
      - x / (2 * Real.pi))
      (1 / (2 * Real.pi) * Real.log (τ / (2 * Real.pi))
        + τ / (2 * Real.pi) * ((τ / (2 * Real.pi))⁻¹ * (1 / (2 * Real.pi)))
        - 1 / (2 * Real.pi)) τ := (h1.mul h2).sub h1
  have hτne : τ ≠ 0 := hτ.ne'
  have heq : (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))
      = 1 / (2 * Real.pi) * Real.log (τ / (2 * Real.pi))
        + τ / (2 * Real.pi) * ((τ / (2 * Real.pi))⁻¹ * (1 / (2 * Real.pi)))
        - 1 / (2 * Real.pi) := by
    field_simp
    ring
  rw [heq]
  exact h3

lemma intervalIntegrable_logMain {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun τ : ℝ => (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi)))
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  refine ContinuousOn.mul continuousOn_const ?_
  intro τ hτ
  have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le ha hτ.1
  exact ((Real.continuousAt_log (by positivity)).comp
    (continuousAt_id.div_const _)).continuousWithinAt

/-- FTC: `∫_a^b (1/2π) log(τ/2π) dτ = M(b) − M(a)` for `0 < a ≤ b`. -/
lemma integral_logMain_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ τ in a..b, (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))
      = mainTerm b - mainTerm a := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ hτ => ?_)
    (intervalIntegrable_logMain ha hab)
  rw [Set.uIcc_of_le hab] at hτ
  exact hasDerivAt_mainTerm (lt_of_lt_of_le ha hτ.1)

/-- Integrated Stirling on a general window `[a, b]`, `1 ≤ a ≤ b`:
`|∫_a^b μ − (M(b) − M(a))| ≤ C` (the `O(1/a)` tail is absorbed). -/
theorem int_mu_cumulative : ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ, 1 ≤ a → a ≤ b →
    |(∫ τ in a..b, mu τ) - (mainTerm b - mainTerm a)| ≤ C := by
  obtain ⟨C, hC⟩ := Zeta23.StirlingVert.mu_stirling
  have hC0 : 0 ≤ C := by
    have h := hC 1 (by norm_num)
    have := abs_nonneg (Zeta23.mu 1 - 1 / (2 * Real.pi) * Real.log (|1| / (2 * Real.pi)))
    nlinarith
  have hμcont : Continuous Zeta23.mu := Zeta23.mu_smooth.continuous
  refine ⟨C, hC0, fun a b ha hab => ?_⟩
  have ha0 : (0 : ℝ) < a := by linarith
  have hint_mu : IntervalIntegrable Zeta23.mu MeasureTheory.volume a b :=
    hμcont.intervalIntegrable _ _
  have hint_main := intervalIntegrable_logMain ha0 hab
  have hsplit : (∫ τ in a..b, Zeta23.mu τ)
      = (∫ τ in a..b, (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi)))
        + ∫ τ in a..b, (Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) := by
    rw [← intervalIntegral.integral_add hint_main (hint_mu.sub hint_main)]
    congr 1
    funext τ
    ring
  rw [hsplit, integral_logMain_eq ha0 hab, add_sub_cancel_left]
  have herr_int : IntervalIntegrable
      (fun τ : ℝ => Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi)))
      MeasureTheory.volume a b := hint_mu.sub hint_main
  have hbound : ∀ τ ∈ Set.Icc a b,
      |Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))| ≤ C / τ ^ 2 := by
    intro τ hτ
    have hτ1 : (1 : ℝ) ≤ τ := le_trans ha hτ.1
    have habs : |τ| = τ := abs_of_pos (by linarith)
    have h := hC τ (by rwa [habs])
    rwa [habs] at h
  have hCtau : IntervalIntegrable (fun τ : ℝ => C / τ ^ 2) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le ha0 hτ.1
    exact (continuousAt_const.div (continuousAt_pow _ _) (by positivity)).continuousWithinAt
  have hCint : ∫ τ in a..b, C / τ ^ 2 = C / a - C / b := by
    have hftc2 : ∀ τ ∈ Set.uIcc a b, HasDerivAt (fun x : ℝ => -C / x) (C / τ ^ 2) τ := by
      intro τ hτ
      rw [Set.uIcc_of_le hab] at hτ
      have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le ha0 hτ.1
      have hinv : HasDerivAt (fun x : ℝ => x⁻¹) (-1 / τ ^ 2) τ := (hasDerivAt_id τ).inv hτ0.ne'
      have h1 := hinv.const_mul (-C)
      have h3 : (fun x : ℝ => -C * x⁻¹) = fun x : ℝ => -C / x := by
        funext x
        ring
      rw [h3] at h1
      have heq : C / τ ^ 2 = -C * (-1 / τ ^ 2) := by ring
      rw [heq]
      exact h1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hftc2 hCtau]
    ring
  have hb0 : (0 : ℝ) < b := by linarith
  calc |∫ τ in a..b, (Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi)))|
      ≤ ∫ τ in a..b, |Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ τ in a..b, C / τ ^ 2 := by
        refine intervalIntegral.integral_mono_on hab herr_int.abs hCtau ?_
        intro τ hτ
        exact hbound τ hτ
    _ = C / a - C / b := hCint
    _ ≤ C / a := by
        have : 0 ≤ C / b := by positivity
        linarith
    _ ≤ C := by
        rw [div_le_iff₀ ha0]
        nlinarith

/-- `M` moves by at most `log T` on `[T, T+1]` for `T ≥ 4`. -/
lemma mainTerm_close {T T₂ : ℝ} (hT : 4 ≤ T) (h1 : T ≤ T₂) (h2 : T₂ ≤ T + 1) :
    |mainTerm T₂ - mainTerm T| ≤ Real.log T := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hπ4 : Real.pi < 4 := Real.pi_lt_four
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  rw [← integral_logMain_eq hT0 h1]
  have hbound : ∀ τ ∈ Set.uIoc T T₂,
      ‖(1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))‖ ≤ Real.log T := by
    intro τ hτ
    rw [Set.uIoc_of_le h1] at hτ
    have hτ1 : T < τ := hτ.1
    have hτ2 : τ ≤ T + 1 := le_trans hτ.2 h2
    have hτ0 : 0 < τ := by linarith
    have hx0 : 0 < τ / (2 * Real.pi) := by positivity
    -- upper: log(τ/2π) ≤ log τ ≤ log(T+1) ≤ log(T²) = 2 log T
    have hup : Real.log (τ / (2 * Real.pi)) ≤ 2 * Real.log T := by
      have e1 : Real.log (τ / (2 * Real.pi)) ≤ Real.log τ := by
        apply Real.log_le_log hx0
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      have e2 : Real.log τ ≤ Real.log (T ^ 2) := by
        apply Real.log_le_log hτ0
        nlinarith
      rw [Real.log_pow] at e2
      push_cast at e2
      linarith
    -- lower: -log(τ/2π) = log(2π/τ) ≤ log 2 ≤ log T
    have hlow : -Real.log (τ / (2 * Real.pi)) ≤ 2 * Real.log T := by
      rw [← Real.log_inv, inv_div]
      have e1 : Real.log (2 * Real.pi / τ) ≤ Real.log T := by
        apply Real.log_le_log (by positivity)
        rw [div_le_iff₀ hτ0]
        have h16 : 16 ≤ T * τ := by nlinarith
        linarith
      linarith
    have habs : |Real.log (τ / (2 * Real.pi))| ≤ 2 * Real.log T := abs_le.mpr ⟨by linarith, hup⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
    calc 1 / (2 * Real.pi) * |Real.log (τ / (2 * Real.pi))|
        ≤ 1 / (2 * Real.pi) * (2 * Real.log T) :=
          mul_le_mul_of_nonneg_left habs (by positivity)
      _ = Real.log T / Real.pi := by field_simp
      _ ≤ Real.log T := by
          rw [div_le_iff₀ hπ]
          nlinarith
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs] at this
  calc |∫ τ in T..T₂, (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))|
      ≤ Real.log T * |T₂ - T| := this
    _ ≤ Real.log T * 1 := by
        apply mul_le_mul_of_nonneg_left _ hlogT
        rw [abs_of_nonneg (by linarith)]
        linarith
    _ = Real.log T := mul_one _

/-! ## The cumulative Riemann--von Mangoldt formula, eventual form. -/

set_option maxHeartbeats 1000000 in
/-- **Cumulative RvM, eventual form**: `∃ C T₀, ∀ T ≥ T₀, |N(0,T] − M(T)| ≤ C log T`.
Route: fix a zero-free ordinate `T₁ ∈ [4,5]`; for `T ≥ T₀` pick a zero-free `T₂ ∈ [T, T+1]`;
apply the folded argument principle on the window `[T₁, T₂]`, split `Λ'/Λ = ζ'/ζ + Γℝ'/Γℝ`,
evaluate the Γ-side as `∫_{T₁}^{T₂} μ` (integrated Stirling gives `M(T₂) − M(T₁) + O(1)`),
bound the ζ-side by Backlund at `T₂` (the bottom edge at `T₁` is a fixed number, the vertical
edge is `≤ π`), and correct `N(0,T₂] → N(0,T]` by the local count. -/
theorem rvm_cumulative_eventually : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |(Ncount 0 T : ℝ) - mainTerm T| ≤ C * Real.log T := by
  obtain ⟨T₁, hT₁mem, hg1⟩ := Zeta23.RvM.exists_goodHeight 4
  have hT₁4 : 4 ≤ T₁ := hT₁mem.1
  have hT₁5 : T₁ ≤ 4 + 1 := hT₁mem.2
  obtain ⟨A₀, hA₀1, hA₀⟩ := Zeta23.RvM.zeta_local_zero_count
  obtain ⟨Cμ, hCμ0, hCμ⟩ := int_mu_cumulative
  obtain ⟨CB, TB, hB⟩ := Zeta23.RvM.backlund_horizontal
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπ1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  set K₁ : ℝ := |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T₁ * I)).im| with hK₁
  have hK₁0 : 0 ≤ K₁ := abs_nonneg _
  set K₀ : ℝ := (Ncount 0 T₁ : ℝ) + |mainTerm T₁| + K₁ / Real.pi + 1 + Cμ with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  refine ⟨K₀ + 2 * A₀ + 2 * |CB| + 1, max TB 6, fun T hT => ?_⟩
  have hTB : TB ≤ T := le_trans (le_max_left _ _) hT
  have hT6 : 6 ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hlogT0 : 0 ≤ Real.log T := by linarith
  -- a zero-free ordinate just above T
  obtain ⟨T₂, hT₂mem, hg2⟩ := Zeta23.RvM.exists_goodHeight T
  have hT₂a : T ≤ T₂ := hT₂mem.1
  have hT₂b : T₂ ≤ T + 1 := hT₂mem.2
  have h1T₁ : 1 ≤ T₁ := by linarith
  have h12 : T₁ < T₂ := by linarith
  -- argument principle + split + Γ-side
  have hN := Zeta23.RvM.N_eq_halfContour_completedZeta h1T₁ h12 hg1 hg2
  have hsplit := Zeta23.RvM.halfContour_completedZeta_split h1T₁ h12 hg1 hg2
  have hgam := Zeta23.RvM.gamma_side (T₁ := T₁) (T₂ := T₂) (by linarith) (by linarith)
  have h5 : (Ncount T₁ T₂ : ℝ)
      = (1 / Real.pi) * (Zeta23.RvM.halfContour (logDeriv riemannZeta) T₁ T₂).im
        + ∫ t in T₁..T₂, mu t := by
    rw [hN, hsplit, Complex.add_im, mul_add, hgam]
  -- window arithmetic
  have hadd1 : (Ncount 0 T₂ : ℝ) = (Ncount 0 T₁ : ℝ) + (Ncount T₁ T₂ : ℝ) := by
    have := Zeta23.Ncount_add (a := 0) (b := T₁) (c := T₂) (by linarith) h12.le
    rw [this]
    push_cast
    ring
  have hadd2 : (Ncount 0 T₂ : ℝ) = (Ncount 0 T : ℝ) + (Ncount T T₂ : ℝ) := by
    have := Zeta23.Ncount_add (a := 0) (b := T) (c := T₂) hT0.le hT₂a
    rw [this]
    push_cast
    ring
  -- the local-count correction
  have hlogsq : Real.log (|T| + 3) ≤ 2 * Real.log T := by
    rw [abs_of_pos hT0]
    calc Real.log (T + 3) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
      _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; ring
  have hw : (Ncount T T₂ : ℝ) ≤ 2 * A₀ * Real.log T := by
    have hsub : Ncount T T₂ ≤ Ncount T (T + 1) := Zeta23.Ncount_mono le_rfl hT₂b
    calc (Ncount T T₂ : ℝ) ≤ (Ncount T (T + 1) : ℝ) := by exact_mod_cast hsub
      _ ≤ A₀ * Real.log (|T| + 3) := hA₀ T
      _ ≤ A₀ * (2 * Real.log T) := mul_le_mul_of_nonneg_left hlogsq (by linarith)
      _ = 2 * A₀ * Real.log T := by ring
  -- the ζ half-contour
  have hbk2 := hB T₂ (by linarith) hg2
  have hvert := Zeta23.RvM.vertical_two T₁ T₂
  have hlogT₂ : Real.log T₂ ≤ 2 * Real.log T := by
    calc Real.log T₂ ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
      _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; ring
  have hlog₂0 : 0 ≤ Real.log T₂ := Real.log_nonneg (by linarith)
  have hζbound : |(Zeta23.RvM.halfContour (logDeriv riemannZeta) T₁ T₂).im|
      ≤ K₁ + Real.pi + |CB| * Real.log T₂ := by
    unfold Zeta23.RvM.halfContour
    have eim : ((∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₁ * I))
        + (∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I)) * I
        - ∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₂ * I)).im
        = (∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₁ * I)).im
          + ((∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I)) * I).im
          - (∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₂ * I)).im := by
      simp [Complex.add_im, Complex.sub_im]
    rw [eim]
    have hmulI : ((∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I)) * I).im
        = (∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im :=
      congrArg Complex.im (intervalIntegral.integral_mul_const (μ := MeasureTheory.volume) I
        (fun t : ℝ => logDeriv riemannZeta (2 + t * I))).symm
    have h2 : |(∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₂ * I)).im| ≤ |CB| * Real.log T₂ :=
      hbk2.trans (mul_le_mul_of_nonneg_right (le_abs_self CB) hlog₂0)
    calc |(∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₁ * I)).im
          + ((∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I)) * I).im
          - (∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₂ * I)).im|
        ≤ |(∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₁ * I)).im|
          + |((∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I)) * I).im|
          + |(∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₂ * I)).im| := by
          exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ K₁ + Real.pi + |CB| * Real.log T₂ := by
          rw [hmulI]
          linarith
  have hA : |(1 / Real.pi) * (Zeta23.RvM.halfContour (logDeriv riemannZeta) T₁ T₂).im|
      ≤ K₁ / Real.pi + 1 + 2 * |CB| * Real.log T := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / Real.pi)]
    have step1 : (1 / Real.pi) * |(Zeta23.RvM.halfContour (logDeriv riemannZeta) T₁ T₂).im|
        ≤ (1 / Real.pi) * (K₁ + Real.pi + |CB| * Real.log T₂) :=
      mul_le_mul_of_nonneg_left hζbound (by positivity)
    have hfrac : (1:ℝ) / Real.pi ≤ 1 := by
      rw [div_le_one hπ]
      exact hπ1
    have e2 : (1 / Real.pi) * Real.pi = 1 := by field_simp
    have e3 : (1 / Real.pi) * (|CB| * Real.log T₂) ≤ 2 * |CB| * Real.log T := by
      calc (1 / Real.pi) * (|CB| * Real.log T₂) ≤ 1 * (|CB| * Real.log T₂) :=
            mul_le_mul_of_nonneg_right hfrac (mul_nonneg (abs_nonneg _) hlog₂0)
        _ = |CB| * Real.log T₂ := one_mul _
        _ ≤ |CB| * (2 * Real.log T) := mul_le_mul_of_nonneg_left hlogT₂ (abs_nonneg _)
        _ = 2 * |CB| * Real.log T := by ring
    calc (1 / Real.pi) * |(Zeta23.RvM.halfContour (logDeriv riemannZeta) T₁ T₂).im|
        ≤ (1 / Real.pi) * K₁ + (1 / Real.pi) * Real.pi + (1 / Real.pi) * (|CB| * Real.log T₂) := by
          rw [← mul_add, ← mul_add]
          exact step1
      _ ≤ K₁ / Real.pi + 1 + 2 * |CB| * Real.log T := by
          rw [e2]
          have e1 : (1 / Real.pi) * K₁ = K₁ / Real.pi := by ring
          linarith
  -- the Γ-side and the main-term shift
  have hμ := hCμ T₁ T₂ h1T₁ h12.le
  have hM := mainTerm_close (by linarith : 4 ≤ T) hT₂a hT₂b
  -- key identity
  have hkey : (Ncount 0 T : ℝ) - mainTerm T
      = (Ncount 0 T₁ : ℝ) - (Ncount T T₂ : ℝ)
        + (1 / Real.pi) * (Zeta23.RvM.halfContour (logDeriv riemannZeta) T₁ T₂).im
        + ((∫ t in T₁..T₂, mu t) - (mainTerm T₂ - mainTerm T₁))
        + (mainTerm T₂ - mainTerm T) - mainTerm T₁ := by
    linarith [h5, hadd1, hadd2]
  rw [hkey]
  have hNc0 : (0:ℝ) ≤ (Ncount 0 T₁ : ℝ) := Nat.cast_nonneg _
  have hNc1 : (0:ℝ) ≤ (Ncount T T₂ : ℝ) := Nat.cast_nonneg _
  have htri : |(Ncount 0 T₁ : ℝ) - (Ncount T T₂ : ℝ)
        + (1 / Real.pi) * (Zeta23.RvM.halfContour (logDeriv riemannZeta) T₁ T₂).im
        + ((∫ t in T₁..T₂, mu t) - (mainTerm T₂ - mainTerm T₁))
        + (mainTerm T₂ - mainTerm T) - mainTerm T₁|
      ≤ (Ncount 0 T₁ : ℝ) + (Ncount T T₂ : ℝ)
        + |(1 / Real.pi) * (Zeta23.RvM.halfContour (logDeriv riemannZeta) T₁ T₂).im|
        + |(∫ t in T₁..T₂, mu t) - (mainTerm T₂ - mainTerm T₁)|
        + |mainTerm T₂ - mainTerm T| + |mainTerm T₁| := by
    have t1 := abs_sub ((Ncount 0 T₁ : ℝ) - (Ncount T T₂ : ℝ)
        + (1 / Real.pi) * (Zeta23.RvM.halfContour (logDeriv riemannZeta) T₁ T₂).im
        + ((∫ t in T₁..T₂, mu t) - (mainTerm T₂ - mainTerm T₁))
        + (mainTerm T₂ - mainTerm T)) (mainTerm T₁)
    have t2 := abs_add_le ((Ncount 0 T₁ : ℝ) - (Ncount T T₂ : ℝ)
        + (1 / Real.pi) * (Zeta23.RvM.halfContour (logDeriv riemannZeta) T₁ T₂).im
        + ((∫ t in T₁..T₂, mu t) - (mainTerm T₂ - mainTerm T₁))) (mainTerm T₂ - mainTerm T)
    have t3 := abs_add_le ((Ncount 0 T₁ : ℝ) - (Ncount T T₂ : ℝ)
        + (1 / Real.pi) * (Zeta23.RvM.halfContour (logDeriv riemannZeta) T₁ T₂).im)
        ((∫ t in T₁..T₂, mu t) - (mainTerm T₂ - mainTerm T₁))
    have t4 := abs_add_le ((Ncount 0 T₁ : ℝ) - (Ncount T T₂ : ℝ))
        ((1 / Real.pi) * (Zeta23.RvM.halfContour (logDeriv riemannZeta) T₁ T₂).im)
    have t5 := abs_sub (Ncount 0 T₁ : ℝ) (Ncount T T₂ : ℝ)
    rw [abs_of_nonneg hNc0, abs_of_nonneg hNc1] at t5
    linarith
  refine htri.trans ?_
  -- constants are absorbed by log T ≥ 1
  have hc1 : (Ncount 0 T₁ : ℝ) ≤ (Ncount 0 T₁ : ℝ) * Real.log T := by nlinarith
  have hc2 : |mainTerm T₁| ≤ |mainTerm T₁| * Real.log T := by nlinarith [abs_nonneg (mainTerm T₁)]
  have hc3 : K₁ / Real.pi + 1 ≤ (K₁ / Real.pi + 1) * Real.log T := by
    have : 0 ≤ K₁ / Real.pi := by positivity
    nlinarith
  have hc4 : Cμ ≤ Cμ * Real.log T := by nlinarith
  rw [hK₀]
  nlinarith [hA, hμ, hM, hw, hc1, hc2, hc3, hc4]

/-! ## Passage to all `T ≥ 2` (finite range absorbed into the constant). -/

/-- **Cumulative RvM for all `T ≥ 2`**, in Zeta23's vocabulary. -/
theorem rvm_cumulative : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
    |(Ncount 0 T : ℝ) - mainTerm T| ≤ C * Real.log T := by
  obtain ⟨C, T₀, hC⟩ := rvm_cumulative_eventually
  set T₀' : ℝ := max T₀ 6 with hT₀'
  have hT₀'6 : 6 ≤ T₀' := le_max_right _ _
  have hT₀'0 : 0 < T₀' := by linarith
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hπ4 : Real.pi < 4 := Real.pi_lt_four
  have hlogT₀' : 0 ≤ Real.log T₀' := Real.log_nonneg (by linarith)
  set K : ℝ := (Ncount 0 T₀' : ℝ) + T₀' * (Real.log T₀' + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨max C (K / Real.log 2) + 1, by positivity, fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hlogT0 : 0 ≤ Real.log T := by linarith
  have hmax0 : 0 ≤ max C (K / Real.log 2) := le_trans (by positivity) (le_max_right _ _)
  rcases le_or_gt T₀' T with hbig | hsmall
  · -- the eventual regime
    have h := hC T (le_trans (le_max_left _ _) hbig)
    calc |(Ncount 0 T : ℝ) - mainTerm T| ≤ C * Real.log T := h
      _ ≤ max C (K / Real.log 2) * Real.log T :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hlogT0
      _ ≤ (max C (K / Real.log 2) + 1) * Real.log T := by nlinarith
  · -- the finite range 2 ≤ T < T₀'
    have hmono : Ncount 0 T ≤ Ncount 0 T₀' := Zeta23.Ncount_mono le_rfl hsmall.le
    have hN : (Ncount 0 T : ℝ) ≤ (Ncount 0 T₀' : ℝ) := by exact_mod_cast hmono
    have hNn : (0 : ℝ) ≤ (Ncount 0 T : ℝ) := Nat.cast_nonneg _
    -- |M T| ≤ T₀' (log T₀' + 1)
    have hx0 : 0 < T / (2 * Real.pi) := by positivity
    have hlogx : |Real.log (T / (2 * Real.pi))| ≤ Real.log T₀' := by
      rw [abs_le]
      constructor
      · rw [neg_le, ← Real.log_inv, inv_div]
        apply Real.log_le_log (by positivity)
        rw [div_le_iff₀ hT0]
        nlinarith
      · apply Real.log_le_log hx0
        rw [div_le_iff₀ (by positivity)]
        nlinarith
    have hM : |mainTerm T| ≤ T₀' * (Real.log T₀' + 1) := by
      have e : mainTerm T = T / (2 * Real.pi) * (Real.log (T / (2 * Real.pi)) - 1) := by
        unfold mainTerm
        ring
      rw [e, abs_mul, abs_of_pos hx0]
      have h1 : |Real.log (T / (2 * Real.pi)) - 1| ≤ Real.log T₀' + 1 := by
        calc |Real.log (T / (2 * Real.pi)) - 1|
            ≤ |Real.log (T / (2 * Real.pi))| + |(1:ℝ)| := abs_sub _ _
          _ ≤ Real.log T₀' + 1 := by rw [abs_one]; linarith
      have h2 : T / (2 * Real.pi) ≤ T₀' := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      exact mul_le_mul h2 h1 (abs_nonneg _) hT₀'0.le
    have hdiff : |(Ncount 0 T : ℝ) - mainTerm T| ≤ K := by
      calc |(Ncount 0 T : ℝ) - mainTerm T|
          ≤ |(Ncount 0 T : ℝ)| + |mainTerm T| := abs_sub _ _
        _ ≤ (Ncount 0 T₀' : ℝ) + T₀' * (Real.log T₀' + 1) := by
            rw [abs_of_nonneg hNn]
            linarith
        _ = K := by rw [hK]
    have hKlog : K ≤ (K / Real.log 2) * Real.log T := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      exact mul_le_mul_of_nonneg_left hlogT hK0
    calc |(Ncount 0 T : ℝ) - mainTerm T| ≤ K := hdiff
      _ ≤ (K / Real.log 2) * Real.log T := hKlog
      _ ≤ max C (K / Real.log 2) * Real.log T :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hlogT0
      _ ≤ (max C (K / Real.log 2) + 1) * Real.log T := by nlinarith

/-! ## The registry node statement, verbatim. -/

open Real in
/-- The RH registry node `RH_rvm_unconditional`, verbatim (name and binder-free form): the
Riemann--von Mangoldt formula `N(T) = (T/2π) log(T/2π) − T/2π + 7/8 + O(log T)` for all
`T ≥ 2`, with `N(T)` the registry's multiplicity-weighted rectangle count. The `7/8` is
absorbed into the remainder (`log T ≥ log 2 > 1/2`). -/
theorem rvm_unconditional :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      |((RvMCount.zetaZeroCount T : ℕ) : ℝ)
          - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8)|
        ≤ C * Real.log T := by
  obtain ⟨C, hC0, hC⟩ := rvm_cumulative
  refine ⟨C + 2, by linarith, fun T hT => ?_⟩
  have hlog2 : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hlog2' : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlogT0 : 0 ≤ Real.log T := by linarith
  have h := hC T hT
  rw [zetaZeroCount_eq_Ncount]
  have e : T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8 = mainTerm T + 7 / 8 := by
    unfold mainTerm
    rfl
  rw [e]
  calc |(Ncount 0 T : ℝ) - (mainTerm T + 7 / 8)|
      = |((Ncount 0 T : ℝ) - mainTerm T) + (-(7 / 8 : ℝ))| := by ring_nf
    _ ≤ |(Ncount 0 T : ℝ) - mainTerm T| + |(-(7 / 8 : ℝ))| := abs_add_le _ _
    _ ≤ C * Real.log T + 7 / 8 := by
        rw [abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 7 / 8)]
        linarith
    _ ≤ (C + 2) * Real.log T := by nlinarith

end RvMBridge2
