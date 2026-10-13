/-
  E6Bridge18 -- the DERIVATIVE partial fraction of xi'/xi, constant-free (2026-09-21; P1 of the
  Weil-to-Li dictionary: the global partial fraction that LiValue (E6Bridge15) needs, obtained
  WITHOUT the Hadamard product).

  THE FUNCTION.  xi(s) := s (s - 1)/2 * Lambda_0(s) + 1/2 (Zeta23.WeilEF.xi, restated here since
  that module's olean is not built on this island), Lambda_0 = Mathlib's completedRiemannZeta_0, so
  xi is ENTIRE (xi_differentiable) and xi(s) = s (s - 1)/2 * Lambda(s) off {0, 1} (xi_eq).  Its zeros
  are the nontrivial zeros of zeta with the same multiplicities; on the complement, logDeriv xi =
  1/s + 1/(s - 1) + logDeriv Lambda (logDeriv_xi_eq).

  THE INTERFACE (fixed for the parallel Taylor agent; the name is the one requested, stated for
  xi, the clean choice: no pole terms).

      def XiLogDerivDerivEq : Prop := forall s, not IsNontrivialZero s ->
        deriv (logDeriv xi) s = - Sum'_rho m(rho) / (s - rho)^2

      theorem summable_inv_sub_sq (s) (hs : not IsNontrivialZero s) :
        Summable (fun rho => (m rho : C) / (s - rho)^2)                      -- PROVED
      theorem xi_logDeriv_deriv_eq_of (h1 : XiDiffRegular) (h2 : XiLogDerivDerivDecay) :
        XiLogDerivDerivEq                                                    -- PROVED modulo h1 h2

  THE CONSTANT-FREE ARGUMENT and what is closed here.  Let
      xiDiffReg s := deriv (logDeriv xi) s + Sum'_rho m(rho)/(s - rho)^2.
    (1) Summability of the sum for every s off the zeros: local-count majorant
        (RvMBridgeGauss.summable_mult_div_one_add_normSq = Zeta23 zero_sum_inv_sq) away from the
        ordinate of s, finitely many zeros near it (zetaSeam.finite_window).     PROVED.
    (2) xiDiffReg extends to an ENTIRE function G (the double poles of deriv (logDeriv xi) at a
        zero of order m are cancelled by the m/(s - rho)^2 term of the sum) with logarithmic growth
        |G(s)| <= C (1 + log (2 + |s|)) (Landau's local partial fraction + Cauchy estimates on
        |Re s| <= 2, Dirichlet series and Stirling on |Re s| >= 2, functional equation on the
        left).                                                                    OBLIGATION XiDiffRegular.
    (3) Liouville with logarithmic growth: such a G is constant.                 PROVED
        (eq_const_of_log_growth: Cauchy's estimate on circles of radius R -> 0 as R -> infinity).
    (4) The constant is 0: xiDiffReg(sigma) -> 0 as sigma -> +infinity on the real axis.  The
        sum tends to 0 (Tannery against the same majorant).                       PROVED
        (tsum_inv_sub_sq_tendsto); deriv (logDeriv xi)(sigma) -> 0 (Dirichlet series of zeta'/zeta
        and psi' = O(1/sigma)).                                                   OBLIGATION XiLogDerivDerivDecay.
    (5) Assembly: G = 0, hence the interface identity off the zeros.             PROVED.

  Both obligations are def : Prop (never a `sorry`); probes show automation neither proves nor
  refutes them.  conjecture1_proved = False; nothing here bears on RH.
-/
import E6Bridge6

open Zeta23 Complex MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace RvMBridge18
open WeilExplicit

/-! ## A. The entire function xi. -/

/-- xi(s) = s (s - 1)/2 * Lambda_0(s) + 1/2 (Riemann's xi; = s(s-1)/2 * Lambda(s) off {0,1}). -/
def xi (s : ℂ) : ℂ := s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2

theorem xi_differentiable : Differentiable ℂ xi := by
  unfold xi
  exact (((differentiable_id.mul (differentiable_id.sub_const 1)).div_const 2).mul
    differentiable_completedZeta₀).add_const _

theorem xi_eq (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    xi s = s * (s - 1) / 2 * completedRiemannZeta s := by
  unfold xi
  rw [completedRiemannZeta_eq]
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  field_simp
  ring

/-- Off {0, 1}, xi agrees with s(s-1)/2 * Lambda on a neighbourhood. -/
lemma xi_eventuallyEq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    xi =ᶠ[𝓝 s] fun z => z * (z - 1) / 2 * completedRiemannZeta z := by
  have hopen : IsOpen ({0, 1} : Set ℂ)ᶜ := (Set.toFinite _).isClosed.isOpen_compl
  have hmem : s ∈ ({0, 1} : Set ℂ)ᶜ := by simp [hs0, hs1]
  filter_upwards [hopen.mem_nhds hmem] with z hz
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
  exact xi_eq z hz.1 hz.2

/-- logDeriv xi = 1/s + 1/(s-1) + logDeriv Lambda off {0, 1} and off the zeros of Lambda. -/
theorem logDeriv_xi_eq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hΛ : completedRiemannZeta s ≠ 0) :
    logDeriv xi s = 1 / s + 1 / (s - 1) + logDeriv completedRiemannZeta s := by
  have hev := xi_eventuallyEq hs0 hs1
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  have hd : HasDerivAt (fun z : ℂ => z * (z - 1) / 2 * completedRiemannZeta z)
      (((1 * (s - 1) + s * 1) / 2) * completedRiemannZeta s
        + s * (s - 1) / 2 * deriv completedRiemannZeta s) s := by
    have h1 : HasDerivAt (fun z : ℂ => z * (z - 1) / 2) ((1 * (s - 1) + s * 1) / 2) s :=
      ((hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)).div_const 2
    exact h1.mul (differentiableAt_completedZeta hs0 hs1).hasDerivAt
  rw [hd.deriv, logDeriv_apply]
  field_simp

/-! ## B. Summability of the double-pole sum off the zeros. -/

lemma normSq_gammaOf_le (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    1 + Complex.normSq (gammaOf ρ) ≤ 5 / 4 + ρ.im ^ 2 := by
  rw [Complex.normSq_apply, Zeta23.WeilEF.gammaOf_re, Zeta23.WeilEF.gammaOf_im]
  nlinarith

/-- The term of the double-pole sum. -/
def polTerm (s ρ : ℂ) : ℂ := (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2

lemma polTerm_eq_zero_of_not_nontrivial {s ρ : ℂ} (h : ¬ IsNontrivialZero ρ) : polTerm s ρ = 0 := by
  unfold polTerm
  rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial h]
  simp

lemma norm_polTerm (s ρ : ℂ) : ‖polTerm s ρ‖ = (WeilExplicit.zeroMult ρ : ℝ) / ‖s - ρ‖ ^ 2 := by
  unfold polTerm
  rw [norm_div, Complex.norm_natCast, norm_pow]

/-- Away from the ordinate of s the double-pole term is bounded by the local-count majorant. -/
lemma norm_polTerm_le_majorant {s ρ : ℂ} (h : IsNontrivialZero ρ) (hfar : 1 ≤ |ρ.im - s.im|) :
    ‖polTerm s ρ‖ ≤ (WeilExplicit.zeroMult ρ : ℝ)
      * ((13 / 4 + 2 * s.im ^ 2) / (1 + Complex.normSq (gammaOf ρ))) := by
  rw [norm_polTerm, ← mul_one_div]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have hγ := normSq_gammaOf_le ρ h.2.1 h.2.2
  have hγ0 := Complex.normSq_nonneg (gammaOf ρ)
  have hd : (ρ.im - s.im) ^ 2 ≤ ‖s - ρ‖ ^ 2 := by
    have := Complex.abs_im_le_norm (s - ρ)
    rw [Complex.sub_im] at this
    have h2 : |s.im - ρ.im| ^ 2 = (s.im - ρ.im) ^ 2 := sq_abs _
    nlinarith [abs_nonneg (s.im - ρ.im)]
  have hd1 : 1 ≤ (ρ.im - s.im) ^ 2 := by
    have := sq_abs (ρ.im - s.im)
    nlinarith [abs_nonneg (ρ.im - s.im)]
  have hpos : 0 < ‖s - ρ‖ ^ 2 := by linarith
  rw [div_le_div_iff₀ hpos (by linarith)]
  -- 1 + normSq gamma <= 5/4 + t^2 <= 5/4 + 2 (t - a)^2 + 2 a^2 <= (13/4 + 2 a^2) (t - a)^2
  have ht : ρ.im ^ 2 ≤ 2 * (ρ.im - s.im) ^ 2 + 2 * s.im ^ 2 := by nlinarith [sq_nonneg (ρ.im - 2 * s.im)]
  nlinarith [sq_nonneg s.im]

/-- The nontrivial zeros within ordinate distance 1 of s are finitely many. -/
lemma finite_zeros_near (s : ℂ) :
    ({ρ : ℂ | IsNontrivialZero ρ} ∩ {ρ : ℂ | |ρ.im - s.im| < 1}).Finite := by
  refine (zetaSeam.finite_window (s.im - 2) (s.im + 1)).subset ?_
  rintro ρ ⟨hnt, hw⟩
  have hw' : |ρ.im - s.im| < 1 := hw
  have h := abs_lt.mp hw'
  exact ⟨hnt, by linarith [h.1], by linarith [h.2]⟩

/-- The summable majorant for the double-pole sum. -/
def polBound (s : ℂ) (ρ : ℂ) : ℝ :=
  ({ρ : ℂ | IsNontrivialZero ρ} ∩ {ρ : ℂ | |ρ.im - s.im| < 1}).indicator (fun ρ => ‖polTerm s ρ‖) ρ
    + (WeilExplicit.zeroMult ρ : ℝ) * ((13 / 4 + 2 * s.im ^ 2) / (1 + Complex.normSq (gammaOf ρ)))

lemma summable_polBound (s : ℂ) : Summable (polBound s) := by
  unfold polBound
  refine Summable.add ?_ (RvMBridgeGauss.summable_mult_div_one_add_normSq _)
  refine summable_of_ne_finset_zero (s := (finite_zeros_near s).toFinset) fun ρ hρ => ?_
  rw [Set.Finite.mem_toFinset] at hρ
  exact Set.indicator_of_notMem hρ _

lemma norm_polTerm_le (s ρ : ℂ) : ‖polTerm s ρ‖ ≤ polBound s ρ := by
  unfold polBound
  have hpos : 0 ≤ (WeilExplicit.zeroMult ρ : ℝ)
      * ((13 / 4 + 2 * s.im ^ 2) / (1 + Complex.normSq (gammaOf ρ))) := by
    have := Complex.normSq_nonneg (gammaOf ρ)
    positivity
  by_cases h : IsNontrivialZero ρ
  · by_cases hn : |ρ.im - s.im| < 1
    · rw [Set.indicator_of_mem (show ρ ∈ {ρ : ℂ | IsNontrivialZero ρ} ∩ {ρ : ℂ | |ρ.im - s.im| < 1}
        from ⟨h, hn⟩)]
      linarith
    · rw [Set.indicator_of_notMem (fun hm => hn hm.2), zero_add]
      exact norm_polTerm_le_majorant h (not_lt.mp hn)
  · rw [polTerm_eq_zero_of_not_nontrivial h, norm_zero]
    have : 0 ≤ ({ρ : ℂ | IsNontrivialZero ρ} ∩ {ρ : ℂ | |ρ.im - s.im| < 1}).indicator
        (fun ρ => ‖polTerm s ρ‖) ρ := Set.indicator_nonneg (fun _ _ => norm_nonneg _) _
    linarith

/-- **Interface, part 1.**  The double-pole sum converges absolutely for every s (the hypothesis
that s is not a zero is not even needed for summability: at a zero the offending term is the junk
value 0). -/
theorem summable_inv_sub_sq (s : ℂ) (_hs : ¬ IsNontrivialZero s) :
    Summable (fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2) :=
  Summable.of_norm_bounded (summable_polBound s) (norm_polTerm_le s)

theorem summable_polTerm (s : ℂ) : Summable (polTerm s) :=
  Summable.of_norm_bounded (summable_polBound s) (norm_polTerm_le s)

/-! ## C. The regularised difference and the two named obligations. -/

/-- xiDiffReg s = deriv (logDeriv xi) s + Sum'_rho m(rho)/(s - rho)^2 (junk at the zeros). -/
def xiDiffReg (s : ℂ) : ℂ :=
  deriv (logDeriv xi) s + ∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2

/-- **The interface identity** (the derivative partial fraction of xi'/xi, no constant). -/
def XiLogDerivDerivEq : Prop :=
  ∀ s : ℂ, ¬ IsNontrivialZero s →
    deriv (logDeriv xi) s = -∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2

/-- **Obligation 1 (removable singularities + logarithmic growth).**  xiDiffReg extends across
the zeros to an entire function G (at a zero of order m, deriv (logDeriv xi) = -m/(s-rho)^2 +
analytic and the sum contributes exactly +m/(s-rho)^2) with |G(s)| <= C (1 + log (2 + |s|))
(Landau's local partial fraction and Cauchy's estimate on |Re s| <= 2; Dirichlet series and
Stirling on Re s >= 2; the functional equation on Re s <= -1). -/
def XiDiffRegular : Prop :=
  ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ s : ℂ, ¬ IsNontrivialZero s → G s = xiDiffReg s) ∧
    ∃ C : ℝ, ∀ s : ℂ, ‖G s‖ ≤ C * (1 + Real.log (2 + ‖s‖))

/-- **Obligation 2 (decay of the logarithmic-derivative part along the real axis).**
deriv (logDeriv xi)(sigma) = -1/sigma^2 - 1/(sigma-1)^2 + (1/4) psi'(sigma/2) + (zeta'/zeta)'(sigma)
tends to 0 as sigma -> +infinity (psi' = O(1/sigma); the Dirichlet series of (zeta'/zeta)' is
O(2^{-sigma})). -/
def XiLogDerivDerivDecay : Prop :=
  Tendsto (fun σ : ℝ => deriv (logDeriv xi) (σ : ℂ)) atTop (𝓝 0)

/-! ## D. The sum decays along the real axis (Tannery). -/

lemma norm_polTerm_le_real {σ : ℝ} (hσ : 2 ≤ σ) {ρ : ℂ} (h : IsNontrivialZero ρ) :
    ‖polTerm (σ : ℂ) ρ‖ ≤ (WeilExplicit.zeroMult ρ : ℝ) * (5 / 4 / (1 + Complex.normSq (gammaOf ρ))) := by
  rw [norm_polTerm, ← mul_one_div]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have hγ := normSq_gammaOf_le ρ h.2.1 h.2.2
  have hγ0 := Complex.normSq_nonneg (gammaOf ρ)
  have hns : ‖(σ : ℂ) - ρ‖ ^ 2 = (σ - ρ.re) ^ 2 + ρ.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hre := h.2.2
  have h1 : 1 ≤ (σ - ρ.re) ^ 2 := by nlinarith
  rw [div_le_div_iff₀ (by rw [hns]; positivity) (by linarith), hns]
  nlinarith

lemma polTerm_tendsto_zero (ρ : ℂ) :
    Tendsto (fun σ : ℝ => polTerm (σ : ℂ) ρ) atTop (𝓝 0) := by
  by_cases h : IsNontrivialZero ρ
  · refine squeeze_zero_norm' (a := fun σ : ℝ => (WeilExplicit.zeroMult ρ : ℝ) / (σ - 1) ^ 2) ?_ ?_
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with σ hσ
      rw [norm_polTerm]
      have hre := h.2.2
      have hpos : 0 < (σ - 1) ^ 2 := by nlinarith
      have hle : (σ - 1) ^ 2 ≤ ‖(σ : ℂ) - ρ‖ ^ 2 := by
        have h1 : σ - 1 ≤ |((σ : ℂ) - ρ).re| := by
          rw [Complex.sub_re, Complex.ofReal_re]
          exact le_trans (by linarith) (le_abs_self _)
        have h2 := Complex.abs_re_le_norm ((σ : ℂ) - ρ)
        have h3 : 0 ≤ σ - 1 := by linarith
        nlinarith [abs_nonneg ((σ : ℂ) - ρ).re]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hpos hle
    · have h1 : Tendsto (fun σ : ℝ => (σ - 1) ^ 2) atTop atTop :=
        (tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_right atTop (-1) tendsto_id)
      exact tendsto_const_nhds.div_atTop h1
  · simp only [polTerm_eq_zero_of_not_nontrivial h]
    exact tendsto_const_nhds

/-- Step (4), the sum half: Sum'_rho m(rho)/(sigma - rho)^2 -> 0 as sigma -> +infinity. -/
theorem tsum_inv_sub_sq_tendsto :
    Tendsto (fun σ : ℝ => ∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / ((σ : ℂ) - ρ) ^ 2) atTop (𝓝 0) := by
  have h0 : (0 : ℂ) = ∑' ρ : ℂ, (0 : ℂ) := tsum_zero.symm
  rw [h0]
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun ρ => (WeilExplicit.zeroMult ρ : ℝ) * (5 / 4 / (1 + Complex.normSq (gammaOf ρ))))
    (RvMBridgeGauss.summable_mult_div_one_add_normSq _) (fun ρ => polTerm_tendsto_zero ρ) ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with σ hσ ρ
  by_cases h : IsNontrivialZero ρ
  · exact norm_polTerm_le_real hσ h
  · rw [show (WeilExplicit.zeroMult ρ : ℂ) / ((σ : ℂ) - ρ) ^ 2 = polTerm (σ : ℂ) ρ from rfl,
      polTerm_eq_zero_of_not_nontrivial h, norm_zero]
    have := Complex.normSq_nonneg (gammaOf ρ)
    positivity

/-! ## E. Liouville with logarithmic growth. -/

/-- An entire function with |G(z)| <= C (1 + log (2 + |z|)) is constant. -/
theorem eq_const_of_log_growth {G : ℂ → ℂ} (hG : Differentiable ℂ G) {C : ℝ}
    (hC : ∀ z : ℂ, ‖G z‖ ≤ C * (1 + Real.log (2 + ‖z‖))) : ∀ z : ℂ, G z = G 0 := by
  have hC0 : 0 ≤ C := by
    have h := hC 0
    rw [norm_zero, add_zero] at h
    have hl : 0 < 1 + Real.log 2 := by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith
    by_contra hneg
    have hlt : C < 0 := not_le.mp hneg
    have : C * (1 + Real.log 2) < 0 := mul_neg_of_neg_of_pos hlt hl
    linarith [norm_nonneg (G 0)]
  have hderiv : ∀ z : ℂ, deriv G z = 0 := by
    intro z
    set a := ‖z‖ with ha
    have hbound : ∀ R : ℝ, 0 < R →
        ‖deriv G z‖ ≤ C * (1 + Real.log (2 + a + R)) / R := by
      intro R hR
      refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hG.diffContOnCl fun w hw => ?_
      refine (hC w).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hC0
      have hwn : ‖w‖ ≤ a + R := by
        rw [Metric.mem_sphere] at hw
        calc ‖w‖ = ‖(w - z) + z‖ := by ring_nf
          _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
          _ = R + a := by rw [← dist_eq_norm, hw]
          _ = a + R := by ring
      have : Real.log (2 + ‖w‖) ≤ Real.log (2 + a + R) :=
        Real.log_le_log (by positivity) (by linarith)
      linarith
    have hlim : Tendsto (fun R : ℝ => C * (1 + Real.log (2 + a + R)) / R) atTop (𝓝 0) := by
      have h1 : Tendsto (fun R : ℝ => C / R) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have h2 : Tendsto (fun R : ℝ => Real.log (2 + a + R) / R) atTop (𝓝 0) := by
        have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-(2 + a)) 1 one_ne_zero).comp
          (tendsto_atTop_add_const_left atTop (2 + a) tendsto_id)
        refine h.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
        simp only [Function.comp, id, pow_one, one_mul]
        congr 1
        ring
      have h3 : Tendsto (fun R : ℝ => C / R + C * (Real.log (2 + a + R) / R)) atTop (𝓝 (0 + C * 0)) :=
        h1.add (h2.const_mul C)
      simp only [mul_zero, add_zero] at h3
      refine h3.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
      field_simp
    have hle : ‖deriv G z‖ ≤ 0 :=
      ge_of_tendsto hlim ((eventually_gt_atTop (0 : ℝ)).mono fun R hR => hbound R hR)
    exact norm_le_zero_iff.mp hle
  exact fun z => is_const_of_deriv_eq_zero hG hderiv z 0

/-! ## F. Assembly: the interface identity modulo the two obligations. -/

lemma not_nontrivialZero_of_one_le_re {s : ℂ} (h : 1 ≤ s.re) : ¬ IsNontrivialZero s :=
  fun hz => absurd hz.2.2 (not_lt.mpr h)

/-- **Interface, part 2, modulo the two named obligations.**  Given the entire log-growth extension
(XiDiffRegular) and the real-axis decay of deriv (logDeriv xi) (XiLogDerivDerivDecay), the
derivative partial fraction holds at every s that is not a nontrivial zero. -/
theorem xi_logDeriv_deriv_eq_of (h1 : XiDiffRegular) (h2 : XiLogDerivDerivDecay) :
    XiLogDerivDerivEq := by
  obtain ⟨G, hG, hagree, C, hC⟩ := h1
  have hconst := eq_const_of_log_growth hG hC
  -- along the real axis G is constant and equals xiDiffReg, which tends to 0
  have hreal : Tendsto (fun σ : ℝ => G (σ : ℂ)) atTop (𝓝 0) := by
    have hx : Tendsto (fun σ : ℝ => xiDiffReg (σ : ℂ)) atTop (𝓝 (0 + 0)) := by
      unfold xiDiffReg
      exact h2.add tsum_inv_sub_sq_tendsto
    rw [add_zero] at hx
    refine hx.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with σ hσ
    exact (hagree (σ : ℂ) (not_nontrivialZero_of_one_le_re (by rwa [Complex.ofReal_re]))).symm
  have hG0 : G 0 = 0 := by
    have hc : Tendsto (fun σ : ℝ => G (σ : ℂ)) atTop (𝓝 (G 0)) := by
      simp only [hconst]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hc hreal
  intro s hs
  have h := hagree s hs
  rw [hconst s, hG0] at h
  unfold xiDiffReg at h
  linear_combination -h

end RvMBridge18
