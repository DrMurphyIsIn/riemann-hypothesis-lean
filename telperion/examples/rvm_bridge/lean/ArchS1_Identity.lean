/-
  ArchS1_Identity -- THE EXACT u-SPACE WEIL IDENTITY (2026-10-11, stage S1 of
  telperion/docs/ARCHIMEDEAN_CONCEPTUAL_BLUEPRINT_2026-10-11.md).

  For every IsWeilTest g, with M = mass g = ||g||_2^2 and k = archK (ArchS1_Kernel):

    Re archSide (autocorr g)
      = Re (h(i/2) + h(-i/2)) + (psiR 0 - log pi) M + (1/2) ∫∫ |g(v) - g(w)|^2 k(v - w) dv dw,

  psiR 0 = Re psi(1/4), and the double integral is a genuine Lebesgue integral (the integrand is
  integrable: integrable_dirichlet).  This is Connes-Consani's principal value W_R (arXiv
  2006.13771, (39)) written as a Dirichlet form.

  Proof (the N -> infinity limit of E6Bridge32/33's truncated identity):
    * truncation: (1/2pi) ∫ h phi_N = c_N M + (1/2) ∫∫ |Δg|^2 k_{N+1}   (truncated_identity;
      E6Bridge32 integral_hsq_mul_phiN + E6Bridge33 Eb_eq_half for each b in {1/2, 5/2, ...});
    * r side: phi_N -> psiR pointwise (the vertical-line digamma series, Zeta23
      re_digamma_vertical, is EXACT), dominated by h (|psiR| + |gamma + 4|);
    * constants: c_N = phi_N(0) -> psiR 0;
    * u side: |Δg|^2 k_{N+1} increases to |Δg|^2 k everywhere (on the diagonal both vanish);
      the lintegral monotone convergence theorem plus the bound from the r side gives
      integrability, then Bochner monotone convergence identifies the limit.
  No local Lipschitz estimate for the 1/(2|u|) singularity is needed: integrability is a
  consequence of the identity's finite left side.

  No zeros, no RH progress.  conjecture1_proved = False.
-/
import E6Bridge34
import ArchS1_Kernel

open Zeta23 Complex MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace ArchS1
open WeilExplicit RvMBridge11 RvMBridge30 RvMBridge31 RvMBridge32 RvMBridge33 RvMBridge34

/-! ## A. Pointwise limits: phi_N -> psiR and c_N -> psiR 0. -/

lemma phiN_eq_serF (N : ℕ) (r : ℝ) :
    phiN N r = -Real.eulerMascheroniConstant - (1 / 4) / ((1 / 4) ^ 2 + (r / 2) ^ 2)
      + ∑ n ∈ Finset.range N, serF (r / 2) n := by
  unfold phiN
  rw [lor_half_eq]
  congr 1
  exact Finset.sum_congr rfl fun n _ => (serF_eq_lor r n).symm

lemma psiR_eq_tsum (r : ℝ) :
    psiR r = -Real.eulerMascheroniConstant - (1 / 4) / ((1 / 4) ^ 2 + (r / 2) ^ 2)
      + ∑' n : ℕ, serF (r / 2) n := by
  rw [psiR_eq, Zeta23.MuFields.re_digamma_vertical (by norm_num) (by norm_num)]
  rfl

/-- phi_N -> psiR: the digamma series is exact. -/
theorem tendsto_phiN (r : ℝ) : Tendsto (fun N => phiN N r) atTop (𝓝 (psiR r)) := by
  have hs : Summable (fun n : ℕ => serF (r / 2) n) :=
    Zeta23.MuFields.summable_re_terms (a := 1 / 4) (by norm_num) (by norm_num) (r / 2)
  have e : (fun N => phiN N r) = fun N => (-Real.eulerMascheroniConstant
      - (1 / 4) / ((1 / 4) ^ 2 + (r / 2) ^ 2)) + ∑ n ∈ Finset.range N, serF (r / 2) n :=
    funext fun N => phiN_eq_serF N r
  rw [e, psiR_eq_tsum]
  exact tendsto_const_nhds.add hs.hasSum.tendsto_sum_nat

lemma phiN_ge (N : ℕ) (r : ℝ) : -Real.eulerMascheroniConstant - 4 ≤ phiN N r := by
  rw [phiN_eq_serF, lor_half_eq]
  have h1 := lor_le (b := 1 / 2) (by norm_num) r
  have h2 : 0 ≤ ∑ n ∈ Finset.range N, serF (r / 2) n :=
    Finset.sum_nonneg fun n _ => serF_nonneg _ (Nat.cast_nonneg n)
  norm_num at h1
  linarith

lemma phiN_le (N : ℕ) (r : ℝ) : phiN N r ≤ psiR r := psiR_ge_finite r N

/-- c_N = phi_N(0). -/
lemma cN_eq_phiN (N : ℕ) : cN N = phiN N 0 := by
  unfold cN phiN
  have h1 : lor (1 / 2) 0 = 4 := by unfold lor; norm_num
  have h2 : ∀ n : ℕ, lor (bN n) 0 = 2 / bN n := fun n => by
    unfold lor
    have := (bN_pos n).ne'
    field_simp
    ring
  rw [h1]
  simp only [h2]
  ring

theorem tendsto_cN : Tendsto (fun N => cN N) atTop (𝓝 (psiR 0)) := by
  rw [funext cN_eq_phiN]
  exact tendsto_phiN 0

/-- psiR 0 is Re psi(1/4). -/
lemma psiR_zero : psiR 0 = (Complex.digamma (1 / 4)).re := by
  unfold psiR
  simp

/-! ## B. The r side: dominated convergence. -/

theorem tendsto_integral_hsq_mul_phiN {g : ℝ → ℂ} (hg : IsWeilTest g) :
    Tendsto (fun N => ∫ r : ℝ, hsq g r * phiN N r) atTop (𝓝 (∫ r : ℝ, hsq g r * psiR r)) := by
  refine tendsto_integral_of_dominated_convergence
    (fun r => |hsq g r * psiR r| + |Real.eulerMascheroniConstant + 4| * hsq g r)
    (fun N => (integrable_hsq_mul_phiN hg N).aestronglyMeasurable)
    ((integrable_hsq_mul_psiR hg).abs.add ((integrable_hsq hg).const_mul _)) ?_ ?_
  · intro N
    filter_upwards with r
    have hh := hsq_nonneg g r
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hh]
    have h1 := phiN_le N r
    have h2 := phiN_ge N r
    have h3 : |phiN N r| ≤ |psiR r| + |Real.eulerMascheroniConstant + 4| := by
      rw [abs_le]
      constructor
      · linarith [abs_nonneg (psiR r), le_abs_self (Real.eulerMascheroniConstant + 4)]
      · linarith [le_abs_self (psiR r), abs_nonneg (Real.eulerMascheroniConstant + 4)]
    calc hsq g r * |phiN N r| ≤ hsq g r * (|psiR r| + |Real.eulerMascheroniConstant + 4|) :=
          mul_le_mul_of_nonneg_left h3 hh
      _ = hsq g r * |psiR r| + |Real.eulerMascheroniConstant + 4| * hsq g r := by ring
  · filter_upwards with r
    exact (tendsto_phiN r).const_mul (hsq g r)

/-! ## C. The truncated identity. -/

/-- The truncated Dirichlet integrand |g(v) - g(w)|^2 k_N(v - w). -/
def DN (g : ℝ → ℂ) (N : ℕ) (z : ℝ × ℝ) : ℝ := ‖g z.1 - g z.2‖ ^ 2 * kTrunc N (z.1 - z.2)

/-- The Dirichlet integrand |g(v) - g(w)|^2 k(v - w). -/
def Dk (g : ℝ → ℂ) (z : ℝ × ℝ) : ℝ := ‖g z.1 - g z.2‖ ^ 2 * archK (z.1 - z.2)

lemma DN_nonneg (g : ℝ → ℂ) (N : ℕ) (z : ℝ × ℝ) : 0 ≤ DN g N z :=
  mul_nonneg (by positivity) (kTrunc_nonneg N _)

lemma Dk_nonneg (g : ℝ → ℂ) (z : ℝ × ℝ) : 0 ≤ Dk g z :=
  mul_nonneg (by positivity) (archK_nonneg _)

lemma DN_eq_sum (g : ℝ → ℂ) (N : ℕ) (z : ℝ × ℝ) :
    DN g N z = ∑ n ∈ Finset.range N, Rfun g (kb n) z := by
  unfold DN kTrunc Rfun
  rw [Finset.mul_sum]

/-- A test function's support sits in some symmetric interval. -/
lemma exists_tsupport_subset_Icc {g : ℝ → ℂ} (hg : IsWeilTest g) :
    ∃ L : ℝ, tsupport g ⊆ Set.Icc (-L) L := by
  obtain ⟨R, hR⟩ := (IsCompact.isBounded hg.2).subset_closedBall 0
  refine ⟨R, ?_⟩
  rwa [Real.closedBall_eq_Icc, zero_sub, zero_add] at hR

lemma integrable_DN {g : ℝ → ℂ} (hg : IsWeilTest g) (N : ℕ) :
    Integrable (DN g N) (volume.prod volume) := by
  obtain ⟨L, hL⟩ := exists_tsupport_subset_Icc hg
  rw [show DN g N = fun z => ∑ n ∈ Finset.range N, Rfun g (kb n) z from funext (DN_eq_sum g N)]
  exact integrable_finsetSum _ fun n _ => integrable_Rfun hg hL (kb_pos n)

lemma integral_DN {g : ℝ → ℂ} (hg : IsWeilTest g) (N : ℕ) :
    ∫ z : ℝ × ℝ, DN g N z ∂(volume.prod volume) = ∑ n ∈ Finset.range N, 2 * Eb g (kb n) := by
  obtain ⟨L, hL⟩ := exists_tsupport_subset_Icc hg
  rw [show DN g N = fun z => ∑ n ∈ Finset.range N, Rfun g (kb n) z from funext (DN_eq_sum g N),
    integral_finsetSum _ fun n _ => integrable_Rfun hg hL (kb_pos n)]
  refine Finset.sum_congr rfl fun n _ => ?_
  have h := Eb_eq_half hg hL (kb_pos n)
  linarith

lemma re_integral_autocorr_mul_expK (g : ℝ → ℂ) (b : ℝ) :
    (∫ u : ℝ, autocorr g u * (expK b u : ℂ)).re = mass g * (2 / b) - Eb g b := by
  unfold Eb
  ring

/-- THE TRUNCATED IDENTITY: (1/2pi) ∫ h phi_N = c_N M + (1/2) ∫∫ |Δg|^2 k_{N+1}. -/
theorem truncated_identity {g : ℝ → ℂ} (hg : IsWeilTest g) (N : ℕ) :
    (1 / (2 * Real.pi)) * ∫ r : ℝ, hsq g r * phiN N r
      = cN N * mass g + (1 / 2) * ∫ z : ℝ × ℝ, DN g (N + 1) z ∂(volume.prod volume) := by
  rw [integral_DN hg (N + 1), Finset.sum_range_succ', kb_zero, integral_hsq_mul_phiN hg N,
    re_integral_autocorr_mul_expK]
  simp only [kb_succ, re_integral_autocorr_mul_expK]
  unfold cN
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hpi := Real.pi_pos.ne'
  field_simp
  ring

/-! ## D. The limit. -/

/-- The value of the Dirichlet form, read from the r side. -/
def dirichletValue (g : ℝ → ℂ) : ℝ :=
  2 * ((1 / (2 * Real.pi)) * (∫ r : ℝ, hsq g r * psiR r) - psiR 0 * mass g)

theorem tendsto_integral_DN {g : ℝ → ℂ} (hg : IsWeilTest g) :
    Tendsto (fun N => ∫ z : ℝ × ℝ, DN g (N + 1) z ∂(volume.prod volume)) atTop
      (𝓝 (dirichletValue g)) := by
  have e : (fun N => ∫ z : ℝ × ℝ, DN g (N + 1) z ∂(volume.prod volume))
      = fun N => 2 * ((1 / (2 * Real.pi)) * (∫ r : ℝ, hsq g r * phiN N r) - cN N * mass g) :=
    funext fun N => by rw [truncated_identity hg N]; ring
  rw [e]
  unfold dirichletValue
  exact (((tendsto_integral_hsq_mul_phiN hg).const_mul _).sub
    (tendsto_cN.mul_const _)).const_mul 2

lemma DN_mono (g : ℝ → ℂ) (z : ℝ × ℝ) : Monotone fun N => DN g (N + 1) z :=
  fun _ _ hab => mul_le_mul_of_nonneg_left (kTrunc_mono _ (by omega)) (by positivity)

lemma tendsto_DN (g : ℝ → ℂ) (z : ℝ × ℝ) :
    Tendsto (fun N => DN g (N + 1) z) atTop (𝓝 (Dk g z)) := by
  by_cases h : z.1 - z.2 = 0
  · have hz : z.1 = z.2 := sub_eq_zero.mp h
    have e1 : (fun N => DN g (N + 1) z) = fun _ => 0 := funext fun N => by simp [DN, hz]
    have e2 : Dk g z = 0 := by simp [Dk, hz]
    rw [e1, e2]
    exact tendsto_const_nhds
  · exact ((tendsto_kTrunc h).comp (tendsto_add_atTop_nat 1)).const_mul _

lemma measurable_Dk {g : ℝ → ℂ} (hg : IsWeilTest g) : Measurable (Dk g) := by
  have hc := hg.1.continuous
  have h1 : Continuous fun z : ℝ × ℝ => ‖g z.1 - g z.2‖ ^ 2 :=
    ((hc.comp continuous_fst).sub (hc.comp continuous_snd)).norm.pow 2
  exact h1.measurable.mul (measurable_archK.comp (measurable_fst.sub measurable_snd))

/-- THE DIRICHLET INTEGRAND IS INTEGRABLE on the plane (despite k(u) ~ 1/(2|u|) at 0). -/
theorem integrable_Dk {g : ℝ → ℂ} (hg : IsWeilTest g) : Integrable (Dk g) (volume.prod volume) := by
  have hmono : Monotone fun N => ∫ z : ℝ × ℝ, DN g (N + 1) z ∂(volume.prod volume) :=
    fun a b hab => integral_mono (integrable_DN hg _) (integrable_DN hg _) fun z => DN_mono g z hab
  have hle : ∀ N, ∫ z : ℝ × ℝ, DN g (N + 1) z ∂(volume.prod volume) ≤ dirichletValue g :=
    fun N => hmono.ge_of_tendsto (tendsto_integral_DN hg) N
  refine ⟨(measurable_Dk hg).aestronglyMeasurable, ?_⟩
  have hlin : Tendsto (fun N => ∫⁻ z, ENNReal.ofReal (DN g (N + 1) z) ∂(volume.prod volume))
      atTop (𝓝 (∫⁻ z, ENNReal.ofReal (Dk g z) ∂(volume.prod volume))) :=
    lintegral_tendsto_of_tendsto_of_monotone
      (fun N => (integrable_DN hg (N + 1)).aemeasurable.ennreal_ofReal)
      (ae_of_all _ fun z _ _ hab => ENNReal.ofReal_le_ofReal (DN_mono g z hab))
      (ae_of_all _ fun z => (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_DN g z))
  have hbd : ∀ N, ∫⁻ z, ENNReal.ofReal (DN g (N + 1) z) ∂(volume.prod volume)
      ≤ ENNReal.ofReal (dirichletValue g) := fun N => by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_DN hg _)
      (ae_of_all _ (DN_nonneg g _))]
    exact ENNReal.ofReal_le_ofReal (hle N)
  have hfin := le_of_tendsto' hlin hbd
  show ∫⁻ z, ‖Dk g z‖ₑ ∂(volume.prod volume) < ⊤
  rw [lintegral_congr fun z => Real.enorm_eq_ofReal (Dk_nonneg g z)]
  exact lt_of_le_of_lt hfin ENNReal.ofReal_lt_top

theorem integral_Dk {g : ℝ → ℂ} (hg : IsWeilTest g) :
    ∫ z : ℝ × ℝ, Dk g z ∂(volume.prod volume) = dirichletValue g :=
  tendsto_nhds_unique
    (integral_tendsto_of_tendsto_of_monotone (fun N => integrable_DN hg (N + 1)) (integrable_Dk hg)
      (ae_of_all _ (DN_mono g)) (ae_of_all _ (tendsto_DN g)))
    (tendsto_integral_DN hg)

/-! ## E. The theorems. -/

/-- Integrability of the Dirichlet integrand, in explicit form. -/
theorem integrable_dirichlet {g : ℝ → ℂ} (hg : IsWeilTest g) :
    Integrable (fun z : ℝ × ℝ => ‖g z.1 - g z.2‖ ^ 2 * archK (z.1 - z.2)) (volume.prod volume) :=
  integrable_Dk hg

/-- THE ARCHIMEDEAN INTEGRAL IN DIRICHLET FORM:
(1/2pi) ∫ |ĝ|^2 psiR = psiR 0 · ||g||^2 + (1/2) ∫∫ |g(v) - g(w)|^2 k(v - w). -/
theorem arch_integral_dirichlet {g : ℝ → ℂ} (hg : IsWeilTest g) :
    (1 / (2 * Real.pi)) * ∫ r : ℝ, hsq g r * psiR r
      = psiR 0 * mass g
        + (1 / 2) * ∫ z : ℝ × ℝ, ‖g z.1 - g z.2‖ ^ 2 * archK (z.1 - z.2) ∂(volume.prod volume) := by
  have h := integral_Dk hg
  unfold dirichletValue at h
  change (1 / (2 * Real.pi)) * ∫ r : ℝ, hsq g r * psiR r
      = psiR 0 * mass g + (1 / 2) * ∫ z : ℝ × ℝ, Dk g z ∂(volume.prod volume)
  rw [h]
  ring

/-- THE EXACT u-SPACE WEIL IDENTITY (stage S1):
Re archSide (autocorr g) = Re(h(i/2) + h(-i/2)) + (Re psi(1/4) - log pi) ||g||^2
  + (1/2) ∫∫ |g(v) - g(w)|^2 k(v - w) dv dw,   k(u) = e^{3|u|/2}/(e^{2|u|} - 1). -/
theorem archSide_autocorr_dirichlet_identity {g : ℝ → ℂ} (hg : IsWeilTest g) :
    (archSide (autocorr g)).re
      = (weilKernel (autocorr g) 0 + weilKernel (autocorr g) 1).re
        + (psiR 0 - Real.log Real.pi) * mass g
        + (1 / 2) * ∫ z : ℝ × ℝ, ‖g z.1 - g z.2‖ ^ 2 * archK (z.1 - z.2) ∂(volume.prod volume) := by
  unfold archSide
  rw [integral_archIntegrand_autocorr_eq hg, autocorr_zero]
  set W0 := weilKernel (autocorr g) 0
  set W1 := weilKernel (autocorr g) 1
  set J := ∫ r : ℝ, hsq g r * psiR r with hJ
  set M := mass g
  have hre : (W0 + W1 - (M : ℂ) * (Real.log Real.pi : ℂ)
      + (1 / (2 * (Real.pi : ℂ))) * (J : ℂ)).re
      = (W0 + W1).re - M * Real.log Real.pi + (1 / (2 * Real.pi)) * J := by
    rw [show (M : ℂ) * (Real.log Real.pi : ℂ) = ((M * Real.log Real.pi : ℝ) : ℂ) by
        push_cast; ring,
      show (1 / (2 * (Real.pi : ℂ))) * (J : ℂ) = (((1 / (2 * Real.pi)) * J : ℝ) : ℂ) by
        push_cast; ring]
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re]
  rw [hre, hJ, arch_integral_dirichlet hg]
  ring

/-- The pole terms in closed form: Re(h(i/2) + h(-i/2)) = 2 Re(ĝ(-i/2) conj ĝ(i/2)). -/
theorem re_poles_eq {g : ℝ → ℂ} (hg : IsWeilTest g) :
    (weilKernel (autocorr g) 0 + weilKernel (autocorr g) 1).re
      = 2 * (paperFT g (-I / 2) * (starRingEnd ℂ) (paperFT g (I / 2))).re := by
  rw [weilKernel_autocorr_zero_eq hg, weilKernel_autocorr_one_eq hg]
  set a := paperFT g (-I / 2)
  set b := paperFT g (I / 2)
  have : b * (starRingEnd ℂ) a = (starRingEnd ℂ) (a * (starRingEnd ℂ) b) := by
    rw [map_mul, Complex.conj_conj, mul_comm]
  rw [this, Complex.add_re, Complex.conj_re]
  ring

/-- The identity with the pole terms written through ĝ(±i/2) and psiR 0 as Re psi(1/4). -/
theorem archSide_autocorr_dirichlet_identity' {g : ℝ → ℂ} (hg : IsWeilTest g) :
    (archSide (autocorr g)).re
      = 2 * (paperFT g (-I / 2) * (starRingEnd ℂ) (paperFT g (I / 2))).re
        + ((Complex.digamma (1 / 4)).re - Real.log Real.pi) * mass g
        + (1 / 2) * ∫ z : ℝ × ℝ, ‖g z.1 - g z.2‖ ^ 2 * archK (z.1 - z.2) ∂(volume.prod volume) := by
  rw [archSide_autocorr_dirichlet_identity hg, re_poles_eq hg, psiR_zero]

/-- Pole-free class (paperFT g (i/2) = 0): no pole terms. -/
theorem archSide_autocorr_dirichlet_identity_poleFree {g : ℝ → ℂ} (hg : IsWeilTest g)
    (h0 : paperFT g (I / 2) = 0) :
    (archSide (autocorr g)).re
      = (psiR 0 - Real.log Real.pi) * mass g
        + (1 / 2) * ∫ z : ℝ × ℝ, ‖g z.1 - g z.2‖ ^ 2 * archK (z.1 - z.2) ∂(volume.prod volume) := by
  rw [archSide_autocorr_dirichlet_identity hg]
  obtain ⟨hz, ho⟩ := poles_vanish hg h0
  rw [hz, ho, add_zero, Complex.zero_re, zero_add]

/-- On the prime-free window 2L <= log 2 the identity is the Weil functional itself. -/
theorem weilForm_autocorr_dirichlet_identity {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) (hL : 2 * L ≤ Real.log 2) :
    (weilForm (autocorr g)).re
      = (weilKernel (autocorr g) 0 + weilKernel (autocorr g) 1).re
        + (psiR 0 - Real.log Real.pi) * mass g
        + (1 / 2) * ∫ z : ℝ × ℝ, ‖g z.1 - g z.2‖ ^ 2 * archK (z.1 - z.2) ∂(volume.prod volume) := by
  rw [weilForm_autocorr_eq_archSide hg hsupp hL, archSide_autocorr_dirichlet_identity hg]

end ArchS1
