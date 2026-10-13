/-
  ArchS3_Mellin -- the Mellin transform of cos on the critical strip (2026-10-11, stage S3
  milestone M2a of telperion/docs/ARCHIMEDEAN_CONCEPTUAL_BLUEPRINT_2026-10-11.md).

  Psi(z) = 2 ∫_0^∞ s^{z-1} cos(2 pi s) ds (0 < Re z < 1) is CC's unitary u in the Mellin picture.
  We reach it through the damped transforms (absolutely convergent for eps > 0):

    ∫_0^∞ s^{z-1} 2cos(2 pi s) e^{-eps s} ds = Gamma(z) ((eps - 2 pi i)^{-z} + (eps + 2 pi i)^{-z})
                                            =: PsiE eps z,
    ∫_0^∞ log s · s^{z-1} 2cos(2 pi s) e^{-eps s} ds = d/dz PsiE eps z =: dPsiE eps z,

  and Psi := PsiE 0.  Proved here:
    * the Gamma integral with a COMPLEX rate r, Re r > 0 (Mathlib has only real r): identity theorem;
    * its z-derivative (Mathlib's Mellin derivative);
    * continuity of PsiE, dPsiE at eps = 0;
    * the closed form Psi z = Gammaℂ z cos(pi z / 2) = Gammaℝ z / Gammaℝ (1 - z);
    * on the critical line z = 1/2 + i t:  |Psi z| = 1  and  Re(Psi'(z) conj Psi(z)) = psiR t - log pi
      (2 theta'(t) is the phase derivative of u).
  The improper-integral form of Psi is in ArchS3_Phi.

  No zeros, no RH progress.  conjecture1_proved = False.
-/
import ArchS3_Delta

open MeasureTheory Filter Topology Complex Set Asymptotics
open scoped ComplexConjugate

noncomputable section

namespace ArchS3

/-! ## A. The Gamma integral with a complex rate. -/

/-- ∫_0^∞ s^{z-1} e^{-r s} ds. -/
def gInt (z r : ℂ) : ℂ := ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (z - 1) * cexp (-(r * s))

lemma continuousOn_ofReal_cpow (w : ℂ) : ContinuousOn (fun s : ℝ => (s : ℂ) ^ w) (Ioi 0) :=
  fun s hs => (continuousAt_ofReal_cpow_const s w (Or.inr (ne_of_gt hs))).continuousWithinAt

lemma norm_gInt_integrand (z r : ℂ) {s : ℝ} (hs : 0 < s) :
    ‖(s : ℂ) ^ (z - 1) * cexp (-(r * s))‖ = s ^ (z.re - 1) * Real.exp (-r.re * s) := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hs, Complex.norm_exp]
  congr 2
  simp

lemma integrableOn_rpow_exp {σ b : ℝ} (hσ : -1 < σ) (hb : 0 < b) :
    IntegrableOn (fun s : ℝ => s ^ σ * Real.exp (-b * s)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow hσ one_pos hb
  simpa [Real.rpow_one] using h

lemma integrableOn_gInt {z r : ℂ} (hz : 0 < z.re) (hr : 0 < r.re) :
    IntegrableOn (fun s : ℝ => (s : ℂ) ^ (z - 1) * cexp (-(r * s))) (Ioi 0) := by
  refine (integrableOn_rpow_exp (σ := z.re - 1) (by linarith) hr).mono' ?_ ?_
  · exact ((continuousOn_ofReal_cpow _).mul (by fun_prop)).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_)
    rw [norm_gInt_integrand z r hs]

/-- d/dr ∫ s^{z-1} e^{-r s} = ∫ s^{z-1} (-s) e^{-r s}  on Re r > 0. -/
lemma hasDerivAt_gInt {z r₀ : ℂ} (hz : 0 < z.re) (hr : 0 < r₀.re) :
    HasDerivAt (fun r => gInt z r)
      (∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (z - 1) * (-(s : ℂ)) * cexp (-(r₀ * s))) r₀ := by
  have hδ : 0 < r₀.re / 2 := by linarith
  have hball : ∀ r ∈ Metric.ball r₀ (r₀.re / 2), r₀.re / 2 < r.re := by
    intro r hr'
    rw [Metric.mem_ball, dist_eq_norm] at hr'
    have := abs_re_le_norm (r - r₀)
    rw [sub_re] at this
    have := (abs_lt.mp (lt_of_le_of_lt this hr')).1
    linarith
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ))) (bound := fun s : ℝ => s ^ z.re * Real.exp (-(r₀.re / 2) * s))
    (F := fun (r : ℂ) (s : ℝ) => (s : ℂ) ^ (z - 1) * cexp (-(r * s)))
    (F' := fun (r : ℂ) (s : ℝ) => (s : ℂ) ^ (z - 1) * (-(s : ℂ)) * cexp (-(r * s)))
    (Metric.ball_mem_nhds r₀ hδ) ?_ (integrableOn_gInt hz hr) ?_ ?_
    (integrableOn_rpow_exp (by linarith) hδ) ?_).2
  · exact Eventually.of_forall fun r =>
      ((continuousOn_ofReal_cpow _).mul (by fun_prop)).aestronglyMeasurable measurableSet_Ioi
  · exact (((continuousOn_ofReal_cpow _).mul (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
      measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs r hr' => ?_)
    have hs' : (0 : ℝ) < s := hs
    have hre := hball r hr'
    rw [mul_comm ((s : ℂ) ^ (z - 1)) (-(s : ℂ)), mul_assoc, norm_mul, norm_gInt_integrand z r hs',
      norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs', ← mul_assoc,
      show s * s ^ (z.re - 1) = s ^ z.re by
        rw [mul_comm, ← Real.rpow_add_one hs'.ne']; ring_nf]
    gcongr
  · refine Eventually.of_forall fun s r _ => ?_
    have h := (((hasDerivAt_id r).mul_const (s : ℂ)).neg.cexp).const_mul ((s : ℂ) ^ (z - 1))
    refine h.congr_deriv ?_
    simp only [id, one_mul, Pi.neg_apply]
    ring

lemma isOpen_rightHalf : IsOpen {r : ℂ | 0 < r.re} := isOpen_lt continuous_const continuous_re

lemma one_div_mem_slitPlane {r : ℂ} (hr : 0 < r.re) : 1 / r ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  left
  have hr0 : r ≠ 0 := fun h => by simp [h] at hr
  rw [one_div, inv_re]
  exact div_pos hr (normSq_pos.mpr hr0)

/-- THE GAMMA INTEGRAL WITH A COMPLEX RATE: ∫_0^∞ s^{z-1} e^{-r s} ds = (1/r)^z Gamma(z), Re r > 0. -/
theorem gInt_eq {z r : ℂ} (hz : 0 < z.re) (hr : 0 < r.re) :
    gInt z r = (1 / r) ^ z * Gamma z := by
  set U : Set ℂ := {r : ℂ | 0 < r.re}
  have hfd : DifferentiableOn ℂ (fun r => gInt z r) U :=
    fun r hr' => (hasDerivAt_gInt hz hr').differentiableAt.differentiableWithinAt
  have hf : AnalyticOnNhd ℂ (fun r => gInt z r) U := hfd.analyticOnNhd isOpen_rightHalf
  have hgd : DifferentiableOn ℂ (fun r : ℂ => (1 / r) ^ z * Gamma z) U := by
    intro r hr'
    have hr0 : r ≠ 0 := fun h => by simp [U, h] at hr'
    exact ((((differentiableAt_const _).div differentiableAt_id hr0).cpow_const
      (one_div_mem_slitPlane (show 0 < r.re from hr'))).mul_const _).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ (fun r : ℂ => (1 / r) ^ z * Gamma z) U :=
    hgd.analyticOnNhd isOpen_rightHalf
  have hU : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have h1 : (1 : ℂ) ∈ U := by simp [U]
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), gInt z w = (1 / w) ^ z * Gamma z := by
    have hT : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have := (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := {1}ᶜ))
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simpa using hx
    refine hT.frequently (Eventually.frequently ?_)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with x hx
    unfold gInt
    exact integral_cpow_mul_exp_neg_mul_Ioi hz hx
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hU h1 hfreq hr

/-! ## B. The z-derivative of the Gamma integral (Mellin derivative). -/

/-- ∫_0^∞ log s · s^{z-1} e^{-r s} ds = d/dz [(1/r)^z Gamma z]. -/
theorem integral_log_gInt {z r : ℂ} (hz : 0 < z.re) (hr : 0 < r.re) :
    ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (z - 1) * ((Real.log s : ℂ) * cexp (-(r * s)))
      = (1 / r) ^ z * Complex.log (1 / r) * Gamma z + (1 / r) ^ z * deriv Gamma z := by
  set f : ℝ → ℂ := fun s => cexp (-(r * s))
  have hnorm : (fun s : ℝ => ‖f s‖) = fun s => Real.exp (-r.re * s) := by
    funext s; simp [f, Complex.norm_exp, Complex.mul_re]
  have hfc : LocallyIntegrableOn f (Ioi 0) :=
    (by fun_prop : Continuous f).locallyIntegrable.locallyIntegrableOn _
  have htop : f =O[atTop] (· ^ (-(z.re + 1))) := by
    rw [← isBigO_norm_left, hnorm]
    exact (isLittleO_exp_neg_mul_rpow_atTop hr _).isBigO
  have hbot : f =O[𝓝[>] 0] (· ^ (-(0 : ℝ))) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : (0 : ℝ) < s := hs
    rw [neg_zero, Real.rpow_zero, norm_one, one_mul]
    simp only [f, Complex.norm_exp]
    rw [show (-(r * (s : ℂ))).re = -(r.re * s) by simp [Complex.mul_re]]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  obtain ⟨-, hD⟩ := mellin_hasDerivAt_of_isBigO_rpow hfc htop (by linarith) hbot hz
  -- mellin f agrees with the closed form near z
  have hev : (fun w => (1 / r) ^ w * Gamma w) =ᶠ[𝓝 z] mellin f := by
    filter_upwards [isOpen_rightHalf.mem_nhds hz] with w hw
    rw [← gInt_eq hw hr]
    simp [mellin, gInt, f, smul_eq_mul]
  have hD' := hD.congr_of_eventuallyEq hev
  have hr0 : r ≠ 0 := fun h => by simp [h] at hr
  have hGam := (differentiableAt_Gamma z (fun m h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])).hasDerivAt
  have hE := ((hasDerivAt_id z).const_cpow (c := 1 / r) (Or.inl (one_div_ne_zero hr0))).mul hGam
  have huniq := hD'.unique hE
  simp only [id, mul_one] at huniq
  rw [show (∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (z - 1) * ((Real.log s : ℂ) * cexp (-(r * s))))
      = mellin (fun t => Real.log t • f t) z by simp [mellin, f, smul_eq_mul, Complex.real_smul],
    huniq]

/-! ## C. The damped transforms of cos and their limits. -/

def rM (ε : ℝ) : ℂ := (ε : ℂ) - 2 * Real.pi * I
def rP (ε : ℝ) : ℂ := (ε : ℂ) + 2 * Real.pi * I

/-- PsiE eps z = Gamma(z) ((eps - 2 pi i)^{-z} + (eps + 2 pi i)^{-z}). -/
def PsiE (ε : ℝ) (z : ℂ) : ℂ := ((1 / rM ε) ^ z + (1 / rP ε) ^ z) * Gamma z

/-- Its z-derivative. -/
def dPsiE (ε : ℝ) (z : ℂ) : ℂ :=
  ((1 / rM ε) ^ z * Complex.log (1 / rM ε) + (1 / rP ε) ^ z * Complex.log (1 / rP ε)) * Gamma z
    + ((1 / rM ε) ^ z + (1 / rP ε) ^ z) * deriv Gamma z

/-- CC's u in the Mellin picture: Psi z = 2 ∫_0^∞ s^{z-1} cos(2 pi s) ds. -/
def Psi (z : ℂ) : ℂ := PsiE 0 z

def dPsi (z : ℂ) : ℂ := dPsiE 0 z

/-- The damped cosine 2 cos(2 pi s) e^{-eps s}. -/
def cosD (ε s : ℝ) : ℂ := ((2 * Real.cos (2 * Real.pi * s) * Real.exp (-ε * s) : ℝ) : ℂ)

lemma cosD_eq (ε s : ℝ) : cosD ε s = cexp (-(rM ε * s)) + cexp (-(rP ε * s)) := by
  unfold cosD rM rP
  have e1 : -(((ε : ℂ) - 2 * Real.pi * I) * s) = ((-ε * s : ℝ) : ℂ) + ((2 * Real.pi * s : ℝ) : ℂ) * I := by
    push_cast; ring
  have e2 : -(((ε : ℂ) + 2 * Real.pi * I) * s) = ((-ε * s : ℝ) : ℂ) - ((2 * Real.pi * s : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [e1, e2, Complex.exp_add, Complex.exp_sub, ← Complex.ofReal_exp]
  push_cast
  rw [Complex.cos, neg_mul, Complex.exp_neg]
  field_simp

lemma rM_re (ε : ℝ) : (rM ε).re = ε := by simp [rM]
lemma rP_re (ε : ℝ) : (rP ε).re = ε := by simp [rP]
lemma rM_ne_zero (ε : ℝ) : rM ε ≠ 0 := fun h => by
  have := congrArg Complex.im h; simp [rM, Real.pi_ne_zero] at this
lemma rP_ne_zero (ε : ℝ) : rP ε ≠ 0 := fun h => by
  have := congrArg Complex.im h; simp [rP, Real.pi_ne_zero] at this

lemma Gamma_poles_ne {z : ℂ} (hz : 0 < z.re) : ∀ m : ℕ, z ≠ -m := fun m h => by
  have := congrArg Complex.re h
  simp at this
  linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

lemma integrableOn_cosD {ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun s : ℝ => (s : ℂ) ^ (z - 1) * cosD ε s) (Ioi 0) := by
  have h1 := integrableOn_gInt hz (r := rM ε) (by rw [rM_re]; exact hε)
  have h2 := integrableOn_gInt hz (r := rP ε) (by rw [rP_re]; exact hε)
  refine (h1.add h2).congr_fun (fun s _ => ?_) measurableSet_Ioi
  simp only [cosD_eq, Pi.add_apply]; ring

/-- THE DAMPED MELLIN TRANSFORM OF cos: ∫_0^∞ s^{z-1} 2cos(2 pi s) e^{-eps s} ds = PsiE eps z. -/
theorem integral_cosD {ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz : 0 < z.re) :
    ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (z - 1) * cosD ε s = PsiE ε z := by
  have h1 := integrableOn_gInt hz (r := rM ε) (by rw [rM_re]; exact hε)
  have h2 := integrableOn_gInt hz (r := rP ε) (by rw [rP_re]; exact hε)
  have e : (fun s : ℝ => (s : ℂ) ^ (z - 1) * cosD ε s)
      = fun s : ℝ => (s : ℂ) ^ (z - 1) * cexp (-(rM ε * s)) + (s : ℂ) ^ (z - 1) * cexp (-(rP ε * s)) := by
    funext s; rw [cosD_eq]; ring
  rw [e, integral_add h1 h2]
  change gInt z (rM ε) + gInt z (rP ε) = PsiE ε z
  rw [gInt_eq hz (by rw [rM_re]; exact hε), gInt_eq hz (by rw [rP_re]; exact hε), PsiE]
  ring

/-- The log-weighted Gamma integrand is integrable (Re z > 0, Re r > 0). -/
lemma integrableOn_log_gInt {z r : ℂ} (hz : 0 < z.re) (hr : 0 < r.re) :
    IntegrableOn (fun s : ℝ => (s : ℂ) ^ (z - 1) * ((Real.log s : ℂ) * cexp (-(r * s)))) (Ioi 0) := by
  set f : ℝ → ℂ := fun s => cexp (-(r * s))
  have hnorm : (fun s : ℝ => ‖f s‖) = fun s => Real.exp (-r.re * s) := by
    funext s; simp [f, Complex.norm_exp, Complex.mul_re]
  have hfc : LocallyIntegrableOn f (Ioi 0) :=
    (by fun_prop : Continuous f).locallyIntegrable.locallyIntegrableOn _
  have htop : f =O[atTop] (· ^ (-(z.re + 1))) := by
    rw [← isBigO_norm_left, hnorm]
    exact (isLittleO_exp_neg_mul_rpow_atTop hr _).isBigO
  have hbot : f =O[𝓝[>] 0] (· ^ (-(0 : ℝ))) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : (0 : ℝ) < s := hs
    rw [neg_zero, Real.rpow_zero, norm_one, one_mul]
    simp only [f, Complex.norm_exp]
    rw [show (-(r * (s : ℂ))).re = -(r.re * s) by simp [Complex.mul_re]]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  obtain ⟨hconv, -⟩ := mellin_hasDerivAt_of_isBigO_rpow hfc htop (by linarith) hbot hz
  have := hconv
  unfold MellinConvergent at this
  refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
  simp [f, smul_eq_mul, Complex.real_smul]

/-- ∫_0^∞ log s · s^{z-1} 2cos(2 pi s) e^{-eps s} ds = dPsiE eps z. -/
theorem integral_log_cosD {ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz : 0 < z.re) :
    ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (z - 1) * ((Real.log s : ℂ) * cosD ε s) = dPsiE ε z := by
  have hM : 0 < (rM ε).re := by rw [rM_re]; exact hε
  have hP : 0 < (rP ε).re := by rw [rP_re]; exact hε
  have hint : ∀ r : ℂ, 0 < r.re →
      IntegrableOn (fun s : ℝ => (s : ℂ) ^ (z - 1) * ((Real.log s : ℂ) * cexp (-(r * s)))) (Ioi 0) :=
    fun r hr => integrableOn_log_gInt hz hr
  have e : (fun s : ℝ => (s : ℂ) ^ (z - 1) * ((Real.log s : ℂ) * cosD ε s))
      = fun s : ℝ => (s : ℂ) ^ (z - 1) * ((Real.log s : ℂ) * cexp (-(rM ε * s)))
          + (s : ℂ) ^ (z - 1) * ((Real.log s : ℂ) * cexp (-(rP ε * s))) := by
    funext s; rw [cosD_eq]; ring
  rw [e, integral_add (hint _ hM) (hint _ hP), integral_log_gInt hz hM, integral_log_gInt hz hP, dPsiE]
  ring

lemma integrableOn_log_cosD {ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun s : ℝ => (s : ℂ) ^ (z - 1) * ((Real.log s : ℂ) * cosD ε s)) (Ioi 0) := by
  have h1 := integrableOn_log_gInt hz (r := rM ε) (by rw [rM_re]; exact hε)
  have h2 := integrableOn_log_gInt hz (r := rP ε) (by rw [rP_re]; exact hε)
  refine (h1.add h2).congr_fun (fun s _ => ?_) measurableSet_Ioi
  simp only [cosD_eq, Pi.add_apply]; ring

lemma one_div_rM_mem_slitPlane (ε : ℝ) : 1 / rM ε ∈ slitPlane := by
  rw [mem_slitPlane_iff]; right
  rw [one_div, inv_im]
  have : (rM ε).im = -(2 * Real.pi) := by simp [rM]
  rw [this]
  have h0 : 0 < normSq (rM ε) := normSq_pos.mpr (rM_ne_zero ε)
  have : 0 < 2 * Real.pi := by positivity
  intro h
  rw [neg_neg, div_eq_zero_iff] at h
  rcases h with h | h <;> linarith

lemma one_div_rP_mem_slitPlane (ε : ℝ) : 1 / rP ε ∈ slitPlane := by
  rw [mem_slitPlane_iff]; right
  rw [one_div, inv_im]
  have : (rP ε).im = 2 * Real.pi := by simp [rP]
  rw [this]
  have : 0 < 2 * Real.pi := by positivity
  intro h
  rw [neg_div, neg_eq_zero, div_eq_zero_iff] at h
  rcases h with h | h
  · linarith
  · exact rP_ne_zero ε (normSq_eq_zero.mp h)

lemma continuous_one_div_rM : Continuous fun ε : ℝ => 1 / rM ε :=
  continuous_const.div (by unfold rM; fun_prop) fun ε => rM_ne_zero ε

lemma continuous_one_div_rP : Continuous fun ε : ℝ => 1 / rP ε :=
  continuous_const.div (by unfold rP; fun_prop) fun ε => rP_ne_zero ε

lemma continuous_PsiE (z : ℂ) : Continuous fun ε : ℝ => PsiE ε z := by
  unfold PsiE
  refine Continuous.mul ?_ continuous_const
  refine Continuous.add ?_ ?_
  · exact continuous_iff_continuousAt.mpr fun ε =>
      (continuous_one_div_rM.continuousAt).cpow continuousAt_const (one_div_rM_mem_slitPlane ε)
  · exact continuous_iff_continuousAt.mpr fun ε =>
      (continuous_one_div_rP.continuousAt).cpow continuousAt_const (one_div_rP_mem_slitPlane ε)

lemma continuous_dPsiE (z : ℂ) : Continuous fun ε : ℝ => dPsiE ε z := by
  unfold dPsiE
  have cM : Continuous fun ε : ℝ => (1 / rM ε) ^ z := continuous_iff_continuousAt.mpr fun ε =>
    (continuous_one_div_rM.continuousAt).cpow continuousAt_const (one_div_rM_mem_slitPlane ε)
  have cP : Continuous fun ε : ℝ => (1 / rP ε) ^ z := continuous_iff_continuousAt.mpr fun ε =>
    (continuous_one_div_rP.continuousAt).cpow continuousAt_const (one_div_rP_mem_slitPlane ε)
  have lM : Continuous fun ε : ℝ => Complex.log (1 / rM ε) := continuous_iff_continuousAt.mpr
    fun ε => (continuous_one_div_rM.continuousAt).clog (one_div_rM_mem_slitPlane ε)
  have lP : Continuous fun ε : ℝ => Complex.log (1 / rP ε) := continuous_iff_continuousAt.mpr
    fun ε => (continuous_one_div_rP.continuousAt).clog (one_div_rP_mem_slitPlane ε)
  exact (((cM.mul lM).add (cP.mul lP)).mul continuous_const).add ((cM.add cP).mul continuous_const)

lemma tendsto_PsiE (z : ℂ) : Tendsto (fun ε : ℝ => PsiE ε z) (𝓝[>] 0) (𝓝 (Psi z)) :=
  ((continuous_PsiE z).tendsto 0).mono_left nhdsWithin_le_nhds

lemma tendsto_dPsiE (z : ℂ) : Tendsto (fun ε : ℝ => dPsiE ε z) (𝓝[>] 0) (𝓝 (dPsi z)) :=
  ((continuous_dPsiE z).tendsto 0).mono_left nhdsWithin_le_nhds

/-- PsiE eps is differentiable in z with derivative dPsiE eps (Re z > 0). -/
lemma hasDerivAt_PsiE (ε : ℝ) {z : ℂ} (hz : 0 < z.re) : HasDerivAt (PsiE ε) (dPsiE ε z) z := by
  have hGam := (differentiableAt_Gamma z (Gamma_poles_ne hz)).hasDerivAt
  have hM := (hasDerivAt_id z).const_cpow (c := 1 / rM ε) (Or.inl (one_div_ne_zero (rM_ne_zero ε)))
  have hP := (hasDerivAt_id z).const_cpow (c := 1 / rP ε) (Or.inl (one_div_ne_zero (rP_ne_zero ε)))
  have h := (hM.add hP).mul hGam
  refine h.congr_deriv ?_
  simp only [id, mul_one, dPsiE, Pi.add_apply]

/-! ## D. The closed form of Psi. -/

lemma one_div_rM_zero : 1 / rM 0 = ((1 / (2 * Real.pi) : ℝ) : ℂ) * I := by
  rw [div_eq_iff (rM_ne_zero 0)]
  unfold rM
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

lemma one_div_rP_zero : 1 / rP 0 = ((1 / (2 * Real.pi) : ℝ) : ℂ) * (-I) := by
  rw [div_eq_iff (rP_ne_zero 0)]
  unfold rP
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- (c · I)^z = c^{-1}... : for c > 0, (c I)^z = exp(z log c) exp(i pi z / 2). -/
lemma cpow_pos_mul_I {c : ℝ} (hc : 0 < c) (z : ℂ) :
    ((c : ℂ) * I) ^ z = cexp (z * Real.log c) * cexp (Real.pi / 2 * I * z) := by
  have hne : (c : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hc.ne') I_ne_zero
  rw [cpow_def_of_ne_zero hne, ← Complex.exp_add]
  congr 1
  rw [Complex.log, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
    abs_of_pos hc, arg_real_mul _ hc, arg_I]
  push_cast
  ring

lemma cpow_pos_mul_neg_I {c : ℝ} (hc : 0 < c) (z : ℂ) :
    ((c : ℂ) * (-I)) ^ z = cexp (z * Real.log c) * cexp (-(Real.pi / 2 * I * z)) := by
  have hne : (c : ℂ) * (-I) ≠ 0 := mul_ne_zero (by exact_mod_cast hc.ne') (neg_ne_zero.mpr I_ne_zero)
  rw [cpow_def_of_ne_zero hne, ← Complex.exp_add]
  congr 1
  rw [Complex.log, norm_mul, Complex.norm_real, norm_neg, Complex.norm_I, mul_one, Real.norm_eq_abs,
    abs_of_pos hc, arg_real_mul _ hc, arg_neg_I]
  push_cast
  ring

/-- Psi z = Gammaℂ z · cos(pi z / 2). -/
theorem Psi_eq_Gammaℂ (z : ℂ) : Psi z = Gammaℂ z * Complex.cos (Real.pi * z / 2) := by
  have hc : (0 : ℝ) < 1 / (2 * Real.pi) := by positivity
  unfold Psi PsiE
  rw [one_div_rM_zero, one_div_rP_zero, cpow_pos_mul_I hc, cpow_pos_mul_neg_I hc, Gammaℂ_def]
  have hlog : (Real.log (1 / (2 * Real.pi)) : ℂ) = -Complex.log (2 * Real.pi) := by
    rw [one_div, Real.log_inv, Complex.ofReal_neg, Complex.ofReal_log (by positivity)]
    push_cast; rfl
  have hcpow : (2 * (Real.pi : ℂ)) ^ (-z) = cexp (z * -Complex.log (2 * Real.pi)) := by
    rw [cpow_def_of_ne_zero (by exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0))]
    ring_nf
  rw [hlog, hcpow, Complex.cos]
  rw [show (Real.pi : ℂ) * z / 2 * I = Real.pi / 2 * I * z by ring,
    show -((Real.pi : ℂ) * z / 2) * I = -(Real.pi / 2 * I * z) by ring]
  ring

lemma no_odd_neg_pole {z : ℂ} (hz : 0 < z.re) : ∀ n : ℕ, z ≠ -(2 * n + 1) := fun n h => by
  have := congrArg Complex.re h
  simp at this
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- Psi z = Gammaℝ z / Gammaℝ (1 - z)  (the functional-equation factor). -/
theorem Psi_eq_Gammaℝ {z : ℂ} (hz : 0 < z.re) : Psi z = Gammaℝ z / Gammaℝ (1 - z) := by
  rw [Gammaℝ_div_Gammaℝ_one_sub (no_odd_neg_pole hz), Psi_eq_Gammaℂ]

/-! ## E. The critical line: |Psi| = 1 and the phase derivative. -/

/-- z_t = 1/2 + i t. -/
def zt (t : ℝ) : ℂ := 1 / 2 + (t : ℂ) * I

lemma zt_re (t : ℝ) : (zt t).re = 1 / 2 := by simp [zt]

lemma one_sub_zt (t : ℝ) : 1 - zt t = conj (zt t) := by
  apply Complex.ext <;> simp [zt]; norm_num

lemma conj_two : conj (2 : ℂ) = 2 := by apply Complex.ext <;> simp

lemma Gammaℝ_conj (s : ℂ) : Gammaℝ (conj s) = conj (Gammaℝ s) := by
  rw [Gammaℝ_def, Gammaℝ_def, map_mul]
  congr 1
  · rw [show -conj s / 2 = conj (-s / 2) by rw [map_div₀, map_neg, conj_two]]
    rw [cpow_conj _ _ (by rw [arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_pos.ne)]
    simp
  · rw [show conj s / 2 = conj (s / 2) by rw [map_div₀, conj_two], Gamma_conj]

lemma Gammaℝ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : Gammaℝ s ≠ 0 := by
  rw [Ne, Gammaℝ_eq_zero_iff]
  rintro ⟨n, hn⟩
  have := congrArg Complex.re hn
  simp at this
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- |Psi(1/2 + i t)| = 1: u is unitary. -/
theorem norm_Psi_zt (t : ℝ) : ‖Psi (zt t)‖ = 1 := by
  have hz : 0 < (zt t).re := by rw [zt_re]; norm_num
  rw [Psi_eq_Gammaℝ hz, one_sub_zt, Gammaℝ_conj, norm_div, Complex.norm_conj]
  exact div_self (norm_ne_zero_iff.mpr (Gammaℝ_ne_zero_of_re_pos hz))

/-- The log-derivative of Gammaℝ: Gammaℝ'(s) = Gammaℝ(s) (-log pi / 2 + digamma(s/2) / 2). -/
lemma hasDerivAt_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt Gammaℝ (Gammaℝ s * (-Complex.log Real.pi / 2 + digamma (s / 2) / 2)) s := by
  have hs2 : 0 < (s / 2).re := by simp; linarith
  have hGne : Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero (Gamma_poles_ne hs2)
  have hGd := (differentiableAt_Gamma (s / 2) (Gamma_poles_ne hs2)).hasDerivAt
  have h1 := ((hasDerivAt_id' s).neg.div_const 2).const_cpow (c := (Real.pi : ℂ))
    (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  have h2 := hGd.comp s ((hasDerivAt_id' s).div_const 2)
  have h := h1.mul h2
  have hfun : Gammaℝ = fun s => (Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) := by
    funext x; rw [Gammaℝ_def]
  rw [hfun]
  refine h.congr_deriv ?_
  have hdig : deriv Gamma (s / 2) = digamma (s / 2) * Gamma (s / 2) := by
    rw [digamma_def, logDeriv_apply]; field_simp
  simp only [Pi.neg_apply, Function.comp, hdig]
  ring

/-- THE PHASE DERIVATIVE: Re(Psi'(z_t) conj Psi(z_t)) = psiR t - log pi  (= 2 theta'(t)). -/
theorem re_dPsi_mul_conj_Psi (t : ℝ) :
    (dPsi (zt t) * conj (Psi (zt t))).re = RvMBridge11.psiR t - Real.log Real.pi := by
  set z := zt t
  have hz : 0 < z.re := by rw [zt_re]; norm_num
  have h1z : 0 < (1 - z).re := by simp [z, zt]; norm_num
  have hG1 := hasDerivAt_Gammaℝ hz
  have hG2 := (hasDerivAt_Gammaℝ h1z).comp z ((hasDerivAt_id z).const_sub 1)
  have hne := Gammaℝ_ne_zero_of_re_pos h1z
  have hq := hG1.div hG2 hne
  -- Psi agrees with the quotient near z
  have hev : (fun w => Gammaℝ w / (Gammaℝ ∘ fun x => 1 - id x) w) =ᶠ[𝓝 z] Psi := by
    filter_upwards [isOpen_rightHalf.mem_nhds hz] with w hw
    simp only [Function.comp, id]
    exact (Psi_eq_Gammaℝ hw).symm
  have hPsi : HasDerivAt Psi (dPsi z) z := hasDerivAt_PsiE 0 hz
  have huniq := (hq.congr_of_eventuallyEq hev.symm).unique hPsi
  -- dPsi z = Psi z * (Lz + L(1-z))
  set Lz := -Complex.log Real.pi / 2 + digamma (z / 2) / 2
  set L1 := -Complex.log Real.pi / 2 + digamma ((1 - z) / 2) / 2
  have hD : dPsi z = Psi z * (Lz + L1) := by
    rw [← huniq, Psi_eq_Gammaℝ hz]
    simp only [Function.comp]
    field_simp
    ring
  have hn : Psi z * conj (Psi z) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_Psi_zt]; simp
  rw [hD, show Psi z * (Lz + L1) * conj (Psi z) = (Psi z * conj (Psi z)) * (Lz + L1) by ring, hn,
    one_mul]
  have hz2 : z / 2 = 1 / 4 + ((t : ℂ) / 2) * I := by simp only [z, zt]; ring
  have h1z2 : (1 - z) / 2 = 1 / 4 + (((-t : ℝ) : ℂ) / 2) * I := by simp only [z, zt]; push_cast; ring
  have hpsi1 : (digamma (z / 2)).re = RvMBridge11.psiR t := by rw [hz2]; rfl
  have hpsi2 : (digamma ((1 - z) / 2)).re = RvMBridge11.psiR t := by
    rw [h1z2, ← RvMBridge30.psiR_neg t]; rfl
  have hlogpi : (Complex.log (Real.pi : ℂ)).re = Real.log Real.pi := by
    rw [← Complex.ofReal_log Real.pi_pos.le, Complex.ofReal_re]
  simp only [Lz, L1, Complex.add_re, Complex.div_re, Complex.neg_re, hpsi1, hpsi2, hlogpi]
  norm_num
  ring

end ArchS3
