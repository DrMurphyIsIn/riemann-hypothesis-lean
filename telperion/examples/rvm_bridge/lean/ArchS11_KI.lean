/-
  ArchS11_KI -- STAGE S11: the spectral certificate for Connes-Consani's operator K_I
  (rvm_bridge island, 2026-10-11).  conjecture1_proved = False.  Nothing here is RH progress.

  K_I is the integral operator on L²(I) with kernel χ(y - x) (CC (104), S8 `prop55_KI`); its spectrum
  depends only on |I|, and we take I = [0, |I|].  The theorems are stated for ANY continuous
  Hermitian kernel κ with |κ(x, y) - chiPoly(y - x)| ≤ δ on I² (`ChiApprox`), δ ≤ deltaChi = 1.41e-7
  (S10's `chi_enclosure`), and instantiated for CC's χ itself (`chiK D`, hypothesis S10's CertBasis).

  T1 (|I| = 1/2, for S12a):       0.95920 ≤ λ_max(K_I) ≤ 0.95921,  and re ⟪K_I f, f⟫ ≤ 0.95921 ‖f‖².
  T2 (|I| = log 2, for S12b):     1.05156 ≤ λ_max(K_I) ≤ 1.0516,
                                  λ₂(K_I) := minmaxEig K_I 2 ≤ 0.6866,
                                  a unit top eigenvector ζ has |⟨ξ₀|ζ⟩|² ≥ 0.901 (ξ₀ = 1/√|I|),
                                  re ⟪K_I f, f⟫ ≤ 0.9995 ‖f‖² + 0.058 |⟨ξ₀|f⟩|²   (CC Lemma 6.9 form),
                                  hence ⟨f, N_I f⟩ = 2ε'(⟨K_I f, f⟩ - ‖f‖²) ≤ (2ε' · 0.058) |⟨ξ₀|f⟩|².
  Method (blueprint bypass B4): exact-rational Galerkin in 8 shifted Legendre polynomials,
  Schur complement with an exactly computed cross term, Hilbert-Schmidt tail, Weyl perturbation
  for χ - chiPoly; all numbers kernel-checked (`decide +kernel`, ArchS11_Cert*).  No `sorry`.
-/
import ArchS11_Bound
import ArchS11_Final
import ArchS11_Cert
import ArchS11_CertPsi
import ArchS11_CertT1
import ArchS11_CertT2a
import ArchS11_CertT2b

open MeasureTheory Set Finset
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace ArchS11

open ArchS5 ArchS11.Data

set_option linter.unusedSectionVars false

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## A. The hypothesis on the kernel. -/

/-- `κ` is a continuous Hermitian kernel within `δ` of `chiPoly (y - x)` on `[0, ℓ]²`. -/
structure ChiApprox (ℓ δ : ℝ) (κ : ℝ × ℝ → 𝕜) : Prop where
  cont : Continuous κ
  symm : ∀ x y, κ (y, x) = (starRingEnd 𝕜) (κ (x, y))
  approx : ∀ x ∈ Icc (0 : ℝ) ℓ, ∀ y ∈ Icc (0 : ℝ) ℓ,
    ‖κ (x, y) - ((ArchS10.chiPoly (y - x) : ℝ) : 𝕜)‖ ≤ δ

/-- The operator `K_I` on `L²([0, ℓ])`. -/
def KI (ℓ : ℝ) (κ : ℝ × ℝ → 𝕜) (hκ : Continuous κ) : Lp 𝕜 2 (volI 0 ℓ) →L[𝕜] Lp 𝕜 2 (volI 0 ℓ) :=
  intOp (kernelOfContinuous 0 ℓ κ hκ)

/-! ## B. The certificate constants. -/

theorem final_facts :
    aA * lamT1 + (ArchS10.Data.deltaChi + dRA) * aA ≤ 95921 / 100000 ∧
    95920 / 100000 ≤ aA * lamT1lo - (ArchS10.Data.deltaChi + dRA) * aA ∧
    aH * lamTop + (ArchS10.Data.deltaChi + dRH) * aH ≤ 10516 / 10000 ∧
    105156 / 100000 ≤ aL * lamToplo - (ArchS10.Data.deltaChi + dRL) * aL ∧
    aH * lamGam + (ArchS10.Data.deltaChi + dRH) * aH ≤ 9995 / 10000 ∧
    aH * lamLam2 + (ArchS10.Data.deltaChi + dRH) * aH ≤ 6866 / 10000 ∧
    aH * lamOvl + (ArchS10.Data.deltaChi + dRH) * aH ≤ 103354 / 100000 ∧
    c0T1 = 0 ∧ c0Top = 0 ∧ c0Gam = -(58 / 1000) / aH ∧ c0Lam2 = -1 / aH ∧
    c0Ovl = -(2 / 100) / aH ∧ aA = 1 / 2 ∧ aH = 6931471808 / 10 ^ 10 ∧
    aL = 6931471803 / 10 ^ 10 ∧ 0 ≤ dRA ∧ 0 ≤ dRH ∧ 0 ≤ dRL ∧ 0 ≤ ArchS10.Data.deltaChi ∧
    EA.length ≤ 47 ∧ EH.length ≤ 47 ∧ EL.length ≤ 47 := by
  have h := final_ok
  simp only [finalOK, Bool.and_eq_true, decide_eq_true_eq] at h
  tauto

theorem aA_real : ((aA : ℚ) : ℝ) = 1 / 2 := by
  rw [final_facts.2.2.2.2.2.2.2.2.2.2.2.2.1]; norm_num

theorem aH_real : ((aH : ℚ) : ℝ) = 0.6931471808 := by
  rw [final_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; norm_num

theorem aL_real : ((aL : ℚ) : ℝ) = 0.6931471803 := by
  rw [final_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; norm_num

theorem log_two_le_aH : Real.log 2 ≤ ((aH : ℚ) : ℝ) := by rw [aH_real]; exact Real.log_two_lt_d9.le

theorem aL_le_log_two : ((aL : ℚ) : ℝ) ≤ Real.log 2 := by rw [aL_real]; exact Real.log_two_gt_d9.le

/-! ## C. Generic upper and lower bounds through a certificate. -/

/-- Pointwise closeness of `κ` to the certified polynomial kernel at scale `a0 ≥ ℓ`. -/
theorem kerF_close {ℓ δ : ℝ} {κ : ℝ × ℝ → 𝕜}
    (happ : ∀ x ∈ Icc (0 : ℝ) ℓ, ∀ y ∈ Icc (0 : ℝ) ℓ, ‖κ (x, y) - ((ArchS10.chiPoly (y - x) : ℝ) : 𝕜)‖ ≤ δ)
    {E : List ℚ} {a0 dR : ℚ} (hr : roundOK E a0 dR = true) (ha0 : (0 : ℝ) < a0)
    (hℓ : ℓ ≤ a0) :
    ∀ x ∈ Icc (0 : ℝ) ℓ, ∀ y ∈ Icc (0 : ℝ) ℓ, ‖κ (x, y) - kerF a0 E 0 (x, y)‖ ≤ δ + dR := by
  intro x hx y hy
  have hv : |y - x| ≤ (a0 : ℝ) := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have h2 := abs_chiPoly_sub_pv hr ha0 hv
  have e : kerF (𝕜 := 𝕜) a0 E 0 (x, y) = ((pv E (|y - x| / a0) : ℝ) : 𝕜) := by
    unfold kerF kR
    congr 2
    rw [Rat.cast_zero, add_zero, ← sub_div, abs_div, abs_of_pos ha0, abs_sub_comm]
  rw [e]
  calc ‖κ (x, y) - ((pv E (|y - x| / a0) : ℝ) : 𝕜)‖
      ≤ ‖κ (x, y) - ((ArchS10.chiPoly (y - x) : ℝ) : 𝕜)‖
        + ‖((ArchS10.chiPoly (y - x) : ℝ) : 𝕜) - ((pv E (|y - x| / a0) : ℝ) : 𝕜)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ δ + dR := by
        refine add_le_add (happ x hx y hy) ?_
        rw [← RCLike.ofReal_sub, RCLike.norm_ofReal]
        exact h2

/-- **Upper form through a certificate at scale `a0 ≥ ℓ`** (extension by zero to `[0, a0]`). -/
theorem form_upper {ℓ δ : ℝ} (hℓ : 0 < ℓ) {κ : ℝ × ℝ → 𝕜} (hκ : ChiApprox ℓ δ κ) (hδ : 0 ≤ δ)
    (hb : binOK = true) {a0 : ℚ} (ha0 : (0 : ℝ) < a0) (hℓa : ℓ ≤ a0) {E : List ℚ} {dR : ℚ}
    (hr : roundOK E a0 dR = true) (hdR : (0 : ℝ) ≤ dR) (hE : E.length ≤ 47)
    {Psi : List (List ℚ)} (hpsi : psiOK E Psi = true) (hlen : lenOK Psi = true)
    {c0 : ℚ} {U B rho Q : List (List ℚ)} {L : List (ℚ × List ℚ)} {al dh : List ℚ} {lam t q : ℚ}
    (hok : (uOK Psi c0 U && rhoOK U B rho && dOK rho al dh && qmatOK U Q dh lam t &&
      ldlOK Q L NG && tailOK E c0 U lam t q) = true)
    (f : Lp 𝕜 2 (volI 0 ℓ)) :
    RCLike.re ⟪KI ℓ κ hκ.cont f, f⟫_𝕜
      ≤ ((a0 : ℝ) * lam + (δ + dR) * ℓ) * ‖f‖ ^ 2
        - c0 * ‖⟪(polyLp ℓ [1] : Lp 𝕜 2 (volI 0 ℓ)), f⟫_𝕜‖ ^ 2 := by
  have hp := abs_re_inner_sub_le hℓ.le hκ.cont (continuous_kerF (𝕜 := 𝕜) a0 E 0)
    (by linarith) (kerF_close hκ.approx hr ha0 hℓa) f
  have he := re_inner_intOp_extL hℓa (continuous_kerF (𝕜 := 𝕜) a0 E 0) f
  have hc := inner_kerLp_const (𝕜 := 𝕜) (a := (a0 : ℝ)) E c0 (extL hℓa f)
  have hbd := form_bound_of_cert (𝕜 := 𝕜) hb ha0 hE hpsi hlen hok (extL hℓa f)
  rw [norm_extL] at hbd
  rw [inner_one_extL hℓa] at hc
  have hk : kerLp (𝕜 := 𝕜) (a0 : ℝ) E 0 = kernelOfContinuous 0 (a0 : ℝ) (kerF a0 E 0)
    (continuous_kerF a0 E 0) := rfl
  rw [← hk] at he
  unfold KI
  have := abs_le.1 hp
  nlinarith [this.2]

/-- **Lower bound through a test vector at scale `a0 ≤ ℓ`.** -/
theorem topEig_lower {ℓ δ : ℝ} {κ : ℝ × ℝ → 𝕜} (hκ : ChiApprox ℓ δ κ) (hδ : 0 ≤ δ)
    (hb : binOK = true) {a0 : ℚ} (ha0 : (0 : ℝ) < a0) (ha0ℓ : (a0 : ℝ) ≤ ℓ) {E : List ℚ} {dR : ℚ}
    (hr : roundOK E a0 dR = true) (hdR : (0 : ℝ) ≤ dR) (hE : E.length ≤ 47)
    {Psi : List (List ℚ)} (hpsi : psiOK E Psi = true) (hlen : lenOK Psi = true)
    {ut Ut : List ℚ} {lam : ℚ}
    (hok : (decide (ut.length = NG) && decide (Ut = lc ut Psi DL) && decide (0 < mom ut ut) &&
      decide (lam * mom ut ut ≤ mom Ut ut)) = true) :
    (a0 : ℝ) * lam - (δ + dR) * a0 ≤ topEig (KI ℓ κ hκ.cont) := by
  obtain ⟨hu0, hlo⟩ := form_lower_of_test (𝕜 := 𝕜) hb ha0 hE hpsi hlen hok
  set u : Lp 𝕜 2 (volI 0 (a0 : ℝ)) := polyLp a0 ut
  have happ' : ∀ x ∈ Icc (0 : ℝ) a0, ∀ y ∈ Icc (0 : ℝ) a0,
      ‖κ (x, y) - ((ArchS10.chiPoly (y - x) : ℝ) : 𝕜)‖ ≤ δ := fun x hx y hy =>
    hκ.approx x ⟨hx.1, hx.2.trans ha0ℓ⟩ y ⟨hy.1, hy.2.trans ha0ℓ⟩
  have hp := abs_re_inner_sub_le ha0.le hκ.cont (continuous_kerF (𝕜 := 𝕜) a0 E 0)
    (by linarith) (kerF_close happ' hr ha0 le_rfl) u
  have he := re_inner_intOp_extL ha0ℓ hκ.cont u
  have hn := norm_extL ha0ℓ u
  have hne : extL ha0ℓ u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    exact hu0 (norm_eq_zero.1 hn.symm)
  refine le_topEig_of _ hne ?_
  unfold KI
  rw [he, hn]
  have hk : kerLp (𝕜 := 𝕜) (a0 : ℝ) E 0 = kernelOfContinuous 0 (a0 : ℝ) (kerF a0 E 0)
    (continuous_kerF a0 E 0) := rfl
  rw [← hk] at hp
  have := abs_le.1 hp
  nlinarith [this.1, sq_nonneg ‖u‖]

/-! ## D. T1: |I| = 1/2. -/

section T1

variable {δ : ℝ} {κ : ℝ × ℝ → 𝕜}

theorem KI_half_form (hκ : ChiApprox (1 / 2) δ κ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ (ArchS10.Data.deltaChi : ℝ)) (f : Lp 𝕜 2 (volI 0 (1 / 2))) :
    RCLike.re ⟪KI (1 / 2) κ hκ.cont f, f⟫_𝕜 ≤ 0.95921 * ‖f‖ ^ 2 := by
  obtain ⟨h1, -, -, -, -, -, -, h8, -, -, -, -, -, -, -, h16, -, -, -, h20, -, -⟩ := final_facts
  have hok := okT1_ok
  unfold okT1 at hok
  have hu := form_upper (𝕜 := 𝕜) (by norm_num) hκ hδ0 bin_ok (a0 := aA) (by rw [aA_real]; norm_num)
    (by rw [aA_real]) roundA_ok (by exact_mod_cast h16) h20 psiA_ok lenA_ok hok f
  rw [h8] at hu
  simp only [Rat.cast_zero, zero_mul, sub_zero] at hu
  refine hu.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
  have h1' : ((aA * lamT1 + (ArchS10.Data.deltaChi + dRA) * aA : ℚ) : ℝ) ≤ ((95921 / 100000 : ℚ) : ℝ) := by
    exact_mod_cast h1
  push_cast at h1'
  rw [aA_real] at h1' ⊢
  nlinarith

/-- **T1**: `λ_max(K_I) ≤ 0.95921` at `|I| = 1/2`. -/
theorem KI_half_topEig_le (hκ : ChiApprox (1 / 2) δ κ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ (ArchS10.Data.deltaChi : ℝ)) : topEig (KI (1 / 2) κ hκ.cont) ≤ 0.95921 :=
  topEig_le_of_forall' _ (by norm_num) fun f => KI_half_form hκ hδ0 hδ f

/-- **T1, lower**: `0.95920 ≤ λ_max(K_I)` at `|I| = 1/2`. -/
theorem KI_half_topEig_ge (hκ : ChiApprox (1 / 2) δ κ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ (ArchS10.Data.deltaChi : ℝ)) : 0.95920 ≤ topEig (KI (1 / 2) κ hκ.cont) := by
  obtain ⟨-, h2, -, -, -, -, -, -, -, -, -, -, -, -, -, h16, -, -, -, h20, -, -⟩ := final_facts
  have hok := okT1lo_ok
  unfold okT1lo at hok
  have hl := topEig_lower (𝕜 := 𝕜) hκ hδ0 bin_ok (a0 := aA) (by rw [aA_real]; norm_num)
    (by rw [aA_real]) roundA_ok (by exact_mod_cast h16) h20 psiA_ok lenA_ok hok
  refine le_trans ?_ hl
  have h2' : ((95920 / 100000 : ℚ) : ℝ) ≤ ((aA * lamT1lo - (ArchS10.Data.deltaChi + dRA) * aA : ℚ) : ℝ) := by
    exact_mod_cast h2
  push_cast at h2'
  rw [aA_real] at h2' ⊢
  nlinarith

end T1

/-! ## E. T2: |I| = log 2. -/

section T2

variable {δ : ℝ} {κ : ℝ × ℝ → 𝕜}

theorem log_two_pos' : 0 < Real.log 2 := Real.log_pos one_lt_two

/-- The four upper certificates at `|I| = log 2` in one form: `re ⟪K f, f⟫ ≤ μ ‖f‖² + γ' ‖⟪1, f⟫‖² / log 2`. -/
theorem KI_log2_form_of {μ γ : ℚ} {c0 : ℚ} {U B rho Q : List (List ℚ)} {L : List (ℚ × List ℚ)}
    {al dh : List ℚ} {lam t q : ℚ}
    (hok : (uOK PsiH c0 U && rhoOK U B rho && dOK rho al dh && qmatOK U Q dh lam t &&
      ldlOK Q L NG && tailOK EH c0 U lam t q) = true)
    (hc0 : c0 = -γ / aH) (hγ : 0 ≤ γ)
    (hμ : aH * lam + (ArchS10.Data.deltaChi + dRH) * aH ≤ μ)
    (hκ : ChiApprox (Real.log 2) δ κ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ (ArchS10.Data.deltaChi : ℝ))
    (f : Lp 𝕜 2 (volI 0 (Real.log 2))) :
    RCLike.re ⟪KI (Real.log 2) κ hκ.cont f, f⟫_𝕜
      ≤ μ * ‖f‖ ^ 2 + γ * ‖⟪(polyLp (Real.log 2) [1] : Lp 𝕜 2 (volI 0 (Real.log 2))), f⟫_𝕜‖ ^ 2
          / Real.log 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h17, -, -, -, h21, -⟩ := final_facts
  have hH : (0 : ℝ) < aH := by rw [aH_real]; norm_num
  have hu := form_upper (𝕜 := 𝕜) log_two_pos' hκ hδ0 bin_ok (a0 := aH) hH log_two_le_aH roundH_ok
    (by exact_mod_cast h17) h21 psiH_ok lenH_ok hok f
  have hμ' : ((aH * lam + (ArchS10.Data.deltaChi + dRH) * aH : ℚ) : ℝ) ≤ (μ : ℝ) := by
    exact_mod_cast hμ
  push_cast at hμ'
  have hdR : (0 : ℝ) ≤ dRH := by exact_mod_cast h17
  have hl2 := log_two_le_aH
  have hl0 := log_two_pos'
  have hA : ((aH : ℝ) * lam + (δ + dRH) * Real.log 2) ≤ μ := by nlinarith
  have hI0 : 0 ≤ ‖⟪(polyLp (Real.log 2) [1] : Lp 𝕜 2 (volI 0 (Real.log 2))), f⟫_𝕜‖ ^ 2 := sq_nonneg _
  have hγ' : (0 : ℝ) ≤ γ := by exact_mod_cast hγ
  have hc : -((c0 : ℚ) : ℝ) = γ / aH := by rw [hc0]; push_cast; ring
  have hcmp : (γ : ℝ) / aH ≤ γ / Real.log 2 := div_le_div_of_nonneg_left hγ' hl0 hl2
  calc RCLike.re ⟪KI (Real.log 2) κ hκ.cont f, f⟫_𝕜
      ≤ ((aH : ℝ) * lam + (δ + dRH) * Real.log 2) * ‖f‖ ^ 2
          - c0 * ‖⟪(polyLp (Real.log 2) [1] : Lp 𝕜 2 (volI 0 (Real.log 2))), f⟫_𝕜‖ ^ 2 := hu
    _ ≤ μ * ‖f‖ ^ 2 + γ / Real.log 2 *
          ‖⟪(polyLp (Real.log 2) [1] : Lp 𝕜 2 (volI 0 (Real.log 2))), f⟫_𝕜‖ ^ 2 := by
        have h1 := mul_le_mul_of_nonneg_right hA (sq_nonneg ‖f‖)
        have h2 := mul_le_mul_of_nonneg_right hcmp hI0
        rw [sub_eq_add_neg, ← neg_mul, hc]
        linarith
    _ = μ * ‖f‖ ^ 2 + γ * ‖⟪(polyLp (Real.log 2) [1] : Lp 𝕜 2 (volI 0 (Real.log 2))), f⟫_𝕜‖ ^ 2
          / Real.log 2 := by ring

/-- **T2, top**: `λ_max(K_I) ≤ 1.0516` at `|I| = log 2`. -/
theorem KI_log2_topEig_le (hκ : ChiApprox (Real.log 2) δ κ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ (ArchS10.Data.deltaChi : ℝ)) : topEig (KI (Real.log 2) κ hκ.cont) ≤ 1.0516 := by
  obtain ⟨-, -, h3, -, -, -, -, -, h9, -⟩ := final_facts
  have hok := okTop_ok
  unfold okTop at hok
  refine topEig_le_of_forall' _ (by norm_num) fun f => ?_
  have := KI_log2_form_of (μ := 10516 / 10000) (γ := 0) hok (by rw [h9]; simp) le_rfl h3 hκ hδ0 hδ f
  have e : ((10516 / 10000 : ℚ) : ℝ) = 1.0516 := by norm_num
  rw [e] at this
  simpa using this

/-- **T2, top, lower**: `1.05156 ≤ λ_max(K_I)` at `|I| = log 2`. -/
theorem KI_log2_topEig_ge (hκ : ChiApprox (Real.log 2) δ κ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ (ArchS10.Data.deltaChi : ℝ)) : 1.05156 ≤ topEig (KI (Real.log 2) κ hκ.cont) := by
  obtain ⟨-, -, -, h4, -, -, -, -, -, -, -, -, -, -, -, -, -, h18, -, -, -, h22⟩ := final_facts
  have hok := okToplo_ok
  unfold okToplo at hok
  have hL : (0 : ℝ) < aL := by rw [aL_real]; norm_num
  have hl := topEig_lower (𝕜 := 𝕜) hκ hδ0 bin_ok (a0 := aL) hL aL_le_log_two roundL_ok
    (by exact_mod_cast h18) h22 psiL_ok lenL_ok hok
  refine le_trans ?_ hl
  have h4' : ((105156 / 100000 : ℚ) : ℝ) ≤ ((aL * lamToplo - (ArchS10.Data.deltaChi + dRL) * aL : ℚ) : ℝ) := by
    exact_mod_cast h4
  push_cast at h4'
  have hdR : (0 : ℝ) ≤ dRL := by exact_mod_cast h18
  nlinarith

/-- **T2, CC Lemma 6.9 form**: `re ⟪K_I f, f⟫ ≤ 0.9995 ‖f‖² + 0.058 |⟪ξ₀, f⟫|²`, with
`|⟪ξ₀, f⟫|² = ‖⟪1, f⟫‖² / log 2`. -/
theorem KI_log2_form_gamma (hκ : ChiApprox (Real.log 2) δ κ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ (ArchS10.Data.deltaChi : ℝ)) (f : Lp 𝕜 2 (volI 0 (Real.log 2))) :
    RCLike.re ⟪KI (Real.log 2) κ hκ.cont f, f⟫_𝕜
      ≤ 0.9995 * ‖f‖ ^ 2 + 0.058 * ‖⟪(polyLp (Real.log 2) [1] : Lp 𝕜 2 (volI 0 (Real.log 2))), f⟫_𝕜‖ ^ 2
          / Real.log 2 := by
  obtain ⟨-, -, -, -, h5, -, -, -, -, h10, -⟩ := final_facts
  have hok := okGam_ok
  unfold okGam at hok
  have := KI_log2_form_of (μ := 9995 / 10000) (γ := 58 / 1000) hok h10 (by norm_num) h5 hκ hδ0 hδ f
  convert this using 2 <;> norm_num

/-- **T2, N_I ≤ γ |⟨ξ₀|ξ⟩|²** (CC Lemma 6.9 / Thm 6.11 input) for any `ε' ≥ 0`, with
`γ = 2 ε' · 0.058`: `2ε' (re ⟪K_I f, f⟫ - ‖f‖²) ≤ (2ε' · 0.058) ‖⟪1, f⟫‖² / log 2`. -/
theorem KI_log2_NI (hκ : ChiApprox (Real.log 2) δ κ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ (ArchS10.Data.deltaChi : ℝ)) {ε : ℝ} (hε : 0 ≤ ε) (f : Lp 𝕜 2 (volI 0 (Real.log 2))) :
    2 * ε * (RCLike.re ⟪KI (Real.log 2) κ hκ.cont f, f⟫_𝕜 - ‖f‖ ^ 2)
      ≤ (2 * ε * 0.058) * ‖⟪(polyLp (Real.log 2) [1] : Lp 𝕜 2 (volI 0 (Real.log 2))), f⟫_𝕜‖ ^ 2
          / Real.log 2 := by
  have h := KI_log2_form_gamma hκ hδ0 hδ f
  have hf : 0 ≤ ‖f‖ ^ 2 := sq_nonneg _
  have h2 : RCLike.re ⟪KI (Real.log 2) κ hκ.cont f, f⟫_𝕜 - ‖f‖ ^ 2
      ≤ 0.058 * ‖⟪(polyLp (Real.log 2) [1] : Lp 𝕜 2 (volI 0 (Real.log 2))), f⟫_𝕜‖ ^ 2 / Real.log 2 := by
    linarith
  have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * ε)
  calc 2 * ε * (RCLike.re ⟪KI (Real.log 2) κ hκ.cont f, f⟫_𝕜 - ‖f‖ ^ 2)
      ≤ 2 * ε * (0.058 * ‖⟪(polyLp (Real.log 2) [1] : Lp 𝕜 2 (volI 0 (Real.log 2))), f⟫_𝕜‖ ^ 2
          / Real.log 2) := this
    _ = _ := by ring

theorem one_ne_zero_log2 : (polyLp (Real.log 2) [1] : Lp 𝕜 2 (volI 0 (Real.log 2))) ≠ 0 := by
  intro h
  have hn := norm_polyLp_sq (𝕜 := 𝕜) log_two_pos' [1]
  rw [h, norm_zero] at hn
  have : mom [1] [1] = 1 := by simp [mom]
  rw [this] at hn
  push_cast at hn
  linarith [log_two_pos']

/-- **T2, λ₂**: `minmaxEig K_I 2 ≤ 0.6866` at `|I| = log 2` (the complement of the constants;
the second eigenvector is odd about the midpoint). -/
theorem KI_log2_lambda2 (hκ : ChiApprox (Real.log 2) δ κ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ (ArchS10.Data.deltaChi : ℝ)) : minmaxEig (KI (Real.log 2) κ hκ.cont) 2 ≤ 0.6866 := by
  obtain ⟨-, -, -, -, -, h6, -, -, -, -, h11, -⟩ := final_facts
  have hok := okLam2_ok
  unfold okLam2 at hok
  set one : Lp 𝕜 2 (volI 0 (Real.log 2)) := polyLp (Real.log 2) [1]
  refine minmaxEig_le _ (𝕜 ∙ one) (by rw [finrank_span_singleton one_ne_zero_log2]) (by norm_num)
    fun x hx => ?_
  have h0 : ⟪one, x⟫_𝕜 = 0 :=
    Submodule.inner_right_of_mem_orthogonal (Submodule.mem_span_singleton_self one) hx
  have := KI_log2_form_of (μ := 6866 / 10000) (γ := 1) hok (by rw [h11]) (by norm_num) h6 hκ hδ0 hδ x
  have e : ((6866 / 10000 : ℚ) : ℝ) = 0.6866 := by norm_num
  rw [h0, norm_zero, e] at this
  simpa using this

/-- **T2, overlap**: a unit top eigenvector `ζ` of `K_I` has `|⟨ξ₀|ζ⟩|² = ‖⟪1, ζ⟫‖² / log 2 ≥ 0.901`
(so `|⟨ξ₀|ζ⟩| ≥ 0.949`). -/
theorem KI_log2_overlap (hκ : ChiApprox (Real.log 2) δ κ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ (ArchS10.Data.deltaChi : ℝ)) :
    ∃ ζ : Lp 𝕜 2 (volI 0 (Real.log 2)), ‖ζ‖ = 1 ∧
      KI (Real.log 2) κ hκ.cont ζ = (topEig (KI (Real.log 2) κ hκ.cont) : 𝕜) • ζ ∧
      0.901 ≤ ‖⟪(polyLp (Real.log 2) [1] : Lp 𝕜 2 (volI 0 (Real.log 2))), ζ⟫_𝕜‖ ^ 2 / Real.log 2 := by
  obtain ⟨-, -, -, -, -, -, h7, -, -, -, -, h12, -⟩ := final_facts
  have hok := okOvl_ok
  unfold okOvl at hok
  have hlo := KI_log2_topEig_ge hκ hδ0 hδ
  obtain ⟨ζ, hζ1, hζ⟩ := exists_eigenvector_topEig_intOp
    (isHermitianKernel_kernelOfContinuous (a := 0) (b := Real.log 2) hκ.cont hκ.symm)
    (by unfold KI at hlo; linarith)
  refine ⟨ζ, hζ1, hζ, ?_⟩
  have hform := KI_log2_form_of (μ := 103354 / 100000) (γ := 2 / 100) hok h12 (by norm_num) h7
    hκ hδ0 hδ ζ
  have hre : RCLike.re ⟪KI (Real.log 2) κ hκ.cont ζ, ζ⟫_𝕜 = topEig (KI (Real.log 2) κ hκ.cont) := by
    show RCLike.re ⟪intOp (kernelOfContinuous 0 (Real.log 2) κ hκ.cont) ζ, ζ⟫_𝕜
      = topEig (intOp (kernelOfContinuous 0 (Real.log 2) κ hκ.cont))
    rw [hζ, inner_smul_left, RCLike.conj_ofReal, inner_self_eq_norm_sq_to_K, hζ1]
    simp
  rw [hre, hζ1] at hform
  push_cast at hform
  have e : (2 / 100 : ℝ) * ‖⟪(polyLp (Real.log 2) [1] : Lp 𝕜 2 (volI 0 (Real.log 2))), ζ⟫_𝕜‖ ^ 2
      / Real.log 2 = 2 / 100 * (‖⟪(polyLp (Real.log 2) [1] : Lp 𝕜 2 (volI 0 (Real.log 2))), ζ⟫_𝕜‖ ^ 2
        / Real.log 2) := by ring
  rw [e] at hform
  norm_num at hform hlo ⊢
  linarith

end T2

/-! ## F. Instantiation with CC's kernel χ (S8, S10). -/

section CC

open ArchS8

/-- CC's kernel `χ(y - x)` on `[0, log 2]²`, clamped so as to be continuous on `ℝ²`. -/
def chiK (D : ProlateDataNat) (p : ℝ × ℝ) : 𝕜 :=
  ((D.Qeps (min |p.2 - p.1| (Real.log 2)) / (2 * D.eps1 0) : ℝ) : 𝕜)

theorem chiK_approx {D : ProlateDataNat} (hB : ArchS10.CertBasis D) {ℓ : ℝ} (hℓ : ℓ ≤ Real.log 2) :
    ChiApprox ℓ (ArchS10.Data.deltaChi : ℝ) (chiK (𝕜 := 𝕜) D) where
  cont := by
    refine RCLike.continuous_ofReal.comp (Continuous.div_const ?_ _)
    refine D.continuousOn_Qeps.comp_continuous
      ((continuous_snd.sub continuous_fst).abs.min continuous_const) fun p => ?_
    exact D.mem_Ioo_of_le hB.T_gt (le_min (abs_nonneg _) (Real.log_nonneg one_le_two))
      (min_le_right _ _)
  symm := by
    intro x y
    unfold chiK
    rw [RCLike.conj_ofReal, abs_sub_comm]
  approx := by
    intro x hx y hy
    have hv : |y - x| ≤ Real.log 2 := by
      rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have e : chiK (𝕜 := 𝕜) D (x, y) = ((D.chi (y - x) : ℝ) : 𝕜) := by
      unfold chiK ProlateData.chi
      rw [min_eq_left hv]
    rw [e, ← RCLike.ofReal_sub, RCLike.norm_ofReal]
    exact ArchS10.chi_enclosure hB hv

/-- **S11, T1 for CC's χ**: at `|I| = 1/2`, `0.95920 ≤ λ_max(K_I) ≤ 0.95921`. -/
theorem KI_chi_half {D : ProlateDataNat} (hB : ArchS10.CertBasis D) :
    0.95920 ≤ topEig (KI (𝕜 := 𝕜) (1 / 2) (chiK D) (chiK_approx hB (by
        linarith [Real.log_two_gt_d9])).cont) ∧
      topEig (KI (𝕜 := 𝕜) (1 / 2) (chiK D) (chiK_approx hB (by
        linarith [Real.log_two_gt_d9])).cont) ≤ 0.95921 := by
  have hd : (0 : ℝ) ≤ ArchS10.Data.deltaChi := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h19, -⟩ := final_facts
    exact_mod_cast h19
  have hh : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  exact ⟨KI_half_topEig_ge (chiK_approx hB hh) hd le_rfl, KI_half_topEig_le (chiK_approx hB hh) hd le_rfl⟩

/-- **S11, T2 for CC's χ**: at `|I| = log 2`, `1.05156 ≤ λ_max(K_I) ≤ 1.0516`, `λ₂ ≤ 0.6866`,
`re ⟪K_I f, f⟫ ≤ 0.9995 ‖f‖² + 0.058 |⟨ξ₀|f⟩|²`. -/
theorem KI_chi_log2 {D : ProlateDataNat} (hB : ArchS10.CertBasis D) :
    1.05156 ≤ topEig (KI (𝕜 := 𝕜) (Real.log 2) (chiK D) (chiK_approx hB le_rfl).cont) ∧
    topEig (KI (𝕜 := 𝕜) (Real.log 2) (chiK D) (chiK_approx hB le_rfl).cont) ≤ 1.0516 ∧
    minmaxEig (KI (𝕜 := 𝕜) (Real.log 2) (chiK D) (chiK_approx hB le_rfl).cont) 2 ≤ 0.6866 ∧
    ∀ f : Lp 𝕜 2 (volI 0 (Real.log 2)),
      RCLike.re ⟪KI (Real.log 2) (chiK D) (chiK_approx hB le_rfl).cont f, f⟫_𝕜
        ≤ 0.9995 * ‖f‖ ^ 2
          + 0.058 * ‖⟪(polyLp (Real.log 2) [1] : Lp 𝕜 2 (volI 0 (Real.log 2))), f⟫_𝕜‖ ^ 2
            / Real.log 2 := by
  have hd : (0 : ℝ) ≤ ArchS10.Data.deltaChi := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h19, -⟩ := final_facts
    exact_mod_cast h19
  have hκ := chiK_approx (𝕜 := 𝕜) hB (le_refl (Real.log 2))
  exact ⟨KI_log2_topEig_ge hκ hd le_rfl, KI_log2_topEig_le hκ hd le_rfl,
    KI_log2_lambda2 hκ hd le_rfl, KI_log2_form_gamma hκ hd le_rfl⟩

end CC

end ArchS11
