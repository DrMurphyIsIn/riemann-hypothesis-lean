import ArchS7_Dilation

/-!
# ArchS7_Theta: the operator `ϑ(g)` and its coefficient formula (interface O3, second half)

For `g` continuous and integrable, `ϑ(g) v = ∫ g(x) ϑ(e^x) v dx` (Bochner integral in `L²(ℝ)_ev`;
CC: `ϑ(g) = ∫ g(ρ) ϑ(ρ) d*ρ` in the additive variable).

* `theta g hg : L²(ℝ)_ev →L L²(ℝ)_ev`, `norm_theta_le` (`‖ϑ(g)‖ ≤ ‖g‖₁`).
* `adjoint_theta`: `ϑ(g)† w = ∫ conj g(x) ϑ(e^{-x}) w dx`.
* `hcoef_theta` (**the coefficient formula of `thm47`**):
  `‖ϑ(g)† w‖² = ∫ (g∗g*)(u) ⟨w | ϑ(e^u) w⟩ du`, with `g∗g* = WeilExplicit.autocorr g`.
  This is `⟨w | ϑ(g∗g*) w⟩ = ⟨w | ϑ(g) ϑ(g)† w⟩` in CC's notation.
* `thm47_theta`: CC Thm 4.7 with the concrete `ϑ` and `ϑ(g)`; the remaining hypotheses are
  O1 + O2 (`h85`) and O4 (S6/S8/S9 data).

conjecture1_proved = False.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace ArchS7

open ArchS6 ArchS8

set_option linter.unusedSectionVars false

/-! ### The scaling on `L²(ℝ)_ev`: group law, adjoint, continuity -/

theorem thE_add (s t : ℝ) (v : evenL2) : thE s (thE t v) = thE (s + t) v :=
  Subtype.ext (by rw [coe_thE, coe_thE, coe_thE, thL_add])

theorem norm_thE (t : ℝ) (v : evenL2) : ‖thE t v‖ = ‖v‖ := scalingEven.norm_θ t v

theorem inner_thE_left (t : ℝ) (a b : evenL2) : ⟪thE t a, b⟫_ℂ = ⟪a, thE (-t) b⟫_ℂ := by
  rw [Submodule.coe_inner, Submodule.coe_inner, coe_thE, coe_thE, inner_thL_left]

theorem inner_thE_thE (x y : ℝ) (w : evenL2) :
    ⟪thE (-x) w, thE (-y) w⟫_ℂ = ⟪w, thE (x - y) w⟫_ℂ := by
  rw [inner_thE_left, neg_neg, thE_add, sub_eq_add_neg]

theorem inner_smul_right_E (w v : evenL2) (r : ℂ) : ⟪w, r • v⟫_ℂ = r * ⟪w, v⟫_ℂ :=
  inner_smul_right (𝕜 := ℂ) w v r

theorem inner_self_E (w : evenL2) : ⟪w, w⟫_ℂ = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_pow]; exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) w

theorem inner_conj_symm_E (a b : evenL2) : conj ⟪b, a⟫_ℂ = ⟪a, b⟫_ℂ :=
  inner_conj_symm (𝕜 := ℂ) a b

theorem continuous_thE (v : evenL2) : Continuous fun t ↦ thE t v :=
  (continuous_thL (v : L2R)).subtype_mk _

/-! ### The operator `ϑ(g)` -/

section Theta

variable (g : ℝ → ℂ) (hg : Integrable g) (hgc : Continuous g)

include hg in
theorem integrable_smul_thE (v : evenL2) : Integrable fun x ↦ g x • thE x v :=
  Integrable.mono' (hg.norm.mul_const ‖v‖)
    (hg.1.smul (continuous_thE v).aestronglyMeasurable)
    (Eventually.of_forall fun x ↦ by rw [norm_smul, norm_thE])

include hg in
theorem integrable_conj_smul_thE (w : evenL2) :
    Integrable fun x ↦ conj (g x) • thE (-x) w :=
  Integrable.mono' (hg.norm.mul_const ‖w‖)
    ((Complex.continuous_conj.comp_aestronglyMeasurable hg.1).smul
      ((continuous_thE w).comp continuous_neg).aestronglyMeasurable)
    (Eventually.of_forall fun x ↦ by rw [norm_smul, norm_thE, Complex.norm_conj])

/-- `ϑ(g)` as a linear map. -/
def thetaLin : evenL2 →ₗ[ℂ] evenL2 where
  toFun v := ∫ x, g x • thE x v
  map_add' v w := by
    simp only [map_add, smul_add]
    exact integral_add (integrable_smul_thE g hg v) (integrable_smul_thE g hg w)
  map_smul' c v := by
    simp only [map_smul, RingHom.id_apply]
    rw [← integral_smul]
    congr 1; funext x; rw [smul_comm]

theorem norm_thetaLin_le (v : evenL2) : ‖thetaLin g hg v‖ ≤ (∫ x, ‖g x‖) * ‖v‖ := by
  show ‖∫ x, g x • thE x v‖ ≤ _
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le (hg.norm.mul_const _) (Eventually.of_forall fun x ↦ ?_)
  rw [norm_smul, norm_thE]

/-- **`ϑ(g) = ∫ g(x) ϑ(e^x) dx`** on `L²(ℝ)_ev`. -/
def theta : evenL2 →L[ℂ] evenL2 :=
  (thetaLin g hg).mkContinuous (∫ x, ‖g x‖) (norm_thetaLin_le g hg)

theorem theta_apply (v : evenL2) : theta g hg v = ∫ x, g x • thE x v := rfl

/-- The adjoint: `ϑ(g)† w = ∫ conj g(x) ϑ(e^{-x}) w dx`. -/
theorem adjoint_theta (w : evenL2) :
    (ContinuousLinearMap.adjoint (theta g hg)) w = ∫ x, conj (g x) • thE (-x) w := by
  apply ext_inner_right ℂ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left, theta_apply,
    ← integral_inner (integrable_smul_thE g hg v), ← inner_conj_symm_E,
    ← integral_inner (integrable_conj_smul_thE g hg w), ← integral_conj]
  congr 1; funext x
  rw [inner_smul_right_E, inner_smul_right_E, map_mul, Complex.conj_conj, inner_conj_symm_E,
    inner_thE_left, neg_neg]

/-- `⟨ϑ(g)† w, ϑ(g)† w⟩ = ∫_y ∫_x conj g(y) g(x) ⟨w | ϑ(e^{x-y}) w⟩`. -/
theorem inner_adjoint_theta (w : evenL2) :
    ⟪(ContinuousLinearMap.adjoint (theta g hg)) w, (ContinuousLinearMap.adjoint (theta g hg)) w⟫_ℂ
      = ∫ y, ∫ x, conj (g y) * (g x * ⟪w, thE (x - y) w⟫_ℂ) := by
  set A := (ContinuousLinearMap.adjoint (theta g hg)) w
  have hA : A = ∫ x, conj (g x) • thE (-x) w := adjoint_theta g hg w
  conv_lhs => rw [hA]
  rw [← integral_inner (integrable_conj_smul_thE g hg w)]
  congr 1; funext y
  rw [inner_smul_right_E, ← inner_conj_symm_E,
    ← integral_inner (integrable_conj_smul_thE g hg w), ← integral_conj, ← integral_const_mul]
  congr 1; funext x
  rw [inner_smul_right_E, map_mul, Complex.conj_conj, inner_conj_symm_E, inner_thE_thE]

include hgc in
/-- **The coefficient formula** (hypothesis `hcoef` of `thm47`):
`‖ϑ(g)† w‖² = ∫ (g∗g*)(u) ⟨w | ϑ(e^u) w⟩ du`. -/
theorem hcoef_theta (w : evenL2) :
    ((‖(ContinuousLinearMap.adjoint (theta g hg)) w‖ ^ 2 : ℝ) : ℂ)
      = ∫ u, WeilExplicit.autocorr g u * ⟪w, scalingEven.θ u w⟫_ℂ := by
  set c : ℝ → ℂ := fun u ↦ ⟪w, thE u w⟫_ℂ with hcdef
  show _ = ∫ u, WeilExplicit.autocorr g u * c u
  have hc : Continuous c := continuous_const.inner (continuous_thE w)
  have hcb : ∀ u, ‖c u‖ ≤ ‖w‖ ^ 2 := fun u ↦ by
    have := norm_inner_le_norm (𝕜 := ℂ) w (thE u w)
    rw [norm_thE] at this; nlinarith [norm_nonneg w]
  have h1 : ((‖(ContinuousLinearMap.adjoint (theta g hg)) w‖ ^ 2 : ℝ) : ℂ)
      = ∫ y, ∫ x, conj (g y) * (g x * c (x - y)) := by
    rw [← inner_adjoint_theta g hg w, inner_self_E]
  rw [h1]
  -- translate `x = u + y`
  have h2 : ∀ y, ∫ x, conj (g y) * (g x * c (x - y)) = ∫ u, conj (g y) * (g (u + y) * c u) := by
    intro y
    have := integral_add_right_eq_self (μ := volume) (fun x ↦ conj (g y) * (g x * c (x - y))) y
    simp only [add_sub_cancel_right] at this
    exact this.symm
  simp_rw [h2]
  -- Fubini
  have hint : Integrable (Function.uncurry fun y u ↦ conj (g y) * (g (u + y) * c u))
      (volume.prod volume) := by
    have hmp : MeasurePreserving (fun z : ℝ × ℝ ↦ (z.1, z.1 + z.2)) (volume.prod volume)
        (volume.prod volume) := measurePreserving_prod_add volume volume
    have hB : Integrable (fun z : ℝ × ℝ ↦ ‖g z.1‖ * ‖g z.2‖) (volume.prod volume) :=
      hg.norm.mul_prod hg.norm
    have hB' : Integrable (fun z : ℝ × ℝ ↦ ‖g z.1‖ * ‖g (z.1 + z.2)‖) (volume.prod volume) :=
      hmp.integrable_comp_of_integrable hB
    refine Integrable.mono' (hB'.mul_const (‖w‖ ^ 2)) ?_ (Eventually.of_forall fun z ↦ ?_)
    · exact (Continuous.aestronglyMeasurable (by
        show Continuous fun z : ℝ × ℝ ↦ conj (g z.1) * (g (z.2 + z.1) * c z.2)
        exact (Complex.continuous_conj.comp (hgc.comp continuous_fst)).mul
          ((hgc.comp (continuous_snd.add continuous_fst)).mul (hc.comp continuous_snd))))
    · simp only [Function.uncurry, norm_mul, Complex.norm_conj]
      rw [add_comm z.2 z.1]
      have := hcb z.2
      have := norm_nonneg (g z.1)
      have := norm_nonneg (g (z.1 + z.2))
      calc ‖g z.1‖ * (‖g (z.1 + z.2)‖ * ‖c z.2‖)
          ≤ ‖g z.1‖ * (‖g (z.1 + z.2)‖ * ‖w‖ ^ 2) := by gcongr
        _ = ‖g z.1‖ * ‖g (z.1 + z.2)‖ * ‖w‖ ^ 2 := by ring
  rw [integral_integral_swap hint]
  congr 1; funext u
  rw [WeilExplicit.autocorr, ← integral_mul_const]
  rw [← integral_add_right_eq_self (μ := volume) (fun v ↦ g v * conj (g (v - u)) * c u) u]
  congr 1; funext y
  simp only [add_sub_cancel_right]
  show conj (g y) * (g (u + y) * c u) = g (y + u) * conj (g y) * c u
  rw [add_comm u y]; ring

end Theta

/-- **CC Theorem 4.7 with the concrete `ϑ` and `ϑ(g)`.**  For `g` continuous and integrable with
`g∗g*` integrable, the real prolate basis `bR` enumerated by `σ`, any S8 `ProlateData D` with the same
`λ_n, phi_n`, Σ|τ_n| < ∞, and CC (85) (`h85`, interface O1 + O2):
`Tr(ϑ(g∗g*) S) = ‖S ϑ(g)‖²_HS = archW g + Re (D.Eplus (g∗g*))`. -/
theorem thm47_theta {ι : Type*} (bR : EigenBasis CopR ι) (D : ProlateDataNat) (σ : ℕ ≃ ι)
    (hDlam : ∀ n, D.lam n = bR.μ (σ n)) (hDphi : ∀ n, D.phi n = phiR bR (σ n))
    (hτ : Summable fun i ↦ |(realProlateBasis bR).τ i|)
    (g : ℝ → ℂ) (hg : Integrable g) (hgc : Continuous g)
    (hf : Integrable (WeilExplicit.autocorr g))
    {κ : Type*} (e : HilbertBasis κ ℂ evenL2)
    (h85 : HasSum (fun k ↦ ‖evenPair.hatP (evenPair.P (theta g hg (e k)))‖ ^ 2)
      (ArchS3.archW g + (∫ x, WeilExplicit.autocorr g x
        * ProlateBasis.δS (realProlateBasis bR) scalingEven |x|).re)) :
    HasSum (fun k ↦ ‖ArchS6.ProlateBasis.soninProj (S := evenPair) (theta g hg (e k))‖ ^ 2)
      (ArchS3.archW g + (D.Eplus (WeilExplicit.autocorr g)).re) :=
  thm47_even bR D σ hDlam hDphi hτ g hf (theta g hg) (hcoef_theta g hg hgc) e h85

/-- **CC (83)**: `archW g + Re (D.Eplus (g∗g*)) ≥ 0` under the same hypotheses. -/
theorem thm47_theta_nonneg {ι : Type*} (bR : EigenBasis CopR ι) (D : ProlateDataNat) (σ : ℕ ≃ ι)
    (hDlam : ∀ n, D.lam n = bR.μ (σ n)) (hDphi : ∀ n, D.phi n = phiR bR (σ n))
    (hτ : Summable fun i ↦ |(realProlateBasis bR).τ i|)
    (g : ℝ → ℂ) (hg : Integrable g) (hgc : Continuous g)
    (hf : Integrable (WeilExplicit.autocorr g))
    {κ : Type*} (e : HilbertBasis κ ℂ evenL2)
    (h85 : HasSum (fun k ↦ ‖evenPair.hatP (evenPair.P (theta g hg (e k)))‖ ^ 2)
      (ArchS3.archW g + (∫ x, WeilExplicit.autocorr g x
        * ProlateBasis.δS (realProlateBasis bR) scalingEven |x|).re)) :
    0 ≤ ArchS3.archW g + (D.Eplus (WeilExplicit.autocorr g)).re :=
  (thm47_theta bR D σ hDlam hDphi hτ g hg hgc hf e h85).nonneg fun _ ↦ sq_nonneg _

/-- **CC Theorem 4.7 for the island's test class** (`IsWeilTest g`: smooth, compact support).
Remaining hypotheses: O4 (`D`, `σ`, `hτ`) and CC (85) (`h85`, O1 + O2). -/
theorem thm47_weil {ι : Type*} (bR : EigenBasis CopR ι) (D : ProlateDataNat) (σ : ℕ ≃ ι)
    (hDlam : ∀ n, D.lam n = bR.μ (σ n)) (hDphi : ∀ n, D.phi n = phiR bR (σ n))
    (hτ : Summable fun i ↦ |(realProlateBasis bR).τ i|)
    {g : ℝ → ℂ} (hW : WeilExplicit.IsWeilTest g)
    {κ : Type*} (e : HilbertBasis κ ℂ evenL2)
    (h85 : HasSum (fun k ↦ ‖evenPair.hatP (evenPair.P
        (theta g (hW.1.continuous.integrable_of_hasCompactSupport hW.2) (e k)))‖ ^ 2)
      (ArchS3.archW g + (∫ x, WeilExplicit.autocorr g x
        * ProlateBasis.δS (realProlateBasis bR) scalingEven |x|).re)) :
    HasSum (fun k ↦ ‖ArchS6.ProlateBasis.soninProj (S := evenPair)
        (theta g (hW.1.continuous.integrable_of_hasCompactSupport hW.2) (e k))‖ ^ 2)
      (ArchS3.archW g + (D.Eplus (WeilExplicit.autocorr g)).re) := by
  have hA := RvMBridge5.isWeilTest_autocorr hW
  exact thm47_theta bR D σ hDlam hDphi hτ g _ hW.1.continuous
    (hA.1.continuous.integrable_of_hasCompactSupport hA.2) e h85

end ArchS7
