import ArchS7_Abstract
import ArchS7_Term
import ArchS6_Real
import ArchS8_Kernel
import ArchS3_Delta

/-!
# ArchS7_Concrete: CC Theorem 4.7 for the concrete real prolate basis on `L²(ℝ)_ev`

Specialises `ArchS7.ProlateBasis.thm47` to S6's pair `evenPair` and its real prolate basis
`realProlateBasis bR` (`ξ_n = J e_n`, `e_n` real eigenfunctions of S9's operator `2cos(2πxω)`).

* `xi_ae`, `zeta_ae`: S6's `ξ_n` and CC's `ζ_n` are a.e. S7's `xiRep (phiR n)` and
  `zetaRep τ_n (phiR n)` (this is the representative identification left open in M1).
* `ae_comp_mul`: a.e. equality survives `v ↦ c v` (`c ≠ 0`).
* `inner_dil`: for a scaling acting pointwise, `⟨a | ϑ(e^{-t}) b⟩ = ∫ conj a · e^{t/2} b(e^t ·)`.
* `hreal_of_pointwise`: the reality hypothesis of `thm47` for the concrete prolates.
* `εS_eq_eps`: **CC's ε of Thm 4.7 is S8's `D.eps`** for any `ProlateData` with the same `λ_n, phi_n`.
* `thm47_concrete`: **CC Thm 4.7 in the island's conventions**,
  `‖S ϑ(g)‖²_HS = archW g + Re (D.Eplus (autocorr g))`, under the interface hypotheses O1-O3
  (see `telperion/docs/ARCH_S7_NOTES.md`).

conjecture1_proved = False.
-/

open MeasureTheory Set Filter FourierTransform
open scoped InnerProductSpace ComplexConjugate ENNReal

noncomputable section

namespace ArchS7

open ArchS6 ArchS8 ArchS5

set_option linter.unusedSectionVars false

/-! ### Measure-theoretic helpers -/

theorem ae_ne_real (a : ℝ) : ∀ᵐ x : ℝ, x ≠ a := by
  rw [ae_iff]
  simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton, measure_singleton]

/-- A.e. equality is preserved by `v ↦ c v`, `c ≠ 0`. -/
theorem ae_comp_mul {F G : ℝ → ℂ} (h : F =ᵐ[volume] G) {c : ℝ} (hc : c ≠ 0) :
    (fun v ↦ F (c * v)) =ᵐ[volume] fun v ↦ G (c * v) := by
  have hm : AEMeasurable (fun v : ℝ ↦ c * v) volume := (measurable_const_mul c).aemeasurable
  have h' : F =ᵐ[volume.map (fun v : ℝ ↦ c * v)] G := by
    rw [Real.map_volume_mul_left hc]
    exact Measure.smul_absolutelyContinuous.ae_le h
  exact ae_eq_comp hm h'

/-! ### Representatives of the concrete prolates -/

theorem cosTransR_neg (e : L2IR 0 1) (w : ℝ) : cosTransR e (-w) = cosTransR e w := by
  unfold cosTransR cosKR
  congr 1; funext v
  congr 2
  rw [show 2 * Real.pi * -w * v = -(2 * Real.pi * w * v) by ring, Real.cos_neg]

theorem phiR_neg {ι : Type*} (bR : EigenBasis CopR ι) (i : ι) (w : ℝ) :
    phiR bR i (-w) = phiR bR i w := by
  rw [phiR, phiR, cosTransR_neg]

theorem phiR_abs {ι : Type*} (bR : EigenBasis CopR ι) (i : ι) (w : ℝ) :
    phiR bR i |w| = phiR bR i w := by
  rcases le_or_gt 0 w with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, phiR_neg]

theorem c2_eq : c2 = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by rw [c2, one_div]

/-- **S6's `ξ_n` is `xiRep (phiR n)`** a.e. -/
theorem xi_ae {ι : Type*} (bR : EigenBasis CopR ι) (i : ι) :
    (((realProlateBasis bR).ξ i : L2R) : ℝ → ℂ) =ᵐ[volume] xiRep (phiR bR i) := by
  have hF : ((ofRealL 0 1 (bR.e i) : L2I 0 1) : ℝ → ℂ) =ᵐ[volI 0 1]
      fun w ↦ ((phiR bR i w : ℝ) : ℂ) := by
    filter_upwards [coeFn_ofRealL (bR.e i), ae_eq_phiR bR i] with w e1 e2
    rw [e1, e2]
  rw [realProlateBasis_ξ]
  filter_upwards [coeFn_J_of _ hF, ae_ne_zero_real] with w e hw
  rw [e, xiRep]
  by_cases h1 : |w| ≤ 1
  · rw [if_pos h1, c2_eq]
    rcases lt_or_gt_of_ne hw with hneg | hpos
    · have m1 : w ∉ Icc (0 : ℝ) 1 := fun h' ↦ by linarith [h'.1]
      have m2 : -w ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [neg_abs_le w, abs_of_neg hneg]⟩
      rw [indicator_of_notMem m1, indicator_of_mem m2, zero_add, abs_of_neg hneg]
      push_cast; ring
    · have m1 : w ∈ Icc (0 : ℝ) 1 := ⟨hpos.le, by rwa [abs_of_pos hpos] at h1⟩
      have m2 : -w ∉ Icc (0 : ℝ) 1 := fun h' ↦ by linarith [h'.1]
      rw [indicator_of_mem m1, indicator_of_notMem m2, add_zero, abs_of_pos hpos]
      push_cast; ring
  · rw [if_neg h1]
    have m1 : w ∉ Icc (0 : ℝ) 1 := fun h' ↦ h1 (by rw [abs_le]; constructor <;> linarith [h'.1, h'.2])
    have m2 : -w ∉ Icc (0 : ℝ) 1 := fun h' ↦ h1 (by rw [abs_le]; constructor <;> linarith [h'.1, h'.2])
    rw [indicator_of_notMem m1, indicator_of_notMem m2, add_zero, mul_zero]

/-- **CC's `ζ_n` is `zetaRep τ_n (phiR n)`** a.e.: it vanishes on `(-1, 1)` and equals
`τ_n phi_n(|v|)/√2` on `|v| > 1`. -/
theorem zeta_ae {ι : Type*} (bR : EigenBasis CopR ι) (i : ι) :
    (((realProlateBasis bR).ζ i : L2R) : ℝ → ℂ) =ᵐ[volume]
      zetaRep ((realProlateBasis bR).τ i) (phiR bR i) := by
  set b := realProlateBasis bR
  have hζ : ((b.ζ i : evenL2) : L2R) = ((b.s i)⁻¹ : ℂ) • ((𝓕 ((b.ξ i : L2R)) : L2R)
      - P1 (𝓕 ((b.ξ i : L2R)) : L2R)) := by
    rw [ArchS6.ProlateBasis.ζ, Submodule.coe_smul, ArchS6.ProlateBasis.ψ,
      ArchS6.ProlateBasis.η]
    rfl
  have hF := fourier_ξ_ae_real bR i
  rw [← realProlateBasis_ξ] at hF
  rw [hζ]
  filter_upwards [Lp.coeFn_smul ((b.s i)⁻¹ : ℂ) ((𝓕 ((b.ξ i : L2R)) : L2R)
      - P1 (𝓕 ((b.ξ i : L2R)) : L2R)),
    Lp.coeFn_sub ((𝓕 ((b.ξ i : L2R)) : L2R)) (P1 (𝓕 ((b.ξ i : L2R)) : L2R)),
    coeFn_P1 (𝓕 ((b.ξ i : L2R)) : L2R), hF, ae_ne_real 1, ae_ne_real (-1)] with w e1 e2 e3 e4 h1 h2
  rw [e1, Pi.smul_apply, e2, Pi.sub_apply, e3, zetaRep, smul_eq_mul]
  by_cases hw : w ∈ Icc (-1 : ℝ) 1
  · have : ¬ 1 ≤ |w| := by
      intro h; rw [le_abs] at h
      rcases h with h | h
      · exact h1 (le_antisymm hw.2 h)
      · exact h2 (by linarith [hw.1])
    rw [indicator_of_mem hw, sub_self, mul_zero, if_neg this]
  · have : 1 ≤ |w| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hw
      rcases hw with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [indicator_of_notMem hw, sub_zero, if_pos this, e4, phiR_abs, c2_eq,
      ArchS6.ProlateBasis.τ, realProlateBasis_lam]
    have hs : b.s i ≠ 0 := (b.s_pos i).ne'
    push_cast
    field_simp

/-! ### Pointwise scalings -/

/-- A scaling acting pointwise: `ϑ(e^t) f (v) = e^{-t/2} f(e^{-t} v)` (CC (61)). -/
def IsPointwise (T : Scaling (evenPair)) : Prop :=
  ∀ t (f : evenL2), (((T.θ t f : evenL2) : L2R) : ℝ → ℂ) =ᵐ[volume]
    fun v ↦ (Real.exp (-t / 2) : ℂ) * ((f : L2R) : ℝ → ℂ) (Real.exp (-t) * v)

theorem inner_evenL2 (a b : evenL2) :
    ⟪a, b⟫_ℂ = ∫ v, conj (((a : L2R) : ℝ → ℂ) v) * ((b : L2R) : ℝ → ℂ) v := by
  rw [Submodule.coe_inner, MeasureTheory.L2.inner_def]
  congr 1; funext v
  rw [RCLike.inner_apply']

/-- For a pointwise scaling, `⟨a | ϑ(e^{-t}) b⟩ = ∫ conj A(v) e^{t/2} B(e^t v) dv` for any
representatives `A`, `B` of `a`, `b`. -/
theorem inner_dil {T : Scaling evenPair} (hT : IsPointwise T) (t : ℝ) {a b : evenL2}
    {A B : ℝ → ℂ} (hA : ((a : L2R) : ℝ → ℂ) =ᵐ[volume] A) (hB : ((b : L2R) : ℝ → ℂ) =ᵐ[volume] B) :
    ⟪a, T.θ (-t) b⟫_ℂ = ∫ v, conj (A v) * dil t B v := by
  rw [inner_evenL2]
  refine integral_congr_ae ?_
  filter_upwards [hA, hT (-t) b, ae_comp_mul hB (Real.exp_pos t).ne'] with v e1 e2 e3
  rw [e1, e2, neg_neg, dil, e3]

/-! ### CC's ε is S8's ε -/

section Identification

variable {ι : Type*} (bR : EigenBasis CopR ι) (T : Scaling evenPair) (hT : IsPointwise T)
  (D : ProlateDataNat) (σ : ℕ ≃ ι) (hDlam : ∀ n, D.lam n = bR.μ (σ n))
  (hDphi : ∀ n, D.phi n = phiR bR (σ n))

include hT hDlam hDphi in
/-- The n-th term of (84) for the concrete basis is S8's `w_n kn_n`. -/
theorem εS_term {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    ((realProlateBasis bR).τ (σ n) : ℂ)
        * ⟪(realProlateBasis bR).ξ (σ n), T.θ (-t) ((realProlateBasis bR).ζ (σ n))⟫_ℂ
      = ((D.w n * D.kn n t : ℝ) : ℂ) := by
  rw [inner_dil hT t (xi_ae bR (σ n)) (zeta_ae bR (σ n)), ← hDphi n]
  have hτ : (realProlateBasis bR).τ (σ n) = D.lam n / Real.sqrt (1 - D.lam n ^ 2) := by
    rw [ArchS6.ProlateBasis.τ, ArchS6.ProlateBasis.s, realProlateBasis_lam, hDlam]
  rw [hτ]
  exact cc84_coeff D n ht

include hT hDlam hDphi in
/-- **CC's ε of Thm 4.7 is S8's `D.eps`** (`t = log ρ ≥ 0`): closes S8 open item 1 for the
concrete basis. -/
theorem εS_eq_eps {t : ℝ} (ht : 0 ≤ t) :
    ProlateBasis.εS (realProlateBasis bR) T t = ((D.eps t : ℝ) : ℂ) := by
  rw [ProlateBasis.εS, ← σ.tsum_eq, ProlateData.eps, Complex.ofReal_tsum]
  congr 1; funext n
  exact εS_term bR T hT D σ hDlam hDphi ht n

include hT hDlam hDphi in
/-- `∫ f(x) ε(e^{|x|}) dx = D.Eplus f`: CC's `E(f)` is S8's `Eplus`. -/
theorem integral_εS_eq_Eplus (f : ℝ → ℂ) :
    ∫ x, f x * ProlateBasis.εS (realProlateBasis bR) T |x| = D.Eplus f := by
  rw [ProlateData.Eplus]
  congr 1; funext x
  rw [εS_eq_eps bR T hT D σ hDlam hDphi (abs_nonneg x)]

end Identification

/-! ### Reality of the prolates -/

theorem xiRep_conj (phi : ℝ → ℝ) (v : ℝ) : conj (xiRep phi v) = xiRep phi v := by
  unfold xiRep; split_ifs <;> simp

/-- The reality hypothesis of `thm47` holds for the concrete prolates and a pointwise scaling. -/
theorem hreal_of_pointwise {ι : Type*} (bR : EigenBasis CopR ι) {T : Scaling evenPair}
    (hT : IsPointwise T) (i : ι) (t : ℝ) :
    ⟪(realProlateBasis bR).ξ i, T.θ t ((realProlateBasis bR).ξ i)⟫_ℂ
      = ⟪(realProlateBasis bR).ξ i, T.θ (-t) ((realProlateBasis bR).ξ i)⟫_ℂ := by
  set X := xiRep (phiR bR i)
  have h1 := inner_dil hT (-t) (xi_ae bR i) (xi_ae bR i)
  have h2 := inner_dil hT t (xi_ae bR i) (xi_ae bR i)
  rw [neg_neg] at h1
  rw [h1, h2]
  simp_rw [xiRep_conj, dil]
  have hsimp' : ∀ w, Real.exp (-t) * (Real.exp t * w) = w := fun w ↦ by
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  have key := MeasureTheory.Measure.integral_comp_mul_left
    (fun v ↦ X v * ((Real.exp (-t / 2) : ℂ) * X (Real.exp (-t) * v))) (Real.exp t)
  simp only [hsimp'] at key
  have hG : (∫ v, X v * ((Real.exp (-t / 2) : ℂ) * X (Real.exp (-t) * v)))
      = (Real.exp t : ℂ) * ∫ w, X (Real.exp t * w) * ((Real.exp (-t / 2) : ℂ) * X w) := by
    rw [key, abs_of_pos (inv_pos.2 (Real.exp_pos t)), Complex.real_smul, ← mul_assoc,
      ← Complex.ofReal_mul, mul_inv_cancel₀ (Real.exp_pos t).ne', Complex.ofReal_one, one_mul]
  rw [hG, ← integral_const_mul]
  congr 1; funext w
  have hE : (Real.exp t : ℂ) * (Real.exp (-t / 2) : ℂ) = (Real.exp (t / 2) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]; ring_nf
  linear_combination (X w * X (Real.exp t * w)) * hE

/-! ### Theorem 4.7, concrete -/

/-- **CC Theorem 4.7 in the island's conventions.**

For the real prolate basis `bR` of S6 (indexed by `ℕ` through `σ`), a pointwise scaling `T` on
`L²(ℝ)_ev` (O3), an operator `V` (`ϑ(g)`) whose adjoint satisfies the coefficient formula against
`f = autocorr g` (O3), any `ProlateData D` with the same `λ_n` and `phi_n` (S8's interface), and CC (85)
in Hilbert–Schmidt form with W∞ = `ArchS3.archW g` (O1, O2):
`Tr(ϑ(g∗g*) S) = ‖S ϑ(g)‖²_HS = archW g + Re (D.Eplus (autocorr g))`. -/
theorem thm47_concrete {ι : Type*} (bR : EigenBasis CopR ι) (T : Scaling evenPair)
    (hT : IsPointwise T) (D : ProlateDataNat) (σ : ℕ ≃ ι) (hDlam : ∀ n, D.lam n = bR.μ (σ n))
    (hDphi : ∀ n, D.phi n = phiR bR (σ n))
    (hτ : Summable fun i ↦ |(realProlateBasis bR).τ i|)
    (g : ℝ → ℂ) (hf : Integrable (WeilExplicit.autocorr g)) (V : evenL2 →L[ℂ] evenL2)
    (hcoef : ∀ v, ((‖(ContinuousLinearMap.adjoint V) v‖ ^ 2 : ℝ) : ℂ)
      = ∫ x, WeilExplicit.autocorr g x * ⟪v, T.θ x v⟫_ℂ)
    {κ : Type*} (e : HilbertBasis κ ℂ evenL2)
    (h85 : HasSum (fun k ↦ ‖evenPair.hatP (evenPair.P (V (e k)))‖ ^ 2)
      (ArchS3.archW g
        + (∫ x, WeilExplicit.autocorr g x * ProlateBasis.δS (realProlateBasis bR) T |x|).re)) :
    HasSum (fun k ↦ ‖ArchS6.ProlateBasis.soninProj (S := evenPair) (V (e k))‖ ^ 2)
      (ArchS3.archW g + (D.Eplus (WeilExplicit.autocorr g)).re) := by
  have : Countable ι := σ.symm.injective.countable
  have h := ProlateBasis.thm47 (realProlateBasis bR) T (hreal_of_pointwise bR hT) hτ e V hf hcoef
    (ArchS3.archW g) h85
  rwa [integral_εS_eq_Eplus bR T hT D σ hDlam hDphi] at h

/-- **CC (83), concrete**: `archW g + Re (D.Eplus (autocorr g)) ≥ 0`. -/
theorem thm47_concrete_nonneg {ι : Type*} (bR : EigenBasis CopR ι) (T : Scaling evenPair)
    (hT : IsPointwise T) (D : ProlateDataNat) (σ : ℕ ≃ ι) (hDlam : ∀ n, D.lam n = bR.μ (σ n))
    (hDphi : ∀ n, D.phi n = phiR bR (σ n))
    (hτ : Summable fun i ↦ |(realProlateBasis bR).τ i|)
    (g : ℝ → ℂ) (hf : Integrable (WeilExplicit.autocorr g)) (V : evenL2 →L[ℂ] evenL2)
    (hcoef : ∀ v, ((‖(ContinuousLinearMap.adjoint V) v‖ ^ 2 : ℝ) : ℂ)
      = ∫ x, WeilExplicit.autocorr g x * ⟪v, T.θ x v⟫_ℂ)
    {κ : Type*} (e : HilbertBasis κ ℂ evenL2)
    (h85 : HasSum (fun k ↦ ‖evenPair.hatP (evenPair.P (V (e k)))‖ ^ 2)
      (ArchS3.archW g
        + (∫ x, WeilExplicit.autocorr g x * ProlateBasis.δS (realProlateBasis bR) T |x|).re)) :
    0 ≤ ArchS3.archW g + (D.Eplus (WeilExplicit.autocorr g)).re :=
  (thm47_concrete bR T hT D σ hDlam hDphi hτ g hf V hcoef e h85).nonneg fun _ ↦ sq_nonneg _

end ArchS7
