/-
  E6Bridge4 -- routes-roadmap milestone E8 = B6 = D6 (2026-09-18): the RH registry node
  RH_limit_explicit_formula (the unconditional Weil 1952 / Guinand 1948 explicit formula for
  Mathlib's riemannZeta, Iwaniec--Kowalski Thm 5.12 normalisation, for every smooth compactly
  supported test function g : R -> C, stated as HasSum over ALL rho : C with the registry
  divisor multiplicity, plus Integrable for the archimedean integrand) discharged from
  Anthropic's zeta-23-lean (Alpoege--Furman, arXiv:2608.13637; Apache-2.0; pinned in
  lakefile.toml).

  WHAT IS CONSUMED (all unconditional in the pinned Zeta23, #print axioms =
  [propext, Classical.choice, Quot.sound], see AxiomGuardRvMBridge.lean):
    Zeta23.WeilEF.EF_lit_zetaZeroConfig   (the literature-form explicit formula [eq:EFstd] for
                                           the canonical zero configuration: Summable + tsum
                                           identity over the nontrivial zeros, weight
                                           analyticOrderAt, test class C_c^2)
    Zeta23.EF.paper_inversion             (Fourier inversion in the paper normalisation)
    Zeta23.EF.integrable_fourier_of_contDiff_two, Zeta23.EF.integrable_paperFT_ofReal
    Zeta23.WeilEF.gammaR_bracket          (Gamma_R'/Gamma_R(1/2+it) + Gamma_R'/Gamma_R(1/2-it)
                                           = Re psi(1/4 + it/2) - log pi)
    Zeta23.WeilEF.integrable_mul_logDeriv_Gammaℝ_of_decay, norm_Hfn_le, continuous_Hfn_line
    Zeta23.RvM.analyticOnNhd_riemannZeta  (zeta analytic off s = 1; the divisor seam)

  WHY THIS IS A NORMALISATION BRIDGE AND NOT A NEW CONTOUR ARGUMENT: zeta-23-lean already
  proves the explicit formula (Zeta23/WeilEF/, ~4500 lines: the rectangle contour with the
  completed zeta Lambda, good heights, the prime side by Fourier inversion of the tilted test
  function, the Gamma_R bracket, absolute convergence of the zero side from the local count).
  The E8 node differs from its statement in five bookkeeping respects, each closed here:
    (i)   the transform: weilKernel g s = int g(u) e^{(s-1/2)u} du is Zeta23's
          Hfn g s = paperFT g ((s-1/2)/i)  (weilKernel_eq_Hfn: I * (x / I) = x);
    (ii)  the archimedean term: the node writes -g(0) log pi + (1/2pi) int h(r) Re psi dr where
          the upstream writes (1/2pi) int h(r) [Re psi - log pi] dr; the difference is
          (1/2pi) int h = g(0), Fourier inversion at the origin (inversion_zero);
    (iii) the node asserts Integrable (archIntegrand g) separately (the upstream only needs the
          bracket integral as a value): integrable_archIntegrand, from the C/(1+t^2) decay of
          the transform times the log growth of digamma on the strip;
    (iv)  the index set: the node sums over ALL rho : C with the divisor weight
          (MeromorphicOn.divisor zeta {0 < Re < 1}).toNat, the upstream over the subtype of
          nontrivial zeros with weight (analyticOrderAt zeta rho).toNat; the divisor is
          supported in the strip and equals analyticOrderAt there (zeroMult_eq_of_strip,
          zeroMult_eq_zero_of_not_nontrivial), so hasSum_subtype_iff_of_support_subset
          transports the sum;
    (v)   the test class: C^infinity (the node) implies C^2 (the upstream), contDiff_infty.
  The corridor bound (E6Bridge3) and the cumulative RvM (E6Bridge2) are the classical inputs
  the design memo (telperion/docs/E8_LIMIT_EXPLICIT_FORMULA_DESIGN_2026-09-18.md, section 8)
  planned to consume; on this island the upstream's own good-height lemma and local count
  play those roles inside EF_lit_zetaZeroConfig, so neither bridge is imported here.

  The six definitions in namespace WeilExplicit are VERBATIM copies of the AUTHORED block of
  telperion/missions/rh/lean/Statements/RHDefs.lean (branch rh/e8-statement), and the theorem
  line is the node statement of
  telperion/missions/rh/lean/Statements/RH_limit_explicit_formula.lean verbatim (name and
  binder-free form), so the registry's normalized-containment grant gate matches
  (../generate.py --check).  Because the registry files may not be present in every checkout
  of this island, the drift check ALSO compares the theorem against the copy embedded between
  the two marker lines below (the registry file's placeholder proof tail is dropped):

  BEGIN REGISTRY STATEMENT
  theorem limit_explicit_formula (g : ℝ → ℂ) (hg : WeilExplicit.IsWeilTest g) :
      Integrable (WeilExplicit.archIntegrand g) ∧
      HasSum (fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℂ) * WeilExplicit.weilKernel g ρ)
        (WeilExplicit.archSide g - WeilExplicit.primeSide g)
  END REGISTRY STATEMENT

  No RH progress is claimed: this is the classical explicit formula, machine-checked; the
  zero side is summed over the zeros wherever they are (off-line zeros are seen literally,
  the transform being entire).  conjecture1_proved = False.
-/
import Zeta23.WeilEF.Main
import Zeta23.RvM.ZetaGrowth

open Zeta23 Complex MeasureTheory

noncomputable section

/-! ## The registry vocabulary, mirrored verbatim (RHDefs.lean, WeilExplicit AUTHORED block). -/

namespace WeilExplicit
open MeasureTheory Complex

/-- The E8 test class: smooth, compactly supported g : R -> C. -/
def IsWeilTest (g : ℝ → ℂ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ HasCompactSupport g

/-- H_g(s) = ∫ g(u) e^{(s - 1/2) u} du, the zero-side transform.  With s = 1/2 + i r this is
    h(r) = ∫ g(u) e^{i r u} du (the Iwaniec-Kowalski pair); entire for compactly supported g,
    so H_g(ρ) at a zero ρ = 1/2 + iγ is h(γ) with γ complex when ρ is off the line.
    H_g(0) = h(i/2) and H_g(1) = h(-i/2) are the two pole terms. -/
noncomputable def weilKernel (g : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ u : ℝ, g u * Complex.exp ((s - 1 / 2) * (u : ℂ))

/-- Multiplicity of ρ as a nontrivial zero: the order of ζ at ρ on the open critical strip
    (0 off the strip and at non-zeros).  The SAME divisor expression as
    RvMCount.zetaZeroCount, so the E8 zero side and the RvM count carry identical weights. -/
noncomputable def zeroMult (ρ : ℂ) : ℕ :=
  ((MeromorphicOn.divisor riemannZeta {s : ℂ | 0 < s.re ∧ s.re < 1} : ℂ → ℤ) ρ).toNat

/-- The archimedean integrand h(r) · Re ψ(1/4 + i r/2), ψ = Γ'/Γ = Complex.digamma. -/
noncomputable def archIntegrand (g : ℝ → ℂ) (r : ℝ) : ℂ :=
  weilKernel g (1 / 2 + (r : ℂ) * I) * ((Complex.digamma (1 / 4 + ((r : ℂ) / 2) * I)).re : ℂ)

/-- The archimedean side: h(i/2) + h(-i/2) - g(0) log π + (1/2π) ∫ h(r) Re ψ(1/4 + i r/2) dr. -/
noncomputable def archSide (g : ℝ → ℂ) : ℂ :=
  weilKernel g 0 + weilKernel g 1 - g 0 * (Real.log Real.pi : ℂ)
    + (1 / (2 * (Real.pi : ℂ))) * ∫ r : ℝ, archIntegrand g r

/-- The prime side: Σ_n Λ(n)/√n · (g(log n) + g(-log n)); a finite sum for compactly
    supported g (Λ(0) = Λ(1) = 0; the two terms are the two vertical edges of the finite
    explicit formula rect_explicit_formula in the T → ∞ limit). -/
noncomputable def primeSide (g : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
    * (g (Real.log n) + g (-Real.log n))

end WeilExplicit

namespace RvMBridge4
open WeilExplicit

/-! ## A. The transform: weilKernel is Zeta23's Hfn (= paperFT at (s - 1/2)/i). -/

/-- The node's test class is contained in the upstream's C_c^2 class. -/
lemma contDiff_two_of_test {g : ℝ → ℂ} (hg : IsWeilTest g) : ContDiff ℝ 2 g :=
  contDiff_infty.mp hg.1 2

/-- weilKernel g s = Hfn g s: the integrands agree since I * ((s - 1/2) / I) = s - 1/2. -/
lemma weilKernel_eq_Hfn (g : ℝ → ℂ) (s : ℂ) : weilKernel g s = Zeta23.WeilEF.Hfn g s := by
  unfold weilKernel Zeta23.WeilEF.Hfn paperFT
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  congr 2
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  field_simp

/-- The upstream zero-side summand shape: H_g(ρ) = h(γ_ρ) with γ_ρ = (ρ - 1/2)/i. -/
lemma weilKernel_eq_paperFT_gammaOf (g : ℝ → ℂ) (s : ℂ) :
    weilKernel g s = paperFT g (gammaOf s) := weilKernel_eq_Hfn g s

/-- On the critical line the transform is the paper Fourier transform h(r). -/
lemma weilKernel_line (g : ℝ → ℂ) (r : ℝ) : weilKernel g (1 / 2 + (r : ℂ) * I) = paperFT g r := by
  rw [weilKernel_eq_Hfn]
  unfold Zeta23.WeilEF.Hfn
  congr 1
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  field_simp
  ring

/-- The pole term at s = 0: H_g(0) = h(i/2). -/
lemma weilKernel_zero (g : ℝ → ℂ) : weilKernel g 0 = paperFT g (I / 2) := by
  rw [weilKernel_eq_Hfn]
  unfold Zeta23.WeilEF.Hfn
  congr 1
  rw [div_eq_iff Complex.I_ne_zero, div_mul_eq_mul_div, Complex.I_mul_I]
  norm_num

/-- The pole term at s = 1: H_g(1) = h(-i/2). -/
lemma weilKernel_one (g : ℝ → ℂ) : weilKernel g 1 = paperFT g (-I / 2) := by
  rw [weilKernel_eq_Hfn]
  unfold Zeta23.WeilEF.Hfn
  congr 1
  rw [div_eq_iff Complex.I_ne_zero]
  rw [show (-I / 2) * I = -(I * I) / 2 by ring, Complex.I_mul_I]
  norm_num

/-- The node's archimedean integrand is the upstream bracket integrand plus h(r) log pi. -/
lemma archIntegrand_eq (g : ℝ → ℂ) (r : ℝ) :
    archIntegrand g r = paperFT g r * ((Zeta23.EF.gammaBracket r : ℝ) : ℂ)
      + paperFT g r * ((Real.log Real.pi : ℝ) : ℂ) := by
  unfold archIntegrand Zeta23.EF.gammaBracket
  rw [weilKernel_line]
  have : (1 / 4 + ((r : ℂ) / 2) * I) = (1 / 4 + I * r / 2) := by ring
  rw [this]
  push_cast
  ring

lemma archIntegrand_funext (g : ℝ → ℂ) :
    archIntegrand g = fun r : ℝ => paperFT g r * ((Zeta23.EF.gammaBracket r : ℝ) : ℂ)
      + paperFT g r * ((Real.log Real.pi : ℝ) : ℂ) := funext (archIntegrand_eq g)

/-- Fourier inversion at the origin: (1/2pi) int h(r) dr = g(0). -/
lemma inversion_zero {g : ℝ → ℂ} (hg : IsWeilTest g) :
    (1 / (2 * (Real.pi : ℂ))) * ∫ r : ℝ, paperFT g r = g 0 := by
  have hk2 := contDiff_two_of_test hg
  have h := Zeta23.EF.paper_inversion hk2.continuous
    (hk2.continuous.integrable_of_hasCompactSupport hg.2)
    (Zeta23.EF.integrable_fourier_of_contDiff_two hk2 hg.2) 0
  rw [h]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp

/-! ## B. Integrability of the archimedean integrand. -/

lemma paperFT_eq_Hfn_half (g : ℝ → ℂ) (t : ℝ) :
    paperFT g t = Zeta23.WeilEF.Hfn g (((1 / 2 : ℝ) : ℂ) + t * I) := by
  rw [← weilKernel_line, weilKernel_eq_Hfn]
  push_cast
  rfl

lemma continuous_paperFT_real {g : ℝ → ℂ} (hg : IsWeilTest g) :
    Continuous (fun t : ℝ => paperFT g t) := by
  have h := Zeta23.WeilEF.continuous_Hfn_line (contDiff_two_of_test hg) hg.2 (1 / 2)
  refine h.congr fun t => ?_
  exact (paperFT_eq_Hfn_half g t).symm

/-- The C/(1 + t^2) decay of the transform on the critical line (two integrations by parts,
done upstream in norm_Hfn_le). -/
lemma norm_paperFT_le {g : ℝ → ℂ} (hg : IsWeilTest g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖paperFT g t‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := Zeta23.WeilEF.norm_Hfn_le (contDiff_two_of_test hg) hg.2
  refine ⟨C, hC0, fun t => ?_⟩
  rw [paperFT_eq_Hfn_half]
  exact hC (1 / 2) t (by norm_num) (by norm_num)

lemma integrable_paperFT {g : ℝ → ℂ} (hg : IsWeilTest g) :
    Integrable (fun t : ℝ => paperFT g t) :=
  Zeta23.EF.integrable_paperFT_ofReal
    (Zeta23.EF.integrable_fourier_of_contDiff_two (contDiff_two_of_test hg) hg.2)

/-- The upstream Gamma_R bracket identity in the node's digamma spelling. -/
lemma gammaBracket_eq (t : ℝ) :
    ((Zeta23.EF.gammaBracket t : ℝ) : ℂ)
      = logDeriv Complex.Gammaℝ (1 / 2 + t * I) + logDeriv Complex.Gammaℝ (1 / 2 - t * I) := by
  rw [Zeta23.WeilEF.gammaR_bracket]
  unfold Zeta23.EF.gammaBracket
  congr 3
  ring_nf

/-- h(r) [Re psi(1/4 + ir/2) - log pi] is integrable: each Gamma_R log-derivative factor on
Re = 1/2 is O(log(2 + |t|)) against the C/(1 + t^2) decay of h. -/
lemma integrable_paperFT_mul_bracket {g : ℝ → ℂ} (hg : IsWeilTest g) :
    Integrable (fun t : ℝ => paperFT g t * ((Zeta23.EF.gammaBracket t : ℝ) : ℂ)) := by
  obtain ⟨C, hC0, hC⟩ := norm_paperFT_le hg
  have hcont := continuous_paperFT_real hg
  have h1 : Integrable (fun t : ℝ => paperFT g t
      * logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) : ℂ) + t * I)) :=
    Zeta23.WeilEF.integrable_mul_logDeriv_Gammaℝ_of_decay hcont hC0 hC (σ := 1 / 2)
      (by norm_num) (by norm_num)
  have h2' : Integrable (fun t : ℝ => paperFT g ((-t : ℝ) : ℂ)
      * logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) : ℂ) + t * I)) := by
    refine Zeta23.WeilEF.integrable_mul_logDeriv_Gammaℝ_of_decay
      (φ := fun t : ℝ => paperFT g ((-t : ℝ) : ℂ))
      (hcont.comp continuous_neg) hC0 (fun t => ?_) (σ := 1 / 2) (by norm_num) (by norm_num)
    have := hC (-t)
    simpa using this
  have h2 := h2'.comp_neg
  refine (h1.add h2).congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply, neg_neg]
  rw [gammaBracket_eq]
  push_cast
  ring_nf

/-- The Integrable conjunct of the node. -/
theorem integrable_archIntegrand {g : ℝ → ℂ} (hg : IsWeilTest g) :
    Integrable (archIntegrand g) := by
  rw [archIntegrand_funext]
  exact (integrable_paperFT_mul_bracket hg).add ((integrable_paperFT hg).mul_const _)

/-! ## C. The two sides in the upstream normalisation. -/

/-- archSide g in the [eq:EFstd] shape: the -g(0) log pi term is absorbed into the bracket by
Fourier inversion at the origin. -/
theorem archSide_eq {g : ℝ → ℂ} (hg : IsWeilTest g) :
    archSide g = paperFT g (I / 2) + paperFT g (-I / 2)
      + (1 / (2 * (Real.pi : ℂ))) * ∫ r : ℝ, paperFT g r * ((Zeta23.EF.gammaBracket r : ℝ) : ℂ) := by
  unfold archSide
  rw [weilKernel_zero, weilKernel_one, archIntegrand_funext,
    integral_add (integrable_paperFT_mul_bracket hg) ((integrable_paperFT hg).mul_const _),
    integral_mul_const]
  have hinv := inversion_zero hg
  linear_combination ((Real.log Real.pi : ℝ) : ℂ) * hinv

/-- The prime side is syntactically the upstream n-sum. -/
theorem primeSide_eq (g : ℝ → ℂ) :
    primeSide g = ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
      * (g (Real.log n) + g (-Real.log n)) := rfl

/-- archSide - primeSide is the upstream literatureRHS. -/
theorem archSide_sub_primeSide {g : ℝ → ℂ} (hg : IsWeilTest g) :
    archSide g - primeSide g = Zeta23.EF.literatureRHS g := by
  rw [archSide_eq hg, primeSide_eq, Zeta23.EF.literatureRHS]
  ring

/-! ## D. The multiplicity seam: the registry divisor weight vs Zeta23's analyticOrderAt. -/

lemma one_not_mem_strip : (1 : ℂ) ∉ {s : ℂ | 0 < s.re ∧ s.re < 1} := by
  intro h
  simp only [Set.mem_ofPred_eq, Complex.one_re] at h
  exact lt_irrefl _ h.2

/-- On the open strip the registry divisor multiplicity is Zeta23's `zeroMult`
(= (analyticOrderAt riemannZeta rho).toNat). -/
lemma zeroMult_eq_of_strip {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    WeilExplicit.zeroMult ρ = Zeta23.zeroMult ρ := by
  have hA : AnalyticOnNhd ℂ riemannZeta {s : ℂ | 0 < s.re ∧ s.re < 1} :=
    Zeta23.RvM.analyticOnNhd_riemannZeta one_not_mem_strip
  unfold WeilExplicit.zeroMult
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hA
    (show ρ ∈ {s : ℂ | 0 < s.re ∧ s.re < 1} from ⟨h0, h1⟩)]
  unfold Zeta23.zeroMult
  induction analyticOrderAt riemannZeta ρ using ENat.recTopCoe with
  | top => simp
  | coe n => simp

/-- Off the strip the divisor vanishes (it is supported within its domain). -/
lemma zeroMult_eq_zero_of_not_strip {ρ : ℂ} (h : ¬ (0 < ρ.re ∧ ρ.re < 1)) :
    WeilExplicit.zeroMult ρ = 0 := by
  unfold WeilExplicit.zeroMult
  have : (MeromorphicOn.divisor riemannZeta {s : ℂ | 0 < s.re ∧ s.re < 1} : ℂ → ℤ) ρ = 0 := by
    by_contra hne
    exact h ((MeromorphicOn.divisor riemannZeta {s : ℂ | 0 < s.re ∧ s.re < 1}).supportWithinDomain
      (Function.mem_support.mpr hne))
  rw [this]
  rfl

/-- The registry multiplicity is supported on the nontrivial zeros. -/
lemma zeroMult_eq_zero_of_not_nontrivial {ρ : ℂ} (h : ¬ IsNontrivialZero ρ) :
    WeilExplicit.zeroMult ρ = 0 := by
  by_cases hs : 0 < ρ.re ∧ ρ.re < 1
  · rw [zeroMult_eq_of_strip hs.1 hs.2]
    have hne : riemannZeta ρ ≠ 0 := fun hz => h ⟨hz, hs.1, hs.2⟩
    unfold Zeta23.zeroMult
    rw [analyticOrderAt_eq_zero.mpr (Or.inr hne)]
    rfl
  · exact zeroMult_eq_zero_of_not_strip hs

/-- On the carrier the registry weight is the configuration's multiplicity. -/
lemma zeroMult_eq_mult {ρ : ℂ} (h : IsNontrivialZero ρ) :
    WeilExplicit.zeroMult ρ = zetaZeroConfig.mult ρ :=
  zeroMult_eq_of_strip h.2.1 h.2.2

/-! ## E. The node statement, verbatim. -/

theorem limit_explicit_formula (g : ℝ → ℂ) (hg : WeilExplicit.IsWeilTest g) :
    Integrable (WeilExplicit.archIntegrand g) ∧
    HasSum (fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℂ) * WeilExplicit.weilKernel g ρ)
      (WeilExplicit.archSide g - WeilExplicit.primeSide g) := by
  refine ⟨integrable_archIntegrand hg, ?_⟩
  obtain ⟨hsum, heq⟩ := Zeta23.WeilEF.EF_lit_zetaZeroConfig g (contDiff_two_of_test hg) hg.2
  have hsupp : Function.support (fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℂ) * weilKernel g ρ)
      ⊆ zetaZeroConfig.carrier := by
    intro ρ hρ
    by_contra hn
    apply hρ
    show (WeilExplicit.zeroMult ρ : ℂ) * weilKernel g ρ = 0
    rw [zeroMult_eq_zero_of_not_nontrivial hn]
    simp
  rw [← hasSum_subtype_iff_of_support_subset hsupp]
  have hcomp : ((fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℂ) * weilKernel g ρ)
      ∘ (Subtype.val : zetaZeroConfig.carrier → ℂ))
      = fun ρ : zetaZeroConfig.carrier => (zetaZeroConfig.mult ρ : ℂ) * paperFT g (gammaOf ρ) := by
    funext ρ
    simp only [Function.comp]
    rw [zeroMult_eq_mult ρ.2, weilKernel_eq_paperFT_gammaOf]
  rw [hcomp, archSide_sub_primeSide hg, ← heq]
  exact hsum.hasSum

end RvMBridge4
