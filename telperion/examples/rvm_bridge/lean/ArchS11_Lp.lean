/-
  ArchS11_Lp -- the L²([0, a]) layer of the S11 certificate (stage S11, rvm_bridge island, 2026-10-11).

  For a > 0 and coefficient lists, on L²([0, a]) over 𝕜 = ℝ or ℂ (S5's `volI 0 a`, `intOp`,
  `kernelOfContinuous`):
    * `polyLp a c` is x ↦ pv c (x / a);  `inner_polyLp`: ⟪polyLp c, polyLp d⟫ = a · mom c d;
    * `kerLp a E c0` is the kernel (x, y) ↦ pv E (|x/a - y/a|) + c0;
      `intOp_kerLp_polyLp`: T (polyLp P) = a • polyLp U whenever pv U = ∫_0^1 k̂(·, t) pv P t;
    * `norm_sq_ker_sub_tail`: the exact Hilbert-Schmidt norm ‖k - p‖² = a² q2 of the one-sided tail
      p(x, y) = Σ_j w_j Φ_j(x/a) U_j(y/a)  (Fubini in both orders);
    * `inner_tail_eq_zero`: ⟪T_p r, r⟫ = 0 when r ⊥ Φ_j (x-degree of p below N);
    * `inner_kerLp_const`: the constant kernel c0 contributes c0 |⟪1, f⟫|²;
    * `extL`: extension by zero L²([0, b]) → L²([0, c]) preserves norms, ⟪1, ·⟫ and kernel forms.
  No `sorry`.  conjecture1_proved = False.
-/
import ArchS11_Poly
import ArchS11_Galerkin
import ArchS5_Spectral

open MeasureTheory Set Finset
open scoped InnerProductSpace ComplexConjugate ENNReal

noncomputable section

namespace ArchS11

open ArchS5 ArchS11.Data

set_option linter.unusedSectionVars false

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## A. Integrals on `[0, a]`. -/

theorem integral_volI_eq {a : ℝ} (ha : 0 ≤ a) (f : ℝ → ℝ) :
    ∫ x, f x ∂(volI 0 a) = ∫ x in (0 : ℝ)..a, f x := by
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ha]

theorem integral_volI_scale {a : ℝ} (ha : 0 < a) (g : ℝ → ℝ) :
    ∫ x, g (x / a) ∂(volI 0 a) = a * ∫ s in (0 : ℝ)..1, g s := by
  rw [integral_volI_eq ha.le, intervalIntegral.integral_comp_div (f := g) ha.ne', zero_div,
    div_self ha.ne', smul_eq_mul]

theorem integrable_volI_prod {a : ℝ} {E' : Type*} [NormedAddCommGroup E'] {F : ℝ × ℝ → E'}
    (hF : Continuous F) : Integrable F ((volI 0 a).prod (volI 0 a)) := by
  rw [volI_prod]
  exact hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

theorem integrable_volI {a : ℝ} {E' : Type*} [NormedAddCommGroup E'] {F : ℝ → E'}
    (hF : Continuous F) : Integrable F (volI 0 a) :=
  hF.continuousOn.integrableOn_compact isCompact_Icc

/-- The scaled double integral: `∫∫_{[0,a]²} F(x/a, y/a) = a² ∫_0^1 ∫_0^1 F`. -/
theorem integral_volI_prod_scale {a : ℝ} (ha : 0 < a) (F : ℝ → ℝ → ℝ)
    (hF : Continuous (Function.uncurry F)) :
    ∫ p, F (p.1 / a) (p.2 / a) ∂((volI 0 a).prod (volI 0 a))
      = a ^ 2 * ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, F s t := by
  have hc : Continuous fun p : ℝ × ℝ => F (p.1 / a) (p.2 / a) :=
    hF.comp (by fun_prop : Continuous fun p : ℝ × ℝ => (p.1 / a, p.2 / a))
  rw [integral_prod _ (integrable_volI_prod hc)]
  have hin : ∀ x : ℝ, ∫ y, F (x / a) (y / a) ∂(volI 0 a) = a * ∫ t in (0 : ℝ)..1, F (x / a) t :=
    fun x => integral_volI_scale ha (fun t => F (x / a) t)
  simp_rw [hin]
  rw [integral_const_mul, integral_volI_scale ha (fun s => ∫ t in (0 : ℝ)..1, F s t)]
  ring

/-! ## B. Polynomials in `L²([0, a])`. -/

theorem memLp_volI {a : ℝ} {f : ℝ → 𝕜} (hf : Continuous f) : MemLp f 2 (volI 0 a) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) a) hf.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hC x hx

/-- `x ↦ pv c (x / a)`, as a 𝕜-valued function. -/
def polyFun (a : ℝ) (c : List ℚ) (x : ℝ) : 𝕜 := ((pv c (x / a) : ℝ) : 𝕜)

theorem continuous_polyFun (a : ℝ) (c : List ℚ) : Continuous (polyFun (𝕜 := 𝕜) a c) :=
  RCLike.continuous_ofReal.comp ((continuous_pv c).comp (continuous_id.div_const a))

/-- The polynomial `x ↦ pv c (x / a)` in `L²([0, a])`. -/
def polyLp (a : ℝ) (c : List ℚ) : Lp 𝕜 2 (volI 0 a) :=
  (memLp_volI (continuous_polyFun a c)).toLp _

theorem polyLp_ae (a : ℝ) (c : List ℚ) :
    (polyLp (𝕜 := 𝕜) a c : ℝ → 𝕜) =ᵐ[volI 0 a] polyFun a c := MemLp.coeFn_toLp _

/-- `⟪g, f⟫ = ∫ conj g · f` for an `L²([0,a])` element `f` and a continuous `g`. -/
theorem inner_polyLp_left {a : ℝ} (c : List ℚ) (f : Lp 𝕜 2 (volI 0 a)) :
    ⟪polyLp a c, f⟫_𝕜 = ∫ x, ((pv c (x / a) : ℝ) : 𝕜) * f x ∂(volI 0 a) := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [polyLp_ae (𝕜 := 𝕜) a c] with x hx
  rw [RCLike.inner_apply', hx, polyFun, RCLike.conj_ofReal]

theorem inner_polyLp {a : ℝ} (ha : 0 < a) (c d : List ℚ) :
    ⟪(polyLp a c : Lp 𝕜 2 (volI 0 a)), polyLp a d⟫_𝕜 = ((a * mom c d : ℝ) : 𝕜) := by
  rw [inner_polyLp_left]
  have : (fun x => ((pv c (x / a) : ℝ) : 𝕜) * (polyLp (𝕜 := 𝕜) a d : ℝ → 𝕜) x)
      =ᵐ[volI 0 a] fun x => ((pv c (x / a) * pv d (x / a) : ℝ) : 𝕜) := by
    filter_upwards [polyLp_ae (𝕜 := 𝕜) a d] with x hx
    rw [hx, polyFun]
    push_cast
    ring
  rw [integral_congr_ae this, integral_ofReal,
    integral_volI_scale ha (fun s => pv c s * pv d s), integral_pv_mul_pv]

theorem norm_polyLp_sq {a : ℝ} (ha : 0 < a) (c : List ℚ) :
    ‖(polyLp a c : Lp 𝕜 2 (volI 0 a))‖ ^ 2 = a * mom c c := by
  rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), inner_polyLp ha, RCLike.ofReal_re]

/-- A checked linear relation between polynomials lifts to `L²`. -/
theorem polyLp_eq_sum {a : ℝ} {q : List ℚ} {n : ℕ} {b : ℕ → ℚ} {P : ℕ → List ℚ}
    (h : ∀ s : ℝ, pv q s = ∑ l ∈ range n, (b l : ℝ) * pv (P l) s) :
    (polyLp a q : Lp 𝕜 2 (volI 0 a)) = ∑ l ∈ range n, ((b l : ℝ) : 𝕜) • polyLp a (P l) := by
  refine Lp.ext ?_
  have hs := Lp.coeFn_finsetSum (range n) fun l => ((b l : ℝ) : 𝕜) • (polyLp (𝕜 := 𝕜) a (P l))
  have hl : ∀ l ∈ range n, (⇑(((b l : ℝ) : 𝕜) • (polyLp (𝕜 := 𝕜) a (P l))) : ℝ → 𝕜)
      =ᵐ[volI 0 a] fun x => ((b l : ℝ) : 𝕜) * polyFun a (P l) x := by
    intro l _
    filter_upwards [Lp.coeFn_smul ((b l : ℝ) : 𝕜) (polyLp (𝕜 := 𝕜) a (P l)),
      polyLp_ae (𝕜 := 𝕜) a (P l)] with x h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul]
  have hall : ∀ᵐ x ∂(volI 0 a), ∀ l ∈ range n,
      (⇑(((b l : ℝ) : 𝕜) • (polyLp (𝕜 := 𝕜) a (P l))) : ℝ → 𝕜) x
        = ((b l : ℝ) : 𝕜) * polyFun a (P l) x :=
    (ae_ball_iff (Finset.countable_toSet _)).2 fun l hl' => hl l hl'
  filter_upwards [polyLp_ae (𝕜 := 𝕜) a q, hs, hall] with x h1 h2 h3
  rw [h1, h2, Finset.sum_apply, Finset.sum_congr rfl h3, polyFun, h]
  push_cast
  simp [polyFun]

theorem polyLp_sub_eq_sum {a : ℝ} {p q : List ℚ} {n : ℕ} {b : ℕ → ℚ} {P : ℕ → List ℚ}
    (h : ∀ s : ℝ, pv p s - pv q s = ∑ l ∈ range n, (b l : ℝ) * pv (P l) s) :
    (polyLp a p - polyLp a q : Lp 𝕜 2 (volI 0 a))
      = ∑ l ∈ range n, ((b l : ℝ) : 𝕜) • polyLp a (P l) := by
  refine Lp.ext ?_
  have hs := Lp.coeFn_finsetSum (range n) fun l => ((b l : ℝ) : 𝕜) • (polyLp (𝕜 := 𝕜) a (P l))
  have hl : ∀ l ∈ range n, (⇑(((b l : ℝ) : 𝕜) • (polyLp (𝕜 := 𝕜) a (P l))) : ℝ → 𝕜)
      =ᵐ[volI 0 a] fun x => ((b l : ℝ) : 𝕜) * polyFun a (P l) x := by
    intro l _
    filter_upwards [Lp.coeFn_smul ((b l : ℝ) : 𝕜) (polyLp (𝕜 := 𝕜) a (P l)),
      polyLp_ae (𝕜 := 𝕜) a (P l)] with x h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul]
  have hall : ∀ᵐ x ∂(volI 0 a), ∀ l ∈ range n,
      (⇑(((b l : ℝ) : 𝕜) • (polyLp (𝕜 := 𝕜) a (P l))) : ℝ → 𝕜) x
        = ((b l : ℝ) : 𝕜) * polyFun a (P l) x :=
    (ae_ball_iff (Finset.countable_toSet _)).2 fun l hl' => hl l hl'
  filter_upwards [Lp.coeFn_sub (polyLp (𝕜 := 𝕜) a p) (polyLp a q), polyLp_ae (𝕜 := 𝕜) a p,
    polyLp_ae (𝕜 := 𝕜) a q, hs, hall] with x h0 h1 h1' h2 h3
  rw [h0, Pi.sub_apply, h1, h1', h2, Finset.sum_apply, Finset.sum_congr rfl h3, polyFun, polyFun,
    ← RCLike.ofReal_sub, h]
  push_cast
  simp [polyFun]

theorem polyLp_mem_span {a : ℝ} {q : List ℚ} {N : ℕ} {b : ℕ → ℚ} {P : ℕ → List ℚ}
    (h : ∀ s : ℝ, pv q s = ∑ l ∈ range N, (b l : ℝ) * pv (P l) s) :
    (polyLp a q : Lp 𝕜 2 (volI 0 a)) ∈
      Submodule.span 𝕜 (Set.range fun l : Fin N => (polyLp a (P l) : Lp 𝕜 2 (volI 0 a))) := by
  rw [polyLp_eq_sum h]
  refine Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨⟨l, Finset.mem_range.1 hl⟩, rfl⟩

/-! ## C. The kernel `pv E (|s - t|) + c0`. -/

/-- The hat kernel on `[0, 1]²`. -/
def kR (E : List ℚ) (c0 : ℚ) (s t : ℝ) : ℝ := pv E |s - t| + c0

theorem continuous_kR (E : List ℚ) (c0 : ℚ) : Continuous (Function.uncurry (kR E c0)) := by
  unfold kR
  exact ((continuous_pv E).comp (continuous_fst.sub continuous_snd).abs).add continuous_const

theorem kR_symm (E : List ℚ) (c0 : ℚ) (s t : ℝ) : kR E c0 s t = kR E c0 t s := by
  unfold kR; rw [abs_sub_comm]

/-- The kernel on `[0, a]²`: `(x, y) ↦ pv E (|x/a - y/a|) + c0`. -/
def kerF (a : ℝ) (E : List ℚ) (c0 : ℚ) (p : ℝ × ℝ) : 𝕜 := ((kR E c0 (p.1 / a) (p.2 / a) : ℝ) : 𝕜)

theorem continuous_kerF (a : ℝ) (E : List ℚ) (c0 : ℚ) : Continuous (kerF (𝕜 := 𝕜) a E c0) :=
  RCLike.continuous_ofReal.comp ((continuous_kR E c0).comp
    (by fun_prop : Continuous fun p : ℝ × ℝ => (p.1 / a, p.2 / a)))

theorem kerF_symm (a : ℝ) (E : List ℚ) (c0 : ℚ) (x y : ℝ) :
    kerF (𝕜 := 𝕜) a E c0 (y, x) = (starRingEnd 𝕜) (kerF a E c0 (x, y)) := by
  unfold kerF
  rw [RCLike.conj_ofReal, kR_symm]

def kerLp (a : ℝ) (E : List ℚ) (c0 : ℚ) : Lp 𝕜 2 ((volI 0 a).prod (volI 0 a)) :=
  kernelOfContinuous 0 a (kerF a E c0) (continuous_kerF a E c0)

theorem isHermitian_kerLp (a : ℝ) (E : List ℚ) (c0 : ℚ) : IsHermitianKernel (kerLp (𝕜 := 𝕜) a E c0) :=
  isHermitianKernel_kernelOfContinuous _ (kerF_symm a E c0)

theorem intOp_kerLp_symm (a : ℝ) (E : List ℚ) (c0 : ℚ) (x y : Lp 𝕜 2 (volI 0 a)) :
    ⟪intOp (kerLp a E c0) x, y⟫_𝕜 = ⟪x, intOp (kerLp a E c0) y⟫_𝕜 :=
  isSymmetric_intOp (isHermitian_kerLp a E c0) x y

/-- **The kernel on polynomials**: `T (polyLp P) = a • polyLp U` if `pv U = ∫_0^1 k̂(·, t) pv P t`. -/
theorem intOp_kerLp_polyLp {a : ℝ} (ha : 0 < a) {E : List ℚ} {c0 : ℚ} {P U : List ℚ}
    (hU : ∀ s ∈ Icc (0 : ℝ) 1, pv U s = ∫ t in (0 : ℝ)..1, kR E c0 s t * pv P t) :
    intOp (kerLp (𝕜 := 𝕜) a E c0) (polyLp a P) = (a : 𝕜) • polyLp a U := by
  unfold kerLp
  refine Lp.ext ?_
  filter_upwards [intOp_kernelOfContinuous_ae_eq (continuous_kerF (𝕜 := 𝕜) a E c0) (polyLp a P),
    Lp.coeFn_smul (a : 𝕜) (polyLp (𝕜 := 𝕜) a U), polyLp_ae (𝕜 := 𝕜) a U,
    ae_restrict_mem (μ := volume) (measurableSet_Icc (a := (0 : ℝ)) (b := a))] with x h1 h2 h3 hx
  rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul]
  have e1 : ∫ y in Icc 0 a, kerF (𝕜 := 𝕜) a E c0 (x, y) * (polyLp (𝕜 := 𝕜) a P : ℝ → 𝕜) y
      = ∫ y in Icc 0 a, ((kR E c0 (x / a) (y / a) * pv P (y / a) : ℝ) : 𝕜) := by
    refine integral_congr_ae ?_
    filter_upwards [polyLp_ae (𝕜 := 𝕜) a P] with y hy
    rw [hy, kerF, polyFun]
    push_cast
    ring
  rw [e1, integral_ofReal]
  have e2 := integral_volI_scale ha (fun t => kR E c0 (x / a) t * pv P t)
  rw [e2, ← hU (x / a) ⟨div_nonneg hx.1 ha.le, (div_le_one ha).2 hx.2⟩, polyFun]
  push_cast
  ring

/-! ## D. Hilbert-Schmidt norm of a real continuous kernel. -/

theorem continuous_ofReal_comp {F : ℝ × ℝ → ℝ} (hF : Continuous F) :
    Continuous fun p => ((F p : ℝ) : 𝕜) := RCLike.continuous_ofReal.comp hF

theorem norm_sq_kernelOfContinuous_real {a : ℝ} {F : ℝ × ℝ → ℝ} (hF : Continuous F) :
    ‖kernelOfContinuous 0 a (fun p => ((F p : ℝ) : 𝕜)) (continuous_ofReal_comp hF)‖ ^ 2
      = ∫ p, F p ^ 2 ∂((volI 0 a).prod (volI 0 a)) := by
  rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), MeasureTheory.L2.inner_def]
  have : (fun p => ⟪(kernelOfContinuous 0 a (fun p => ((F p : ℝ) : 𝕜))
        (continuous_ofReal_comp hF) : ℝ × ℝ → 𝕜) p,
        (kernelOfContinuous 0 a (fun p => ((F p : ℝ) : 𝕜)) (continuous_ofReal_comp hF)
          : ℝ × ℝ → 𝕜) p⟫_𝕜) =ᵐ[(volI 0 a).prod (volI 0 a)] fun p => ((F p ^ 2 : ℝ) : 𝕜) := by
    filter_upwards [kernelOfContinuous_ae_eq (a := 0) (b := a) (continuous_ofReal_comp (𝕜 := 𝕜) hF)]
      with p hp
    rw [hp, RCLike.inner_apply', RCLike.conj_ofReal]
    push_cast
    ring
  rw [integral_congr_ae this, integral_ofReal, RCLike.ofReal_re]

/-! ## E. The one-sided tail kernel. -/

/-- `p̂(s, t) = Σ_{j<N} w_j Φ_j(s) U_j(t)`. -/
def tR (N : ℕ) (Phi U : ℕ → List ℚ) (w : ℕ → ℚ) (s t : ℝ) : ℝ :=
  ∑ j ∈ range N, (w j : ℝ) * (pv (Phi j) s * pv (U j) t)

theorem continuous_tR (N : ℕ) (Phi U : ℕ → List ℚ) (w : ℕ → ℚ) :
    Continuous (Function.uncurry (tR N Phi U w)) := by
  unfold tR
  exact continuous_finsetSum _ fun j _ => continuous_const.mul
    (((continuous_pv _).comp continuous_fst).mul ((continuous_pv _).comp continuous_snd))

def tailF (a : ℝ) (N : ℕ) (Phi U : ℕ → List ℚ) (w : ℕ → ℚ) (p : ℝ × ℝ) : 𝕜 :=
  ((tR N Phi U w (p.1 / a) (p.2 / a) : ℝ) : 𝕜)

theorem continuous_tailF (a : ℝ) (N : ℕ) (Phi U : ℕ → List ℚ) (w : ℕ → ℚ) :
    Continuous (tailF (𝕜 := 𝕜) a N Phi U w) :=
  RCLike.continuous_ofReal.comp ((continuous_tR N Phi U w).comp
    (by fun_prop : Continuous fun p : ℝ × ℝ => (p.1 / a, p.2 / a)))

def tailLp (a : ℝ) (N : ℕ) (Phi U : ℕ → List ℚ) (w : ℕ → ℚ) :
    Lp 𝕜 2 ((volI 0 a).prod (volI 0 a)) :=
  kernelOfContinuous 0 a (tailF a N Phi U w) (continuous_tailF a N Phi U w)

/-- The real double-integral value of `‖k - p‖²` (hat units). -/
def q2R (E : List ℚ) (c0 : ℚ) (N : ℕ) (Phi U : ℕ → List ℚ) (w : ℕ → ℚ) : ℝ :=
  (KKh E c0 : ℝ) - 2 * ∑ j ∈ range N, (w j : ℝ) * (mom (U j) (U j) : ℝ)
    + ∑ j ∈ range N, ∑ l ∈ range N, (w j : ℝ) * (w l : ℝ) * (mom (Phi j) (Phi l) : ℝ)
        * (mom (U j) (U l) : ℝ)

/-- **Exact Hilbert-Schmidt norm of the tail**: `‖k - p‖²_{L²([0,a]²)} = a² q2`. -/
theorem norm_sq_ker_sub_tail {a : ℝ} (ha : 0 < a) (E : List ℚ) (c0 : ℚ) (N : ℕ)
    (Phi U : ℕ → List ℚ) (w : ℕ → ℚ)
    (hU : ∀ j < N, ∀ s ∈ Icc (0 : ℝ) 1, pv (U j) s = ∫ t in (0 : ℝ)..1, kR E c0 s t * pv (Phi j) t) :
    ‖(kerLp a E c0 - tailLp a N Phi U w : Lp 𝕜 2 ((volI 0 a).prod (volI 0 a)))‖ ^ 2
      = a ^ 2 * q2R E c0 N Phi U w := by
  set F : ℝ × ℝ → ℝ := fun p => kR E c0 (p.1 / a) (p.2 / a) - tR N Phi U w (p.1 / a) (p.2 / a)
    with hFdef
  have hFc : Continuous F := ((continuous_kR E c0).comp
    (by fun_prop : Continuous fun p : ℝ × ℝ => (p.1 / a, p.2 / a))).sub ((continuous_tR N Phi U w).comp
    (by fun_prop : Continuous fun p : ℝ × ℝ => (p.1 / a, p.2 / a)))
  have hK : (kerLp a E c0 - tailLp a N Phi U w : Lp 𝕜 2 ((volI 0 a).prod (volI 0 a)))
      = kernelOfContinuous 0 a (fun p => ((F p : ℝ) : 𝕜)) (continuous_ofReal_comp hFc) := by
    rw [kerLp, tailLp, kernelOfContinuous_sub]
    congr 1
    funext p
    simp [kerF, tailF, hFdef]
  rw [hK, norm_sq_kernelOfContinuous_real hFc]
  -- expand (k - t)^2
  set μ2 := (volI 0 a).prod (volI 0 a)
  have hsc : Continuous fun p : ℝ × ℝ => (p.1 / a, p.2 / a) := by fun_prop
  have ck : Continuous fun p : ℝ × ℝ => kR E c0 (p.1 / a) (p.2 / a) := (continuous_kR E c0).comp hsc
  have cphi : ∀ j, Continuous fun p : ℝ × ℝ => pv (Phi j) (p.1 / a) :=
    fun j => (continuous_pv _).comp (continuous_fst.div_const a)
  have cU : ∀ j, Continuous fun p : ℝ × ℝ => pv (U j) (p.2 / a) :=
    fun j => (continuous_pv _).comp (continuous_snd.div_const a)
  have hexp : ∀ p : ℝ × ℝ, F p ^ 2 = kR E c0 (p.1 / a) (p.2 / a) ^ 2
      - 2 * ∑ j ∈ range N, (w j : ℝ) * (kR E c0 (p.1 / a) (p.2 / a) * pv (Phi j) (p.1 / a)
          * pv (U j) (p.2 / a))
      + ∑ j ∈ range N, ∑ l ∈ range N, ((w j : ℝ) * (w l : ℝ)) *
          ((pv (Phi j) (p.1 / a) * pv (Phi l) (p.1 / a)) * (pv (U j) (p.2 / a) * pv (U l) (p.2 / a))) := by
    intro p
    simp only [hFdef, tR]
    rw [sub_sq, sq (∑ j ∈ range N, _), Finset.sum_mul_sum, Finset.mul_sum]
    congr 1
    · congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    · exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  simp_rw [hexp]
  have i1 : Integrable (fun p : ℝ × ℝ => kR E c0 (p.1 / a) (p.2 / a) ^ 2) μ2 :=
    integrable_volI_prod (ck.pow 2)
  have i2 : ∀ j, Integrable (fun p : ℝ × ℝ => (w j : ℝ) * (kR E c0 (p.1 / a) (p.2 / a)
      * pv (Phi j) (p.1 / a) * pv (U j) (p.2 / a))) μ2 :=
    fun j => integrable_volI_prod (continuous_const.mul ((ck.mul (cphi j)).mul (cU j)))
  have i3 : ∀ j l, Integrable (fun p : ℝ × ℝ => ((w j : ℝ) * (w l : ℝ)) *
      ((pv (Phi j) (p.1 / a) * pv (Phi l) (p.1 / a)) * (pv (U j) (p.2 / a) * pv (U l) (p.2 / a)))) μ2 :=
    fun j l => integrable_volI_prod (continuous_const.mul (((cphi j).mul (cphi l)).mul
      ((cU j).mul (cU l))))
  rw [integral_add (f := fun p : ℝ × ℝ => kR E c0 (p.1 / a) (p.2 / a) ^ 2
        - 2 * ∑ j ∈ range N, (w j : ℝ) * (kR E c0 (p.1 / a) (p.2 / a) * pv (Phi j) (p.1 / a)
          * pv (U j) (p.2 / a)))
      (g := fun p : ℝ × ℝ => ∑ j ∈ range N, ∑ l ∈ range N, ((w j : ℝ) * (w l : ℝ)) *
          ((pv (Phi j) (p.1 / a) * pv (Phi l) (p.1 / a)) * (pv (U j) (p.2 / a) * pv (U l) (p.2 / a))))
      (i1.sub ((integrable_finsetSum _ fun j _ => i2 j).const_mul 2))
      (integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => i3 j l),
    integral_sub (f := fun p : ℝ × ℝ => kR E c0 (p.1 / a) (p.2 / a) ^ 2)
      (g := fun p : ℝ × ℝ => 2 * ∑ j ∈ range N, (w j : ℝ) * (kR E c0 (p.1 / a) (p.2 / a)
        * pv (Phi j) (p.1 / a) * pv (U j) (p.2 / a)))
      i1 ((integrable_finsetSum _ fun j _ => i2 j).const_mul 2),
    integral_const_mul, integral_finsetSum _ fun j _ => i2 j,
    integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => i3 j l]
  -- the three pieces
  have hk2 : ∫ p, kR E c0 (p.1 / a) (p.2 / a) ^ 2 ∂μ2 = a ^ 2 * (KKh E c0 : ℝ) := by
    have hc2 : Continuous (Function.uncurry fun s t => kR E c0 s t ^ 2) :=
      ((continuous_kR E c0).pow 2).congr fun p => rfl
    rw [integral_volI_prod_scale ha (fun s t => kR E c0 s t ^ 2) hc2]
    simp only [kR]
    rw [KKh_eq]
  have hkp : ∀ j < N, ∫ p, (w j : ℝ) * (kR E c0 (p.1 / a) (p.2 / a) * pv (Phi j) (p.1 / a)
      * pv (U j) (p.2 / a)) ∂μ2 = a ^ 2 * ((w j : ℝ) * (mom (U j) (U j) : ℝ)) := by
    intro j hj
    have cpr : Continuous fun p : ℝ × ℝ => kR E c0 (p.1 / a) (p.2 / a) * pv (Phi j) (p.1 / a)
        * pv (U j) (p.2 / a) := (ck.mul (cphi j)).mul (cU j)
    rw [integral_const_mul, integral_prod_symm _ (integrable_volI_prod cpr)]
    have hin' : ∀ᵐ y ∂(volI 0 a), ∫ x, kR E c0 (x / a) (y / a) * pv (Phi j) (x / a)
        * pv (U j) (y / a) ∂(volI 0 a) = a * (pv (U j) (y / a) * pv (U j) (y / a)) := by
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc (a := (0 : ℝ)) (b := a))]
        with y hy
      have hy' : y / a ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg hy.1 ha.le, (div_le_one ha).2 hy.2⟩
      rw [integral_mul_const]
      have := integral_volI_scale ha (fun s => kR E c0 s (y / a) * pv (Phi j) s)
      rw [this, hU j hj _ hy']
      have hsymm : ∫ t in (0 : ℝ)..1, kR E c0 t (y / a) * pv (Phi j) t
          = ∫ t in (0 : ℝ)..1, kR E c0 (y / a) t * pv (Phi j) t :=
        intervalIntegral.integral_congr fun t _ => by rw [kR_symm]
      rw [hsymm]
      ring
    rw [integral_congr_ae hin', integral_const_mul,
      integral_volI_scale ha (fun s => pv (U j) s * pv (U j) s), integral_pv_mul_pv]
    ring
  have hpp : ∀ j l, ∫ p, ((w j : ℝ) * (w l : ℝ)) * ((pv (Phi j) (p.1 / a) * pv (Phi l) (p.1 / a))
      * (pv (U j) (p.2 / a) * pv (U l) (p.2 / a))) ∂μ2
      = a ^ 2 * ((w j : ℝ) * (w l : ℝ) * (mom (Phi j) (Phi l) : ℝ) * (mom (U j) (U l) : ℝ)) := by
    intro j l
    rw [integral_const_mul, integral_prod_mul (fun x => pv (Phi j) (x / a) * pv (Phi l) (x / a))
      (fun y => pv (U j) (y / a) * pv (U l) (y / a)),
      integral_volI_scale ha (fun s => pv (Phi j) s * pv (Phi l) s),
      integral_volI_scale ha (fun s => pv (U j) s * pv (U l) s), integral_pv_mul_pv,
      integral_pv_mul_pv]
    ring
  rw [hk2, Finset.sum_congr rfl fun j hj => hkp j (Finset.mem_range.1 hj),
    Finset.sum_congr rfl fun j _ => integral_finsetSum _ fun l _ => i3 j l]
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => hpp j l]
  unfold q2R
  have e2 : ∑ j ∈ range N, a ^ 2 * ((w j : ℝ) * (mom (U j) (U j) : ℝ))
      = a ^ 2 * ∑ j ∈ range N, (w j : ℝ) * (mom (U j) (U j) : ℝ) := by rw [Finset.mul_sum]
  have e3 : ∑ j ∈ range N, ∑ l ∈ range N, a ^ 2 * ((w j : ℝ) * (w l : ℝ) * (mom (Phi j) (Phi l) : ℝ)
        * (mom (U j) (U l) : ℝ))
      = a ^ 2 * ∑ j ∈ range N, ∑ l ∈ range N, (w j : ℝ) * (w l : ℝ) * (mom (Phi j) (Phi l) : ℝ)
        * (mom (U j) (U l) : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
  rw [e2, e3]
  ring

/-- **The tail kernel is invisible to `Vᗮ`**: `⟪T_p r, r⟫ = 0` if `r ⊥ Φ_j (· / a)` for `j < N`. -/
theorem inner_tail_eq_zero {a : ℝ} (N : ℕ) (Phi U : ℕ → List ℚ) (w : ℕ → ℚ)
    (r : Lp 𝕜 2 (volI 0 a)) (hr : ∀ j < N, ⟪polyLp a (Phi j), r⟫_𝕜 = 0) :
    ⟪intOp (tailLp a N Phi U w) r, r⟫_𝕜 = 0 := by
  rw [← inner_conj_symm, inner_intOp_eq_integral]
  have hae : (fun p : ℝ × ℝ => conj (r p.1) * (tailLp (𝕜 := 𝕜) a N Phi U w : ℝ × ℝ → 𝕜) p * r p.2)
      =ᵐ[(volI 0 a).prod (volI 0 a)] fun p => ∑ j ∈ range N, ((w j : ℝ) : 𝕜) *
        ((conj (r p.1) * ((pv (Phi j) (p.1 / a) : ℝ) : 𝕜)) * (((pv (U j) (p.2 / a) : ℝ) : 𝕜) * r p.2)) := by
    filter_upwards [kernelOfContinuous_ae_eq (a := 0) (b := a) (continuous_tailF (𝕜 := 𝕜) a N Phi U w)]
      with p hp
    rw [tailLp, hp, tailF, tR]
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hint : ∀ j ∈ range N, Integrable (fun p : ℝ × ℝ => ((w j : ℝ) : 𝕜) *
      ((conj (r p.1) * ((pv (Phi j) (p.1 / a) : ℝ) : 𝕜)) * (((pv (U j) (p.2 / a) : ℝ) : 𝕜) * r p.2)))
      ((volI 0 a).prod (volI 0 a)) := by
    intro j _
    refine Integrable.const_mul ?_ _
    refine Integrable.mul_prod (f := fun x => conj (r x) * ((pv (Phi j) (x / a) : ℝ) : 𝕜))
      (g := fun y => ((pv (U j) (y / a) : ℝ) : 𝕜) * r y) ?_ ?_
    · exact (ArchS5.memLp_conj (Lp.memLp r)).integrable_mul (memLp_volI (continuous_polyFun a (Phi j)))
    · exact (memLp_volI (continuous_polyFun a (U j))).integrable_mul (Lp.memLp r)
  rw [integral_congr_ae hae, integral_finsetSum _ hint]
  rw [Finset.sum_eq_zero fun j hj => ?_]
  · simp
  rw [integral_const_mul, integral_prod_mul (fun x => conj (r x) * ((pv (Phi j) (x / a) : ℝ) : 𝕜))
    (fun y => ((pv (U j) (y / a) : ℝ) : 𝕜) * r y)]
  have h0 : ∫ x, conj (r x) * ((pv (Phi j) (x / a) : ℝ) : 𝕜) ∂(volI 0 a) = 0 := by
    have := hr j (Finset.mem_range.1 hj)
    rw [inner_polyLp_left] at this
    have e : ∫ x, conj (r x) * ((pv (Phi j) (x / a) : ℝ) : 𝕜) ∂(volI 0 a)
        = conj (∫ x, ((pv (Phi j) (x / a) : ℝ) : 𝕜) * r x ∂(volI 0 a)) := by
      rw [← integral_conj]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [map_mul, RCLike.conj_ofReal]
      ring
    rw [e, this, map_zero]
  rw [h0]
  simp

/-! ## F. The constant part of the kernel. -/

theorem re_inner_intOp_swap {a : ℝ} (K : Lp 𝕜 2 ((volI 0 a).prod (volI 0 a))) (f : Lp 𝕜 2 (volI 0 a)) :
    RCLike.re ⟪intOp K f, f⟫_𝕜 = RCLike.re ⟪f, intOp K f⟫_𝕜 := by
  rw [← inner_conj_symm, RCLike.conj_re]

theorem inner_one_eq_integral {a : ℝ} (f : Lp 𝕜 2 (volI 0 a)) :
    ⟪(polyLp a [1] : Lp 𝕜 2 (volI 0 a)), f⟫_𝕜 = ∫ x, f x ∂(volI 0 a) := by
  rw [inner_polyLp_left]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [pv_one]

/-- `re ⟪T_{E,c0} f, f⟫ = re ⟪T_{E,0} f, f⟫ + c0 ‖⟪1, f⟫‖²`. -/
theorem inner_kerLp_const {a : ℝ} (E : List ℚ) (c0 : ℚ) (f : Lp 𝕜 2 (volI 0 a)) :
    RCLike.re ⟪intOp (kerLp a E c0) f, f⟫_𝕜
      = RCLike.re ⟪intOp (kerLp a E 0) f, f⟫_𝕜
        + c0 * ‖⟪(polyLp a [1] : Lp 𝕜 2 (volI 0 a)), f⟫_𝕜‖ ^ 2 := by
  have hf1 : Integrable (fun x => f x) (volI 0 a) := (Lp.memLp f).integrable one_le_two
  have hfc : Integrable (fun x => conj (f x)) (volI 0 a) :=
    (ArchS5.memLp_conj (Lp.memLp f)).integrable one_le_two
  have hK : (kerLp (𝕜 := 𝕜) a E c0 : ℝ × ℝ → 𝕜) =ᵐ[(volI 0 a).prod (volI 0 a)]
      fun p => (kerLp (𝕜 := 𝕜) a E 0 : ℝ × ℝ → 𝕜) p + ((c0 : ℝ) : 𝕜) := by
    filter_upwards [kernelOfContinuous_ae_eq (a := 0) (b := a) (continuous_kerF (𝕜 := 𝕜) a E c0),
      kernelOfContinuous_ae_eq (a := 0) (b := a) (continuous_kerF (𝕜 := 𝕜) a E 0)] with p h1 h2
    rw [kerLp, kerLp, h1, h2, kerF, kerF, kR, kR]
    push_cast
    ring
  have hI : ∫ p, conj (f p.1) * (kerLp (𝕜 := 𝕜) a E c0 : ℝ × ℝ → 𝕜) p * f p.2
        ∂((volI 0 a).prod (volI 0 a))
      = (∫ p, conj (f p.1) * (kerLp (𝕜 := 𝕜) a E 0 : ℝ × ℝ → 𝕜) p * f p.2
          ∂((volI 0 a).prod (volI 0 a)))
        + ((c0 : ℝ) : 𝕜) * ((∫ x, conj (f x) ∂(volI 0 a)) * ∫ y, f y ∂(volI 0 a)) := by
    rw [← integral_prod_mul, ← integral_const_mul,
      ← integral_add (integrable_conj_mul_kernel_mul _ (Lp.memLp f) (Lp.memLp f))
        ((hfc.mul_prod hf1).const_mul _)]
    refine integral_congr_ae ?_
    filter_upwards [hK] with p hp
    rw [hp]
    ring
  rw [re_inner_intOp_swap, re_inner_intOp_swap (kerLp a E 0), inner_intOp_eq_integral,
    inner_intOp_eq_integral, hI, map_add, inner_one_eq_integral, integral_conj, RCLike.conj_mul,
    ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]

/-! ## G. Extension by zero from `[0, b]` to `[0, c]`. -/

section Ext

variable {b c : ℝ}

theorem volI_restrict_of_le (hbc : b ≤ c) : (volI 0 c).restrict (Icc 0 b) = volI 0 b := by
  rw [volI, Measure.restrict_restrict measurableSet_Icc,
    Set.inter_eq_left.2 (Set.Icc_subset_Icc_right hbc)]

theorem memLp_ext (hbc : b ≤ c) (f : Lp 𝕜 2 (volI 0 b)) :
    MemLp (Set.indicator (Icc 0 b) (f : ℝ → 𝕜)) 2 (volI 0 c) := by
  rw [memLp_indicator_iff_restrict measurableSet_Icc, volI_restrict_of_le hbc]
  exact Lp.memLp f

/-- Extension by zero `L²([0, b]) → L²([0, c])`. -/
def extL (hbc : b ≤ c) (f : Lp 𝕜 2 (volI 0 b)) : Lp 𝕜 2 (volI 0 c) := (memLp_ext hbc f).toLp _

theorem extL_ae (hbc : b ≤ c) (f : Lp 𝕜 2 (volI 0 b)) :
    (extL hbc f : ℝ → 𝕜) =ᵐ[volI 0 c] Set.indicator (Icc 0 b) (f : ℝ → 𝕜) := MemLp.coeFn_toLp _

theorem integral_extL (hbc : b ≤ c) (f : Lp 𝕜 2 (volI 0 b)) (g : ℝ → 𝕜) :
    ∫ x, g x * extL hbc f x ∂(volI 0 c) = ∫ x, g x * f x ∂(volI 0 b) := by
  have h1 : (fun x => g x * extL hbc f x) =ᵐ[volI 0 c]
      Set.indicator (Icc 0 b) (fun x => g x * f x) := by
    filter_upwards [extL_ae hbc f] with x hx
    rw [hx]
    by_cases hx' : x ∈ Icc 0 b <;> simp [hx']
  rw [integral_congr_ae h1, integral_indicator measurableSet_Icc, volI_restrict_of_le hbc]

theorem inner_extL (hbc : b ≤ c) (f g : Lp 𝕜 2 (volI 0 b)) :
    ⟪extL hbc f, extL hbc g⟫_𝕜 = ⟪f, g⟫_𝕜 := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have h1 : (fun x => ⟪(extL hbc f : ℝ → 𝕜) x, (extL hbc g : ℝ → 𝕜) x⟫_𝕜) =ᵐ[volI 0 c]
      Set.indicator (Icc 0 b) (fun x => ⟪(f : ℝ → 𝕜) x, (g : ℝ → 𝕜) x⟫_𝕜) := by
    filter_upwards [extL_ae hbc f, extL_ae hbc g] with x hx1 hx2
    rw [hx1, hx2]
    by_cases hx' : x ∈ Icc 0 b <;> simp [hx']
  rw [integral_congr_ae h1, integral_indicator measurableSet_Icc, volI_restrict_of_le hbc]

theorem norm_extL (hbc : b ≤ c) (f : Lp 𝕜 2 (volI 0 b)) : ‖extL hbc f‖ = ‖f‖ := by
  have h := inner_extL hbc f f
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖extL hbc f‖ ^ 2 = ‖f‖ ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

theorem inner_one_extL (hbc : b ≤ c) (f : Lp 𝕜 2 (volI 0 b)) :
    ⟪(polyLp c [1] : Lp 𝕜 2 (volI 0 c)), extL hbc f⟫_𝕜 = ⟪(polyLp b [1] : Lp 𝕜 2 (volI 0 b)), f⟫_𝕜 := by
  rw [inner_one_eq_integral, inner_one_eq_integral]
  have := integral_extL hbc f (fun _ => 1)
  simpa using this

/-- **Kernel forms are preserved by extension by zero.** -/
theorem inner_intOp_extL (hbc : b ≤ c) {k : ℝ × ℝ → 𝕜} (hk : Continuous k) (f : Lp 𝕜 2 (volI 0 b)) :
    ⟪extL hbc f, intOp (kernelOfContinuous 0 c k hk) (extL hbc f)⟫_𝕜
      = ⟪f, intOp (kernelOfContinuous 0 b k hk) f⟫_𝕜 := by
  rw [inner_intOp_eq_integral, inner_intOp_eq_integral]
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := volI 0 c) (ν := volI 0 c)).ae_eq_comp
    (extL_ae hbc f)
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := volI 0 c) (ν := volI 0 c)).ae_eq_comp
    (extL_ae hbc f)
  have hL : (fun p : ℝ × ℝ => conj ((extL hbc f : ℝ → 𝕜) p.1) *
      (kernelOfContinuous 0 c k hk : ℝ × ℝ → 𝕜) p * (extL hbc f : ℝ → 𝕜) p.2)
      =ᵐ[(volI 0 c).prod (volI 0 c)]
      Set.indicator (Icc 0 b ×ˢ Icc 0 b) (fun p => conj ((f : ℝ → 𝕜) p.1) * k p * (f : ℝ → 𝕜) p.2) := by
    filter_upwards [h1, h2, kernelOfContinuous_ae_eq (a := 0) (b := c) hk] with p hp1 hp2 hp3
    simp only [Function.comp_apply] at hp1 hp2
    rw [hp1, hp2, hp3]
    by_cases hx : p.1 ∈ Icc 0 b <;> by_cases hy : p.2 ∈ Icc 0 b <;>
      simp only [Set.indicator_apply, Set.mem_prod, hx, hy, and_self, and_false,
        and_true, if_true, if_false, map_zero, zero_mul, mul_zero]
  have hR : (fun p : ℝ × ℝ => conj ((f : ℝ → 𝕜) p.1) *
      (kernelOfContinuous 0 b k hk : ℝ × ℝ → 𝕜) p * (f : ℝ → 𝕜) p.2)
      =ᵐ[(volI 0 b).prod (volI 0 b)] fun p => conj ((f : ℝ → 𝕜) p.1) * k p * (f : ℝ → 𝕜) p.2 := by
    filter_upwards [kernelOfContinuous_ae_eq (a := 0) (b := b) hk] with p hp
    rw [hp]
  rw [integral_congr_ae hL, integral_congr_ae hR, integral_indicator
    (measurableSet_Icc.prod measurableSet_Icc), volI_prod, volI_prod,
    Measure.restrict_restrict (measurableSet_Icc.prod measurableSet_Icc),
    Set.inter_eq_left.2 (Set.prod_mono (Set.Icc_subset_Icc_right hbc)
      (Set.Icc_subset_Icc_right hbc))]

theorem re_inner_intOp_extL (hbc : b ≤ c) {k : ℝ × ℝ → 𝕜} (hk : Continuous k)
    (f : Lp 𝕜 2 (volI 0 b)) :
    RCLike.re ⟪intOp (kernelOfContinuous 0 c k hk) (extL hbc f), extL hbc f⟫_𝕜
      = RCLike.re ⟪intOp (kernelOfContinuous 0 b k hk) f, f⟫_𝕜 := by
  rw [re_inner_intOp_swap, re_inner_intOp_swap, inner_intOp_extL]

end Ext

end ArchS11
