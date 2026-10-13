/-
  Hodge1_ArchSectors -- the four-piece parity decomposition of archW and of the strip energy on the
  two-condition pole-free class (2026-10-12, Phase 1b-A).

  conjecture1_proved = False.  No zeros, no primes.

  A complex test g splits as g = e + o (even/odd parts) and e = vEr + i vEi, o = vOr + i vOi with four
  REAL pieces of definite parity.  PROVED HERE:
    * archW g = archW vEr + archW vEi + archW vOr + archW vOi  (`archW_decomp`): with
      C v (r) = int v cos(r u), S v (r) = int v sin(r u), the transform of g is
      (C vEr - S vOi) + i (C vEi + S vOr) (the other C, S vanish by parity), so |g^|^2 is the sum of the
      four |v^|^2 plus the cross term 2 (C vEi S vOr - C vEr S vOi), which is ODD in r; Psi is even, so
      the cross term integrates to zero against Psi;
    * |g(x)|^2 + |g(-x)|^2 = 2 (vEr^2 + vEi^2 + vOr^2 + vOi^2)(x) (parallelogram), hence the mass and the
      symmetric strip energy SformC a b g = int_a^b |g(x)|^2 + |g(-x)|^2 split over the four pieces;
    * on PoleFree2 (int g e^{-u/2} = int g e^{u/2} = 0) every piece has vanishing pole functional:
      int vEr cosh(u/2) = int vEi cosh(u/2) = 0 and int vOr sinh(u/2) = int vOi sinh(u/2) = 0;
    * `archW_ge_of_sectors`: real even/odd sector inequalities  lam int v^2 + w Sform v v <= archW v  on the
      pieces with Pl v = 0 give  lam int |g|^2 + w SformC s0 l g <= archW g  for every PoleFree2 g;
    * `stripSet_le_SformC`: for L <= l and s0 <= log 2 - l (0 < s0), int_{stripSet L} |g|^2 <= SformC s0 l g.
  No `sorry`.
-/
import Hodge1_ArchSplit
import Hodge1_Reduction
import ZhuParity

open Real MeasureTheory Set Complex

noncomputable section

namespace Hodge1
open WeilExplicit RvMBridgeZhu Zeta23
open KWin (Pl poleF integral_odd_eq_zero paperFT_ofReal_line)

/-! ## A. The four real pieces. -/

def vEr (g : ℝ → ℂ) (x : ℝ) : ℝ := (evenPart g x).re
def vEi (g : ℝ → ℂ) (x : ℝ) : ℝ := (evenPart g x).im
def vOr (g : ℝ → ℂ) (x : ℝ) : ℝ := (oddPart g x).re
def vOi (g : ℝ → ℂ) (x : ℝ) : ℝ := (oddPart g x).im

lemma vEr_neg (g : ℝ → ℂ) (x : ℝ) : vEr g (-x) = vEr g x := by unfold vEr; rw [evenPart_neg]
lemma vEi_neg (g : ℝ → ℂ) (x : ℝ) : vEi g (-x) = vEi g x := by unfold vEi; rw [evenPart_neg]
lemma vOr_neg (g : ℝ → ℂ) (x : ℝ) : vOr g (-x) = -vOr g x := by
  unfold vOr; rw [oddPart_neg, Complex.neg_re]
lemma vOi_neg (g : ℝ → ℂ) (x : ℝ) : vOi g (-x) = -vOi g x := by
  unfold vOi; rw [oddPart_neg, Complex.neg_im]

lemma isWeilTest_vEr {g : ℝ → ℂ} (hg : IsWeilTest g) : IsWeilTest (fun u => (vEr g u : ℂ)) :=
  isWeilTest_re (isWeilTest_evenPart hg)
lemma isWeilTest_vEi {g : ℝ → ℂ} (hg : IsWeilTest g) : IsWeilTest (fun u => (vEi g u : ℂ)) :=
  isWeilTest_im (isWeilTest_evenPart hg)
lemma isWeilTest_vOr {g : ℝ → ℂ} (hg : IsWeilTest g) : IsWeilTest (fun u => (vOr g u : ℂ)) :=
  isWeilTest_re (isWeilTest_oddPart hg)
lemma isWeilTest_vOi {g : ℝ → ℂ} (hg : IsWeilTest g) : IsWeilTest (fun u => (vOi g u : ℂ)) :=
  isWeilTest_im (isWeilTest_oddPart hg)

lemma tsupport_re_subset {f : ℝ → ℂ} {L : ℝ} (hs : tsupport f ⊆ Icc (-L) L) :
    tsupport (fun u => ((f u).re : ℂ)) ⊆ Icc (-L) L :=
  (tsupport_comp_subset (g := fun z : ℂ => ((z.re : ℝ) : ℂ)) (by simp) f).trans hs

lemma tsupport_im_subset {f : ℝ → ℂ} {L : ℝ} (hs : tsupport f ⊆ Icc (-L) L) :
    tsupport (fun u => ((f u).im : ℂ)) ⊆ Icc (-L) L :=
  (tsupport_comp_subset (g := fun z : ℂ => ((z.im : ℝ) : ℂ)) (by simp) f).trans hs

lemma g_decomp (g : ℝ → ℂ) (x : ℝ) :
    g x = ((vEr g x : ℂ) + (vEi g x : ℂ) * I) + ((vOr g x : ℂ) + (vOi g x : ℂ) * I) := by
  unfold vEr vEi vOr vOi
  rw [Complex.re_add_im, Complex.re_add_im]
  have := congrFun (evenPart_add_oddPart g) x
  simp only [Pi.add_apply] at this
  exact this.symm

/-- The parallelogram identity on the four pieces. -/
lemma norm_sq_sym (g : ℝ → ℂ) (x : ℝ) :
    ‖g x‖ ^ 2 + ‖g (-x)‖ ^ 2 = 2 * (vEr g x ^ 2 + vEi g x ^ 2 + vOr g x ^ 2 + vOi g x ^ 2) := by
  rw [g_decomp g x, g_decomp g (-x), vEr_neg, vEi_neg, vOr_neg, vOi_neg]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.ofReal_neg,
    Complex.neg_re, Complex.neg_im]
  ring

/-! ## B. The mass and the strip energy. -/

/-- The symmetric strip energy of a complex test. -/
def SformC (a b : ℝ) (g : ℝ → ℂ) : ℝ := ∫ x in a..b, (‖g x‖ ^ 2 + ‖g (-x)‖ ^ 2)

lemma SformC_decomp {g : ℝ → ℂ} (hg : IsWeilTest g) (a b : ℝ) :
    SformC a b g = Sform a b (vEr g) (vEr g) + Sform a b (vEi g) (vEi g)
      + Sform a b (vOr g) (vOr g) + Sform a b (vOi g) (vOi g) := by
  have cE := KWin.continuous_v (isWeilTest_vEr hg)
  have cI := KWin.continuous_v (isWeilTest_vEi hg)
  have cO := KWin.continuous_v (isWeilTest_vOr hg)
  have cJ := KWin.continuous_v (isWeilTest_vOi hg)
  unfold SformC Sform
  rw [← intervalIntegral.integral_add (Sform_integrable cE cE a b) (Sform_integrable cI cI a b),
    ← intervalIntegral.integral_add ((Sform_integrable cE cE a b).add (Sform_integrable cI cI a b))
      (Sform_integrable cO cO a b),
    ← intervalIntegral.integral_add (((Sform_integrable cE cE a b).add (Sform_integrable cI cI a b)).add
      (Sform_integrable cO cO a b)) (Sform_integrable cJ cJ a b)]
  congr 1
  funext x
  rw [norm_sq_sym, vEr_neg, vEi_neg, vOr_neg, vOi_neg]
  ring

lemma mass_decomp {g : ℝ → ℂ} (hg : IsWeilTest g) :
    ∫ x, ‖g x‖ ^ 2 = (∫ x, vEr g x ^ 2) + (∫ x, vEi g x ^ 2) + (∫ x, vOr g x ^ 2) + ∫ x, vOi g x ^ 2 := by
  have hint : ∀ {v : ℝ → ℝ}, IsWeilTest (fun u => (v u : ℂ)) → Integrable (fun x => v x ^ 2) := by
    intro v hv
    have := integrable_norm_sq hv
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h1 := hint (isWeilTest_vEr hg)
  have h2 := hint (isWeilTest_vEi hg)
  have h3 := hint (isWeilTest_vOr hg)
  have h4 := hint (isWeilTest_vOi hg)
  have hsym : ∫ x, ‖g x‖ ^ 2 = (1 / 2 : ℝ) * ∫ x, (‖g x‖ ^ 2 + ‖g (-x)‖ ^ 2) := by
    rw [integral_add (integrable_norm_sq hg) (integrable_norm_sq (isWeilTest_comp_neg hg)),
      integral_neg_eq_self (fun x => ‖g x‖ ^ 2)]
    ring
  rw [hsym]
  have e : (fun x => ‖g x‖ ^ 2 + ‖g (-x)‖ ^ 2)
      = fun x => 2 * (((vEr g x ^ 2 + vEi g x ^ 2) + vOr g x ^ 2) + vOi g x ^ 2) := by
    funext x; rw [norm_sq_sym]
  have h12 : Integrable (fun x => vEr g x ^ 2 + vEi g x ^ 2) := h1.add h2
  have h123 : Integrable (fun x => vEr g x ^ 2 + vEi g x ^ 2 + vOr g x ^ 2) := h12.add h3
  rw [e, integral_const_mul, integral_add h123 h4, integral_add h12 h3, integral_add h1 h2]
  ring

/-! ## C. The transform. -/

def Cf (v : ℝ → ℝ) (r : ℝ) : ℝ := ∫ u, v u * Real.cos (r * u)
def Sf (v : ℝ → ℝ) (r : ℝ) : ℝ := ∫ u, v u * Real.sin (r * u)

lemma Cf_neg (v : ℝ → ℝ) (r : ℝ) : Cf v (-r) = Cf v r := by
  unfold Cf; congr 1; funext u; rw [neg_mul, Real.cos_neg]

lemma Sf_neg (v : ℝ → ℝ) (r : ℝ) : Sf v (-r) = -Sf v r := by
  unfold Sf; rw [← integral_neg]; congr 1; funext u; rw [neg_mul, Real.sin_neg]; ring

lemma Sf_even {v : ℝ → ℝ} (hev : ∀ u, v (-u) = v u) (r : ℝ) : Sf v r = 0 :=
  integral_odd_eq_zero fun u => by rw [hev, mul_neg, Real.sin_neg]; ring

lemma Cf_odd {v : ℝ → ℝ} (hodd : ∀ u, v (-u) = -v u) (r : ℝ) : Cf v r = 0 :=
  integral_odd_eq_zero fun u => by rw [hodd, mul_neg, Real.cos_neg]; ring

lemma hsq_ofReal {v : ℝ → ℝ} (hf : IsWeilTest (fun u => (v u : ℂ))) (r : ℝ) :
    RvMBridge31.hsq (fun u => (v u : ℂ)) r = Cf v r ^ 2 + Sf v r ^ 2 := by
  unfold RvMBridge31.hsq
  rw [paperFT_ofReal_line hf, Complex.sq_norm, Complex.normSq_add_mul_I]
  rfl

lemma integrable_ofReal_mul_exp {v : ℝ → ℝ} (hf : IsWeilTest (fun u => (v u : ℂ))) (r : ℝ) :
    Integrable (fun u => (v u : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))) :=
  (hf.1.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hf.2.mul_right

lemma paperFT_decomp {g : ℝ → ℂ} (hg : IsWeilTest g) (r : ℝ) :
    paperFT g r = ((Cf (vEr g) r - Sf (vEi g) r + Cf (vOr g) r - Sf (vOi g) r : ℝ) : ℂ)
      + ((Sf (vEr g) r + Cf (vEi g) r + Sf (vOr g) r + Cf (vOi g) r : ℝ) : ℂ) * I := by
  have i1 := integrable_ofReal_mul_exp (isWeilTest_vEr hg) r
  have i2 := (integrable_ofReal_mul_exp (isWeilTest_vEi hg) r).const_mul I
  have i3 := integrable_ofReal_mul_exp (isWeilTest_vOr hg) r
  have i4 := (integrable_ofReal_mul_exp (isWeilTest_vOi hg) r).const_mul I
  have hsplit : paperFT g r = paperFT (fun u => (vEr g u : ℂ)) r + I * paperFT (fun u => (vEi g u : ℂ)) r
      + paperFT (fun u => (vOr g u : ℂ)) r + I * paperFT (fun u => (vOi g u : ℂ)) r := by
    unfold paperFT
    have i12 : Integrable (fun u => (vEr g u : ℂ) * Complex.exp (I * (r : ℂ) * (u : ℂ))
        + I * ((vEi g u : ℂ) * Complex.exp (I * (r : ℂ) * (u : ℂ)))) := i1.add i2
    have i123 : Integrable (fun u => (vEr g u : ℂ) * Complex.exp (I * (r : ℂ) * (u : ℂ))
        + I * ((vEi g u : ℂ) * Complex.exp (I * (r : ℂ) * (u : ℂ)))
        + (vOr g u : ℂ) * Complex.exp (I * (r : ℂ) * (u : ℂ))) := i12.add i3
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add i1 i2, ← integral_add i12 i3,
      ← integral_add i123 i4]
    congr 1
    funext u
    rw [g_decomp g u]
    ring
  rw [hsplit, paperFT_ofReal_line (isWeilTest_vEr hg), paperFT_ofReal_line (isWeilTest_vEi hg),
    paperFT_ofReal_line (isWeilTest_vOr hg), paperFT_ofReal_line (isWeilTest_vOi hg)]
  unfold Cf Sf
  push_cast
  linear_combination (((∫ u, vEi g u * Real.sin (r * u) : ℝ) : ℂ)
    + ((∫ u, vOi g u * Real.sin (r * u) : ℝ) : ℂ)) * I_sq

/-! ## D. archW splits over the four pieces. -/

theorem archW_decomp {g : ℝ → ℂ} (hg : IsWeilTest g) :
    ArchS3.archW g = ArchS3.archW (fun u => (vEr g u : ℂ)) + ArchS3.archW (fun u => (vEi g u : ℂ))
      + ArchS3.archW (fun u => (vOr g u : ℂ)) + ArchS3.archW (fun u => (vOi g u : ℂ)) := by
  set W : ℝ → ℝ := fun r => RvMBridge11.psiR r - Real.log Real.pi with hW
  have hWe : ∀ r, W (-r) = W r := fun r => by rw [hW]; simp only; rw [RvMBridge30.psiR_neg]
  have hiW : ∀ {f : ℝ → ℂ}, IsWeilTest f → Integrable (fun r => RvMBridge31.hsq f r * W r) := by
    intro f hf
    have h1 := RvMBridge31.integrable_hsq_mul_psiR hf
    have h2 := (RvMBridge31.integrable_hsq hf).mul_const (Real.log Real.pi)
    refine (h1.sub h2).congr (Filter.Eventually.of_forall fun r => ?_)
    simp only [Pi.sub_apply, hW]
    ring
  have hE := isWeilTest_vEr hg
  have hI := isWeilTest_vEi hg
  have hO := isWeilTest_vOr hg
  have hJ := isWeilTest_vOi hg
  -- parity zeros
  have sE : ∀ r, Sf (vEr g) r = 0 := Sf_even (vEr_neg g)
  have sI : ∀ r, Sf (vEi g) r = 0 := Sf_even (vEi_neg g)
  have cO : ∀ r, Cf (vOr g) r = 0 := Cf_odd (vOr_neg g)
  have cJ : ∀ r, Cf (vOi g) r = 0 := Cf_odd (vOi_neg g)
  set cross : ℝ → ℝ := fun r => 2 * (Cf (vEi g) r * Sf (vOr g) r - Cf (vEr g) r * Sf (vOi g) r)
    with hcross
  have hpt : ∀ r, RvMBridge31.hsq g r * W r
      = (RvMBridge31.hsq (fun u => (vEr g u : ℂ)) r * W r + RvMBridge31.hsq (fun u => (vEi g u : ℂ)) r * W r
        + RvMBridge31.hsq (fun u => (vOr g u : ℂ)) r * W r + RvMBridge31.hsq (fun u => (vOi g u : ℂ)) r * W r)
        + cross r * W r := by
    intro r
    have h0 : RvMBridge31.hsq g r = ‖paperFT g r‖ ^ 2 := rfl
    rw [h0, paperFT_decomp hg r, Complex.sq_norm, Complex.normSq_add_mul_I, hsq_ofReal hE,
      hsq_ofReal hI, hsq_ofReal hO, hsq_ofReal hJ, sE, sI, cO, cJ, hcross]
    ring
  have hs2 : Integrable (fun r => RvMBridge31.hsq (fun u => (vEr g u : ℂ)) r * W r
      + RvMBridge31.hsq (fun u => (vEi g u : ℂ)) r * W r) := (hiW hE).add (hiW hI)
  have hs3 : Integrable (fun r => RvMBridge31.hsq (fun u => (vEr g u : ℂ)) r * W r
      + RvMBridge31.hsq (fun u => (vEi g u : ℂ)) r * W r
      + RvMBridge31.hsq (fun u => (vOr g u : ℂ)) r * W r) := hs2.add (hiW hO)
  have hsum : Integrable (fun r => RvMBridge31.hsq (fun u => (vEr g u : ℂ)) r * W r
      + RvMBridge31.hsq (fun u => (vEi g u : ℂ)) r * W r
      + RvMBridge31.hsq (fun u => (vOr g u : ℂ)) r * W r
      + RvMBridge31.hsq (fun u => (vOi g u : ℂ)) r * W r) := hs3.add (hiW hJ)
  have hcrossi : Integrable fun r => cross r * W r := by
    refine ((hiW hg).sub hsum).congr (Filter.Eventually.of_forall fun r => ?_)
    simp only [Pi.sub_apply]
    rw [hpt r]
    ring
  have hodd : ∀ r, cross (-r) * W (-r) = -(cross r * W r) := by
    intro r
    rw [hWe, hcross]
    simp only
    rw [Cf_neg, Cf_neg, Sf_neg, Sf_neg]
    ring
  have hzero : ∫ r, cross r * W r = 0 := integral_odd_eq_zero hodd
  have hmain : ∫ r, RvMBridge31.hsq g r * W r
      = (∫ r, RvMBridge31.hsq (fun u => (vEr g u : ℂ)) r * W r)
        + (∫ r, RvMBridge31.hsq (fun u => (vEi g u : ℂ)) r * W r)
        + (∫ r, RvMBridge31.hsq (fun u => (vOr g u : ℂ)) r * W r)
        + ∫ r, RvMBridge31.hsq (fun u => (vOi g u : ℂ)) r * W r := by
    rw [show (fun r => RvMBridge31.hsq g r * W r) = _ from funext hpt, integral_add hsum hcrossi, hzero,
      add_zero, integral_add hs3 (hiW hJ), integral_add hs2 (hiW hO), integral_add (hiW hE) (hiW hI)]
  unfold ArchS3.archW
  rw [show (fun r => RvMBridge31.hsq g r * (RvMBridge11.psiR r - Real.log Real.pi))
      = fun r => RvMBridge31.hsq g r * W r from rfl, hmain]
  ring

/-! ## E. The pole conditions descend to the pieces. -/

lemma integrable_mul_cont {f : ℝ → ℂ} (hf : IsWeilTest f) {w : ℝ → ℂ} (hw : Continuous w) :
    Integrable fun u => f u * w u :=
  (hf.1.continuous.mul hw).integrable_of_hasCompactSupport hf.2.mul_right

lemma cexp_half (u : ℝ) : ((Real.exp (u / 2) : ℝ) : ℂ) = Complex.exp ((u : ℂ) / 2) := by
  push_cast; rfl

lemma cexp_neg_half (u : ℝ) : ((Real.exp (-(u / 2)) : ℝ) : ℂ) = Complex.exp (-(u : ℂ) / 2) := by
  push_cast; congr 1; ring

/-- On PoleFree2: `int g cosh(u/2) = 0` and `int g sinh(u/2) = 0`. -/
lemma poleFree2_cosh_sinh {g : ℝ → ℂ} (hg : IsWeilTest g) (hP : PoleFree2 g) :
    (∫ u, g u * ((Real.cosh (u / 2) : ℝ) : ℂ)) = 0 ∧ (∫ u, g u * ((Real.sinh (u / 2) : ℝ) : ℂ)) = 0 := by
  have h0 := hP.1
  have h1 := hP.2
  rw [paperFT_I_half] at h0
  rw [paperFT_neg_I_half] at h1
  have ip := integrable_mul_cont hg (w := fun u : ℝ => Complex.exp ((u : ℂ) / 2)) (by fun_prop)
  have im := integrable_mul_cont hg (w := fun u : ℝ => Complex.exp (-(u : ℂ) / 2)) (by fun_prop)
  constructor
  · have e : (fun u => g u * ((Real.cosh (u / 2) : ℝ) : ℂ))
        = fun u => (1 / 2 : ℂ) * (g u * Complex.exp ((u : ℂ) / 2) + g u * Complex.exp (-(u : ℂ) / 2)) := by
      funext u
      rw [Real.cosh_eq]
      push_cast
      rw [show -((u : ℂ) / 2) = -(u : ℂ) / 2 by ring]
      ring
    rw [e, integral_const_mul, integral_add ip im, h0, h1]
    simp
  · have e : (fun u => g u * ((Real.sinh (u / 2) : ℝ) : ℂ))
        = fun u => (1 / 2 : ℂ) * (g u * Complex.exp ((u : ℂ) / 2) - g u * Complex.exp (-(u : ℂ) / 2)) := by
      funext u
      rw [Real.sinh_eq]
      push_cast
      rw [show -((u : ℂ) / 2) = -(u : ℂ) / 2 by ring]
      ring
    rw [e, integral_const_mul, integral_sub ip im, h0, h1]
    simp

/-- The integral of the real or imaginary part of `f * (real weight)`. -/
lemma integral_re_mul {f : ℝ → ℂ} (hf : IsWeilTest f) {w : ℝ → ℝ} (hw : Continuous w) :
    ∫ u, (f u).re * w u = (∫ u, f u * ((w u : ℝ) : ℂ)).re := by
  have hi := integrable_mul_cont hf (w := fun u => ((w u : ℝ) : ℂ)) (by fun_prop)
  have h := integral_re hi
  simp only [RCLike.re_to_complex] at h
  rw [← h]
  congr 1; funext u
  simp

lemma integral_im_mul {f : ℝ → ℂ} (hf : IsWeilTest f) {w : ℝ → ℝ} (hw : Continuous w) :
    ∫ u, (f u).im * w u = (∫ u, f u * ((w u : ℝ) : ℂ)).im := by
  have hi := integrable_mul_cont hf (w := fun u => ((w u : ℝ) : ℂ)) (by fun_prop)
  have h := integral_im hi
  simp only [RCLike.im_to_complex] at h
  rw [← h]
  congr 1; funext u
  simp

theorem poleFree2_pieces {g : ℝ → ℂ} (hg : IsWeilTest g) (hP : PoleFree2 g) :
    (∫ u, vEr g u * Real.cosh (u / 2)) = 0 ∧ (∫ u, vEi g u * Real.cosh (u / 2)) = 0
      ∧ (∫ u, vOr g u * Real.sinh (u / 2)) = 0 ∧ (∫ u, vOi g u * Real.sinh (u / 2)) = 0 := by
  obtain ⟨hc, hs⟩ := poleFree2_cosh_sinh hg hP
  have hE := isWeilTest_evenPart hg
  have hO := isWeilTest_oddPart hg
  have ccosh : Continuous fun u : ℝ => Real.cosh (u / 2) := by fun_prop
  have csinh : Continuous fun u : ℝ => Real.sinh (u / 2) := by fun_prop
  have iEc := integrable_mul_cont hE (w := fun u => ((Real.cosh (u / 2) : ℝ) : ℂ)) (by fun_prop)
  have iOc := integrable_mul_cont hO (w := fun u => ((Real.cosh (u / 2) : ℝ) : ℂ)) (by fun_prop)
  have iEs := integrable_mul_cont hE (w := fun u => ((Real.sinh (u / 2) : ℝ) : ℂ)) (by fun_prop)
  have iOs := integrable_mul_cont hO (w := fun u => ((Real.sinh (u / 2) : ℝ) : ℂ)) (by fun_prop)
  -- the odd part integrates to zero against cosh, the even part against sinh
  have zOc : ∫ u, oddPart g u * ((Real.cosh (u / 2) : ℝ) : ℂ) = 0 :=
    integral_eq_zero_of_odd fun u => by
      rw [oddPart_neg, show -u / 2 = -(u / 2) by ring, Real.cosh_neg]; ring
  have zEs : ∫ u, evenPart g u * ((Real.sinh (u / 2) : ℝ) : ℂ) = 0 :=
    integral_eq_zero_of_odd fun u => by
      rw [evenPart_neg, show -u / 2 = -(u / 2) by ring, Real.sinh_neg]; push_cast; ring
  have hgs : ∀ w : ℝ → ℝ, (fun u => g u * ((w u : ℝ) : ℂ))
      = fun u => evenPart g u * ((w u : ℝ) : ℂ) + oddPart g u * ((w u : ℝ) : ℂ) := by
    intro w; funext u
    have := congrFun (evenPart_add_oddPart g) u
    simp only [Pi.add_apply] at this
    rw [← this]; ring
  have Ec : ∫ u, evenPart g u * ((Real.cosh (u / 2) : ℝ) : ℂ) = 0 := by
    have := hc
    rw [hgs (fun u => Real.cosh (u / 2)), integral_add iEc iOc, zOc, add_zero] at this
    exact this
  have Os : ∫ u, oddPart g u * ((Real.sinh (u / 2) : ℝ) : ℂ) = 0 := by
    have := hs
    rw [hgs (fun u => Real.sinh (u / 2)), integral_add iEs iOs, zEs, zero_add] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold vEr; rw [integral_re_mul hE ccosh, Ec, Complex.zero_re]
  · unfold vEi; rw [integral_im_mul hE ccosh, Ec, Complex.zero_im]
  · unfold vOr; rw [integral_re_mul hO csinh, Os, Complex.zero_re]
  · unfold vOi; rw [integral_im_mul hO csinh, Os, Complex.zero_im]

/-! ## F. Assembly. -/

/-- The pole functional on `[-l, l]` of a piece supported in `[-l, l]` is its integral over ℝ. -/
lemma Pl_eq_integral {v : ℝ → ℝ} (hf : IsWeilTest (fun u => (v u : ℂ))) {l : ℝ} (hl : 0 < l)
    (hs : tsupport (fun u => (v u : ℂ)) ⊆ Icc (-l) l) (par : ℕ) :
    Pl l par v = ∫ u, v u * poleF par u :=
  (KWin2.integral_eq_interval' hf hl le_rfl hs _).symm

/-- **The sector assembly**: real even/odd sector inequalities on the pole-free pieces give the
complex inequality on PoleFree2. -/
theorem archW_ge_of_sectors {l s0 w lam : ℝ} (hl : 0 < l)
    (hE : ∀ v : ℝ → ℝ, IsWeilTest (fun u => (v u : ℂ)) → (∀ u, v (-u) = v u) →
      tsupport (fun u => (v u : ℂ)) ⊆ Icc (-l) l → Pl l 0 v = 0 →
      lam * (∫ x, v x ^ 2) + w * Sform s0 l v v ≤ ArchS3.archW (fun u => (v u : ℂ)))
    (hO : ∀ v : ℝ → ℝ, IsWeilTest (fun u => (v u : ℂ)) → (∀ u, v (-u) = -v u) →
      tsupport (fun u => (v u : ℂ)) ⊆ Icc (-l) l → Pl l 1 v = 0 →
      lam * (∫ x, v x ^ 2) + w * Sform s0 l v v ≤ ArchS3.archW (fun u => (v u : ℂ)))
    {g : ℝ → ℂ} (hg : IsWeilTest g) (hP : PoleFree2 g) (hsupp : tsupport g ⊆ Icc (-l) l) :
    lam * (∫ x, ‖g x‖ ^ 2) + w * SformC s0 l g ≤ ArchS3.archW g := by
  obtain ⟨pE, pI, pO, pJ⟩ := poleFree2_pieces hg hP
  have sE : tsupport (fun u => (vEr g u : ℂ)) ⊆ Icc (-l) l :=
    tsupport_re_subset (tsupport_evenPart_subset hsupp)
  have sI : tsupport (fun u => (vEi g u : ℂ)) ⊆ Icc (-l) l :=
    tsupport_im_subset (tsupport_evenPart_subset hsupp)
  have sO : tsupport (fun u => (vOr g u : ℂ)) ⊆ Icc (-l) l :=
    tsupport_re_subset (tsupport_oddPart_subset hsupp)
  have sJ : tsupport (fun u => (vOi g u : ℂ)) ⊆ Icc (-l) l :=
    tsupport_im_subset (tsupport_oddPart_subset hsupp)
  have hpE : ∀ u, poleF 0 u = Real.cosh (u / 2) := fun u => by simp [poleF]
  have hpO : ∀ u, poleF 1 u = Real.sinh (u / 2) := fun u => by simp [poleF]
  have e1 := hE (vEr g) (isWeilTest_vEr hg) (vEr_neg g) sE (by
    rw [Pl_eq_integral (isWeilTest_vEr hg) hl sE]; simp_rw [hpE]; exact pE)
  have e2 := hE (vEi g) (isWeilTest_vEi hg) (vEi_neg g) sI (by
    rw [Pl_eq_integral (isWeilTest_vEi hg) hl sI]; simp_rw [hpE]; exact pI)
  have e3 := hO (vOr g) (isWeilTest_vOr hg) (vOr_neg g) sO (by
    rw [Pl_eq_integral (isWeilTest_vOr hg) hl sO]; simp_rw [hpO]; exact pO)
  have e4 := hO (vOi g) (isWeilTest_vOi hg) (vOi_neg g) sJ (by
    rw [Pl_eq_integral (isWeilTest_vOi hg) hl sJ]; simp_rw [hpO]; exact pJ)
  rw [archW_decomp hg, mass_decomp hg, SformC_decomp hg]
  linarith

/-! ## G. The strip set inside the symmetric strip block. -/

theorem stripSet_le_SformC {g : ℝ → ℂ} (hg : IsWeilTest g) {L l s0 : ℝ} (hLl : L ≤ l) (hs0 : 0 < s0)
    (hsl : s0 ≤ Real.log 2 - l) (hs0l : s0 ≤ l) :
    ∫ u in stripSet L, ‖g u‖ ^ 2 ≤ SformC s0 l g := by
  have hI := integrable_norm_sq hg
  have hsub : stripSet L ⊆ Icc (-l) (-s0) ∪ Icc s0 l := by
    intro x hx
    rcases hx with hx | hx
    · left; rw [mem_Icc] at hx ⊢; constructor <;> linarith [hx.1, hx.2]
    · right; rw [mem_Icc] at hx ⊢; constructor <;> linarith [hx.1, hx.2]
  have hdisj : Disjoint (Icc (-l) (-s0)) (Icc s0 l) := by
    refine Set.disjoint_left.mpr fun x hx hy => ?_
    rw [mem_Icc] at hx hy
    linarith [hx.2, hy.1]
  have hmono : ∫ u in stripSet L, ‖g u‖ ^ 2 ≤ ∫ u in Icc (-l) (-s0) ∪ Icc s0 l, ‖g u‖ ^ 2 :=
    setIntegral_mono_set hI.integrableOn (Filter.Eventually.of_forall fun x => by positivity)
      (Filter.Eventually.of_forall hsub)
  rw [setIntegral_union hdisj measurableSet_Icc hI.integrableOn hI.integrableOn] at hmono
  have hle : -l ≤ -s0 := by linarith
  have hle' : s0 ≤ l := hs0l
  have hc : Continuous fun u => ‖g u‖ ^ 2 := by have := hg.1.continuous; fun_prop
  have h1 : ∫ u in Icc (-l) (-s0), ‖g u‖ ^ 2 = ∫ x in s0..l, ‖g (-x)‖ ^ 2 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
      intervalIntegral.integral_comp_neg (fun x => ‖g x‖ ^ 2)]
  have h2 : ∫ u in Icc s0 l, ‖g u‖ ^ 2 = ∫ x in s0..l, ‖g x‖ ^ 2 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle']
  rw [h1, h2] at hmono
  unfold SformC
  have hn : IntervalIntegrable (fun x => ‖g (-x)‖ ^ 2) volume s0 l :=
    (hc.comp continuous_neg).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hc.intervalIntegrable _ _) hn]
  linarith

end Hodge1

end
