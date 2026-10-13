/-
  PFConverseD -- pole-free Weil converse, part D (2026-10-13): the trivial converse of
  `rh_of_rr_windows`, so that "RH iff RR-square windows exist" is literally kernel-checked.

  * `collapse_bounded`: every negative semidefinite form B on V satisfies the bounded RR-square
    axioms with Div = V, f = 0, h0 = 0 and h1 = -B(X, X)/2.  This is the collapse lemma of
    weil_form_enclosure/lean/RRSquare.lean in its simplest form: with Div = V the axioms ask for
    nothing beyond the Hodge-index conclusion.
  * `lineWindow`: for one test g with Re weilForm (autocorr g) >= 0, the one-dimensional window
    V = R, tau v = v * g, B(x, y) = -Re weilForm (autocorr g) * x * y, carried by `collapse_bounded`.
  * `rr_windows_of_rh`: RH gives a family of such windows covering every pole-free Weil test.
  * `rh_iff_exists_rr_windows`: RiemannHypothesis iff such a covering family exists.

  THIS DIRECTION IS TRIVIAL, AND THAT IS THE POINT.  The windows built here are read off from Weil
  positivity itself (RH -> Weil positivity is E6Bridge5), and they carry no geometry: no sections
  (h0 = 0), no effective divisors, no ample class (f = 0).  An existence statement
  "there exist RR-square windows covering the pole-free tests" is therefore just Weil's criterion
  in another notation, which is exactly what the collapse lemma predicts.  The open content of
  Conjecture RR-square is a CONSTRUCTION of windows whose divisors, sections and degree are defined
  without reference to the zeros (so that the RR axioms are checked independently of positivity),
  never the existence of some window.  Nothing here is progress on RH.  conjecture1_proved = False.
-/
import PFConverseC

open Zeta23 Complex MeasureTheory

noncomputable section

namespace RvMBridgePF
open WeilExplicit

/-! ## A. Real scaling of the Weil quadratic form. -/

/-- The autocorrelation is quadratic under real scaling. -/
lemma autocorr_real_mul (r : ℝ) (g : ℝ → ℂ) :
    autocorr (fun x => (r : ℂ) * g x) = fun u => ((r ^ 2 : ℝ) : ℂ) * autocorr g u := by
  funext u
  unfold autocorr
  rw [← integral_const_mul]
  congr 1
  funext v
  simp only [map_mul, Complex.conj_ofReal]
  push_cast
  ring

lemma weilKernel_const_mul (k : ℂ) (f : ℝ → ℂ) (s : ℂ) :
    weilKernel (fun u => k * f u) s = k * weilKernel f s := by
  unfold weilKernel
  rw [← integral_const_mul]
  congr 1
  funext u
  ring

/-- The Weil functional is homogeneous (no integrability needed: both sides use the
unconditional `integral_const_mul` and `tsum_mul_left`). -/
lemma weilForm_const_mul (k : ℂ) (f : ℝ → ℂ) :
    weilForm (fun u => k * f u) = k * weilForm f := by
  have h1 : (∫ r : ℝ, archIntegrand (fun u => k * f u) r) = k * ∫ r : ℝ, archIntegrand f r := by
    rw [← integral_const_mul]
    congr 1
    funext r
    unfold archIntegrand
    rw [weilKernel_const_mul]
    ring
  have h2 : primeSide (fun u => k * f u) = k * primeSide f := by
    unfold primeSide
    rw [← tsum_mul_left]
    congr 1
    funext n
    ring
  unfold weilForm archSide
  rw [h1, h2, weilKernel_const_mul, weilKernel_const_mul]
  ring

lemma re_weilForm_autocorr_real_mul (r : ℝ) (g : ℝ → ℂ) :
    (weilForm (autocorr (fun x => (r : ℂ) * g x))).re = r ^ 2 * (weilForm (autocorr g)).re := by
  rw [autocorr_real_mul, weilForm_const_mul, Complex.re_ofReal_mul]

/-! ## B. The collapse model. -/

namespace RRSquare

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Collapse.**  A negative semidefinite form satisfies the bounded RR-square axioms with
Div = V, f = 0, no sections and h1 = -B(X, X)/2.  The model is empty of geometry: it only
restates B <= 0. -/
def collapse_bounded (B : LinearMap.BilinForm ℝ V) (hB : ∀ v, B v v ≤ 0) :
    RRAxiomsBounded B 0 LinearMap.id where
  deg := 0
  deg_ι v := by simp
  Prin := ⊥
  deg_prin _ _ := rfl
  Eff _ := True
  h0 _ := 0
  h1 X := -(1 / 2) * B X X
  h0_nonneg _ := le_rfl
  h1_nonneg X := by have := hB X; linarith
  K := 0
  a _ := 0
  χ := 0
  rr v n := by
    simp only [LinearMap.id_apply, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
    ring
  eff _ h := absurd h (lt_irrefl 0)
  compat v hv := by
    have : v = 0 := by simpa using hv
    simp [this]
  β _ := 0
  bound _ := le_rfl

end RRSquare

/-! ## C. One window per test, and the converse. -/

open RRSquare in
/-- The one-dimensional window through a test g with Re weilForm (autocorr g) >= 0:
V = Div = R, tau v = v * g, B(x, y) = -w x y with w = Re weilForm (autocorr g), c = 1, f = 0. -/
def lineWindow (g : ℝ → ℂ) (hw : 0 ≤ (weilForm (autocorr g)).re) : RRWindow where
  V := ℝ
  Div := ℝ
  B := (-(weilForm (autocorr g)).re) • LinearMap.mul ℝ ℝ
  f := 0
  ι := LinearMap.id
  ax := Sum.inl (collapse_bounded _ fun v => by
    simp only [LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
    nlinarith [mul_self_nonneg v])
  τ v := fun x => (v : ℂ) * g x
  c := 1
  hc := one_pos
  hdiag v := by
    simp only [LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
    rw [re_weilForm_autocorr_real_mul]
    ring
  hpole _ _ := by simp

/-- **RH gives RR-square windows covering every pole-free test** (the trivial direction). -/
theorem rr_windows_of_rh (hRH : RiemannHypothesis) :
    ∃ (ι' : Type) (W : ι' → RRWindow), ∀ g : ℝ → ℂ, IsWeilTest g → PoleFree g →
      ∃ i : ι', ∃ v : (W i).V, (W i).τ v = g := by
  refine ⟨{ g : ℝ → ℂ // IsWeilTest g },
    fun g => lineWindow g.1 (RvMBridge5.rh_implies_weil_positivity hRH g.1 g.2), ?_⟩
  intro g hg _
  refine ⟨⟨g, hg⟩, (1 : ℝ), ?_⟩
  funext x
  show ((1 : ℝ) : ℂ) * g x = g x
  simp

/-- **RH iff RR-square windows covering the pole-free tests exist.**  The forward direction is
`rr_windows_of_rh` (trivial, via the collapse model); the reverse is `rh_of_rr_windows`.  The
equivalence shows that the existence form is circular: the content is the construction. -/
theorem rh_iff_exists_rr_windows :
    RiemannHypothesis ↔ ∃ (ι' : Type) (W : ι' → RRWindow), ∀ g : ℝ → ℂ, IsWeilTest g →
      PoleFree g → ∃ i : ι', ∃ v : (W i).V, (W i).τ v = g :=
  ⟨rr_windows_of_rh, fun ⟨_, W, h⟩ => rh_of_rr_windows W h⟩

end RvMBridgePF
