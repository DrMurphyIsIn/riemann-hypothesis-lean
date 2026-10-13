/-
  M6gapP15ZeroFree -- lane m6gap, gap (3) of the M6 row (ROUTE_C_SYNTHESIS_2026-09-23 sections 5.2,
  7.2): Polymath15 condition (i) at `X ≤ 55/8`, hypothesis-free, on the dbn island, in both forms.

  Inputs (all proved, all on this island):
    * the 55/16 height floor on the right half, `M6gap.HeightFloor.zeta_ne_zero_low_right`
      (M6gapHeightFloor, the cross-pin port of `AND_height_floor_kernel`'s artifact);
    * `H_t(iy) ≠ 0` for real `t, y` (M6gapImAxis, from `Φ > 0`: the T = 0 / x = 0 case);
    * C2 `dbn_H0_eq_xi` (`H_0(z) = (1/8) ξ(1/2 + iz/2)`) and the C4 unpacking
      `DBN.riemannXi_eq_zero_iff_strip_zero` / coordinate lemmas `DBN.xiArg_re`, `DBN.xiArg_surj`;
    * the symmetries `H_neg` (DBNDefs) and `M6gap.H_conj` (M6gapImAxis).

  WHAT IS PROVED HERE (axioms [propext, Classical.choice, Quot.sound]; see AxiomGuardDBN):
    * `H0_ne_zero_of_abs_re_le`: `H_0` has NO zero with `|Re z| ≤ 55/8` (any `Im z`).  The four
      copies `z, conj z, -z, -conj z` of a zero reduce to `Re z ≥ 0 ≥ Im z`, where `s = 1/2 + iz/2`
      has `Re s ≥ 1/2`, `0 ≤ Im s = Re z / 2 ≤ 55/16`: `Im s = 0` is the imaginary axis of `H_0`
      (Φ > 0), `Im s > 0` is the height floor.
    * `zeta_strip_zero_abs_im_gt`: every zero of `ζ` with `0 < Re ρ < 1` has `|Im ρ| > 55/16`
      (real zeros included: the source island's `abs_im_gt_of_zero` assumes `Im ρ ≠ 0`).
    * `p15_prop33_i_of_le`: Polymath15 Prop 3.3(i) (H_0 form, p.15) at every `X ≤ 55/8`, for
      every `y0, t0`: no zero `H_0(x + iy) = 0` with `0 ≤ x ≤ X`, `√(y0² + 2t0) ≤ y ≤ 1`.
    * `p15_prop33_i_of_thm12_i`: the P15 p.16 bridge Thm 1.2(i) (zeta form) ⇒ Prop 3.3(i) (H_0
      form), for EVERY `X` and every `t0 ≥ 0`, via C2 + the C4 coordinate map (a zero `x + iy` of
      `H_0` gives, through `conj`, the zeta zero `(1+y)/2 + i x/2`).
    * Root-namespace, registry-shaped forms (after `end M6gap`):
      `m6gap_dbn_H0_zero_free_abs_re_le`, `m6gap_dbn_p15_prop33_i`,
      `m6gap_dbn_p15_prop33_i_of_thm12_i` (the zeta-form ones are in M6gapHeightFloor, the
      imaginary-axis ones in M6gapImAxis).

  What this is NOT: conditions (ii) and (iii) of P15 (the canopy at `t0` and the barrier), the
  criterion itself (M4), or any bound on Λ.  Condition (i) at `X = 55/8` is only the first of three
  inputs, and whether any `c0 < 1/2` is certifiable at this X is open (synthesis section 7.3).

  conjecture1_proved = False.  Nothing here bears on the Riemann Hypothesis.
-/
import M6gapHeightFloor
import M6gapImAxis

open Complex ComplexConjugate

namespace M6gap

open DBN

/-- Imaginary part of the C4 reindexing `z ↦ 1/2 + i z/2` (the companion of `DBN.xiArg_re`). -/
theorem xiArg_im (z : ℂ) : (1 / 2 + Complex.I * z / 2).im = z.re / 2 := by
  simp only [Complex.add_im, Complex.div_ofNat_im, Complex.I_mul_im, Complex.one_im]
  ring

/-- Real part of the inverse reindexing `s ↦ -2 i (s - 1/2)`. -/
theorem xiArgInv_re (s : ℂ) : (-2 * Complex.I * (s - 1 / 2)).re = 2 * s.im := by
  simp only [Complex.mul_im, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.neg_re,
    Complex.neg_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re, Complex.one_im]
  ring

/-- **The quarter-plane core**: no zero of `H_0` with `0 ≤ Re w ≤ 55/8` and `Im w ≤ 0`. -/
theorem H0_ne_zero_core {w : ℂ} (h1 : 0 ≤ w.re) (h2 : w.re ≤ 55 / 8) (h3 : w.im ≤ 0) :
    H 0 w ≠ 0 := by
  intro hw
  rcases h1.eq_or_lt with h0 | hpos
  · exact H_ne_zero_of_re_eq_zero 0 h0.symm hw
  have hxi := (H_zero_eq_zero_iff_of_H0_eq_xi dbn_H0_eq_xi w).mp hw
  obtain ⟨hζ, _, hlt⟩ := (riemannXi_eq_zero_iff_strip_zero _).mp hxi
  refine HeightFloor.zeta_ne_zero_low_right ?_ hlt ?_ ?_ hζ
  · rw [xiArg_re]; linarith
  · rw [xiArg_im]; linarith
  · rw [xiArg_im]; linarith

/-- **`H_0` has no zero with `|Re z| ≤ 55/8`.** -/
theorem H0_ne_zero_of_abs_re_le {z : ℂ} (hz : |z.re| ≤ 55 / 8) : H 0 z ≠ 0 := by
  intro h0
  set w : ℂ := ((|z.re| : ℝ) : ℂ) + ((-|z.im| : ℝ) : ℂ) * Complex.I with hw
  have hwre : w.re = |z.re| := by simp [hw]
  have hwim : w.im = -|z.im| := by simp [hw]
  have hwz : H 0 w = 0 := by
    rcases le_total 0 z.re with hx | hx <;> rcases le_total 0 z.im with hy | hy
    · have e : w = conj z := by
        apply Complex.ext
        · rw [hwre, Complex.conj_re, abs_of_nonneg hx]
        · rw [hwim, Complex.conj_im, abs_of_nonneg hy]
      rw [e, H_conj, h0, map_zero]
    · have e : w = z := by
        apply Complex.ext
        · rw [hwre, abs_of_nonneg hx]
        · rw [hwim, abs_of_nonpos hy, neg_neg]
      rw [e, h0]
    · have e : w = -z := by
        apply Complex.ext
        · rw [hwre, Complex.neg_re, abs_of_nonpos hx]
        · rw [hwim, Complex.neg_im, abs_of_nonneg hy]
      rw [e, H_neg, h0]
    · have e : w = -conj z := by
        apply Complex.ext
        · rw [hwre, Complex.neg_re, Complex.conj_re, abs_of_nonpos hx]
        · rw [hwim, Complex.neg_im, Complex.conj_im, abs_of_nonpos hy]
      rw [e, H_neg, H_conj, h0, map_zero]
  refine H0_ne_zero_core ?_ ?_ ?_ hwz
  · rw [hwre]; exact abs_nonneg _
  · rw [hwre]; exact hz
  · rw [hwim]; exact neg_nonpos.mpr (abs_nonneg _)

/-- **Every zero of `ζ` in the open critical strip has `|Im ρ| > 55/16`**, real zeros included,
by the C2 route (such a zero is the zero `-2i(ρ - 1/2)` of `H_0`, whose real part is `2 Im ρ`).
An independent cross-check of the C2-free `M6gap.HeightFloor.strip_zero_abs_im_gt`. -/
theorem zeta_strip_zero_abs_im_gt {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) : 55 / 16 < |ρ.im| := by
  by_contra hlt
  have hle : |ρ.im| ≤ 55 / 16 := not_lt.mp hlt
  have hxi : LiCriterion.riemannXi ρ = 0 :=
    (riemannXi_eq_zero_iff_strip_zero ρ).mpr ⟨hz, h0, h1⟩
  have hH : H 0 (-2 * Complex.I * (ρ - 1 / 2)) = 0 := by
    rw [H_zero_eq_zero_iff_of_H0_eq_xi dbn_H0_eq_xi, xiArg_surj]
    exact hxi
  refine H0_ne_zero_of_abs_re_le ?_ hH
  rw [xiArgInv_re, abs_mul, abs_two]
  linarith

/-- **Polymath15 Prop 3.3(i), H_0 form, at every `X ≤ 55/8`** (arXiv:1904.12438 p.15: "There are no
zeroes H_0(x + iy) = 0 with 0 ≤ x ≤ X and √(y0² + 2t0) ≤ y ≤ 1"), for every `y0` and `t0`. -/
theorem p15_prop33_i_of_le {X : ℝ} (hX : X ≤ 55 / 8) (y0 t0 : ℝ) :
    ∀ x y : ℝ, 0 ≤ x → x ≤ X → Real.sqrt (y0 ^ 2 + 2 * t0) ≤ y → y ≤ 1 →
      H 0 ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
  intro x y hx0 hxX _ _
  refine H0_ne_zero_of_abs_re_le ?_
  have hre : ((x : ℂ) + (y : ℂ) * Complex.I).re = x := by simp
  rw [hre, abs_of_nonneg hx0]
  linarith

/-- The zeta point of the conjugate of `x + iy`: `1/2 + i conj(x + iy)/2 = (1+y)/2 + i x/2`. -/
lemma xiArg_conj (x y : ℝ) :
    (1 / 2 + Complex.I * conj ((x : ℂ) + (y : ℂ) * Complex.I) / 2 : ℂ)
      = (((1 + y) / 2 : ℝ) : ℂ) + ((x / 2 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · rw [xiArg_re]
    simp
    ring
  · rw [xiArg_im]
    simp

/-- **The Polymath15 p.16 bridge: Thm 1.2(i) (zeta form) implies Prop 3.3(i) (H_0 form)**, for every
`X`, `y0` and every `t0 ≥ 0`, via C2 (`dbn_H0_eq_xi`) and the C4 coordinate map.  A zero `x + iy` of
`H_0` (`0 ≤ x ≤ X`, `√(y0² + 2t0) ≤ y ≤ 1`) gives through `conj` the zero `x - iy`, i.e. the zeta
zero `σ + iT` with `σ = (1+y)/2 ∈ [(1+y0)/2, 1]` and `T = x/2 ∈ [0, X/2]`. -/
theorem p15_prop33_i_of_thm12_i {X y0 t0 : ℝ} (ht0 : 0 ≤ t0)
    (hi : ∀ σ T : ℝ, (1 + y0) / 2 ≤ σ → σ ≤ 1 → 0 ≤ T → T ≤ X / 2 →
      riemannZeta ((σ : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    ∀ x y : ℝ, 0 ≤ x → x ≤ X → Real.sqrt (y0 ^ 2 + 2 * t0) ≤ y → y ≤ 1 →
      H 0 ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
  intro x y hx0 hxX hyl hy1 hH
  have hc : H 0 (conj ((x : ℂ) + (y : ℂ) * Complex.I)) = 0 := by
    rw [H_conj, hH, map_zero]
  have hxi := (H_zero_eq_zero_iff_of_H0_eq_xi dbn_H0_eq_xi _).mp hc
  obtain ⟨hζ, _, _⟩ := (riemannXi_eq_zero_iff_strip_zero _).mp hxi
  rw [xiArg_conj] at hζ
  have hyy0 : y0 ≤ y := by
    have h1 : y0 ≤ |y0| := le_abs_self y0
    have h2 : Real.sqrt (y0 ^ 2) = |y0| := Real.sqrt_sq_eq_abs y0
    have h3 : Real.sqrt (y0 ^ 2) ≤ Real.sqrt (y0 ^ 2 + 2 * t0) :=
      Real.sqrt_le_sqrt (by linarith)
    linarith
  exact hi ((1 + y) / 2) (x / 2) (by linarith) (by linarith) (by linarith) (by linarith) hζ

/-- The P15 p.16 composite at `X ≤ 55/8`: Prop 3.3(i) obtained FROM the zeta-form Thm 1.2(i)
(`M6gap.HeightFloor.p15_thm12_i_of_le`) through the bridge, for `y0 ≥ 0`, `t0 ≥ 0` (a second
derivation of `p15_prop33_i_of_le` on that range, exercising the bridge end to end). -/
theorem p15_prop33_i_of_le_via_bridge {X y0 t0 : ℝ} (hX : X ≤ 55 / 8) (hy0 : 0 ≤ y0)
    (ht0 : 0 ≤ t0) :
    ∀ x y : ℝ, 0 ≤ x → x ≤ X → Real.sqrt (y0 ^ 2 + 2 * t0) ≤ y → y ≤ 1 →
      H 0 ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0 :=
  p15_prop33_i_of_thm12_i ht0 (HeightFloor.p15_thm12_i_of_le hX hy0)

end M6gap

/-! ### Registry-shaped forms (root namespace; proposed nodes, NOT registered by this lane) -/

/-- `H_0` has no zero with `|Re z| ≤ 55/8`. -/
theorem m6gap_dbn_H0_zero_free_abs_re_le :
    ∀ z : ℂ, |z.re| ≤ 55 / 8 → DBN.H 0 z ≠ 0 :=
  fun _ hz ↦ M6gap.H0_ne_zero_of_abs_re_le hz

/-- Polymath15 Prop 3.3(i) (H_0 form) at every `X ≤ 55/8`, every `y0`, `t0`. -/
theorem m6gap_dbn_p15_prop33_i :
    ∀ X y0 t0 : ℝ, X ≤ 55 / 8 →
      ∀ x y : ℝ, 0 ≤ x → x ≤ X → Real.sqrt (y0 ^ 2 + 2 * t0) ≤ y → y ≤ 1 →
        DBN.H 0 ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0 :=
  fun _ y0 t0 hX ↦ M6gap.p15_prop33_i_of_le hX y0 t0

/-- The Polymath15 p.16 bridge Thm 1.2(i) ⇒ Prop 3.3(i), every `X`, `y0`, `t0 ≥ 0`. -/
theorem m6gap_dbn_p15_prop33_i_of_thm12_i :
    ∀ X y0 t0 : ℝ, 0 ≤ t0 →
      (∀ σ T : ℝ, (1 + y0) / 2 ≤ σ → σ ≤ 1 → 0 ≤ T → T ≤ X / 2 →
        riemannZeta ((σ : ℂ) + (T : ℂ) * Complex.I) ≠ 0) →
      ∀ x y : ℝ, 0 ≤ x → x ≤ X → Real.sqrt (y0 ^ 2 + 2 * t0) ≤ y → y ≤ 1 →
        DBN.H 0 ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0 :=
  fun _ _ _ ht0 hi ↦ M6gap.p15_prop33_i_of_thm12_i ht0 hi
