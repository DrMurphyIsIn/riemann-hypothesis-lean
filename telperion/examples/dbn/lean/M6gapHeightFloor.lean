/-
  M6gapHeightFloor -- lane m6gap, gap (2) of the M6 row (ROUTE_C_SYNTHESIS_2026-09-23 section 5.2):
  the 55/16 height floor of registry node `AND_height_floor_kernel` REBUILT on the dbn island
  (Lean v4.34.0-rc1), plus its extension to the real segment and the zeta form of Polymath15
  Thm 1.2(i) at `X ≤ 55/8`.  C2-free and Φ-free: the import closure is Mathlib plus the ten ported
  Mathlib-only modules M6gapEMZeta .. M6gapHeightFloorBoxes, M6gapZetaZeroConfinement,
  M6gapDlvpZetaSymmetry (no DBN module).

  Source: `telperion/examples/zeta_reflection/lean/HeightFloor.lean` (Lean v4.32.0).  The four
  bricks it rests on (`HeightFloorCheck`, `HeightFloorTrig`, `HeightFloorEM`, `HeightFloorBoxes`)
  and their Euler-Maclaurin closure (`EMZeta`, `EMZetaComplex`, `EMZetaTail`, `ZetaEMSum`) compile
  on this island with NO proof edits (only module names and an `M6gap.` namespace prefix).  The
  source's two other imports are ported as their Mathlib-only parts: `DlvpZetaSymmetry` whole
  (M6gapDlvpZetaSymmetry) and the four Mathlib-only theorems of `ZetaZeroConfinement`
  (M6gapZetaZeroConfinement); the source's transitive closure through the dVP zero-free region
  (~70 zero_free_bridge modules, used only by `ZetaZeroConfinement.zero_in_band`) is not needed.

  WHAT IS PROVED HERE (axioms [propext, Classical.choice, Quot.sound]; see AxiomGuardDBN):
    * the source theorems VERBATIM (statements and proofs): `zeta_ne_zero_low_right` (no zero with
      `1/2 ≤ Re s < 1`, `0 < Im s ≤ 55/16`), `strip_clear_low`, `height_floor H` (the registry
      statement of `AND_height_floor_kernel`, for every `H`), `height_floor_280000`,
      `im_gt_of_zero`, `abs_im_gt_of_zero`;
    * `G2_norm_le_of_zero_of_im_nonneg`, `zeta_ne_zero_low_right_of_im_nonneg` -- the same with
      `0 ≤ Im s`: the source uses `0 < Im s` only to exclude `s ∈ {0, 1, -1, -2}`, which
      `1/2 ≤ Re s < 1` already excludes, and the 32-box cover of HeightFloorBoxes already includes
      `t = 0`.  So the real segment `[1/2, 1)` is zero-free by the SAME certificate (an
      Euler-Maclaurin route to the T = 0 case, independent of the Φ > 0 route of M6gapImAxis);
    * `zeta_ne_zero_of_half_le_of_im_le` -- no zero with `1/2 ≤ Re s` and `0 ≤ Im s ≤ 55/16`
      (`Re s ≥ 1` from Mathlib's `riemannZeta_ne_zero_of_one_le_re`);
    * `strip_clear_low_of_im_nonneg`, `strip_zero_abs_im_gt` -- every zero of `ζ` with
      `0 < Re ρ < 1` has `|Im ρ| > 55/16`, REAL ZEROS INCLUDED (the source's `abs_im_gt_of_zero`
      assumes `Im ρ ≠ 0`); left half by the width fold `ρ ↦ 1 - conj ρ`, lower half by `conj`;
    * `p15_thm12_i_of_le` -- Polymath15 Thm 1.2(i) in its zeta form, for every `X ≤ 55/8` and every
      `y0 ≥ 0`: no zero `ζ(σ + iT) = 0` with `(1+y0)/2 ≤ σ ≤ 1` and `0 ≤ T ≤ X/2`;
    * root-namespace, registry-shaped forms (after `end M6gap.HeightFloor`): `m6gap_height_floor`
      (the `AND_height_floor_kernel` statement), `m6gap_dbn_zeta_zero_free_low`,
      `m6gap_dbn_p15_thm12_i`.

  conjecture1_proved = False.  A finite zero-free rectangle at low height (the first zero is at
  height ≈ 14.13); nothing here bears on the Riemann Hypothesis or on the de Bruijn-Newman constant.
-/
import M6gapHeightFloorBoxes
import M6gapZetaZeroConfinement
import M6gapDlvpZetaSymmetry

open Complex

namespace M6gap.HeightFloor

/-- **No zero on the right half of the low rectangle** (source `HeightFloor.zeta_ne_zero_low_right`,
statement and proof verbatim). -/
theorem zeta_ne_zero_low_right {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re < 1) (h3 : 0 < s.im)
    (h4 : s.im ≤ 55 / 16) : riemannZeta s ≠ 0 := by
  intro hz
  have hle := G2_norm_le_of_zero h1 h2 h3 h4 hz
  have hgt := Boxes.G2_norm_gt s.re s.im h1 h2.le h3.le h4
  rw [Complex.re_add_im s] at hgt
  linarith

/-- **The low strip is zero-free**: no zero with `0 < Re ρ < 1`, `0 < Im ρ ≤ 55/16`.  This is the
    `hclear_low` input of `ZetaZeroConfinement.no_low_zeros_of_strip_clear`.  (Source
    `HeightFloor.strip_clear_low`, statement and proof verbatim.) -/
theorem strip_clear_low : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
    0 < ρ.im → ρ.im ≤ 55 / 16 → False := by
  intro ρ hz h0 h1 him hT
  by_cases hh : 1 / 2 ≤ ρ.re
  · exact zeta_ne_zero_low_right hh h1 him hT hz
  · have hz' := ZeroFreeBridge.riemannZeta_reflect_line_eq_zero h0 h1 hz
    have hre : (1 - (starRingEnd ℂ) ρ).re = 1 - ρ.re := by simp
    have him' : (1 - (starRingEnd ℂ) ρ).im = ρ.im := by simp
    exact zeta_ne_zero_low_right (by rw [hre]; linarith) (by rw [hre]; linarith)
      (by rw [him']; exact him) (by rw [him']; exact hT) hz'

/-- **THE HEIGHT FLOOR, at every height `H`** (the capstone's `hγ`, hypothesis-free; source
    `HeightFloor.height_floor`, the registry statement of `AND_height_floor_kernel`, verbatim). -/
theorem height_floor (H : ℝ) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ H → 55 / 16 ≤ |ρ.im| :=
  ZetaZeroConfinement.no_low_zeros_of_strip_clear H strip_clear_low

/-- **The `hγ` binder of `AllZeros_h280000_Indexed.all_nontrivial_zeros_up_to_height_280000`,
    verbatim, discharged.** (Source `HeightFloor.height_floor_280000`.) -/
theorem height_floor_280000 :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 280000 → 55 / 16 ≤ |ρ.im| :=
  height_floor 280000

/-- Height-free form: a zero with positive ordinate has ordinate `> 55/16`. (Source
    `HeightFloor.im_gt_of_zero`.) -/
theorem im_gt_of_zero {ρ : ℂ} (hz : riemannZeta ρ = 0) (him : 0 < ρ.im) : 55 / 16 < ρ.im := by
  by_contra h
  obtain ⟨h0, h1⟩ := ZetaZeroConfinement.zeta_zero_re_mem_strip (ne_of_gt him) hz
  exact strip_clear_low ρ hz h0 h1 him (le_of_not_gt h)

/-- Both half-planes: every non-real zero has `|Im ρ| > 55/16` (conjugate symmetry). (Source
    `HeightFloor.abs_im_gt_of_zero`.) -/
theorem abs_im_gt_of_zero {ρ : ℂ} (hz : riemannZeta ρ = 0) (him : ρ.im ≠ 0) :
    55 / 16 < |ρ.im| := by
  rcases lt_or_gt_of_ne him with hneg | hpos
  · have hc : riemannZeta ((starRingEnd ℂ) ρ) = 0 := by
      rw [riemannZeta_conj, hz, map_zero]
    have hcim : ((starRingEnd ℂ) ρ).im = -ρ.im := by simp
    have := im_gt_of_zero hc (by rw [hcim]; linarith)
    rw [hcim] at this
    rw [abs_of_neg hneg]; exact this
  · rw [abs_of_pos hpos]; exact im_gt_of_zero hz hpos

/-- **The Euler-Maclaurin reduction with `0 ≤ Im s`**: a zero of `ζ` with `1/2 ≤ Re s < 1`,
`0 ≤ Im s ≤ 55/16` forces `‖G2 s‖ ≤ 23/100`.  (The source's `G2_norm_le_of_zero` assumes
`0 < Im s`, used only to exclude `s ∈ {0, 1, -1, -2}`; here `1/2 ≤ Re s < 1` excludes them.) -/
theorem G2_norm_le_of_zero_of_im_nonneg {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re < 1)
    (h3 : 0 ≤ s.im) (h4 : s.im ≤ 55 / 16) (hz : riemannZeta s = 0) : ‖G2 s‖ ≤ 23 / 100 := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at h1
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at h2
  have hsm1 : s ≠ -1 := by rintro rfl; norm_num at h1
  have hsm2 : s ≠ -2 := by rintro rfl; norm_num at h1
  have henc := ZetaReflection.em_zeta_strip3_enclosure (s := s) (by linarith) hs1 (N := 2)
    (by norm_num) hsm1 hsm2
  rw [hz, zero_sub, norm_neg] at henc
  rw [← G2_eq hs0 hs1 h2, norm_mul]
  calc ‖s - 1‖ * ‖ZetaReflection.emZetaFinite3 s 2‖
      ≤ ‖s - 1‖ * ((1 / 12) * ‖s * (s + 1) * (s + 2)‖ * ((2 : ℕ) : ℝ) ^ (-(s.re + 3 - 1))
          / (s.re + 3 - 1) / 6) := by
        gcongr
    _ ≤ 23 / 100 := tail_le h1 h2.le h3 h4

/-- **No zero on the closed-bottom right half**: `1/2 ≤ Re s < 1`, `0 ≤ Im s ≤ 55/16`.  At
`Im s = 0` this is `ζ(σ) ≠ 0` for real `σ ∈ [1/2, 1)`, by the same 32-box certificate. -/
theorem zeta_ne_zero_low_right_of_im_nonneg {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re < 1)
    (h3 : 0 ≤ s.im) (h4 : s.im ≤ 55 / 16) : riemannZeta s ≠ 0 := by
  intro hz
  have hle := G2_norm_le_of_zero_of_im_nonneg h1 h2 h3 h4 hz
  have hgt := Boxes.G2_norm_gt s.re s.im h1 h2.le h3 h4
  rw [Complex.re_add_im s] at hgt
  linarith

/-- The real segment `[1/2, 1)` is zero-free (Euler-Maclaurin route). -/
theorem riemannZeta_ofReal_ne_zero_of_mem_Ico {σ : ℝ} (h1 : 1 / 2 ≤ σ) (h2 : σ < 1) :
    riemannZeta (σ : ℂ) ≠ 0 :=
  zeta_ne_zero_low_right_of_im_nonneg (by simpa using h1) (by simpa using h2) (by simp)
    (by norm_num)

/-- **No zero with `1/2 ≤ Re s` and `0 ≤ Im s ≤ 55/16`** (`Re s ≥ 1`: Mathlib's
`riemannZeta_ne_zero_of_one_le_re`, which includes Mathlib's value at the pole `s = 1`). -/
theorem zeta_ne_zero_of_half_le_of_im_le {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h3 : 0 ≤ s.im)
    (h4 : s.im ≤ 55 / 16) : riemannZeta s ≠ 0 := by
  rcases lt_or_ge s.re 1 with h2 | h2
  · exact zeta_ne_zero_low_right_of_im_nonneg h1 h2 h3 h4
  · exact riemannZeta_ne_zero_of_one_le_re h2

/-- **The low strip is zero-free, real segment included**: no zero with `0 < Re ρ < 1` and
`0 ≤ Im ρ ≤ 55/16` (the source's `strip_clear_low` with `0 ≤ Im ρ`; same width fold). -/
theorem strip_clear_low_of_im_nonneg : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
    0 ≤ ρ.im → ρ.im ≤ 55 / 16 → False := by
  intro ρ hz h0 h1 him hT
  by_cases hh : 1 / 2 ≤ ρ.re
  · exact zeta_ne_zero_low_right_of_im_nonneg hh h1 him hT hz
  · have hz' := ZeroFreeBridge.riemannZeta_reflect_line_eq_zero h0 h1 hz
    have hre : (1 - (starRingEnd ℂ) ρ).re = 1 - ρ.re := by simp
    have him' : (1 - (starRingEnd ℂ) ρ).im = ρ.im := by simp
    exact zeta_ne_zero_low_right_of_im_nonneg (by rw [hre]; linarith) (by rw [hre]; linarith)
      (by rw [him']; exact him) (by rw [him']; exact hT) hz'

/-- **Every zero of `ζ` in the open critical strip has `|Im ρ| > 55/16`, real zeros included**
(C2-free; lower half by `conj`). -/
theorem strip_zero_abs_im_gt {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    55 / 16 < |ρ.im| := by
  by_contra hlt
  have hle : |ρ.im| ≤ 55 / 16 := not_lt.mp hlt
  rcases le_total 0 ρ.im with him | him
  · rw [abs_of_nonneg him] at hle
    exact strip_clear_low_of_im_nonneg ρ hz h0 h1 him hle
  · rw [abs_of_nonpos him] at hle
    have hc := ZeroFreeBridge.riemannZeta_conj_eq_zero hz
    refine strip_clear_low_of_im_nonneg _ hc ?_ ?_ ?_ ?_
    · rw [Complex.conj_re]; exact h0
    · rw [Complex.conj_re]; exact h1
    · rw [Complex.conj_im]; linarith
    · rw [Complex.conj_im]; linarith

/-- **Polymath15 Thm 1.2(i), zeta form, at every `X ≤ 55/8`** (arXiv:1904.12438 p.2: "There are no
zeroes ζ(σ + iT) = 0 with (1+y0)/2 ≤ σ ≤ 1 and 0 ≤ T ≤ X/2"), for every `y0 ≥ 0` (P15 assumes
`0 < y0 ≤ 1` and `X > 0`; only `y0 ≥ 0` is used here, i.e. `σ ≥ 1/2`). -/
theorem p15_thm12_i_of_le {X y0 : ℝ} (hX : X ≤ 55 / 8) (hy0 : 0 ≤ y0) :
    ∀ σ T : ℝ, (1 + y0) / 2 ≤ σ → σ ≤ 1 → 0 ≤ T → T ≤ X / 2 →
      riemannZeta ((σ : ℂ) + (T : ℂ) * I) ≠ 0 := by
  intro σ T hσ _ hT0 hTX
  refine zeta_ne_zero_of_half_le_of_im_le ?_ ?_ ?_
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
    linarith
  · simpa using hT0
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, mul_zero, Complex.I_im, mul_one, zero_add]
    linarith

end M6gap.HeightFloor

/-! ### Registry-shaped forms (root namespace; proposed nodes, NOT registered by this lane) -/

/-- The `AND_height_floor_kernel` registry statement, on the dbn island (cross-pin port). -/
theorem m6gap_height_floor (H : ℝ) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ H → 55 / 16 ≤ |ρ.im| :=
  M6gap.HeightFloor.height_floor H

/-- No zero of `ζ` in the open critical strip with `|Im ρ| ≤ 55/16`, real zeros included
(C2-free). -/
theorem m6gap_dbn_zeta_zero_free_low :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 55 / 16 < |ρ.im| :=
  fun _ hz h0 h1 ↦ M6gap.HeightFloor.strip_zero_abs_im_gt hz h0 h1

/-- Polymath15 Thm 1.2(i) (zeta form) at every `X ≤ 55/8`, every `y0 ≥ 0` (C2-free). -/
theorem m6gap_dbn_p15_thm12_i :
    ∀ X y0 : ℝ, X ≤ 55 / 8 → 0 ≤ y0 →
      ∀ σ T : ℝ, (1 + y0) / 2 ≤ σ → σ ≤ 1 → 0 ≤ T → T ≤ X / 2 →
        riemannZeta ((σ : ℂ) + (T : ℂ) * Complex.I) ≠ 0 :=
  fun _ _ hX hy0 ↦ M6gap.HeightFloor.p15_thm12_i_of_le hX hy0
