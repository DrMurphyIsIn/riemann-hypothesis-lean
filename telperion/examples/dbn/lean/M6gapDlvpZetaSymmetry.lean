/- PHASE 4 (dVP frontier / RH-in-a-box, piece 3 — functional-equation symmetry): halve the work.

   M6GAP PORT (lane m6gap, 2026-09-23): a copy of telperion/examples/li_positivity/lean/
   DlvpZetaSymmetry.lean (identical to zero_free_bridge/lean/DlvpZetaSymmetry.lean; li_positivity is
   on this island's pin, Lean v4.34.0-rc1 / Mathlib de5ce8a9).  The ONLY edit is the namespace
   prefix `M6gap.` (no clash with a sibling lane's copy).  Mathlib-only.  Consumed by
   M6gapHeightFloor (the width fold rho -> 1 - conj rho of the 55/16 height floor).


   For the "all nontrivial zeros up to height `T` lie on the critical line" certificate, the
   functional equation `ζ(1-s) = 2·(2π)^{-s}·Γ(s)·cos(πs/2)·ζ(s)` (`riemannZeta_one_sub`) reflects
   zeros across `Re = 1/2`: if `ζ ρ = 0` then `ζ (1-ρ) = 0`, and `1-ρ` has real part `1 - Re ρ`
   (reflected about `1/2`) and imaginary part `-Im ρ` (so `|Im|` is unchanged).

   Hence it SUFFICES to clear the right half of the critical strip: if there are no zeros with
   `1/2 < Re < 1` and `|Im| ≤ T`, then every strip zero with `|Im| ≤ T` lies on `Re = 1/2`.  This
   halves the region the box-driver must certify.  Self-contained: only `riemannZeta_one_sub`.

   conjecture1_proved = False (NOT a proof of RH — a symmetry reduction, not an exclusion of zeros).
-/
import Mathlib

open Complex

namespace M6gap.ZeroFreeBridge

/-- **Functional-equation reflection of a ζ-zero across `Re = 1/2`.**  A zero `ρ` in the open
    critical strip (`0 < Re ρ < 1`) reflects to a zero at `1 - ρ` (`riemannZeta_one_sub`, the
    factor is finite so it kills `ζ ρ = 0`). -/
theorem riemannZeta_one_sub_eq_zero {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hz : riemannZeta ρ = 0) : riemannZeta (1 - ρ) = 0 := by
  have hn : ∀ n : ℕ, ρ ≠ -n := by
    intro n h; rw [h] at h0
    simp only [Complex.neg_re, Complex.natCast_re] at h0
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hne1 : ρ ≠ 1 := by intro h; rw [h] at h1; simp at h1
  rw [riemannZeta_one_sub hn hne1, hz, mul_zero]

/-- **Halving the work via `Re = 1/2` symmetry.**  If ζ has no zeros in the right half of the
    critical strip `1/2 < Re < 1` with `|Im| ≤ T`, then every zero in the strip `0 < Re < 1` with
    `|Im| ≤ T` lies on the critical line `Re = 1/2`.  (Pure functional-equation reflection.) -/
theorem zeta_zero_on_line_of_right_half_clear (T : ℝ)
    (hclear : ∀ ρ : ℂ, 1/2 < ρ.re → ρ.re < 1 → |ρ.im| ≤ T → riemannZeta ρ ≠ 0)
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hT : |ρ.im| ≤ T) (hz : riemannZeta ρ = 0) :
    ρ.re = 1/2 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- Re ρ < 1/2 : reflect to 1 - ρ (Re > 1/2, |Im| unchanged)
    have hz1 : riemannZeta (1 - ρ) = 0 := riemannZeta_one_sub_eq_zero h0 h1 hz
    refine hclear (1 - ρ) ?_ ?_ ?_ hz1
    · rw [Complex.sub_re, Complex.one_re]; linarith
    · rw [Complex.sub_re, Complex.one_re]; linarith
    · rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]; exact hT
  · -- Re ρ > 1/2 : the zero is itself in the cleared region
    exact hclear ρ hgt h1 hT hz

/-- **Conjugation reflection of a ζ-zero across the real axis.**  `ζ ρ = 0 ⟹ ζ (conj ρ) = 0`
    (`riemannZeta_conj`, `conj 0 = 0`). -/
theorem riemannZeta_conj_eq_zero {ρ : ℂ} (hz : riemannZeta ρ = 0) :
    riemannZeta ((starRingEnd ℂ) ρ) = 0 := by rw [riemannZeta_conj, hz, map_zero]

/-- **Quartering the work via both symmetries (`Re = 1/2` and the real axis).**  If ζ has no zeros
    in the quarter `1/2 < Re < 1`, `0 < Im ≤ T`, then every strip zero `0 < Re < 1` OFF the real
    axis with `|Im| ≤ T` lies on the critical line `Re = 1/2`.  Uses `riemannZeta_one_sub`
    (reflection across `Re = 1/2`) and `riemannZeta_conj` (reflection across the real axis) to map
    any such zero into the quarter. -/
theorem zeta_zero_on_line_of_quarter_clear (T : ℝ)
    (hclear : ∀ ρ : ℂ, 1/2 < ρ.re → ρ.re < 1 → 0 < ρ.im → ρ.im ≤ T → riemannZeta ρ ≠ 0)
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (him : ρ.im ≠ 0) (hT : |ρ.im| ≤ T)
    (hz : riemannZeta ρ = 0) : ρ.re = 1/2 := by
  obtain ⟨hTlo, hThi⟩ := abs_le.mp hT
  by_contra hne
  rcases lt_or_gt_of_ne hne with hltRe | hgtRe <;> rcases lt_or_gt_of_ne him with hltIm | hgtIm
  · -- Re < 1/2, Im < 0 : reflect to 1 - ρ  (Re = 1-Re > 1/2, Im = -Im > 0)
    refine hclear (1 - ρ) ?_ ?_ ?_ ?_ (riemannZeta_one_sub_eq_zero h0 h1 hz)
    · rw [Complex.sub_re, Complex.one_re]; linarith
    · rw [Complex.sub_re, Complex.one_re]; linarith
    · rw [Complex.sub_im, Complex.one_im, zero_sub]; linarith
    · rw [Complex.sub_im, Complex.one_im, zero_sub]; linarith
  · -- Re < 1/2, Im > 0 : reflect to conj (1 - ρ)  (Re = 1-Re > 1/2, Im = Im > 0)
    refine hclear ((starRingEnd ℂ) (1 - ρ)) ?_ ?_ ?_ ?_
      (riemannZeta_conj_eq_zero (riemannZeta_one_sub_eq_zero h0 h1 hz))
    · rw [Complex.conj_re, Complex.sub_re, Complex.one_re]; linarith
    · rw [Complex.conj_re, Complex.sub_re, Complex.one_re]; linarith
    · rw [Complex.conj_im, Complex.sub_im, Complex.one_im, zero_sub, neg_neg]; linarith
    · rw [Complex.conj_im, Complex.sub_im, Complex.one_im, zero_sub, neg_neg]; linarith
  · -- Re > 1/2, Im < 0 : reflect to conj ρ  (Re = Re > 1/2, Im = -Im > 0)
    refine hclear ((starRingEnd ℂ) ρ) ?_ ?_ ?_ ?_ (riemannZeta_conj_eq_zero hz)
    · rw [Complex.conj_re]; linarith
    · rw [Complex.conj_re]; linarith
    · rw [Complex.conj_im]; linarith
    · rw [Complex.conj_im]; linarith
  · -- Re > 1/2, Im > 0 : the zero is itself in the quarter
    exact hclear ρ hgtRe h1 hgtIm hThi hz

/-- **Width-fold reflection across the critical line, PRESERVING the imaginary part.**  Composing
    the functional equation (`riemannZeta_one_sub_eq_zero`, `ρ ↦ 1 - ρ`) with conjugation
    (`riemannZeta_conj_eq_zero`, `ρ ↦ conj ρ`) yields the reflection `ρ ↦ 1 - conj ρ` across the
    vertical line `Re = 1/2` that keeps `Im` fixed: a zero at `β + iγ` (`0 < β < 1`) maps to a zero
    at `(1 - β) + iγ`.  This is the symmetry that folds a fixed-`Im`-band box `[a, 1-a] × [T0,T1]`
    onto its left half `[a, 1/2] × [T0,T1]` (unlike `riemannZeta_one_sub_eq_zero`, which flips the
    sign of `Im` and so leaves a single `Im`-band). -/
theorem riemannZeta_reflect_line_eq_zero {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hz : riemannZeta ρ = 0) : riemannZeta (1 - (starRingEnd ℂ) ρ) = 0 := by
  have hc : riemannZeta ((starRingEnd ℂ) ρ) = 0 := riemannZeta_conj_eq_zero hz
  have h0' : 0 < ((starRingEnd ℂ) ρ).re := by rw [Complex.conj_re]; exact h0
  have h1' : ((starRingEnd ℂ) ρ).re < 1 := by rw [Complex.conj_re]; exact h1
  exact riemannZeta_one_sub_eq_zero h0' h1' hc

end M6gap.ZeroFreeBridge


