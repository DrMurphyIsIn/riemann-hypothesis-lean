/- M6gapZetaZeroConfinement -- lane m6gap: the Mathlib-only part of ZetaZeroConfinement on the dbn island.

   M6GAP PORT (lane m6gap, 2026-09-23): the four Mathlib-only theorems of
   telperion/examples/li_positivity/lean/ZetaZeroConfinement.lean (same pin as this island, Lean
   v4.34.0-rc1 / Mathlib de5ce8a9; the zeta_zero_localization copy is the v4.32.0 source of
   HeightFloor's import), copied VERBATIM (statements and proofs):
     `zeta_zero_iff_completed_zero_of_im_ne`, `zeta_zero_reflect`, `zeta_zero_re_mem_strip`,
     `no_low_zeros_of_strip_clear`.
   OMITTED: `zero_in_band` (the dVP confinement band), which needs the effective de la Vallee
   Poussin region `ZeroFreeBridge.riemannZeta_ne_zero_region` and through it ~70 zero_free_bridge
   modules; the height floor does not use it.  The only other edit is the namespace prefix
   `M6gap.` (no clash with a sibling lane's copy).  Consumed by M6gapHeightFloor.

   conjecture1_proved = False (functional-equation bookkeeping; NOT a proof of RH).
-/
import Mathlib

open Complex

namespace M6gap.ZetaZeroConfinement

/-- **Unconditional strip bridge for off-real points.**  For `ρ.im ≠ 0` the Archimedean factor
    `Gammaℝ ρ` is nonzero (its only zeros are the non-positive even integers, all real), so
    `riemannZeta ρ = 0 ↔ completedRiemannZeta ρ = 0`. -/
theorem zeta_zero_iff_completed_zero_of_im_ne {ρ : ℂ} (him : ρ.im ≠ 0) :
    riemannZeta ρ = 0 ↔ completedRiemannZeta ρ = 0 := by
  have hρ0 : ρ ≠ 0 := by
    intro h; apply him; rw [h]; simp
  have hGne : Gammaℝ ρ ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    apply him
    rw [hn]
    simp
  rw [riemannZeta_def_of_ne_zero hρ0, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h hGne
  · intro h; exact Or.inl h

/-- **The functional-equation reflection of an off-real zeta zero.**  `ζ ρ = 0` with `ρ.im ≠ 0`
    forces `ζ (1 - ρ) = 0`. -/
theorem zeta_zero_reflect {ρ : ℂ} (him : ρ.im ≠ 0) (hzero : riemannZeta ρ = 0) :
    riemannZeta (1 - ρ) = 0 := by
  have hΛ : completedRiemannZeta ρ = 0 := (zeta_zero_iff_completed_zero_of_im_ne him).1 hzero
  have hΛ' : completedRiemannZeta (1 - ρ) = 0 := by
    rw [completedRiemannZeta_one_sub]; exact hΛ
  have him' : (1 - ρ).im ≠ 0 := by
    rw [Complex.sub_im, Complex.one_im, zero_sub, neg_ne_zero]; exact him
  exact (zeta_zero_iff_completed_zero_of_im_ne him').2 hΛ'

/-- **Critical-strip location of a nontrivial (off-real) zeta zero.**  `ζ ρ = 0` with `ρ.im ≠ 0`
    forces `0 < ρ.re ∧ ρ.re < 1`.  `Re < 1` is `riemannZeta_ne_zero_of_one_le_re` directly; `0 < Re`
    is the same lemma applied to the functional-equation reflection `1 - ρ` (`zeta_zero_reflect`),
    whose real part `1 - ρ.re ≥ 1` when `ρ.re ≤ 0`.  Off-real is essential — the trivial zeros lie
    on the real axis at the negative even integers (`Re ≤ 0`). -/
theorem zeta_zero_re_mem_strip {ρ : ℂ} (him : ρ.im ≠ 0) (hz : riemannZeta ρ = 0) :
    0 < ρ.re ∧ ρ.re < 1 := by
  refine ⟨?_, ?_⟩
  · by_contra h
    push_neg at h
    have hrefl : riemannZeta (1 - ρ) = 0 := zeta_zero_reflect him hz
    have hge : (1 : ℝ) ≤ (1 - ρ).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    exact riemannZeta_ne_zero_of_one_le_re hge hrefl
  · by_contra h
    push_neg at h
    exact riemannZeta_ne_zero_of_one_le_re h hz

/-- **No low zeros ⟹ the `55/16` height floor.**  If `riemannZeta` has NO zero in the open critical
    strip below height `55/16` (`hclear_low`: no `ρ` with `0 < Re < 1` and `0 < Im ≤ 55/16`), then
    every nontrivial zero up to height `T` satisfies `55/16 ≤ |ρ.im|` — i.e. this DISCHARGES the
    `hγ_all` residual of `AllZerosUpToHeight.all_nontrivial_zeros_up_to_height_on_line` (and the
    concrete `hγ` of `AllZeros_h100`) from a single, precise box obligation instead of an appeal to
    an unformalized "no zeros below height 14" fact.

    `hclear_low` is (mostly) what a winding-`0` box certificate over the low critical strip supplies:
    `zeta_count_eq_winding_generic` with `N = 0` gives `∑ divisor = 0` with `divisor ≥ 1` on the
    support, forcing the support (hence the set of captured box zeros) empty.  NOTE the box must span
    (essentially) the FULL strip width at low height, NOT the thin confinement band `[a, 1-a]`: below
    `55/16` the dVP region is silent (it requires `55/16 ≤ |γ|`), so a low zero is not confined to the
    band.  CORRECTION (2026-09-08): an earlier revision suggested counting `completedRiemannZeta`
    over `[0,1] × [0, 55/16]` "since `Λ` has no pole" — that was WRONG: `Λ` has simple poles at BOTH
    `s = 0` and `s = 1` (`Λ = Λ₀ - 1/s - 1/(1-s)`), so a `[0,1]`-width `Λ`-box hits two poles, not
    none.  The correct closure (RH_IN_BOX_INTERFACE §6.3) counts `ζ` over the pole-free boxes
    `[0, 1/1000]` (left sliver, #332) and `[1/1000, 999/1000]` (band, #329) and folds the right
    sliver into the left one via the Im-preserving FE reflection `riemannZeta_reflect_line_eq_zero`
    — assembled in `StripClear.hclear_low_of_box_certs`. -/
theorem no_low_zeros_of_strip_clear (T : ℝ)
    (hclear_low : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      0 < ρ.im → ρ.im ≤ 55 / 16 → False) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ T → 55 / 16 ≤ |ρ.im| := by
  intro ρ hz him0 _
  rw [abs_of_pos him0]
  by_contra h
  push_neg at h
  obtain ⟨hre0, hre1⟩ := zeta_zero_re_mem_strip (ne_of_gt him0) hz
  exact hclear_low ρ hz hre0 hre1 him0 (le_of_lt h)

end M6gap.ZetaZeroConfinement
