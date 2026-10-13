/-  ZetaEMSum.lean -- ANDÚRIL cert-forge: the Dirichlet-sum reduction of the EM finite part.

    M6GAP CROSS-PIN PORT (lane m6gap, 2026-09-23): a copy of
    telperion/examples/zeta_reflection/lean/ZetaEMSum.lean (Lean v4.32.0, Mathlib v4.32.0) onto the dbn
    island (Lean v4.34.0-rc1, Mathlib de5ce8a9).  The ONLY edits are: module names prefixed `M6gap`
    in the imports, every namespace prefixed `M6gap.` (so no declaration can clash with a sibling
    lane's port), and comment wording on this island's word-level placeholder scan.  No proof was
    changed.  Consumed by M6gapHeightFloor (the 55/16 height floor on this island).


    `emZetaFinite3 s N` (`EMZetaTail`) is `1/(s-1) + 1/2 + ∫₁^N saw₁·(−s x^{−s−1}) + b₂·s·N^{−s−1}/2`.
    The saw integral is not elementary; but `em_cpow_partial` rewrites it in terms of the
    ELEMENTARY finite Dirichlet sum `Σ_{n∈Ico 1 N} n^{−s}` and the boxable `∫₁^N x^{−s}` (closed by
    `integral_cpow`).  Substituting and simplifying yields the standard Euler–Maclaurin ζ finite part

        emZetaFinite3 s N = Σ_{n=1}^{N−1} n^{−s} + N^{1−s}/(s−1) + N^{−s}/2 + b₂·s·N^{−s−1}/2,

    every summand of which the forge boxes (the sum termwise via `ZeroHypBand_t14.term_re/term_im` +
    the trig climb; the three tail terms via elementary cpow amplitude/phase boxes).  This file proves
    the reduction ONCE, parametric in `s` and `N`; the forge instantiates it at `s = 1/2 + 14i` and
    `s = 1/2 + 15i`, `N = 200`.

    conjecture1_proved = False.  An algebraic rewrite of an already-proved finite part, not a proof of RH.
-/
import M6gapEMZetaTail
import M6gapEMZetaComplex
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Complex MeasureTheory M6gap.ZetaReflection

namespace M6gap.ZetaEMSum

/-- **The Dirichlet-sum form of `emZetaFinite3`.**  For `s ≠ 0`, `s ≠ 1`, `N ≥ 1`:
        `emZetaFinite3 s N = Σ_{n∈Ico 1 N} n^{−s} + N^{1−s}/(s−1) + N^{−s}/2 + b₂·s·N^{−s−1}/2`.
    Proof: expand `emZetaFinite3`, rewrite the saw integral by `em_cpow_partial`, close `∫₁^N x^{−s}`
    by `integral_cpow` (`Re(−s) = −1/2 > −1`), and finish with field algebra. -/
theorem emZetaFinite3_eq_dirichlet {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N)
    (hsre : -1 < (-s).re) :
    emZetaFinite3 s N
      = (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
        + (N : ℂ) ^ (1 - s) / (s - 1)
        + (N : ℂ) ^ (-s) / 2
        + (bernoulli 2 : ℂ) * (s * (N : ℝ) ^ (-s - 1)) / 2 := by
  have hNc : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  -- em_cpow_partial: the saw integral in terms of the Dirichlet sum and ∫₁^N x^{-s}.
  have hpart := em_cpow_partial hs0 (N := N) hN
  -- Close ∫₁^N x^{-s} = (N^{1-s} - 1^{1-s})/(1-s)  via integral_cpow with r = -s.
  have hint : (∫ x in (1 : ℝ)..(N : ℝ), (x : ℂ) ^ (-s))
      = ((N : ℂ) ^ (-s + 1) - (1 : ℂ) ^ (-s + 1)) / (-s + 1) := by
    have := integral_cpow (a := (1 : ℝ)) (b := (N : ℝ)) (r := -s) (Or.inl hsre)
    simpa using this
  have hone1 : ((1 : ℝ) : ℂ) ^ (-s) = 1 := by rw [Complex.ofReal_one, Complex.one_cpow]
  have hone2 : (1 : ℂ) ^ (-s + 1) = 1 := Complex.one_cpow _
  rw [hone1] at hpart
  rw [hone2] at hint
  -- Unfold emZetaFinite3 FIRST, then name the integrals/sum as atoms so the tail is field-algebra.
  rw [emZetaFinite3]
  set Isaw : ℂ := ∫ x in (1 : ℝ)..(N : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1))
    with hIsaw
  set Ipow : ℂ := ∫ x in (1 : ℝ)..(N : ℝ), (x : ℂ) ^ (-s) with hIpow
  set S : ℂ := ∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s) with hS
  -- hpart : S = Ipow - (N^{-s} - 1)/2 + Isaw ;  hint : Ipow = (N^{-s+1} - 1)/(-s+1).
  have hsm1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hden : (-s + 1) ≠ 0 := by
    rw [show (-s + 1 : ℂ) = -(s - 1) by ring]; exact neg_ne_zero.mpr hsm1
  have hpow : (N : ℂ) ^ (-s + 1) = (N : ℂ) ^ (1 - s) := by rw [show (-s + 1 : ℂ) = 1 - s by ring]
  have hNcast : (((N : ℝ) : ℂ)) ^ (-s) = (N : ℂ) ^ (-s) := by norm_cast
  rw [hNcast] at hpart
  have hIsaw_eq : Isaw = S - Ipow + ((N : ℂ) ^ (-s) - 1) / 2 := by linear_combination -hpart
  rw [hIsaw_eq, hint, hpow]
  field_simp
  ring
