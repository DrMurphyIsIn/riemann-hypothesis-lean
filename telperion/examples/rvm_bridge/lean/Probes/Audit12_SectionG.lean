/- Audit probes for E6Bridge12 section G (dominance form). -/
import E6Bridge12
open Zeta23 Complex MeasureTheory Filter Topology RvMBridge6 RvMBridge7 RvMBridge12 WeilExplicit RvMBridgeGauss

/- 1. The finite_window bounds (c - D - 1, c + D] cover |Im ρ - c| ≤ D for ANY real c, D ≥ 0,
   negative ordinates included; and the finiteness lemma is general in (T₁, T₂) (expected SUCCESS). -/
example (c D : ℝ) (ρ : ℂ) (h : |ρ.im - c| ≤ D) : c - D - 1 < ρ.im ∧ ρ.im ≤ c + D := by
  have := abs_le.mp h; constructor <;> linarith [this.1, this.2]
example : (zeroWindowSet (-100000) 2).Finite := zeroWindowSet_finite _ _
example (T₁ T₂ : ℝ) :
    ({ρ | IsNontrivialZero ρ} ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}).Finite := zetaSeam.finite_window T₁ T₂

/- 2. windowSum and tailEnvelope unfold definitionally to explicit expressions (expected SUCCESS).
   NOTE: constB c is itself a tsum over all zeros; a consumer needs a numeric UPPER bound for it. -/
example (c D lam : ℝ) : windowSum c D lam = ∑ ρ ∈ zeroWindow c D,
    (WeilExplicit.zeroMult ρ : ℝ) * ((ρ.im - c) ^ 2 * Real.exp (-(2 * lam) * (ρ.im - c) ^ 2)) := rfl
example (c D lam : ℝ) : tailEnvelope c D lam
    = Real.exp (2 * (lam - 1) * (1 / 4 - D ^ 2)) * constB c := rfl
example (c : ℝ) : constB c = ∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℝ)
    * ((Real.exp (1 / 2) * (2 * c ^ 2 + 13 / 4) / (min 1 1) ^ 2) / (1 + Complex.normSq (gammaOf ρ))) := rfl
example (c D : ℝ) (ρ : ℂ) : ρ ∈ zeroWindow c D ↔ IsNontrivialZero ρ ∧ |ρ.im - c| ≤ D := mem_zeroWindow

/- 3. The tail envelope is gated on 1 ≤ lam: tail_bound_window at lam = 1/2 does not elaborate
   (expected FAIL). -/
example (c D : ℝ) (hD : 0 ≤ D) :
    ‖∑' ρ : ↥(winSet c D)ᶜ, term c (1 / 2) ρ‖ ≤ tailEnvelope c D (1 / 2) := by
  unfold tailEnvelope
  exact tail_bound_window hD (by norm_num)

/- 4. hdom is load-bearing: the dominance theorem's proof without hdom fails (expected FAIL). -/
example {c D lam : ℝ} (hD : 0 ≤ D) (hlam : 1 ≤ lam) (hwin : WindowOnLine c D) :
    0 ≤ (zeroSide (gaussTest c lam)).re := by
  have hlam0 : 0 < lam := by linarith
  rw [zeroSide_split c D lam hlam0, Complex.add_re, re_window_eq_windowSum hwin]
  have htail := tail_bound_window (c := c) hD hlam
  have h := abs_le.mp (Complex.abs_re_le_norm (∑' ρ : ↥(winSet c D)ᶜ, term c lam ρ))
  linarith [h.1, windowSum_nonneg c D lam]

/- 5. The two dominance-form theorems compose as stated; the single-near-zero form is the special
   case via near_term_le_windowSum (expected SUCCESS). -/
example {c D lam : ℝ} (hD : 0 ≤ D) (hlam : 1 ≤ lam) (hwin : WindowOnLine c D)
    (hdom : tailEnvelope c D lam ≤ windowSum c D lam) : 0 ≤ (zeroSide (gaussTest c lam)).re := by
  have := re_zeroSide_ge_windowSum_sub hD hlam hwin
  linarith
example {c D lam : ℝ} {ρ₁ : ℂ} (h₁nt : IsNontrivialZero ρ₁) (h₁win : |ρ₁.im - c| ≤ D) :
    (WeilExplicit.zeroMult ρ₁ : ℝ) * ((ρ₁.im - c) ^ 2 * Real.exp (-(2 * lam) * (ρ₁.im - c) ^ 2))
      ≤ windowSum c D lam := near_term_le_windowSum h₁nt h₁win
