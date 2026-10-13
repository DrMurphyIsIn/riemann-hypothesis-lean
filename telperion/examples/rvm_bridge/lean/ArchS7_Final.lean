import ArchS7_H85
import ArchS6_Trace

/-!
# ArchS7_Final: Connes–Consani Theorem 4.7 with no interface hypotheses

For every test function `g` (`IsWeilTest`: smooth, compact support), with S6's real prolate basis
`bR` (any real orthonormal eigenbasis of S9's operator `2cos(2πxω)` on `[0,1]`), any enumeration
`σ : ℕ ≃ ι`, S6's `ProlateData` instance `prolateData bR σ`, and any Hilbert basis `e` of `L²(ℝ)_ev`:

  `Tr(ϑ(g∗g*) S) = Σ_k ‖S ϑ(g) e_k‖² = W∞(g∗g*) + E(g∗g*)`,

with `W∞ = ArchS3.archW g` and `E = (prolateData bR σ).Eplus (autocorr g)` (CC's ε of (84) = S8's `eps`).
All inputs are theorems: (85) from S3 via `ArchS7_H85`, CC Lemma 4.1 via `ArchS7_Lemma41`, the scaling
and `ϑ(g)` via `ArchS7_Dilation`/`ArchS7_Theta`, `ProlateData` and Σ|τ_n| < ∞ from S6.

conjecture1_proved = False.
-/

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace ArchS7

open ArchS6 ArchS8

/-- **CC Theorem 4.7, unconditional (in the island's conventions).** -/
theorem cc_thm47 {ι : Type*} (bR : EigenBasis CopR ι) (σ : ℕ ≃ ι)
    {g : ℝ → ℂ} (hW : WeilExplicit.IsWeilTest g) {κ : Type*} (e : HilbertBasis κ ℂ evenL2) :
    HasSum (fun k ↦ ‖ArchS6.ProlateBasis.soninProj (S := evenPair)
        (theta g (hW.1.continuous.integrable_of_hasCompactSupport hW.2) (e k))‖ ^ 2)
      (ArchS3.archW g + ((prolateData bR σ).Eplus (WeilExplicit.autocorr g)).re) :=
  thm47_weil_O1 bR (prolateData bR σ) σ (prolateData_lam bR σ) (prolateData_phi bR σ)
    (summable_abs_tau bR) hW e

/-- **CC (83), unconditional**: `W∞(g∗g*) + E(g∗g*) ≥ 0`. -/
theorem cc_thm47_nonneg {ι : Type*} (bR : EigenBasis CopR ι) (σ : ℕ ≃ ι)
    {g : ℝ → ℂ} (hW : WeilExplicit.IsWeilTest g) :
    0 ≤ ArchS3.archW g + ((prolateData bR σ).Eplus (WeilExplicit.autocorr g)).re := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ evenL2
  exact (cc_thm47 bR σ hW b).nonneg fun _ ↦ sq_nonneg _

/-- The data exist: a real prolate basis and an enumeration. -/
theorem exists_prolate_enumeration :
    ∃ (ι : Type) (_ : EigenBasis CopR ι), Nonempty (ℕ ≃ ι) := by
  obtain ⟨ι, b, -⟩ := exists_eigenBasis_CopR
  exact ⟨ι, b, exists_equiv_nat b⟩

end ArchS7
