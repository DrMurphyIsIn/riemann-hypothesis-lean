/-
  WeilFormDefs -- the E8 vocabulary for the `weil_form_enclosure` emitter.

  The `WeilExplicit` block below is a VERBATIM mirror of the AUTHORED block of
  telperion/missions/rh/lean/Statements/RHDefs.lean (branch rh/e8-statement), which is itself
  mirrored verbatim in telperion/examples/rvm_bridge/lean/E6Bridge4.lean, where the registry node

      theorem limit_explicit_formula (g : ℝ → ℂ) (hg : WeilExplicit.IsWeilTest g) :
          Integrable (WeilExplicit.archIntegrand g) ∧
          HasSum (fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℂ) * WeilExplicit.weilKernel g ρ)
            (WeilExplicit.archSide g - WeilExplicit.primeSide g)

  is PROVED against Anthropic's zeta-23-lean (PR #560).  `examples/weil_form_enclosure/generate.py
  --check` gates the mirror byte-for-byte against that file, so a vocabulary drift on either side
  fails CI rather than silently decoupling this island's theorems from the proved node.

  The `WeilForm` namespace adds the two names this emitter's theorems are stated in:
  `weilForm f = archSide f - primeSide f` (the E8 right-hand side, i.e. the pairing itself) and
  `crossCorr g_i g_j` (the cross-correlation whose diagonal is the autocorrelation).  They are
  PROPOSED registry vocabulary; they live here until the mission CLI carries them into
  missions/mirrormere/lean/Statements/MMDefs.lean.

  No RH progress is claimed.  Nothing in this file is proved about zeta; these are definitions,
  and the theorems in WeilFormEnclosure.lean are consequences of Arb enclosures carried as
  explicit hypotheses.  conjecture1_proved = False.
-/
import Mathlib

open MeasureTheory Complex

noncomputable section

/-! ## The registry vocabulary, mirrored verbatim (RHDefs.lean / E6Bridge4.lean). -/

namespace WeilExplicit
open MeasureTheory Complex

/-- The E8 test class: smooth, compactly supported g : R -> C. -/
def IsWeilTest (g : ℝ → ℂ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ HasCompactSupport g

/-- H_g(s) = ∫ g(u) e^{(s - 1/2) u} du, the zero-side transform.  With s = 1/2 + i r this is
    h(r) = ∫ g(u) e^{i r u} du (the Iwaniec-Kowalski pair); entire for compactly supported g,
    so H_g(ρ) at a zero ρ = 1/2 + iγ is h(γ) with γ complex when ρ is off the line.
    H_g(0) = h(i/2) and H_g(1) = h(-i/2) are the two pole terms. -/
noncomputable def weilKernel (g : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ u : ℝ, g u * Complex.exp ((s - 1 / 2) * (u : ℂ))

/-- Multiplicity of ρ as a nontrivial zero: the order of ζ at ρ on the open critical strip
    (0 off the strip and at non-zeros).  The SAME divisor expression as
    RvMCount.zetaZeroCount, so the E8 zero side and the RvM count carry identical weights. -/
noncomputable def zeroMult (ρ : ℂ) : ℕ :=
  ((MeromorphicOn.divisor riemannZeta {s : ℂ | 0 < s.re ∧ s.re < 1} : ℂ → ℤ) ρ).toNat

/-- The archimedean integrand h(r) · Re ψ(1/4 + i r/2), ψ = Γ'/Γ = Complex.digamma. -/
noncomputable def archIntegrand (g : ℝ → ℂ) (r : ℝ) : ℂ :=
  weilKernel g (1 / 2 + (r : ℂ) * I) * ((Complex.digamma (1 / 4 + ((r : ℂ) / 2) * I)).re : ℂ)

/-- The archimedean side: h(i/2) + h(-i/2) - g(0) log π + (1/2π) ∫ h(r) Re ψ(1/4 + i r/2) dr. -/
noncomputable def archSide (g : ℝ → ℂ) : ℂ :=
  weilKernel g 0 + weilKernel g 1 - g 0 * (Real.log Real.pi : ℂ)
    + (1 / (2 * (Real.pi : ℂ))) * ∫ r : ℝ, archIntegrand g r

/-- The prime side: Σ_n Λ(n)/√n · (g(log n) + g(-log n)); a finite sum for compactly
    supported g (Λ(0) = Λ(1) = 0; the two terms are the two vertical edges of the finite
    explicit formula rect_explicit_formula in the T → ∞ limit). -/
noncomputable def primeSide (g : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
    * (g (Real.log n) + g (-Real.log n))

end WeilExplicit

/-! ## The pairing and the cross-correlation (proposed registry vocabulary). -/

namespace WeilForm
open WeilExplicit

/-- The Weil pairing of a test function: the E8 right-hand side `archSide f - primeSide f`,
    which `RH_limit_explicit_formula` identifies with the sum over the zeros
    `Σ_ρ zeroMult ρ · weilKernel f ρ`.  Evaluating THIS is what the `weil_form_enclosure`
    emitter's Arb backend does; the kernel only ever sees an enclosure of it as a hypothesis. -/
noncomputable def weilForm (f : ℝ → ℂ) : ℂ :=
  archSide f - primeSide f

/-- The cross-correlation `f_{ij}(x) = ∫ g_i(t) conj (g_j (t - x)) dt`.  Its diagonal
    `crossCorr g g` is the autocorrelation `g ⋆ g̃` on which Weil positivity is stated; the
    off-diagonal entries are the Weil-Gram matrix's off-diagonal entries. -/
noncomputable def crossCorr (gi gj : ℝ → ℂ) : ℝ → ℂ :=
  fun x => ∫ t : ℝ, gi t * (starRingEnd ℂ) (gj (t - x))

/-- The autocorrelation, the diagonal of `crossCorr`. -/
noncomputable abbrev autocorr (g : ℝ → ℂ) : ℝ → ℂ := crossCorr g g

end WeilForm
