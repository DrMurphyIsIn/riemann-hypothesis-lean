/- Audit probes for E6Bridge19. -/
import E6Bridge19
import E6Bridge22
open Zeta23 Complex Filter Topology RvMBridge15 RvMBridge15.BombieriLagarias RvMBridge18 RvMBridge19 RvMBridge22 WeilExplicit

/- 1. The interface: E6Bridge19 uses RvMBridge18.xi and RvMBridge18.XiLogDerivDerivEq directly;
   the rfl restatement holds (expected SUCCESS). -/
example : XiLogDerivDerivEq = (∀ s : ℂ, ¬ IsNontrivialZero s →
    deriv (logDeriv xi) s = -∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2) := rfl

/- 2. The COMPOSITION through E6Bridge22: LocalCountSum + StripDerivBound + NoRealZeroInUnitInterval
   give LiValue n and the B7 node (expected SUCCESS; replaces the author's stale probe). -/
theorem audit_liValue_of_two (h1 : LocalCountSum) (h2 : StripDerivBound)
    (hR : NoRealZeroInUnitInterval) (n : ℕ) (hn : 0 < n) : LiValue n :=
  liValue_of (xiLogDerivDerivEq_of_two h1 h2) hR n hn
theorem audit_bl_of_two (h1 : LocalCountSum) (h2 : StripDerivBound)
    (hR : NoRealZeroInUnitInterval) (n : ℕ) (hn : 0 < n) :
    Tendsto (liZeroSum n) atTop (𝓝 (BombieriLagarias.archSide n + finiteSide n)) :=
  RvMBridge15.bl_explicit_formula_of hn (audit_liValue_of_two h1 h2 hR n hn)
#print axioms audit_liValue_of_two
#print axioms audit_bl_of_two

/- 3. Both directions of the Lambda-form equivalence, and the growth corollary (expected SUCCESS). -/
example (h : XiLogDerivDerivEq) : LambdaDerivPartialFraction := xiDerivPartialFraction_iff.mp h
example (h : LambdaDerivPartialFraction) : XiLogDerivDerivEq := xiDerivPartialFraction_iff.mpr h
example (h : RvMBridge20.XiDiffExtGrowthRight) (hR : NoRealZeroInUnitInterval) : LiValue 3 :=
  liValue_of_growth h hR 3 (by norm_num)

/- 4. Pole-term signs, abstractly: for f = s(s-1)/2, deriv (logDeriv f) s = -1/s^2 - 1/(s-1)^2
   at s = 3 (expected SUCCESS). -/
/- The pole terms enter with + sign in the Lambda form: deriv (logDeriv Λ) = deriv (logDeriv ξ)
   + 1/s^2 + 1/(s-1)^2, as the product rule on ξ = (s(s-1)/2) Λ gives (consumption, SUCCESS). -/
theorem audit_pole_signs {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hz : ¬ IsNontrivialZero s) :
    deriv (logDeriv completedRiemannZeta) s = deriv (logDeriv xi) s + 1 / s ^ 2 + 1 / (s - 1) ^ 2 :=
  deriv_logDeriv_lambda_eq hs0 hs1 hz
#print axioms audit_pole_signs

/- 5. NoRealZeroInUnitInterval is not automation-closable (expected FAIL). -/
example : NoRealZeroInUnitInterval := by unfold NoRealZeroInUnitInterval; intro σ h0 h1; simp
example : NoRealZeroInUnitInterval := by unfold NoRealZeroInUnitInterval; aesop

/- 6. LiValue does not follow from hR alone (expected FAIL). -/
example (hR : NoRealZeroInUnitInterval) : LiValue 1 := liValue_of ?_ hR 1 one_pos

/- 7. The radius: every nontrivial zero has norm ≥ zeroRadius > 0 (expected SUCCESS). -/
example {ρ : ℂ} (h : IsNontrivialZero ρ) : zeroRadius ≤ ‖ρ‖ := zeroRadius_le h
example : 0 < zeroRadius := zeroRadius_pos
