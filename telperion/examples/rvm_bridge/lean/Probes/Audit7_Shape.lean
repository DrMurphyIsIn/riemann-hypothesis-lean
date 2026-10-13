/- Audit probe for E6Bridge7. -/
import E6Bridge7
open Zeta23 Complex RvMBridge6 RvMBridge7 WeilExplicit
open scoped ComplexConjugate

/- 1. The theorem consumes O2's shape verbatim (expected SUCCESS). -/
example : RvMBridge6.GaussianDominance := RvMBridge7.gaussian_dominance
example (hA : RvMBridge6.GaussianApprox)
    (hpos : ∀ g : ℝ → ℂ, IsWeilTest g → 0 ≤ (weilForm (autocorr g)).re) : RiemannHypothesis :=
  RvMBridge6.weil_positivity_implies_rh_of' hA RvMBridge7.gaussian_dominance hpos

/- 2. The pair adds, not cancels: the reflected term is the conjugate (expected SUCCESS). -/
theorem audit_term_reflect (c lam : ℝ) (ρ : ℂ) : term c lam (reflect ρ) = conj (term c lam ρ) := by
  unfold term
  rw [zeroMult_reflect, gammaOf_reflect, gaussTest_conj, map_mul, Complex.conj_natCast]
#print axioms audit_term_reflect

/- 3. On the line phi_c is never positive, so M > 0 cannot come from an on-line rho_0
   (expected SUCCESS). -/
theorem audit_phi_nonpos_on_line (c : ℝ) {ρ₀ : ℂ} (h : ρ₀.re = 1 / 2) : phi c ρ₀ ≤ 0 := by
  unfold phi
  rw [h]
  nlinarith [sq_nonneg (ρ₀.im - c)]
#print axioms audit_phi_nonpos_on_line

/- 4. The off-line hypothesis deleted: the generic-centre step and the M > 0 step both fail
   (expected FAIL). -/
example {ρ₀ : ℂ} (h₀ : IsNontrivialZero ρ₀) :
    ∃ c : ℝ, |c - ρ₀.im| < |1 / 2 - ρ₀.re| ∧ c ∉ badSet ρ₀ := by
  exact exists_generic_centre ‹_›

example {ρ₀ : ℂ} (h₀ : IsNontrivialZero ρ₀) (c : ℝ) (hcI : |c - ρ₀.im| ≤ |1 / 2 - ρ₀.re|) :
    0 < phi c ρ₀ := by
  unfold phi
  nlinarith [sq_nonneg (ρ₀.im - c), sq_nonneg (1 / 2 - ρ₀.re), abs_nonneg (c - ρ₀.im)]

/- 5. The concrete phase instance x = 1, y = 1/4, lam0 = 100 (expected SUCCESS: instantiation). -/
example : ∃ lam : ℝ, (100 : ℝ) ≤ lam ∧
    ((1 : ℝ) ^ 2 - (1 / 4 : ℝ) ^ 2) * Real.cos (4 * lam * 1 * (1 / 4))
      + 2 * 1 * (1 / 4) * Real.sin (4 * lam * 1 * (1 / 4)) = -((1 : ℝ) ^ 2 + (1 / 4) ^ 2) :=
  exists_lam_trig 100 1 (1 / 4) (by norm_num)

/- 6. The final inequality with the file's constants, abstractly (expected SUCCESS):
   -2K e^{2 lam M} + e^{2 lam (M - eta)} A + B < 0 when lam >= max(A/(2 eta K), B/(2 M K)). -/
theorem audit_final_ineq (K M η A B lam : ℝ) (hK : 0 < K) (hM : 0 < M) (hη : 0 < η)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hlamA : A / (2 * η * K) ≤ lam) (hlamB : B / (2 * M * K) ≤ lam) :
    -(2 * K * Real.exp (2 * lam * M)) + (Real.exp (2 * lam * (M - η)) * A + B) < 0 := by
  have h1 : A ≤ K * Real.exp (2 * lam * η) := by
    have : A / K ≤ 2 * lam * η := by
      rw [div_le_iff₀ hK]
      have := (div_le_iff₀ (by positivity : (0:ℝ) < 2 * η * K)).mp hlamA
      linarith
    have := Real.add_one_le_exp (2 * lam * η)
    have : A / K ≤ Real.exp (2 * lam * η) := by linarith
    rwa [div_le_iff₀ hK, mul_comm] at this
  have h2 : B < K * Real.exp (2 * lam * M) := by
    have : B / K ≤ 2 * lam * M := by
      rw [div_le_iff₀ hK]
      have := (div_le_iff₀ (by positivity : (0:ℝ) < 2 * M * K)).mp hlamB
      linarith
    have := Real.add_one_le_exp (2 * lam * M)
    have : B / K < Real.exp (2 * lam * M) := by linarith
    rwa [div_lt_iff₀ hK, mul_comm] at this
  have hsplit : Real.exp (2 * lam * (M - η)) * Real.exp (2 * lam * η) = Real.exp (2 * lam * M) := by
    rw [← Real.exp_add]; congr 1; ring
  have hE : 0 < Real.exp (2 * lam * (M - η)) := Real.exp_pos _
  have h3 : Real.exp (2 * lam * (M - η)) * A ≤ K * Real.exp (2 * lam * M) := by
    calc Real.exp (2 * lam * (M - η)) * A
        ≤ Real.exp (2 * lam * (M - η)) * (K * Real.exp (2 * lam * η)) :=
          mul_le_mul_of_nonneg_left h1 hE.le
      _ = K * Real.exp (2 * lam * M) := by rw [← hsplit]; ring
  linarith
#print axioms audit_final_ineq
