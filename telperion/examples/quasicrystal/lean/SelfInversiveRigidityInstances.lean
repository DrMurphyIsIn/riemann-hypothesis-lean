/- telperion 0.1.6 | family SelfInversiveRigidityInstances | input-hash a763749ebea430d8
   2 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib
import TwoFreqRigidity

namespace SelfInversiveRigidityInstances

/-- Concrete two-frequency sum `F(x) = c₁·e^{iλ₁x} + c₂·e^{iλ₂x}` with Gaussian-
    rational coefficients `c₁ = (3 / 5) + (4 / 5)i`, `c₂ = 1 + 0i` and frequencies
    `λ₁ = 1`, `λ₂ = 2`. -/
noncomputable def rigidity_unit_modulus_c1 : ℂ := ⟨((3 / 5)), ((4 / 5))⟩
noncomputable def rigidity_unit_modulus_c2 : ℂ := ⟨(1), (0)⟩

/-- **Equal-modulus rigidity** (rigidity_unit_modulus): since `|c₁|² = |c₂|²` exactly, `‖c₁‖ = ‖c₂‖`,
    so by `Quasicrystal.twoFreq_realRooted_iff` the two-frequency sum is REAL-ROOTED —
    every zero has zero imaginary part.  Reverse-Dyson R3(n=2): reality of the support
    is forced by an equal-modulus condition on the coefficients alone.
    conjecture1_proved = False. -/
theorem rigidity_unit_modulus :
    ∀ x : ℂ, Quasicrystal.twoFreq rigidity_unit_modulus_c1 rigidity_unit_modulus_c2 (1) (2) x = 0 → x.im = 0 := by
  have hc1 : rigidity_unit_modulus_c1 ≠ 0 := by
    have h : Complex.normSq rigidity_unit_modulus_c1 ≠ 0 := by
      unfold rigidity_unit_modulus_c1; simp only [Complex.normSq_mk]; norm_num
    exact fun hz => h (by rw [hz]; simp)
  have hc2 : rigidity_unit_modulus_c2 ≠ 0 := by
    have h : Complex.normSq rigidity_unit_modulus_c2 ≠ 0 := by
      unfold rigidity_unit_modulus_c2; simp only [Complex.normSq_mk]; norm_num
    exact fun hz => h (by rw [hz]; simp)
  have hlam : (1 : ℝ) ≠ (2) := by norm_num
  have hmod : ‖rigidity_unit_modulus_c1‖ = ‖rigidity_unit_modulus_c2‖ := by
    have hns : Complex.normSq rigidity_unit_modulus_c1 = Complex.normSq rigidity_unit_modulus_c2 := by
      unfold rigidity_unit_modulus_c1 rigidity_unit_modulus_c2; simp only [Complex.normSq_mk]; norm_num
    rw [Complex.norm_def, Complex.norm_def, hns]
  exact (Quasicrystal.twoFreq_realRooted_iff rigidity_unit_modulus_c1 rigidity_unit_modulus_c2 (1) (2) hc1 hc2 hlam).mpr hmod

/-- Concrete two-frequency sum `F(x) = c₁·e^{iλ₁x} + c₂·e^{iλ₂x}` with Gaussian-
    rational coefficients `c₁ = 1 + 1i`, `c₂ = 1 + (-1)i` and frequencies
    `λ₁ = 0`, `λ₂ = 3`. -/
noncomputable def rigidity_conjugate_pair_c1 : ℂ := ⟨(1), (1)⟩
noncomputable def rigidity_conjugate_pair_c2 : ℂ := ⟨(1), ((-1))⟩

/-- **Equal-modulus rigidity** (rigidity_conjugate_pair): since `|c₁|² = |c₂|²` exactly, `‖c₁‖ = ‖c₂‖`,
    so by `Quasicrystal.twoFreq_realRooted_iff` the two-frequency sum is REAL-ROOTED —
    every zero has zero imaginary part.  Reverse-Dyson R3(n=2): reality of the support
    is forced by an equal-modulus condition on the coefficients alone.
    conjecture1_proved = False. -/
theorem rigidity_conjugate_pair :
    ∀ x : ℂ, Quasicrystal.twoFreq rigidity_conjugate_pair_c1 rigidity_conjugate_pair_c2 (0) (3) x = 0 → x.im = 0 := by
  have hc1 : rigidity_conjugate_pair_c1 ≠ 0 := by
    have h : Complex.normSq rigidity_conjugate_pair_c1 ≠ 0 := by
      unfold rigidity_conjugate_pair_c1; simp only [Complex.normSq_mk]; norm_num
    exact fun hz => h (by rw [hz]; simp)
  have hc2 : rigidity_conjugate_pair_c2 ≠ 0 := by
    have h : Complex.normSq rigidity_conjugate_pair_c2 ≠ 0 := by
      unfold rigidity_conjugate_pair_c2; simp only [Complex.normSq_mk]; norm_num
    exact fun hz => h (by rw [hz]; simp)
  have hlam : (0 : ℝ) ≠ (3) := by norm_num
  have hmod : ‖rigidity_conjugate_pair_c1‖ = ‖rigidity_conjugate_pair_c2‖ := by
    have hns : Complex.normSq rigidity_conjugate_pair_c1 = Complex.normSq rigidity_conjugate_pair_c2 := by
      unfold rigidity_conjugate_pair_c1 rigidity_conjugate_pair_c2; simp only [Complex.normSq_mk]; norm_num
    rw [Complex.norm_def, Complex.norm_def, hns]
  exact (Quasicrystal.twoFreq_realRooted_iff rigidity_conjugate_pair_c1 rigidity_conjugate_pair_c2 (0) (3) hc1 hc2 hlam).mpr hmod

end SelfInversiveRigidityInstances
