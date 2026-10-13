/- Audit probes for E6Bridge15. -/
import E6Bridge15
open Zeta23 Complex MeasureTheory Filter Topology RvMBridge15 RvMBridge15.BombieriLagarias WeilExplicit
open scoped ComplexConjugate

/- 1. LiValue 0 is FALSE, my own proof: liLimit 0 = 0, archSide 0 = 1, finiteSide 0 = 0 (expected SUCCESS). -/
theorem audit_liLimit_zero : liLimit 0 = 0 := by
  unfold liLimit liPaired liKernel
  simp
theorem audit_archSide_zero : BombieriLagarias.archSide 0 = 1 := by
  unfold BombieriLagarias.archSide
  simp
theorem audit_finiteSide_zero : finiteSide 0 = 0 := by
  unfold finiteSide
  simp
theorem audit_liValue_zero_false : ¬ LiValue 0 := by
  unfold LiValue
  rw [audit_liLimit_zero, audit_archSide_zero, audit_finiteSide_zero]
  norm_num
#print axioms audit_liValue_zero_false

/- 2. The window is conjugation-closed, the kernel commutes with conj, multiplicities match
   (expected SUCCESS, consumption of the file's lemmas). -/
example (T : ℝ) (ρ : ℂ) : conj ρ ∈ windowSet T ↔ ρ ∈ windowSet T := conj_mem_windowSet
example (n : ℕ) (ρ : ℂ) : liKernel n (conj ρ) = conj (liKernel n ρ) := liKernel_conj n ρ
example (ρ : ℂ) : WeilExplicit.zeroMult (conj ρ) = WeilExplicit.zeroMult ρ := zeroMult_conj ρ

/- 3. On the line, my own re-derivation: |ρ - 1|^2 = |ρ|^2 when Re ρ = 1/2 (expected SUCCESS). -/
theorem audit_on_line_modulus {ρ : ℂ} (h : ρ.re = 1 / 2) : Complex.normSq (ρ - 1) = Complex.normSq ρ := by
  rw [Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, h]
  ring
#print axioms audit_on_line_modulus

/- 4. The bound instance: the j = 1 term's real part is Re ρ / |ρ|^2 (expected SUCCESS). -/
example (ρ : ℂ) : (1 / ρ).re = ρ.re / Complex.normSq ρ := by
  rw [one_div, Complex.inv_re]

/- 5. The filter is atTop on ℝ and the node's shape is consumed (expected SUCCESS). -/
example (n : ℕ) (hn : 0 < n) (h : LiValue n) :
    Tendsto (liZeroSum n) (atTop : Filter ℝ) (𝓝 (BombieriLagarias.archSide n + finiteSide n)) :=
  bl_explicit_formula_of hn h

/- 6. The UNPAIRED family is not claimed summable, and automation cannot produce it
   (expected FAIL). -/
example (n : ℕ) : Summable (liTerm n) := by
  exact?

/- 7. The node without LiValue does not follow from the convergence half (expected FAIL). -/
example (n : ℕ) (hn : 0 < n) :
    Tendsto (liZeroSum n) atTop (𝓝 (BombieriLagarias.archSide n + finiteSide n)) :=
  liZeroSum_tendsto n

/- 8. LiValue is not automation-trivial in either direction at n = 1 (expected FAIL). -/
example : LiValue 1 := by unfold LiValue liLimit; simp
example : ¬ LiValue 1 := by unfold LiValue liLimit; simp
