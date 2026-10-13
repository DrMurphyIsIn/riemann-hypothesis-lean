/- Audit probes for E6Bridge24 / E6Bridge27. -/
import E6Bridge27
open Zeta23 Complex Filter Topology Metric RvMBridge22 RvMBridge24 RvMBridge27

/- 1. The unconditional chain, re-composed from the three discharged facts (expected SUCCESS). -/
theorem audit_partialFraction : RvMBridge18.XiLogDerivDerivEq :=
  RvMBridge22.xiLogDerivDerivEq_of_two RvMBridge23.local_count_sum RvMBridge24.stripDerivBound
theorem audit_liValue (n : ℕ) (hn : 0 < n) : RvMBridge15.LiValue n :=
  RvMBridge19.liValue_of audit_partialFraction RvMBridge25.noRealZeroInUnitInterval n hn
theorem audit_node (n : ℕ) (hn : 0 < n) :
    Tendsto (RvMBridge15.BombieriLagarias.liZeroSum n) atTop
      (𝓝 (RvMBridge15.BombieriLagarias.archSide n + RvMBridge15.BombieriLagarias.finiteSide n)) :=
  RvMBridge15.bl_explicit_formula_of hn (audit_liValue n hn)
#print axioms audit_partialFraction
#print axioms audit_liValue
#print axioms audit_node
#print axioms RvMBridge27.bl_explicit_formula
#print axioms RvMBridge27.liValue
#print axioms RvMBridge27.xi_logDeriv_deriv_eq

/- 2. The two symmetric-difference distance steps, abstractly (expected SUCCESS). -/
theorem audit_far_part {s w ρ : ℂ} (hdist : dist w s ≤ 1 / 2) (hout : 2 < |ρ.im - s.im|) :
    3 / 2 ≤ ‖w - ρ‖ := by
  have h1 : |w.im - s.im| ≤ 1 / 2 := by
    rw [dist_eq_norm] at hdist
    have := Complex.abs_im_le_norm (w - s); rw [Complex.sub_im] at this; linarith
  have h2 : |w.im - ρ.im| ≤ ‖w - ρ‖ := by
    have := Complex.abs_im_le_norm (w - ρ); rwa [Complex.sub_im] at this
  have h3 : 3 / 2 < |w.im - ρ.im| := by
    have := abs_sub_abs_le_abs_sub (ρ.im - s.im) (w.im - s.im)
    have e : ρ.im - s.im - (w.im - s.im) = -(w.im - ρ.im) := by ring
    rw [e, abs_neg] at this; linarith
  linarith
theorem audit_near_part {w ρ : ℂ} {c : ℂ} (hρ : 8 / 5 < dist ρ c) (hw : dist w c ≤ 3 / 2) :
    1 / 10 ≤ dist w ρ := by
  have := dist_triangle ρ w c
  rw [dist_comm ρ w] at this; linarith
#print axioms audit_far_part
#print axioms audit_near_part

/- 3. Digamma hypotheses on the right half-circle: Re(w/2) ∈ (0, 7/4], |Im(w/2)| ≥ 3 ≥ 1
   (expected SUCCESS). -/
example {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 7 / 2) (h3 : 6 ≤ |w.im|) :
    0 < (w / 2).re ∧ (w / 2).re ≤ 2 ∧ 1 ≤ |(w / 2).im| := by
  have e1 : (w / 2).re = w.re / 2 := by simp [Complex.div_re]
  have e2 : (w / 2).im = w.im / 2 := by simp [Complex.div_im]
  refine ⟨by rw [e1]; linarith, by rw [e1]; linarith, ?_⟩
  rw [e2, abs_div, abs_two]; linarith

/- 4. The reflected point: Re w < 1/2 with |Re w - Re s| ≤ 1/2, 1/4 ≤ Re s gives
   1/2 ≤ Re(1 - w) ≤ 7/2 and the same |Im| (expected SUCCESS). -/
example {s w : ℂ} (hre : 1 / 4 ≤ s.re) (hw : |w.re - s.re| ≤ 1 / 2) (hhalf : w.re < 1 / 2) :
    1 / 2 ≤ (1 - w).re ∧ (1 - w).re ≤ 7 / 2 ∧ |(1 - w).im| = |w.im| := by
  have h := abs_le.mp hw
  refine ⟨by rw [Complex.sub_re, Complex.one_re]; linarith,
    by rw [Complex.sub_re, Complex.one_re]; linarith [h.1], ?_⟩
  rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]

/- 5. The two regimes overlap on 13/2 ≤ |Im s| ≤ 7 and cover 5 ≤ |Im s| (expected SUCCESS). -/
example (t : ℝ) (h : 5 ≤ |t|) : |t| ≤ 7 ∨ 13 / 2 ≤ |t| := by
  rcases le_or_gt |t| 7 with h7 | h7
  · exact Or.inl h7
  · exact Or.inr (by linarith)

/- 6. The strip bound cannot be applied AT a zero: its off-zero hypothesis is load-bearing
   (expected FAIL: the hypothesis ¬IsNontrivialZero s cannot be discharged from IsNontrivialZero s). -/
example {s : ℂ} (hs : IsNontrivialZero s) (h1 : 1 / 4 ≤ s.re) (h2 : s.re ≤ 9 / 4) (h3 : 5 ≤ |s.im|) :
    ∃ C : ℝ, ‖deriv (logDeriv RvMBridge18.xi) s + ∑ ρ ∈ window s, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2‖
      ≤ C * (1 + Real.log (2 + |s.im|)) := by
  obtain ⟨C, hC⟩ := stripDerivBound
  exact ⟨C, hC s h1 h2 h3 hs⟩

/- 7. Consumption: the compact rectangle of the low regime is the LARGER one (expected SUCCESS). -/
example : ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 9 / 4 → |s.im| ≤ 7 → ¬ IsNontrivialZero s →
    ‖deriv (logDeriv RvMBridge18.xi) s + ∑ ρ ∈ window s, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2‖ ≤ K :=
  target_bound_low
