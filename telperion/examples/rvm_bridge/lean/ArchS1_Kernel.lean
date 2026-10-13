/-
  ArchS1_Kernel -- the archimedean Dirichlet kernel k (2026-10-11, stage S1 of
  telperion/docs/ARCHIMEDEAN_CONCEPTUAL_BLUEPRINT_2026-10-11.md).

      k(u) = sum_{n >= 0} e^{-(2n + 1/2)|u|} = e^{3|u|/2} / (e^{2|u|} - 1)      (u ≠ 0)

  The abscissae kb n = 2n + 1/2 are the Lorentzian abscissae of the vertical-line digamma series
  at a = 1/4 (E6Bridge32: kb 0 = 1/2 is the a-term, kb (n+1) = bN n).  In Lean the closed form
  archK is total and equals the tsum at EVERY u (at u = 0 both are 0: the series diverges and
  the denominator vanishes).  archK is also CC's tau(e^{|u|}) (arXiv 2006.13771, (39)):
  e^{u/2}/2 * (1/(1 + e^u) + 1/(e^u - 1)) = archK u for u > 0.

  No zeros, no RH progress.  conjecture1_proved = False.
-/
import E6Bridge32

open MeasureTheory Filter Topology

noncomputable section

namespace ArchS1
open RvMBridge32

/-! ## A. The abscissae and the truncated kernels. -/

/-- kb n = 2n + 1/2. -/
def kb (n : ℕ) : ℝ := 2 * n + 1 / 2

lemma kb_pos (n : ℕ) : 0 < kb n := by unfold kb; positivity

lemma kb_zero : kb 0 = 1 / 2 := by unfold kb; norm_num

lemma kb_succ (n : ℕ) : kb (n + 1) = bN n := by unfold kb bN; push_cast; ring

/-- The truncated kernel k_N(u) = sum_{n<N} e^{-(2n+1/2)|u|}. -/
def kTrunc (N : ℕ) (u : ℝ) : ℝ := ∑ n ∈ Finset.range N, expK (kb n) u

lemma kTrunc_nonneg (N : ℕ) (u : ℝ) : 0 ≤ kTrunc N u :=
  Finset.sum_nonneg fun _ _ => expK_nonneg _ _

lemma kTrunc_succ_le (N : ℕ) (u : ℝ) : kTrunc N u ≤ kTrunc (N + 1) u := by
  unfold kTrunc
  rw [Finset.sum_range_succ]
  linarith [expK_nonneg (kb N) u]

lemma kTrunc_mono (u : ℝ) : Monotone fun N => kTrunc N u :=
  monotone_nat_of_le_succ fun N => kTrunc_succ_le N u

/-- k_{N+1} = e^{-|u|/2} + sum_{n<N} e^{-b_n |u|}, in E6Bridge32's abscissae. -/
lemma kTrunc_succ_eq (N : ℕ) (u : ℝ) :
    kTrunc (N + 1) u = expK (1 / 2) u + ∑ n ∈ Finset.range N, expK (bN n) u := by
  unfold kTrunc
  rw [Finset.sum_range_succ', kb_zero, add_comm]
  congr 1
  exact Finset.sum_congr rfl fun n _ => by rw [kb_succ]

/-! ## B. The closed form. -/

/-- k(u) = e^{3|u|/2} / (e^{2|u|} - 1). -/
def archK (u : ℝ) : ℝ := Real.exp (3 / 2 * |u|) / (Real.exp (2 * |u|) - 1)

lemma archK_zero : archK 0 = 0 := by simp [archK]

lemma archK_nonneg (u : ℝ) : 0 ≤ archK u := by
  unfold archK
  have : 1 ≤ Real.exp (2 * |u|) := Real.one_le_exp (by positivity)
  exact div_nonneg (Real.exp_pos _).le (by linarith)

lemma archK_neg (u : ℝ) : archK (-u) = archK u := by simp [archK]

lemma measurable_archK : Measurable archK := by
  unfold archK
  exact (by fun_prop : Continuous fun u : ℝ => Real.exp (3 / 2 * |u|)).measurable.div
    (by fun_prop : Continuous fun u : ℝ => Real.exp (2 * |u|) - 1).measurable

lemma expK_kb_eq (n : ℕ) (u : ℝ) :
    expK (kb n) u = Real.exp (-(1 / 2) * |u|) * Real.exp (-2 * |u|) ^ n := by
  unfold expK kb
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

/-- THE CLOSED FORM: for u ≠ 0 the series sum_n e^{-(2n+1/2)|u|} converges to archK u. -/
theorem hasSum_archK {u : ℝ} (hu : u ≠ 0) : HasSum (fun n : ℕ => expK (kb n) u) (archK u) := by
  have hau : 0 < |u| := abs_pos.mpr hu
  have hr0 : 0 ≤ Real.exp (-2 * |u|) := (Real.exp_pos _).le
  have hr1 : Real.exp (-2 * |u|) < 1 := (Real.exp_lt_exp.mpr (by linarith : -2 * |u| < 0)).trans_eq Real.exp_zero
  have h := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (Real.exp (-(1 / 2) * |u|))
  have e : (fun n : ℕ => expK (kb n) u)
      = fun n => Real.exp (-(1 / 2) * |u|) * Real.exp (-2 * |u|) ^ n := funext fun n => expK_kb_eq n u
  rw [e]
  have hE : Real.exp (2 * |u|) * Real.exp (-2 * |u|) = 1 := by
    rw [← Real.exp_add]; simp
  have hF : Real.exp (3 / 2 * |u|) = Real.exp (2 * |u|) * Real.exp (-(1 / 2) * |u|) := by
    rw [← Real.exp_add]; congr 1; ring
  have hD : Real.exp (2 * |u|) - 1 = Real.exp (2 * |u|) * (1 - Real.exp (-2 * |u|)) := by
    rw [mul_sub, hE, mul_one]
  have hv : archK u = Real.exp (-(1 / 2) * |u|) * (1 - Real.exp (-2 * |u|))⁻¹ := by
    unfold archK
    rw [hF, hD, mul_div_mul_left _ _ (Real.exp_pos _).ne', div_eq_mul_inv]
  rw [hv]
  exact h

/-- archK is the tsum of the series at every u (both sides vanish at u = 0). -/
theorem tsum_expK_kb (u : ℝ) : ∑' n : ℕ, expK (kb n) u = archK u := by
  rcases eq_or_ne u 0 with rfl | hu
  · rw [archK_zero]
    apply tsum_eq_zero_of_not_summable
    intro hs
    have h1 : ∀ n : ℕ, expK (kb n) 0 = 1 := fun n => by simp [expK]
    have := hs.tendsto_atTop_zero
    simp only [h1] at this
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds this)
  · exact (hasSum_archK hu).tsum_eq

/-- k_N ↑ k pointwise off the diagonal. -/
theorem tendsto_kTrunc {u : ℝ} (hu : u ≠ 0) :
    Tendsto (fun N => kTrunc N u) atTop (𝓝 (archK u)) :=
  (hasSum_archK hu).tendsto_sum_nat

lemma kTrunc_le_archK {u : ℝ} (hu : u ≠ 0) (N : ℕ) : kTrunc N u ≤ archK u :=
  (kTrunc_mono u).ge_of_tendsto (tendsto_kTrunc hu) N

/-- CC's tau(e^{|u|}) (arXiv 2006.13771, (39)) is archK: for u > 0,
e^{u/2}/2 * (1/(1 + e^u) + 1/(e^u - 1)) = e^{3u/2}/(e^{2u} - 1). -/
theorem archK_eq_tau {u : ℝ} (hu : 0 < u) :
    archK u = Real.exp (u / 2) / 2 * (1 / (1 + Real.exp u) + 1 / (Real.exp u - 1)) := by
  unfold archK
  rw [abs_of_pos hu]
  have hx : 1 < Real.exp u := Real.one_lt_exp_iff.mpr hu
  have h2 : Real.exp (2 * u) = Real.exp u * Real.exp u := by rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp (3 / 2 * u) = Real.exp (u / 2) * Real.exp u := by
    rw [← Real.exp_add]; ring_nf
  rw [h2, h3]
  generalize Real.exp u = x at hx ⊢
  generalize Real.exp (u / 2) = y
  have hx1 : x - 1 ≠ 0 := by linarith
  have hx2 : 1 + x ≠ 0 := by linarith
  have hx3 : x * x - 1 ≠ 0 := by nlinarith
  rw [div_add_div _ _ hx2 hx1, show 1 * (x - 1) + (1 + x) * 1 = 2 * x by ring,
    show (1 + x) * (x - 1) = x * x - 1 by ring]
  field_simp

end ArchS1
