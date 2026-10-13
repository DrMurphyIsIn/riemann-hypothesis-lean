/-
  ZhuSplit -- the envelope step of Zhu's frequency split, eq. (4) (arXiv:2608.24827 Section 4),
  on the rvm_bridge island (2026-09-23).

  On [T#, ∞) Zhu uses Lemma 3.1 plus the trivial comb bound P_L(t) <= A_L to get
      Psi_L(t) >= log(t/2pi) - 1/t - A_L >= beta*,
  the last step because the middle expression is increasing in t.  `weilSymbol_ge_betaStar` is
  exactly that inequality, with the envelope taken from ZhuEnvelope and the comb bound proved here
  (the comb is a finite sum with nonnegative coefficients, so P_L(t) <= P_L(0) = A_L).  Together
  with `symbolRepresentation` this is what makes eq. (4) provable; the split itself (evenness of
  |F|^2 Psi_L and the half-line Parseval) is not assembled on this branch.  Nothing about zeros.
  No `sorry`.  conjecture1_proved = False.
-/
import ZhuEnvelope
import ZhuLegendre

open MeasureTheory

noncomputable section

namespace RvMBridgeZhu
open WeilWindow

/-- The prime comb is bounded by its mass: `P_L(t) ≤ A_L` (Zhu Lemma 3.2, the trivial half). -/
theorem comb_le_combMass (L t : ℝ) :
    (∑' n : ℕ, if Real.log n < 2 * L then
        2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * Real.cos (t * Real.log n) else 0)
      ≤ combMass L := by
  set N0 : ℕ := ⌈Real.exp (2 * L)⌉₊ + 1 with hN0
  have hbig : ∀ n : ℕ, n ∉ Finset.range N0 → ¬ Real.log n < 2 * L := by
    intro n hn hlt
    have hn' : N0 ≤ n := by simpa [Finset.mem_range] using hn
    have h1 : Real.exp (2 * L) < (n : ℝ) := by
      have := Nat.le_ceil (Real.exp (2 * L))
      have h2 : ((⌈Real.exp (2 * L)⌉₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'
      push_cast at h2
      linarith
    have h3 : 2 * L < Real.log n := by
      rw [← Real.log_exp (2 * L)]
      exact Real.log_lt_log (Real.exp_pos _) h1
    linarith
  unfold combMass
  rw [tsum_eq_sum (s := Finset.range N0) (fun n hn => by rw [if_neg (hbig n hn)]),
    tsum_eq_sum (s := Finset.range N0) (fun n hn => by rw [if_neg (hbig n hn)])]
  refine Finset.sum_le_sum fun n _ => ?_
  split_ifs with h
  · have hc : 0 ≤ 2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
      have := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      positivity
    calc 2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * Real.cos (t * Real.log n)
        ≤ 2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * 1 :=
          mul_le_mul_of_nonneg_left (Real.cos_le_one _) hc
      _ = 2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n := mul_one _
  · exact le_rfl

/-- The envelope step of eq. (4): for `15/4 ≤ T# ≤ t`, `Ψ_L(t) ≥ β*(L, T#)`. -/
theorem weilSymbol_ge_betaStar {L Tsharp t : ℝ} (hT : 15 / 4 ≤ Tsharp) (ht : Tsharp ≤ t) :
    betaStar L Tsharp ≤ weilSymbol L t := by
  have henv := envelopeBound t (hT.trans ht)
  have hcomb := comb_le_combMass L t
  have hT0 : 0 < Tsharp := by linarith
  have hlog : Real.log (Tsharp / (2 * Real.pi)) ≤ Real.log (t / (2 * Real.pi)) :=
    Real.log_le_log (by positivity) (by gcongr)
  have hinv : 1 / t ≤ 1 / Tsharp := one_div_le_one_div_of_le hT0 ht
  unfold betaStar weilSymbol
  linarith

end RvMBridgeZhu

end
