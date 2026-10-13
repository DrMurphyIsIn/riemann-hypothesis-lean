/-
  ZhuTail -- the eq. (13) tail data of Zhu's window reduction PROVED in the kernel with crude
  explicit constants (rvm_bridge island, 2026-09-23; lead's brief of the same day).

  Zhu evaluates the tail-block deviation eps_D and the leading-tail coupling norm eps_B numerically
  (both < 1e-100 in the certified run).  The node only needs eps_D + eps_B < beta*, so ANY proved
  bound that is small enough will do.  This module proves, for every L > 0, T# >= 1, N >= 1 with
  the cut e L T#/2 <= 2N:
      LegendreLocalization    L T# N (epsDfun L T# N)    (epsBfun L T# N)
      LegendreLocalizationOdd L T# N (epsDfunOdd L T# N) (epsBfunOdd L T# N)
  with closed forms
      b_N   = 2 sqrt L (N+1) (T# L)^{2N} / (4N+1)!!                 (even tail majorant, eq. 6 + 12)
      K     = 2 cosh(L/2)^2 + T# S / pi,  S = symbolSup L T#        (entry constant)
      U     = (1 + 2L)/2                                           (uniform head bound, from int T_n^2 = 1)
      eps_D = (10/7) K b_N^2,   eps_B = (10/7 + N) K U b_N.
  Ingredients: |Psi_L - beta*| <= S on [0, T#] (psiR monotone between psiR(0) >= -4.2315 and the
  Stirling upper bound at T#, plus |P_L| <= A_L); every entry of M_R - beta* I is bounded by
  K B_k B_j with B = tail majorant (modes above the cut) or U (below); the majorant ratio
  b_{j+1}/b_j <= 3/10 for j >= N under the cut (double-factorial growth beats (T# L)^2, e > 2.718),
  so Gershgorin rows and Schur sums are dominated by geometric series.
  Nothing about zeros.  No `sorry`.  conjecture1_proved = False.
-/
import ZhuOrtho
import ZhuSplit

open MeasureTheory intervalIntegral
open scoped Nat

/-! ## A. Registry-facing definitions (namespace WeilWindow, mirrored verbatim into RHDefs). -/

namespace WeilWindow

/-- A crude explicit bound for `sup_{0 ≤ t ≤ T#} |Ψ_L(t) - β*|`: `Re ψ(1/4 + it/2)` lies between
    `ψ(1/4) ≥ -4.2315` and its Stirling upper bound at `T#`, `|P_L| ≤ A_L`. -/
noncomputable def symbolSup (L Tsharp : ℝ) : ℝ :=
  8463 / 2000 + (Real.log (Tsharp / 2) + 13 / Tsharp ^ 2) + Real.log Real.pi + combMass L
    + |betaStar L Tsharp|

/-- The tail majorant of the even modes: `b_j = 2 sqrt L (j+1) (T# L)^{2j} / (4j+1)!!` bounds
    `|T̂_{2j}(t)|` on `[0, T#]` and `|p_{2j}| / cosh(L/2)`. -/
noncomputable def tailMajorant (L Tsharp : ℝ) (j : ℕ) : ℝ :=
  2 * Real.sqrt L * ((j : ℝ) + 1) * ((Tsharp * L) ^ (2 * j) / ((2 * (2 * j) + 1)‼ : ℕ))

/-- The tail majorant of the odd modes: `2 sqrt L (j+2) (T# L)^{2j+1} / (4j+3)!!`. -/
noncomputable def tailMajorantOdd (L Tsharp : ℝ) (j : ℕ) : ℝ :=
  2 * Real.sqrt L * ((j : ℝ) + 2) * ((Tsharp * L) ^ (2 * j + 1) / ((2 * (2 * j + 1) + 1)‼ : ℕ))

/-- The entry constant `K = 2 cosh(L/2)² + T# S / π`: `|M_R(k,j) - β* δ_kj| ≤ K B_k B_j`. -/
noncomputable def entryConst (L Tsharp : ℝ) : ℝ :=
  2 * Real.cosh (L / 2) ^ 2 + Tsharp * symbolSup L Tsharp / Real.pi

/-- The proved tail-block deviation, even sector: `eps_D = (10/7) K b_N²`. -/
noncomputable def epsDfun (L Tsharp : ℝ) (N : ℕ) : ℝ :=
  (10 / 7) * entryConst L Tsharp * tailMajorant L Tsharp N ^ 2

/-- The proved coupling norm, even sector: `eps_B = (10/7 + N) K ((1+2L)/2) b_N`. -/
noncomputable def epsBfun (L Tsharp : ℝ) (N : ℕ) : ℝ :=
  (10 / 7 + (N : ℝ)) * entryConst L Tsharp * ((1 + 2 * L) / 2) * tailMajorant L Tsharp N

/-- The proved tail-block deviation, odd sector. -/
noncomputable def epsDfunOdd (L Tsharp : ℝ) (N : ℕ) : ℝ :=
  (10 / 7) * entryConst L Tsharp * tailMajorantOdd L Tsharp N ^ 2

/-- The proved coupling norm, odd sector. -/
noncomputable def epsBfunOdd (L Tsharp : ℝ) (N : ℕ) : ℝ :=
  (10 / 7 + (N : ℝ)) * entryConst L Tsharp * ((1 + 2 * L) / 2) * tailMajorantOdd L Tsharp N

end WeilWindow

noncomputable section

namespace RvMBridgeZhu
open WeilWindow RvMBridge11 RvMBridge30

/-! ## B. The symbol is bounded on `[0, T#]`. -/

/-- The Stirling UPPER bound: `Re ψ(1/4 + it/2) ≤ log(t/2) + 13/t²` for `t ≥ 1`. -/
lemma psiR_le_stirling {t : ℝ} (ht : 1 ≤ t) : psiR t ≤ Real.log (t / 2) + 13 / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  set w : ℂ := 1 / 4 + ((t : ℂ) / 2) * Complex.I with hw
  have hwre : w.re = 1 / 4 := by simp [hw]
  have hwim : w.im = t / 2 := by simp [hw]
  have hpsi : psiR t = (Complex.digamma w).re := rfl
  have hst := Zeta23.StirlingVert.digamma_stirling (w := w) (by rw [hwre]; norm_num)
    (by rw [hwim, abs_of_pos (by linarith)]; linarith)
  rw [hwim] at hst
  have hrem : (Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w).re ≤ 3 / (t / 2) ^ 2 := by
    have h1 := Complex.abs_re_le_norm (Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w)
    exact (le_abs_self _).trans (h1.trans hst)
  have hlog : (Complex.log w).re ≤ Real.log (t / 2) + 1 / (8 * t ^ 2) := by
    rw [Complex.log_re]
    have hn : ‖w‖ ^ 2 = 1 / 16 + t ^ 2 / 4 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hwre, hwim]; ring
    have hpos : 0 < ‖w‖ := norm_pos_iff.mpr (fun h => by rw [h] at hwre; simp at hwre)
    have e : Real.log ‖w‖ = (1 / 2) * Real.log (‖w‖ ^ 2) := by
      rw [Real.log_pow]; push_cast; ring
    rw [e, hn, show (1 : ℝ) / 16 + t ^ 2 / 4 = (t / 2) ^ 2 * (1 + 1 / (4 * t ^ 2)) by field_simp; ring,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have hl : Real.log (1 + 1 / (4 * t ^ 2)) ≤ 1 / (4 * t ^ 2) := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / (4 * t ^ 2))
      linarith
    have h8 : (1 : ℝ) / (8 * t ^ 2) = (1 / 2) * (1 / (4 * t ^ 2)) := by ring
    push_cast
    linarith
  have hinv : 0 ≤ ((1 / 2 : ℂ) / w).re := by
    rw [Complex.div_re, Complex.normSq_apply, hwre, hwim]
    simp
    positivity
  have hsplit : (Complex.digamma w).re
      = (Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w).re
        + (Complex.log w).re - ((1 / 2 : ℂ) / w).re := by
    simp only [Complex.add_re, Complex.sub_re]; ring
  have h3 : 3 / (t / 2) ^ 2 + 1 / (8 * t ^ 2) ≤ 13 / t ^ 2 := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg t]
  rw [hpsi, hsplit]
  linarith

/-- The comb is bounded below by `-A_L`. -/
theorem comb_ge_neg_combMass (L t : ℝ) :
    -combMass L ≤ ∑' n : ℕ, if Real.log n < 2 * L then
        2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * Real.cos (t * Real.log n) else 0 := by
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
    tsum_eq_sum (s := Finset.range N0) (fun n hn => by rw [if_neg (hbig n hn)]), ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun n _ => ?_
  split_ifs with h
  · have hc : 0 ≤ 2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
      have := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      positivity
    have := Real.neg_one_le_cos (t * Real.log n)
    nlinarith
  · simp

lemma combMass_nonneg (L : ℝ) : 0 ≤ combMass L := by
  have h1 := comb_le_combMass L 0
  have h2 := comb_ge_neg_combMass L 0
  linarith

/-- `|Ψ_L(t) - β*| ≤ symbolSup L T#` for `0 ≤ t ≤ T#`, `T# ≥ 1`. -/
theorem abs_weilSymbol_sub_betaStar_le {L T t : ℝ} (hT : 1 ≤ T) (ht0 : 0 ≤ t) (htT : t ≤ T) :
    |weilSymbol L t - betaStar L T| ≤ symbolSup L T := by
  have hlow : psiR 0 ≤ psiR t := psiR_mono le_rfl (by rw [abs_of_nonneg ht0]; exact ht0)
  have hup : psiR t ≤ psiR T := psiR_mono ht0 (by rw [abs_of_nonneg (by linarith)]; exact htT)
  have hfl := psiR_floor_0
  have hst := psiR_le_stirling hT
  have hc1 := comb_le_combMass L t
  have hc2 := comb_ge_neg_combMass L t
  have hpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlogT : -1 ≤ Real.log (T / 2) := by
    have : Real.log (1 / 2) ≤ Real.log (T / 2) := Real.log_le_log (by norm_num) (by linarith)
    have h2 : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
    have := Real.log_two_lt_d9
    linarith
  have h13 : 0 < 13 / T ^ 2 := by positivity
  have hnn : 0 ≤ Real.log (T / 2) + 13 / T ^ 2 := by
    rcases le_or_gt 2 T with h2 | h2
    · have : 0 ≤ Real.log (T / 2) := Real.log_nonneg (by linarith)
      linarith
    · have : (13 : ℝ) / 4 ≤ 13 / T ^ 2 := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
      linarith
  have hpsi : psiR t = (Complex.digamma (1 / 4 + ((t : ℂ) / 2) * Complex.I)).re := rfl
  unfold weilSymbol symbolSup
  rw [← hpsi]
  set P := ∑' n : ℕ, if Real.log n < 2 * L then
      2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * Real.cos (t * Real.log n) else 0
  have hb1 := neg_abs_le (betaStar L T)
  have hb2 := le_abs_self (betaStar L T)
  rw [abs_le]
  constructor <;> linarith

/-! ## C. Entry bounds. -/

/-- `|C_{nm}| ≤ (T# S / π) B_n B_m` from pointwise bounds on the two transforms on `[0, T#]`. -/
theorem combMatrix_abs_le {L T : ℝ} (hT : 1 ≤ T) {n m : ℕ} {Bn Bm : ℝ}
    (hn : ∀ t ∈ Set.Icc (0 : ℝ) T, |legendreModeFT L n t| ≤ Bn)
    (hm : ∀ t ∈ Set.Icc (0 : ℝ) T, |legendreModeFT L m t| ≤ Bm) :
    |combMatrix L T n m| ≤ T * symbolSup L T / Real.pi * (Bn * Bm) := by
  unfold combMatrix
  have hBn : 0 ≤ Bn := (abs_nonneg _).trans (hn 0 ⟨le_rfl, by linarith⟩)
  have hBm : 0 ≤ Bm := (abs_nonneg _).trans (hm 0 ⟨le_rfl, by linarith⟩)
  have hS : 0 ≤ symbolSup L T := (abs_nonneg _).trans (abs_weilSymbol_sub_betaStar_le hT le_rfl (by linarith))
  have hI : ‖∫ t in (0 : ℝ)..T, (weilSymbol L t - betaStar L T) * (legendreModeFT L n t * legendreModeFT L m t)‖
      ≤ symbolSup L T * (Bn * Bm) * |T - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [Set.uIoc_of_le (by linarith)] at ht
    have ht' : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have h1 := abs_weilSymbol_sub_betaStar_le (L := L) hT ht'.1 ht'.2
    have h2 := hn t ht'
    have h3 := hm t ht'
    exact mul_le_mul h1 (mul_le_mul h2 h3 (abs_nonneg _) hBn) (by positivity) hS
  have hTpos : (0 : ℝ) < T := by linarith
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos hTpos] at hI
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
  have hpi := Real.pi_pos
  calc 1 / Real.pi * |∫ t in (0 : ℝ)..T, (weilSymbol L t - betaStar L T) * (legendreModeFT L n t * legendreModeFT L m t)|
      ≤ 1 / Real.pi * (symbolSup L T * (Bn * Bm) * T) := mul_le_mul_of_nonneg_left hI (by positivity)
    _ = T * symbolSup L T / Real.pi * (Bn * Bm) := by field_simp

theorem combMatrixOdd_abs_le {L T : ℝ} (hT : 1 ≤ T) {n m : ℕ} {Bn Bm : ℝ}
    (hn : ∀ t ∈ Set.Icc (0 : ℝ) T, |legendreModeFTs L n t| ≤ Bn)
    (hm : ∀ t ∈ Set.Icc (0 : ℝ) T, |legendreModeFTs L m t| ≤ Bm) :
    |combMatrixOdd L T n m| ≤ T * symbolSup L T / Real.pi * (Bn * Bm) := by
  unfold combMatrixOdd
  have hBn : 0 ≤ Bn := (abs_nonneg _).trans (hn 0 ⟨le_rfl, by linarith⟩)
  have hBm : 0 ≤ Bm := (abs_nonneg _).trans (hm 0 ⟨le_rfl, by linarith⟩)
  have hS : 0 ≤ symbolSup L T := (abs_nonneg _).trans (abs_weilSymbol_sub_betaStar_le hT le_rfl (by linarith))
  have hI : ‖∫ t in (0 : ℝ)..T, (weilSymbol L t - betaStar L T) * (legendreModeFTs L n t * legendreModeFTs L m t)‖
      ≤ symbolSup L T * (Bn * Bm) * |T - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [Set.uIoc_of_le (by linarith)] at ht
    have ht' : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have h1 := abs_weilSymbol_sub_betaStar_le (L := L) hT ht'.1 ht'.2
    have h2 := hn t ht'
    have h3 := hm t ht'
    exact mul_le_mul h1 (mul_le_mul h2 h3 (abs_nonneg _) hBn) (by positivity) hS
  have hTpos : (0 : ℝ) < T := by linarith
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos hTpos] at hI
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
  have hpi := Real.pi_pos
  calc 1 / Real.pi * |∫ t in (0 : ℝ)..T, (weilSymbol L t - betaStar L T) * (legendreModeFTs L n t * legendreModeFTs L m t)|
      ≤ 1 / Real.pi * (symbolSup L T * (Bn * Bm) * T) := mul_le_mul_of_nonneg_left hI (by positivity)
    _ = T * symbolSup L T / Real.pi * (Bn * Bm) := by field_simp

/-- The entry bound, even sector: pointwise bounds `B_k`, `B_j` on the transforms (on `[0,T#]`) and
`cosh(L/2) B` on the pole entries give `|M_R(k,j) - β* δ| ≤ K B_k B_j`. -/
theorem reducedMat_entry_abs_le {L T : ℝ} (hT : 1 ≤ T) {k j : ℕ} {Bk Bj : ℝ}
    (hk : ∀ t ∈ Set.Icc (0 : ℝ) T, |legendreModeFT L (2 * k) t| ≤ Bk)
    (hj : ∀ t ∈ Set.Icc (0 : ℝ) T, |legendreModeFT L (2 * j) t| ≤ Bj)
    (hpk : |poleVec L (2 * k)| ≤ Real.cosh (L / 2) * Bk)
    (hpj : |poleVec L (2 * j)| ≤ Real.cosh (L / 2) * Bj) :
    |reducedMat L T k j - (if k = j then betaStar L T else 0)| ≤ entryConst L T * Bk * Bj := by
  have hBk : 0 ≤ Bk := (abs_nonneg _).trans (hk 0 ⟨le_rfl, by linarith⟩)
  have hBj : 0 ≤ Bj := (abs_nonneg _).trans (hj 0 ⟨le_rfl, by linarith⟩)
  have hC := combMatrix_abs_le hT hk hj
  have hcosh := Real.cosh_pos (L / 2)
  have e : reducedMat L T k j - (if k = j then betaStar L T else 0)
      = 2 * poleVec L (2 * k) * poleVec L (2 * j) + combMatrix L T (2 * k) (2 * j) := by
    unfold reducedMat; ring
  rw [e]
  calc |2 * poleVec L (2 * k) * poleVec L (2 * j) + combMatrix L T (2 * k) (2 * j)|
      ≤ |2 * poleVec L (2 * k) * poleVec L (2 * j)| + |combMatrix L T (2 * k) (2 * j)| := abs_add_le _ _
    _ ≤ 2 * (Real.cosh (L / 2) * Bk) * (Real.cosh (L / 2) * Bj) + T * symbolSup L T / Real.pi * (Bk * Bj) := by
        gcongr
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        gcongr
    _ = entryConst L T * Bk * Bj := by unfold entryConst; ring

theorem reducedMatOdd_entry_abs_le {L T : ℝ} (hT : 1 ≤ T) {k j : ℕ} {Bk Bj : ℝ}
    (hk : ∀ t ∈ Set.Icc (0 : ℝ) T, |legendreModeFTs L (2 * k + 1) t| ≤ Bk)
    (hj : ∀ t ∈ Set.Icc (0 : ℝ) T, |legendreModeFTs L (2 * j + 1) t| ≤ Bj)
    (hpk : |poleVecOdd L (2 * k + 1)| ≤ Real.cosh (L / 2) * Bk)
    (hpj : |poleVecOdd L (2 * j + 1)| ≤ Real.cosh (L / 2) * Bj) :
    |reducedMatOdd L T k j - (if k = j then betaStar L T else 0)| ≤ entryConst L T * Bk * Bj := by
  have hBk : 0 ≤ Bk := (abs_nonneg _).trans (hk 0 ⟨le_rfl, by linarith⟩)
  have hBj : 0 ≤ Bj := (abs_nonneg _).trans (hj 0 ⟨le_rfl, by linarith⟩)
  have hC := combMatrixOdd_abs_le hT hk hj
  have hcosh := Real.cosh_pos (L / 2)
  have e : reducedMatOdd L T k j - (if k = j then betaStar L T else 0)
      = -(2 * poleVecOdd L (2 * k + 1) * poleVecOdd L (2 * j + 1)) + combMatrixOdd L T (2 * k + 1) (2 * j + 1) := by
    unfold reducedMatOdd; ring
  rw [e]
  calc |-(2 * poleVecOdd L (2 * k + 1) * poleVecOdd L (2 * j + 1)) + combMatrixOdd L T (2 * k + 1) (2 * j + 1)|
      ≤ |-(2 * poleVecOdd L (2 * k + 1) * poleVecOdd L (2 * j + 1))| + |combMatrixOdd L T (2 * k + 1) (2 * j + 1)| :=
        abs_add_le _ _
    _ ≤ 2 * (Real.cosh (L / 2) * Bk) * (Real.cosh (L / 2) * Bj) + T * symbolSup L T / Real.pi * (Bk * Bj) := by
        gcongr
        rw [abs_neg, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        gcongr
    _ = entryConst L T * Bk * Bj := by unfold entryConst; ring

/-! ## D. The tail majorants: bounds, ratio, monotonicity. -/

lemma sqrt_le_succ (L : ℝ) (j : ℕ) :
    Real.sqrt (L * ((2 * j : ℕ) + 1 / 2)) ≤ Real.sqrt L * ((j : ℝ) + 1) := by
  rcases le_or_gt L 0 with hL | hL
  · rw [Real.sqrt_eq_zero'.mpr (by push_cast; nlinarith), Real.sqrt_eq_zero'.mpr hL]; simp
  rw [Real.sqrt_mul hL.le]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  push_cast
  nlinarith [sq_nonneg (j : ℝ)]

lemma sqrt_le_succ_odd (L : ℝ) (j : ℕ) :
    Real.sqrt (L * ((2 * j + 1 : ℕ) + 1 / 2)) ≤ Real.sqrt L * ((j : ℝ) + 2) := by
  rcases le_or_gt L 0 with hL | hL
  · rw [Real.sqrt_eq_zero'.mpr (by push_cast; nlinarith), Real.sqrt_eq_zero'.mpr hL]; simp
  rw [Real.sqrt_mul hL.le]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  push_cast
  nlinarith [sq_nonneg (j : ℝ)]

lemma tailMajorant_nonneg {L T : ℝ} (hL : 0 < L) (hT : 0 ≤ T) (j : ℕ) : 0 ≤ tailMajorant L T j := by
  unfold tailMajorant; positivity

lemma tailMajorantOdd_nonneg {L T : ℝ} (hL : 0 < L) (hT : 0 ≤ T) (j : ℕ) : 0 ≤ tailMajorantOdd L T j := by
  unfold tailMajorantOdd; positivity

/-- On `[0, T#]` the even-mode transform is bounded by the tail majorant. -/
theorem legendreModeFT_le_tailMajorant {L T : ℝ} (hL : 0 < L) (hT : 0 ≤ T) (j : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) : |legendreModeFT L (2 * j) t| ≤ tailMajorant L T j := by
  refine (legendreModeFT_abs_le hL j ht.1).trans ?_
  unfold tailMajorant
  have hpow : (t * L) ^ (2 * j) ≤ (T * L) ^ (2 * j) :=
    pow_le_pow_left₀ (by nlinarith [ht.1]) (by nlinarith [ht.2]) _
  have hs := sqrt_le_succ L j
  have hpos : (0 : ℝ) < ((2 * (2 * j) + 1)‼ : ℕ) := by exact_mod_cast Nat.doubleFactorial_pos _
  have h0 : 0 ≤ (t * L) ^ (2 * j) / ((2 * (2 * j) + 1)‼ : ℕ) :=
    div_nonneg (pow_nonneg (mul_nonneg ht.1 hL.le) _) hpos.le
  calc 2 * Real.sqrt (L * ((2 * j : ℕ) + 1 / 2)) * ((t * L) ^ (2 * j) / ((2 * (2 * j) + 1)‼ : ℕ))
      ≤ 2 * (Real.sqrt L * ((j : ℝ) + 1)) * ((T * L) ^ (2 * j) / ((2 * (2 * j) + 1)‼ : ℕ)) :=
        mul_le_mul (by gcongr) (div_le_div_of_nonneg_right hpow hpos.le) h0 (by positivity)
    _ = _ := by ring

theorem legendreModeFTs_le_tailMajorantOdd {L T : ℝ} (hL : 0 < L) (hT : 0 ≤ T) (j : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) : |legendreModeFTs L (2 * j + 1) t| ≤ tailMajorantOdd L T j := by
  refine (legendreModeFTs_abs_le hL j ht.1).trans ?_
  unfold tailMajorantOdd
  have hpow : (t * L) ^ (2 * j + 1) ≤ (T * L) ^ (2 * j + 1) :=
    pow_le_pow_left₀ (by nlinarith [ht.1]) (by nlinarith [ht.2]) _
  have hs := sqrt_le_succ_odd L j
  have hpos : (0 : ℝ) < ((2 * (2 * j + 1) + 1)‼ : ℕ) := by exact_mod_cast Nat.doubleFactorial_pos _
  have h0 : 0 ≤ (t * L) ^ (2 * j + 1) / ((2 * (2 * j + 1) + 1)‼ : ℕ) :=
    div_nonneg (pow_nonneg (mul_nonneg ht.1 hL.le) _) hpos.le
  calc 2 * Real.sqrt (L * ((2 * j + 1 : ℕ) + 1 / 2)) * ((t * L) ^ (2 * j + 1) / ((2 * (2 * j + 1) + 1)‼ : ℕ))
      ≤ 2 * (Real.sqrt L * ((j : ℝ) + 2)) * ((T * L) ^ (2 * j + 1) / ((2 * (2 * j + 1) + 1)‼ : ℕ)) :=
        mul_le_mul (by gcongr) (div_le_div_of_nonneg_right hpow hpos.le) h0 (by positivity)
    _ = _ := by ring

/-- The pole entries are bounded by `cosh(L/2)` times the tail majorant (`T# ≥ 1/2`). -/
theorem poleVec_le_tailMajorant {L T : ℝ} (hL : 0 < L) (hT : 1 ≤ T) (j : ℕ) :
    |poleVec L (2 * j)| ≤ Real.cosh (L / 2) * tailMajorant L T j := by
  refine (poleVec_abs_le hL j).trans ?_
  unfold tailMajorant
  have hpow : (L / 2) ^ (2 * j) ≤ (T * L) ^ (2 * j) :=
    pow_le_pow_left₀ (by positivity) (by nlinarith) _
  have hs := sqrt_le_succ L j
  have hpos : (0 : ℝ) < ((2 * (2 * j) + 1)‼ : ℕ) := by exact_mod_cast Nat.doubleFactorial_pos _
  have hc := Real.cosh_pos (L / 2)
  calc 2 * Real.sqrt (L * ((2 * j : ℕ) + 1 / 2)) * Real.cosh (L / 2) * ((L / 2) ^ (2 * j) / ((2 * (2 * j) + 1)‼ : ℕ))
      ≤ 2 * (Real.sqrt L * ((j : ℝ) + 1)) * Real.cosh (L / 2) * ((T * L) ^ (2 * j) / ((2 * (2 * j) + 1)‼ : ℕ)) := by
        gcongr
    _ = _ := by ring

theorem poleVecOdd_le_tailMajorantOdd {L T : ℝ} (hL : 0 < L) (hT : 1 ≤ T) (j : ℕ) :
    |poleVecOdd L (2 * j + 1)| ≤ Real.cosh (L / 2) * tailMajorantOdd L T j := by
  refine (poleVecOdd_abs_le hL j).trans ?_
  unfold tailMajorantOdd
  have hpow : (L / 2) ^ (2 * j + 1) ≤ (T * L) ^ (2 * j + 1) :=
    pow_le_pow_left₀ (by positivity) (by nlinarith) _
  have hs := sqrt_le_succ_odd L j
  have hpos : (0 : ℝ) < ((2 * (2 * j + 1) + 1)‼ : ℕ) := by exact_mod_cast Nat.doubleFactorial_pos _
  have hc := Real.cosh_pos (L / 2)
  calc 2 * Real.sqrt (L * ((2 * j + 1 : ℕ) + 1 / 2)) * Real.cosh (L / 2) * ((L / 2) ^ (2 * j + 1) / ((2 * (2 * j + 1) + 1)‼ : ℕ))
      ≤ 2 * (Real.sqrt L * ((j : ℝ) + 2)) * Real.cosh (L / 2) * ((T * L) ^ (2 * j + 1) / ((2 * (2 * j + 1) + 1)‼ : ℕ)) := by
        gcongr
    _ = _ := by ring

/-- The cut gives `(7389/1000) (T# L)² ≤ 16 N²`. -/
lemma cut_sq {L T : ℝ} {N : ℕ} (hL : 0 < L) (hT : 0 ≤ T) (hcut : Real.exp 1 * L * T / 2 ≤ 2 * N) :
    (7389 / 1000 : ℝ) * (T * L) ^ 2 ≤ 16 * (N : ℝ) ^ 2 := by
  have he := Real.exp_one_gt_d9
  have h1 : (27182818283 / 10000000000 : ℝ) * (T * L) ≤ 4 * N := by
    have : Real.exp 1 * (T * L) ≤ 4 * N := by nlinarith
    have hTL : 0 ≤ T * L := by positivity
    nlinarith
  have hTL : 0 ≤ T * L := by positivity
  nlinarith [mul_le_mul h1 h1 (by positivity) (by positivity)]

/-- The ratio bound for the even majorant above the cut. -/
theorem tailMajorant_succ_le {L T : ℝ} {N : ℕ} (hL : 0 < L) (hT : 0 ≤ T) (hN : 1 ≤ N)
    (hcut : Real.exp 1 * L * T / 2 ≤ 2 * N) {j : ℕ} (hj : N ≤ j) :
    tailMajorant L T (j + 1) ≤ (3 / 10) * tailMajorant L T j := by
  unfold tailMajorant
  have hdf : ((2 * (2 * (j + 1)) + 1)‼ : ℕ) = (4 * j + 5) * ((4 * j + 3) * (2 * (2 * j) + 1)‼) := by
    rw [show 2 * (2 * (j + 1)) + 1 = (4 * j + 3) + 2 by ring, Nat.doubleFactorial_add_two,
      show 4 * j + 3 = (2 * (2 * j) + 1) + 2 by ring, Nat.doubleFactorial_add_two]
    ring
  rw [hdf]
  push_cast
  have hpos : (0 : ℝ) < ((2 * (2 * j) + 1)‼ : ℕ) := by exact_mod_cast Nat.doubleFactorial_pos _
  have hsq := cut_sq hL hT hcut
  have hjN : (N : ℝ) ≤ j := by exact_mod_cast hj
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hTL : 0 ≤ (T * L) ^ (2 * j) := by positivity
  have hsL : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  -- key polynomial inequality: (j+2)(TL)² ≤ (3/10)(j+1)(4j+3)(4j+5)
  have hkey : ((j : ℝ) + 2) * (T * L) ^ 2 ≤ (3 / 10) * (((j : ℝ) + 1) * ((4 * j + 3) * (4 * j + 5))) := by
    have h1 : (T * L) ^ 2 ≤ (16 / (7389 / 1000)) * (j : ℝ) ^ 2 := by
      have : (N : ℝ) ^ 2 ≤ (j : ℝ) ^ 2 := by gcongr
      nlinarith
    have h2 : 16 * (j : ℝ) ^ 2 ≤ (4 * j + 3) * (4 * j + 5) := by nlinarith
    have hj0 : (0 : ℝ) ≤ j := by linarith
    nlinarith [mul_nonneg hj0 (sq_nonneg (j : ℝ))]
  rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_add]
  have hDpos : (0 : ℝ) < (4 * (j : ℝ) + 5) * ((4 * (j : ℝ) + 3) * ((2 * (2 * j) + 1)‼ : ℕ)) := by positivity
  calc 2 * Real.sqrt L * ((j : ℝ) + 1 + 1) * ((T * L) ^ (2 * j) * (T * L) ^ 2
          / ((4 * (j : ℝ) + 5) * ((4 * (j : ℝ) + 3) * ((2 * (2 * j) + 1)‼ : ℕ))))
      = (2 * Real.sqrt L * (T * L) ^ (2 * j) * (((j : ℝ) + 2) * (T * L) ^ 2))
          / ((4 * (j : ℝ) + 5) * ((4 * (j : ℝ) + 3) * ((2 * (2 * j) + 1)‼ : ℕ))) := by ring
    _ ≤ (2 * Real.sqrt L * (T * L) ^ (2 * j) * ((3 / 10) * (((j : ℝ) + 1) * ((4 * j + 3) * (4 * j + 5)))))
          / ((4 * (j : ℝ) + 5) * ((4 * (j : ℝ) + 3) * ((2 * (2 * j) + 1)‼ : ℕ))) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hkey (by positivity)) hDpos.le
    _ = 3 / 10 * (2 * Real.sqrt L * ((j : ℝ) + 1) * ((T * L) ^ (2 * j) / ((2 * (2 * j) + 1)‼ : ℕ))) := by
        field_simp

theorem tailMajorantOdd_succ_le {L T : ℝ} {N : ℕ} (hL : 0 < L) (hT : 0 ≤ T) (hN : 1 ≤ N)
    (hcut : Real.exp 1 * L * T / 2 ≤ 2 * N) {j : ℕ} (hj : N ≤ j) :
    tailMajorantOdd L T (j + 1) ≤ (3 / 10) * tailMajorantOdd L T j := by
  unfold tailMajorantOdd
  have hdf : ((2 * (2 * (j + 1) + 1) + 1)‼ : ℕ) = (4 * j + 7) * ((4 * j + 5) * (2 * (2 * j + 1) + 1)‼) := by
    rw [show 2 * (2 * (j + 1) + 1) + 1 = (4 * j + 5) + 2 by ring, Nat.doubleFactorial_add_two,
      show 4 * j + 5 = (2 * (2 * j + 1) + 1) + 2 by ring, Nat.doubleFactorial_add_two]
    ring
  rw [hdf]
  push_cast
  have hpos : (0 : ℝ) < ((2 * (2 * j + 1) + 1)‼ : ℕ) := by exact_mod_cast Nat.doubleFactorial_pos _
  have hsq := cut_sq hL hT hcut
  have hjN : (N : ℝ) ≤ j := by exact_mod_cast hj
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsL : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have hkey : ((j : ℝ) + 3) * (T * L) ^ 2 ≤ (3 / 10) * (((j : ℝ) + 2) * ((4 * j + 5) * (4 * j + 7))) := by
    have h1 : (T * L) ^ 2 ≤ (16 / (7389 / 1000)) * (j : ℝ) ^ 2 := by
      have : (N : ℝ) ^ 2 ≤ (j : ℝ) ^ 2 := by gcongr
      nlinarith
    have h2 : 16 * (j : ℝ) ^ 2 ≤ (4 * j + 5) * (4 * j + 7) := by nlinarith
    have hj0 : (0 : ℝ) ≤ j := by linarith
    nlinarith [mul_nonneg hj0 (sq_nonneg (j : ℝ))]
  rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 2 by ring, pow_add]
  have hDpos : (0 : ℝ) < (4 * (j : ℝ) + 7) * ((4 * (j : ℝ) + 5) * ((2 * (2 * j + 1) + 1)‼ : ℕ)) := by positivity
  calc 2 * Real.sqrt L * ((j : ℝ) + 1 + 2) * ((T * L) ^ (2 * j + 1) * (T * L) ^ 2
          / ((4 * (j : ℝ) + 7) * ((4 * (j : ℝ) + 5) * ((2 * (2 * j + 1) + 1)‼ : ℕ))))
      = (2 * Real.sqrt L * (T * L) ^ (2 * j + 1) * (((j : ℝ) + 3) * (T * L) ^ 2))
          / ((4 * (j : ℝ) + 7) * ((4 * (j : ℝ) + 5) * ((2 * (2 * j + 1) + 1)‼ : ℕ))) := by ring
    _ ≤ (2 * Real.sqrt L * (T * L) ^ (2 * j + 1) * ((3 / 10) * (((j : ℝ) + 2) * ((4 * j + 5) * (4 * j + 7)))))
          / ((4 * (j : ℝ) + 7) * ((4 * (j : ℝ) + 5) * ((2 * (2 * j + 1) + 1)‼ : ℕ))) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hkey (by positivity)) hDpos.le
    _ = 3 / 10 * (2 * Real.sqrt L * ((j : ℝ) + 2) * ((T * L) ^ (2 * j + 1) / ((2 * (2 * j + 1) + 1)‼ : ℕ))) := by
        field_simp

/-! ## E. The generic geometric-tail lemma and the localization assembly. -/

/-- A nonnegative sequence with ratio `≤ r < 1` beyond `N` has tail sum `≤ g N / (1 - r)`. -/
theorem tail_tsum_le {g : ℕ → ℝ} {N : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hnn : ∀ j, 0 ≤ g j)
    (hratio : ∀ j, N ≤ j → g (j + 1) ≤ r * g j) :
    Summable (fun j : ℕ => if N ≤ j then g j else 0) ∧
      ∑' j : ℕ, (if N ≤ j then g j else 0) ≤ g N / (1 - r) := by
  have hgeo : ∀ i : ℕ, g (N + i) ≤ g N * r ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [← add_assoc, pow_succ]
      calc g (N + i + 1) ≤ r * g (N + i) := hratio _ (by omega)
        _ ≤ r * (g N * r ^ i) := mul_le_mul_of_nonneg_left ih hr0
        _ = g N * (r ^ i * r) := by ring
  set f : ℕ → ℝ := fun j => if N ≤ j then g j else 0 with hf
  have hf_nn : ∀ j, 0 ≤ f j := fun j => by simp only [hf]; split_ifs <;> [exact hnn j; exact le_rfl]
  have hshift : ∀ i, f (i + N) = g (N + i) := fun i => by
    simp only [hf]; rw [if_pos (by omega), add_comm]
  have hg_sum : Summable (fun i : ℕ => g N * r ^ i) := (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hs : Summable (fun i : ℕ => f (i + N)) :=
    Summable.of_nonneg_of_le (fun i => hf_nn _) (fun i => by rw [hshift]; exact hgeo i) hg_sum
  have hfs : Summable f := (summable_nat_add_iff N).mp hs
  refine ⟨hfs, ?_⟩
  have hsplit := hfs.sum_add_tsum_nat_add N
  have hzero : ∑ i ∈ Finset.range N, f i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    simp only [hf]; rw [if_neg (by simpa [Finset.mem_range] using hi)]
  rw [hzero, zero_add] at hsplit
  rw [← hsplit]
  calc ∑' i : ℕ, f (i + N) ≤ ∑' i : ℕ, g N * r ^ i :=
        hs.tsum_le_tsum (fun i => by rw [hshift]; exact hgeo i) hg_sum
    _ = g N * (1 - r)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    _ = g N / (1 - r) := by rw [div_eq_mul_inv]

/-- The abstract localization statement from entry bounds and a geometric tail majorant. -/
theorem localization_of_bounds {M : ℕ → ℕ → ℝ} {β : ℝ} {b : ℕ → ℝ} {K U : ℝ} {N : ℕ}
    (hK : 0 ≤ K) (hU : 0 ≤ U) (hb : ∀ j, 0 ≤ b j)
    (hratio : ∀ j, N ≤ j → b (j + 1) ≤ (3 / 10) * b j)
    (htail : ∀ k j, N ≤ k → N ≤ j → |M k j - (if k = j then β else 0)| ≤ K * b k * b j)
    (hmix : ∀ k j, N ≤ k → j < N → |M k j| ≤ K * b k * U) :
    (∀ k, N ≤ k →
      Summable (fun j : ℕ => if N ≤ j then |M k j - (if k = j then β else 0)| else 0) ∧
      ∑' j : ℕ, (if N ≤ j then |M k j - (if k = j then β else 0)| else 0) ≤ (10 / 7) * K * b N ^ 2) ∧
    (∀ j, j < N →
      Summable (fun k : ℕ => if N ≤ k then |M k j| else 0) ∧
      ∑' k : ℕ, (if N ≤ k then |M k j| else 0) ≤ (10 / 7 + (N : ℝ)) * K * U * b N) ∧
    (∀ k, N ≤ k → ∑ j ∈ Finset.range N, |M k j| ≤ (10 / 7 + (N : ℝ)) * K * U * b N) := by
  have hmono : ∀ k, N ≤ k → b k ≤ b N := by
    intro k hk
    induction k with
    | zero => rw [Nat.le_zero.mp hk]
    | succ k ih =>
      rcases Nat.lt_or_ge k N with h | h
      · rw [show k + 1 = N by omega]
      · calc b (k + 1) ≤ (3 / 10) * b k := hratio k h
          _ ≤ b k := by linarith [hb k]
          _ ≤ b N := ih h
  have htail_sum := tail_tsum_le (g := b) (N := N) (r := 3 / 10) (by norm_num) (by norm_num) hb hratio
  have hnorm : (1 : ℝ) - 3 / 10 = 7 / 10 := by norm_num
  rw [hnorm] at htail_sum
  have hbN := hb N
  refine ⟨fun k hk => ?_, fun j hj => ?_, fun k hk => ?_⟩
  · -- Gershgorin row
    have hle : ∀ j, (if N ≤ j then |M k j - (if k = j then β else 0)| else 0)
        ≤ (if N ≤ j then K * b k * b j else 0) := fun j => by
      rcases le_or_gt N j with h | h
      · rw [if_pos h, if_pos h]; exact htail k j hk h
      · rw [if_neg (not_le.mpr h), if_neg (not_le.mpr h)]
    have hg_sum : Summable (fun j : ℕ => if N ≤ j then K * b k * b j else 0) := by
      have := htail_sum.1.mul_left (K * b k)
      refine this.congr fun j => ?_
      split_ifs <;> simp
    have hs : Summable (fun j : ℕ => if N ≤ j then |M k j - (if k = j then β else 0)| else 0) :=
      Summable.of_nonneg_of_le (fun j => by split_ifs <;> positivity) hle hg_sum
    refine ⟨hs, ?_⟩
    calc ∑' j : ℕ, (if N ≤ j then |M k j - (if k = j then β else 0)| else 0)
        ≤ ∑' j : ℕ, (if N ≤ j then K * b k * b j else 0) := hs.tsum_le_tsum hle hg_sum
      _ = K * b k * ∑' j : ℕ, (if N ≤ j then b j else 0) := by
          rw [← tsum_mul_left]; congr 1; funext j; split_ifs <;> simp
      _ ≤ K * b k * (b N / (7 / 10)) :=
          mul_le_mul_of_nonneg_left htail_sum.2 (mul_nonneg hK (hb k))
      _ ≤ K * b N * (b N / (7 / 10)) := by gcongr; exact hmono k hk
      _ = (10 / 7) * K * b N ^ 2 := by ring
  · -- Schur column
    have hle : ∀ k, (if N ≤ k then |M k j| else 0) ≤ (if N ≤ k then K * U * b k else 0) := fun k => by
      split_ifs with h
      · have := hmix k j h hj; linarith
      · exact le_rfl
    have hg_sum : Summable (fun k : ℕ => if N ≤ k then K * U * b k else 0) := by
      have := htail_sum.1.mul_left (K * U)
      refine this.congr fun k => ?_
      split_ifs <;> simp
    have hs : Summable (fun k : ℕ => if N ≤ k then |M k j| else 0) :=
      Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity) hle hg_sum
    refine ⟨hs, ?_⟩
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    calc ∑' k : ℕ, (if N ≤ k then |M k j| else 0)
        ≤ ∑' k : ℕ, (if N ≤ k then K * U * b k else 0) := hs.tsum_le_tsum hle hg_sum
      _ = K * U * ∑' k : ℕ, (if N ≤ k then b k else 0) := by
          rw [← tsum_mul_left]; congr 1; funext k; split_ifs <;> simp
      _ ≤ K * U * (b N / (7 / 10)) := mul_le_mul_of_nonneg_left htail_sum.2 (mul_nonneg hK hU)
      _ = (10 / 7) * K * U * b N := by ring
      _ ≤ (10 / 7 + (N : ℝ)) * K * U * b N := by
          have : 0 ≤ K * U * b N := by positivity
          nlinarith
  · -- Schur row
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    calc ∑ j ∈ Finset.range N, |M k j|
        ≤ ∑ j ∈ Finset.range N, K * b k * U :=
          Finset.sum_le_sum fun j hj => hmix k j hk (Finset.mem_range.mp hj)
      _ = (N : ℝ) * (K * b k * U) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (K * b N * U) := by gcongr; exact hmono k hk
      _ ≤ (10 / 7 + (N : ℝ)) * K * U * b N := by
          have : 0 ≤ K * U * b N := by positivity
          nlinarith

/-- **The eq. (13) tail data, even sector, PROVED** for every `L > 0`, `T# ≥ 1`, `N ≥ 1` with the
cut `e L T#/2 ≤ 2N`. -/
theorem legendreLocalization_of_cut {L T : ℝ} {N : ℕ} (hL : 0 < L) (hT : 1 ≤ T) (hN : 1 ≤ N)
    (hcut : Real.exp 1 * L * T / 2 ≤ 2 * N) :
    LegendreLocalization L T N (epsDfun L T N) (epsBfun L T N) := by
  have hT0 : 0 ≤ T := by linarith
  have hS : 0 ≤ symbolSup L T :=
    (abs_nonneg _).trans (abs_weilSymbol_sub_betaStar_le hT le_rfl (by linarith))
  have hK : 0 ≤ entryConst L T := by unfold entryConst; positivity
  have hU : (0 : ℝ) ≤ (1 + 2 * L) / 2 := by positivity
  have hcosh := Real.cosh_pos (L / 2)
  have h := localization_of_bounds (M := reducedMat L T) (β := betaStar L T) (b := tailMajorant L T)
    (K := entryConst L T) (U := (1 + 2 * L) / 2) (N := N) hK hU (tailMajorant_nonneg hL hT0)
    (fun j hj => tailMajorant_succ_le hL hT0 hN hcut hj)
    (fun k j _ _ => reducedMat_entry_abs_le hT (fun t ht => legendreModeFT_le_tailMajorant hL hT0 k ht)
      (fun t ht => legendreModeFT_le_tailMajorant hL hT0 j ht) (poleVec_le_tailMajorant hL hT k)
      (poleVec_le_tailMajorant hL hT j))
    (fun k j hk hj => by
      have := reducedMat_entry_abs_le hT (fun t ht => legendreModeFT_le_tailMajorant hL hT0 k ht)
        (fun t _ => legendreModeFT_abs_le_uniform hL (2 * j) t) (poleVec_le_tailMajorant hL hT k)
        (poleVec_abs_le_uniform hL (2 * j))
      rwa [if_neg (by omega), sub_zero] at this)
  unfold LegendreLocalization epsDfun epsBfun
  exact h

/-- **The eq. (13) tail data, odd sector, PROVED** under the same hypotheses. -/
theorem legendreLocalizationOdd_of_cut {L T : ℝ} {N : ℕ} (hL : 0 < L) (hT : 1 ≤ T) (hN : 1 ≤ N)
    (hcut : Real.exp 1 * L * T / 2 ≤ 2 * N) :
    LegendreLocalizationOdd L T N (epsDfunOdd L T N) (epsBfunOdd L T N) := by
  have hT0 : 0 ≤ T := by linarith
  have hS : 0 ≤ symbolSup L T :=
    (abs_nonneg _).trans (abs_weilSymbol_sub_betaStar_le hT le_rfl (by linarith))
  have hK : 0 ≤ entryConst L T := by unfold entryConst; positivity
  have hU : (0 : ℝ) ≤ (1 + 2 * L) / 2 := by positivity
  have hcosh := Real.cosh_pos (L / 2)
  have h := localization_of_bounds (M := reducedMatOdd L T) (β := betaStar L T) (b := tailMajorantOdd L T)
    (K := entryConst L T) (U := (1 + 2 * L) / 2) (N := N) hK hU (tailMajorantOdd_nonneg hL hT0)
    (fun j hj => tailMajorantOdd_succ_le hL hT0 hN hcut hj)
    (fun k j _ _ => reducedMatOdd_entry_abs_le hT (fun t ht => legendreModeFTs_le_tailMajorantOdd hL hT0 k ht)
      (fun t ht => legendreModeFTs_le_tailMajorantOdd hL hT0 j ht) (poleVecOdd_le_tailMajorantOdd hL hT k)
      (poleVecOdd_le_tailMajorantOdd hL hT j))
    (fun k j hk hj => by
      have := reducedMatOdd_entry_abs_le hT (fun t ht => legendreModeFTs_le_tailMajorantOdd hL hT0 k ht)
        (fun t _ => legendreModeFTs_abs_le_uniform hL (2 * j + 1) t) (poleVecOdd_le_tailMajorantOdd hL hT k)
        (poleVecOdd_abs_le_uniform hL (2 * j + 1))
      rwa [if_neg (by omega), sub_zero] at this)
  unfold LegendreLocalizationOdd epsDfunOdd epsBfunOdd
  exact h

end RvMBridgeZhu

end
