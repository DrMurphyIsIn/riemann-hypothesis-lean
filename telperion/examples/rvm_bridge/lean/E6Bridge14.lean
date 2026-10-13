/-
  E6Bridge14 -- EFFECTIVE Gaussian dominance (open lemma 1 of the wall reconciliation,
  docs/WALL_ASSAULT_SEAMS_RECONCILIATION_2026-09-21.md S3), 2026-09-21.

  E6Bridge7.gaussian_dominance chooses the Gaussian parameter lam AFTER the zero configuration
  (the gap eta, the window sum A, the tail B are extracted from the zeros by existence).  This
  module carries the local data as EXPLICIT PARAMETERS and gives an EXPLICIT threshold:

      effectiveThreshold y0 xmin N B D
        = max 1 (max (log (max 1 (4 N (D^2 + 1/4) / y0^2)) / (2 xmin^2))
                     (log (max 1 (4 B / y0^2)) / (2 y0^2)))

  and proves: if rho_0 is a nontrivial zero at distance >= y0 > 0 from the line which has MAXIMAL
  distance from the line among the zeros within ordinate distance D >= 1 of it, if every other
  zero in that window at a different ordinate is at ordinate distance >= xmin > 0 (the local
  spacing floor), if the window holds at most N zeros with multiplicity, and if
  lam >= effectiveThreshold y0 xmin N (constB (Im rho_0)) D, then

      Re Sum_rho m(rho) (gamma_rho - Im rho_0)^2 exp (-2 lam (gamma_rho - Im rho_0)^2) < 0.

  The centre is c := Im rho_0 EXACTLY (no genericity): every zero at the ordinate of rho_0 has
  x = 0, so its summand is -m y^2 e^{2 lam y^2} <= 0 with the phase automatically pi
  (E6Bridge6.gaussTest_axis); rho_0 itself gives at most -Y e^{2 lam Y}, Y = (1/2 - Re rho_0)^2
  >= y0^2.  A window zero at a different ordinate has |x| >= xmin and y^2 <= Y (maximality), so
  |summand| <= m (D^2 + 1/4) e^{2 lam (Y - xmin^2)}; summed, <= N (D^2 + 1/4) e^{-2 lam xmin^2}
  e^{2 lam Y}.  The tail beyond the window is <= e^{2 (lam - 1)(1/4 - D^2)} constB c <= constB c
  (E6Bridge12.tail_bound_window).  The two log terms of the threshold make the window
  competitor and the tail each <= (y0^2/4) e^{2 lam Y}, so the total is <= -(y0^2/2) e^{2 lam Y}.

  The maximality hypothesis is the honest form of "clustering control": without it a zero at a
  nearby ordinate and larger |1/2 - beta| has a larger exponent and its summand can be positive.
  The spacing floor is load-bearing in the certificate: the threshold is unbounded as xmin -> 0
  (effectiveThreshold_unbounded_of_small_spacing).

  Also delivered: the localisation instrument offline_zeros_small_or_margin.  If the Gaussian
  functional is >= 0 for every centre in [T1, T2] and every lam >= the threshold built from
  (y0, xmin, N, Bmax, D), then EITHER every zero with ordinate in [T1 - D, T2 + D] is within y0 of
  the line, OR some zero in the margins [T1 - D, T1) or (T2, T2 + D] is at distance >= y0 (the
  zero of maximal distance over the widened band, which exists by finiteness, lies in a margin
  and the instrument cannot see it; slide the band).

  WHAT IS CONSUMED (all unconditional, #print axioms = [propext, Classical.choice, Quot.sound]):
    RvMBridge12.zeroSide_split, tail_bound_window;  RvMBridgeGauss.zeroWindow, mem_zeroWindow,
    term_eq_zero_of_not_nontrivial;  RvMBridge7.norm_term, phi, wsq, term;
    RvMBridge6.gaussTest_axis, constB_nonneg;  RvMBridge4.zeroMult_eq_mult;
    Zeta23.zetaSeam.finite_window, one_le_mult, WeilEF.gammaOf_re/gammaOf_im.

  conjecture1_proved = False: this is an unconditional inequality about a Gaussian-weighted sum
  over the zeros of zeta, wherever they are.
-/
import E6Bridge12

open Zeta23 Complex MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace RvMBridge14
open WeilExplicit RvMBridge6 RvMBridge7 RvMBridge12 RvMBridgeGauss

/-! ## A. The explicit threshold. -/

/-- The explicit lam threshold for effective Gaussian dominance with parameters
(y0 = distance floor from the line, xmin = ordinate spacing floor, N = window count,
B = tail constant, D = window half-width). -/
def effectiveThreshold (y0 xmin : ℝ) (N : ℕ) (B D : ℝ) : ℝ :=
  max 1 (max (Real.log (max 1 (4 * N * (D ^ 2 + 1 / 4) / y0 ^ 2)) / (2 * xmin ^ 2))
             (Real.log (max 1 (4 * B / y0 ^ 2)) / (2 * y0 ^ 2)))

lemma one_le_effectiveThreshold (y0 xmin : ℝ) (N : ℕ) (B D : ℝ) :
    1 ≤ effectiveThreshold y0 xmin N B D := le_max_left _ _

lemma effectiveThreshold_pos (y0 xmin : ℝ) (N : ℕ) (B D : ℝ) :
    0 < effectiveThreshold y0 xmin N B D :=
  lt_of_lt_of_le one_pos (one_le_effectiveThreshold _ _ _ _ _)

/-- log (max 1 Q) / (2 a) <= lam  implies  Q <= e^{2 lam a}. -/
lemma le_exp_of_log_le {Q a lam : ℝ} (ha : 0 < a) (h : Real.log (max 1 Q) / (2 * a) ≤ lam) :
    Q ≤ Real.exp (2 * lam * a) := by
  have hmax : 0 < max 1 Q := lt_max_of_lt_left one_pos
  have h1 : Real.log (max 1 Q) ≤ 2 * lam * a := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * a)).mp h
    linarith
  calc Q ≤ max 1 Q := le_max_right _ _
    _ = Real.exp (Real.log (max 1 Q)) := (Real.exp_log hmax).symm
    _ ≤ Real.exp (2 * lam * a) := Real.exp_le_exp.mpr h1

/-- The threshold is monotone in the tail constant. -/
lemma effectiveThreshold_mono_B {y0 xmin : ℝ} (N : ℕ) {B B' D : ℝ} (hy0 : 0 < y0)
    (hB : B ≤ B') :
    effectiveThreshold y0 xmin N B D ≤ effectiveThreshold y0 xmin N B' D := by
  unfold effectiveThreshold
  refine max_le_max le_rfl (max_le_max le_rfl ?_)
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine Real.log_le_log (lt_max_of_lt_left one_pos) (max_le_max le_rfl ?_)
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- The spacing floor is load-bearing in the certificate: for N >= 1, D >= 1, 0 < y0 <= 1/2 the
threshold exceeds any bound once xmin is small enough. -/
theorem effectiveThreshold_unbounded_of_small_spacing {y0 : ℝ} (hy0 : 0 < y0) (hy1 : y0 ≤ 1 / 2)
    {N : ℕ} (hN : 1 ≤ N) {D : ℝ} (_hD : 1 ≤ D) (B K : ℝ) :
    ∃ xmin : ℝ, 0 < xmin ∧ K ≤ effectiveThreshold y0 xmin N B D := by
  have hQ : (1 : ℝ) < 4 * N * (D ^ 2 + 1 / 4) / y0 ^ 2 := by
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hy2 : y0 ^ 2 ≤ 1 / 4 := by nlinarith
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  set L : ℝ := Real.log (max 1 (4 * N * (D ^ 2 + 1 / 4) / y0 ^ 2)) with hL
  have hLpos : 0 < L := by
    rw [hL, max_eq_right hQ.le]
    exact Real.log_pos hQ
  -- choose xmin with 2 xmin^2 <= L / max K 1
  set xmin : ℝ := Real.sqrt (L / (2 * max K 1)) with hxmin
  have hK1 : 0 < max K 1 := lt_max_of_lt_right one_pos
  have hx0 : 0 < xmin := Real.sqrt_pos.mpr (by positivity)
  refine ⟨xmin, hx0, ?_⟩
  have hsq : xmin ^ 2 = L / (2 * max K 1) := Real.sq_sqrt (by positivity)
  have hterm : max K 1 ≤ L / (2 * xmin ^ 2) := by
    rw [hsq]
    have : L / (2 * (L / (2 * max K 1))) = max K 1 := by
      field_simp
    rw [this]
  calc K ≤ max K 1 := le_max_left _ _
    _ ≤ L / (2 * xmin ^ 2) := hterm
    _ ≤ effectiveThreshold y0 xmin N B D :=
        (le_max_left _ _).trans (le_max_right _ _)

/-! ## B. The window sum as a finite sum, and the summand at the centre ordinate. -/

/-- The window part of the zero side is a finite sum over the certified window. -/
lemma tsum_winSet_eq_sum (c D lam : ℝ) :
    ∑' ρ : winSet c D, term c lam ρ = ∑ ρ ∈ zeroWindow c D, term c lam ρ := by
  rw [tsum_subtype, tsum_eq_sum (s := zeroWindow c D)]
  · exact Finset.sum_congr rfl fun ρ hρ =>
      Set.indicator_of_mem (show ρ ∈ winSet c D from (mem_zeroWindow.mp hρ).2) _
  · intro ρ hρ
    by_cases hw : ρ ∈ winSet c D
    · rw [Set.indicator_of_mem hw]
      exact term_eq_zero_of_not_nontrivial c lam fun h => hρ (mem_zeroWindow.mpr ⟨h, hw⟩)
    · exact Set.indicator_of_notMem hw _

/-- At the centre ordinate the summand is m (-(y^2) e^{2 lam y^2}), y = 1/2 - Re rho. -/
lemma re_term_centre (c lam : ℝ) {ρ : ℂ} (h : ρ.im = c) :
    (term c lam ρ).re
      = (WeilExplicit.zeroMult ρ : ℝ)
        * (-((1 / 2 - ρ.re) ^ 2) * Real.exp (2 * lam * (1 / 2 - ρ.re) ^ 2)) := by
  have hγ : gammaOf ρ = (c : ℂ) + ((1 / 2 - ρ.re : ℝ) : ℂ) * I := by
    apply Complex.ext
    · rw [Zeta23.WeilEF.gammaOf_re]
      simp [h]
    · rw [Zeta23.WeilEF.gammaOf_im]
      simp
  unfold term
  rw [hγ, gaussTest_axis]
  have : ((WeilExplicit.zeroMult ρ : ℂ)
      * ((-((1 / 2 - ρ.re) ^ 2) * Real.exp (2 * lam * (1 / 2 - ρ.re) ^ 2) : ℝ) : ℂ))
      = (((WeilExplicit.zeroMult ρ : ℝ)
        * (-((1 / 2 - ρ.re) ^ 2) * Real.exp (2 * lam * (1 / 2 - ρ.re) ^ 2)) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [this, Complex.ofReal_re]

lemma re_term_centre_nonpos (c lam : ℝ) {ρ : ℂ} (h : ρ.im = c) : (term c lam ρ).re ≤ 0 := by
  rw [re_term_centre c lam h]
  have h1 : (0 : ℝ) ≤ WeilExplicit.zeroMult ρ := Nat.cast_nonneg _
  have h2 : 0 ≤ (1 / 2 - ρ.re) ^ 2 * Real.exp (2 * lam * (1 / 2 - ρ.re) ^ 2) := by positivity
  nlinarith

/-! ## C. The window estimate with explicit parameters. -/

/-- Pointwise: a window zero at a different ordinate, with |x| >= xmin and y^2 <= Y, has
|summand| <= m (D^2 + 1/4) e^{2 lam (Y - xmin^2)}. -/
lemma norm_term_le_competitor {c D xmin Y lam : ℝ} (hlam : 0 ≤ lam) (hx0 : 0 ≤ xmin) {ρ : ℂ}
    (hnt : IsNontrivialZero ρ) (hwin : |ρ.im - c| ≤ D) (hY : (1 / 2 - ρ.re) ^ 2 ≤ Y)
    (hx : xmin ≤ |ρ.im - c|) :
    ‖term c lam ρ‖
      ≤ (WeilExplicit.zeroMult ρ : ℝ) * (D ^ 2 + 1 / 4) * Real.exp (2 * lam * (Y - xmin ^ 2)) := by
  rw [norm_term]
  have hm : (0 : ℝ) ≤ WeilExplicit.zeroMult ρ := Nat.cast_nonneg _
  have hD0 : 0 ≤ D := (abs_nonneg _).trans hwin
  have hxD : (ρ.im - c) ^ 2 ≤ D ^ 2 := by
    rw [← sq_abs (ρ.im - c)]
    exact pow_le_pow_left₀ (abs_nonneg _) hwin 2
  have hy4 : (1 / 2 - ρ.re) ^ 2 ≤ 1 / 4 := by
    have hy : |1 / 2 - ρ.re| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith [hnt.2.1, hnt.2.2]
    have := pow_le_pow_left₀ (abs_nonneg _) hy 2
    rw [sq_abs] at this
    linarith
  have hxmin : xmin ^ 2 ≤ (ρ.im - c) ^ 2 := by
    rw [← sq_abs (ρ.im - c)]
    exact pow_le_pow_left₀ hx0 hx 2
  have hw : wsq c ρ ≤ D ^ 2 + 1 / 4 := by
    unfold wsq
    linarith
  have hφ : phi c ρ ≤ Y - xmin ^ 2 := by
    unfold phi
    linarith
  have hexp : Real.exp (2 * lam * phi c ρ) ≤ Real.exp (2 * lam * (Y - xmin ^ 2)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hw0 : 0 ≤ wsq c ρ := by unfold wsq; positivity
  calc (WeilExplicit.zeroMult ρ : ℝ) * wsq c ρ * Real.exp (2 * lam * phi c ρ)
      ≤ (WeilExplicit.zeroMult ρ : ℝ) * (D ^ 2 + 1 / 4) * Real.exp (2 * lam * (Y - xmin ^ 2)) := by
        gcongr

/-- The finite window sum: at most  -Y e^{2 lam Y} + (D^2 + 1/4) e^{2 lam (Y - xmin^2)} (window count). -/
lemma re_window_sum_le {ρ₀ : ℂ} (h₀ : IsNontrivialZero ρ₀) {D xmin : ℝ}
    (hmax : ∀ ρ : ℂ, IsNontrivialZero ρ → |ρ.im - ρ₀.im| ≤ D →
      |1 / 2 - ρ.re| ≤ |1 / 2 - ρ₀.re|)
    (hsep : ∀ ρ : ℂ, IsNontrivialZero ρ → |ρ.im - ρ₀.im| ≤ D → ρ.im ≠ ρ₀.im →
      xmin ≤ |ρ.im - ρ₀.im|)
    {lam : ℝ} (hlam : 0 ≤ lam) (hD : 0 ≤ D) (hx0 : 0 ≤ xmin) :
    (∑ ρ ∈ zeroWindow ρ₀.im D, term ρ₀.im lam ρ).re
      ≤ -((1 / 2 - ρ₀.re) ^ 2 * Real.exp (2 * lam * (1 / 2 - ρ₀.re) ^ 2))
        + (D ^ 2 + 1 / 4) * Real.exp (2 * lam * ((1 / 2 - ρ₀.re) ^ 2 - xmin ^ 2))
          * ∑ ρ ∈ zeroWindow ρ₀.im D, (WeilExplicit.zeroMult ρ : ℝ) := by
  classical
  set c : ℝ := ρ₀.im with hc
  set Y : ℝ := (1 / 2 - ρ₀.re) ^ 2 with hY
  set Ecomp : ℝ := (D ^ 2 + 1 / 4) * Real.exp (2 * lam * (Y - xmin ^ 2)) with hEcomp
  have hEcomp0 : 0 ≤ Ecomp := by positivity
  -- the pointwise bound U
  set U : ℂ → ℝ := fun ρ => (if ρ = ρ₀ then -(Y * Real.exp (2 * lam * Y)) else 0)
    + (WeilExplicit.zeroMult ρ : ℝ) * Ecomp with hU
  have hpt : ∀ ρ ∈ zeroWindow c D, (term c lam ρ).re ≤ U ρ := by
    intro ρ hρ
    obtain ⟨hnt, hwin⟩ := mem_zeroWindow.mp hρ
    have hm : (0 : ℝ) ≤ WeilExplicit.zeroMult ρ := Nat.cast_nonneg _
    have hsecond : 0 ≤ (WeilExplicit.zeroMult ρ : ℝ) * Ecomp := mul_nonneg hm hEcomp0
    by_cases hρ₀ : ρ = ρ₀
    · subst hρ₀
      simp only [hU, if_true]
      rw [re_term_centre c lam rfl, ← hY]
      have hm1 : (1 : ℝ) ≤ WeilExplicit.zeroMult ρ := by
        rw [RvMBridge4.zeroMult_eq_mult hnt]
        exact_mod_cast zetaSeam.one_le_mult ρ hnt
      have hYE : 0 ≤ Y * Real.exp (2 * lam * Y) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hm1 hYE]
    · simp only [hU, if_neg hρ₀, zero_add]
      by_cases him : ρ.im = c
      · exact (re_term_centre_nonpos c lam him).trans hsecond
      · have hYρ : (1 / 2 - ρ.re) ^ 2 ≤ Y := by
          rw [hY, ← sq_abs (1 / 2 - ρ.re), ← sq_abs (1 / 2 - ρ₀.re)]
          exact pow_le_pow_left₀ (abs_nonneg _) (hmax ρ hnt hwin) 2
        have hx := hsep ρ hnt hwin him
        calc (term c lam ρ).re ≤ ‖term c lam ρ‖ := Complex.re_le_norm _
          _ ≤ (WeilExplicit.zeroMult ρ : ℝ) * (D ^ 2 + 1 / 4)
              * Real.exp (2 * lam * (Y - xmin ^ 2)) :=
              norm_term_le_competitor hlam hx0 hnt hwin hYρ hx
          _ = (WeilExplicit.zeroMult ρ : ℝ) * Ecomp := by rw [hEcomp]; ring
  have hsumU : ∑ ρ ∈ zeroWindow c D, U ρ
      = -(Y * Real.exp (2 * lam * Y))
        + (∑ ρ ∈ zeroWindow c D, (WeilExplicit.zeroMult ρ : ℝ)) * Ecomp := by
    simp only [hU]
    have hmem : ρ₀ ∈ zeroWindow c D := mem_zeroWindow.mpr ⟨h₀, by simp [hc, hD]⟩
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (zeroWindow c D) ρ₀, if_pos hmem,
      Finset.sum_mul]
  rw [Complex.re_sum]
  calc ∑ ρ ∈ zeroWindow c D, (term c lam ρ).re
      ≤ ∑ ρ ∈ zeroWindow c D, U ρ := Finset.sum_le_sum hpt
    _ = _ := by rw [hsumU, hEcomp]; ring

/-! ## D. The effective theorem. -/

/-- **Effective Gaussian dominance.**  Parameters: y0 (distance floor), xmin (ordinate spacing
floor), N (window count with multiplicity), D (window half-width); tail constant constB (Im rho_0).
Hypotheses are plain inequalities a consumer can certify; the threshold is explicit. -/
theorem effective_gaussian_dominance {ρ₀ : ℂ} (h₀ : IsNontrivialZero ρ₀)
    {y0 : ℝ} (hy0 : 0 < y0) (hy : y0 ≤ |1 / 2 - ρ₀.re|)
    {D xmin : ℝ} (hD : 1 ≤ D) (hx : 0 < xmin)
    (hmax : ∀ ρ : ℂ, IsNontrivialZero ρ → |ρ.im - ρ₀.im| ≤ D →
      |1 / 2 - ρ.re| ≤ |1 / 2 - ρ₀.re|)
    (hsep : ∀ ρ : ℂ, IsNontrivialZero ρ → |ρ.im - ρ₀.im| ≤ D → ρ.im ≠ ρ₀.im →
      xmin ≤ |ρ.im - ρ₀.im|)
    {N : ℕ} (hN : ∑ ρ ∈ zeroWindow ρ₀.im D, WeilExplicit.zeroMult ρ ≤ N)
    {lam : ℝ} (hlam : effectiveThreshold y0 xmin N (constB ρ₀.im) D ≤ lam) :
    (zeroSide (gaussTest ρ₀.im lam)).re < 0 := by
  set c : ℝ := ρ₀.im with hc
  set Y : ℝ := (1 / 2 - ρ₀.re) ^ 2 with hY
  have hlam1 : 1 ≤ lam := (one_le_effectiveThreshold _ _ _ _ _).trans hlam
  have hlam0 : 0 < lam := by linarith
  have hD0 : 0 ≤ D := by linarith
  -- the two threshold consequences
  have hthr1 : Real.log (max 1 (4 * N * (D ^ 2 + 1 / 4) / y0 ^ 2)) / (2 * xmin ^ 2) ≤ lam :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hlam
  have hthr2 : Real.log (max 1 (4 * constB c / y0 ^ 2)) / (2 * y0 ^ 2) ≤ lam :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hlam
  have hQ1 : 4 * N * (D ^ 2 + 1 / 4) / y0 ^ 2 ≤ Real.exp (2 * lam * xmin ^ 2) :=
    le_exp_of_log_le (by positivity) hthr1
  have hQ2 : 4 * constB c / y0 ^ 2 ≤ Real.exp (2 * lam * y0 ^ 2) :=
    le_exp_of_log_le (by positivity) hthr2
  -- Y >= y0^2
  have hYy : y0 ^ 2 ≤ Y := by
    rw [hY, ← sq_abs (1 / 2 - ρ₀.re)]
    exact pow_le_pow_left₀ hy0.le hy 2
  set E : ℝ := Real.exp (2 * lam * Y) with hE
  have hE0 : 0 < E := Real.exp_pos _
  -- split
  rw [zeroSide_split c D lam hlam0, Complex.add_re, tsum_winSet_eq_sum]
  have hwin := re_window_sum_le h₀ hmax hsep hlam0.le hD0 hx.le
  rw [← hc, ← hY] at hwin
  have htail := tail_bound_window (c := c) hD0 hlam1
  have htail_re := Complex.re_le_norm (∑' ρ : ↥(winSet c D)ᶜ, term c lam ρ)
  -- the tail envelope is at most constB c
  have henv : Real.exp (2 * (lam - 1) * (1 / 4 - D ^ 2)) * constB c ≤ constB c := by
    have h1 : Real.exp (2 * (lam - 1) * (1 / 4 - D ^ 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      apply mul_nonpos_of_nonneg_of_nonpos (by linarith)
      nlinarith
    have := constB_nonneg c
    nlinarith
  -- competitor <= (y0^2/4) E
  have hcount : (∑ ρ ∈ zeroWindow c D, (WeilExplicit.zeroMult ρ : ℝ)) ≤ N := by
    exact_mod_cast hN
  have hcount0 : 0 ≤ ∑ ρ ∈ zeroWindow c D, (WeilExplicit.zeroMult ρ : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hcomp : (D ^ 2 + 1 / 4) * Real.exp (2 * lam * (Y - xmin ^ 2))
      * ∑ ρ ∈ zeroWindow c D, (WeilExplicit.zeroMult ρ : ℝ) ≤ y0 ^ 2 / 4 * E := by
    have hF : Real.exp (2 * lam * (Y - xmin ^ 2)) * Real.exp (2 * lam * xmin ^ 2) = E := by
      rw [← Real.exp_add, hE]
      congr 1
      ring
    have hNQ : (N : ℝ) * (D ^ 2 + 1 / 4) ≤ y0 ^ 2 / 4 * Real.exp (2 * lam * xmin ^ 2) := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < y0 ^ 2)).mp hQ1
      linarith
    have hexp0 : 0 < Real.exp (2 * lam * (Y - xmin ^ 2)) := Real.exp_pos _
    have hstep : (D ^ 2 + 1 / 4) * Real.exp (2 * lam * (Y - xmin ^ 2))
        * ∑ ρ ∈ zeroWindow c D, (WeilExplicit.zeroMult ρ : ℝ)
        ≤ Real.exp (2 * lam * (Y - xmin ^ 2)) * ((N : ℝ) * (D ^ 2 + 1 / 4)) := by
      have := mul_le_mul_of_nonneg_left hcount (by positivity : (0 : ℝ) ≤ (D ^ 2 + 1 / 4)
        * Real.exp (2 * lam * (Y - xmin ^ 2)))
      linarith
    calc (D ^ 2 + 1 / 4) * Real.exp (2 * lam * (Y - xmin ^ 2))
          * ∑ ρ ∈ zeroWindow c D, (WeilExplicit.zeroMult ρ : ℝ)
        ≤ Real.exp (2 * lam * (Y - xmin ^ 2)) * ((N : ℝ) * (D ^ 2 + 1 / 4)) := hstep
      _ ≤ Real.exp (2 * lam * (Y - xmin ^ 2)) * (y0 ^ 2 / 4 * Real.exp (2 * lam * xmin ^ 2)) :=
          mul_le_mul_of_nonneg_left hNQ hexp0.le
      _ = y0 ^ 2 / 4 * E := by rw [← hF]; ring
  -- tail <= (y0^2/4) E
  have htailB : constB c ≤ y0 ^ 2 / 4 * E := by
    have h1 : constB c ≤ y0 ^ 2 / 4 * Real.exp (2 * lam * y0 ^ 2) := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < y0 ^ 2)).mp hQ2
      linarith
    have h2 : Real.exp (2 * lam * y0 ^ 2) ≤ E := Real.exp_le_exp.mpr (by nlinarith)
    calc constB c ≤ y0 ^ 2 / 4 * Real.exp (2 * lam * y0 ^ 2) := h1
      _ ≤ y0 ^ 2 / 4 * E := mul_le_mul_of_nonneg_left h2 (by positivity)
  -- main term <= -y0^2 E
  have hmain : -(Y * E) ≤ -(y0 ^ 2 * E) := by nlinarith
  have hy0E : 0 < y0 ^ 2 * E := by positivity
  linarith

/-! ## E. The localisation instrument. -/

/-- The finite band of nontrivial zeros with T1 - D <= Im rho <= T2 + D. -/
lemma band_finite (T₁ T₂ D : ℝ) :
    ({ρ : ℂ | IsNontrivialZero ρ ∧ T₁ - D ≤ ρ.im ∧ ρ.im ≤ T₂ + D}).Finite := by
  refine (zetaSeam.finite_window (T₁ - D - 1) (T₂ + D)).subset ?_
  rintro ρ ⟨hnt, h1, h2⟩
  exact ⟨hnt, by linarith, h2⟩

/-- **Localisation instrument.**  Gaussian positivity on the band [T1, T2] at every lam above
the explicit threshold implies: either every zero with ordinate in [T1 - D, T2 + D] is within
y0 of the line, or some zero in a margin ([T1 - D, T1) or (T2, T2 + D]) is at distance >= y0
from the line (and is the zero of maximal distance over the widened band). -/
theorem offline_zeros_small_or_margin (T₁ T₂ : ℝ) {y0 xmin D : ℝ} (hy0 : 0 < y0) (hx : 0 < xmin)
    (hD : 1 ≤ D) (N : ℕ) (Bmax : ℝ)
    (hN : ∀ c : ℝ, T₁ ≤ c → c ≤ T₂ → ∑ ρ ∈ zeroWindow c D, WeilExplicit.zeroMult ρ ≤ N)
    (hsep : ∀ ρ ρ' : ℂ, IsNontrivialZero ρ → T₁ ≤ ρ.im → ρ.im ≤ T₂ → IsNontrivialZero ρ' →
      |ρ'.im - ρ.im| ≤ D → ρ'.im ≠ ρ.im → xmin ≤ |ρ'.im - ρ.im|)
    (hB : ∀ c : ℝ, T₁ ≤ c → c ≤ T₂ → constB c ≤ Bmax)
    (hpos : ∀ c : ℝ, T₁ ≤ c → c ≤ T₂ → ∀ lam : ℝ, effectiveThreshold y0 xmin N Bmax D ≤ lam →
      0 ≤ (zeroSide (gaussTest c lam)).re) :
    (∀ ρ : ℂ, IsNontrivialZero ρ → T₁ - D ≤ ρ.im → ρ.im ≤ T₂ + D → |1 / 2 - ρ.re| < y0) ∨
    (∃ ρ : ℂ, IsNontrivialZero ρ ∧ T₁ - D ≤ ρ.im ∧ ρ.im ≤ T₂ + D ∧ (ρ.im < T₁ ∨ T₂ < ρ.im) ∧
      y0 ≤ |1 / 2 - ρ.re| ∧
      ∀ ρ' : ℂ, IsNontrivialZero ρ' → T₁ - D ≤ ρ'.im → ρ'.im ≤ T₂ + D →
        |1 / 2 - ρ'.re| ≤ |1 / 2 - ρ.re|) := by
  classical
  set S : Finset ℂ := (band_finite T₁ T₂ D).toFinset with hS
  have hmemS : ∀ ρ, ρ ∈ S ↔ IsNontrivialZero ρ ∧ T₁ - D ≤ ρ.im ∧ ρ.im ≤ T₂ + D := by
    intro ρ
    rw [hS, Set.Finite.mem_toFinset]
    rfl
  rcases S.eq_empty_or_nonempty with hemp | hne
  · left
    intro ρ hnt h1 h2
    have : ρ ∈ S := (hmemS ρ).mpr ⟨hnt, h1, h2⟩
    rw [hemp] at this
    exact absurd this (Finset.notMem_empty ρ)
  obtain ⟨ρ₀, hρ₀S, hmaxS⟩ := Finset.exists_max_image S (fun ρ => |1 / 2 - ρ.re|) hne
  obtain ⟨h₀, h₀1, h₀2⟩ := (hmemS ρ₀).mp hρ₀S
  by_cases hbig : y0 ≤ |1 / 2 - ρ₀.re|
  · by_cases hin : T₁ ≤ ρ₀.im ∧ ρ₀.im ≤ T₂
    · exfalso
      -- the effective theorem at c = Im rho_0 contradicts positivity
      have hmax : ∀ ρ : ℂ, IsNontrivialZero ρ → |ρ.im - ρ₀.im| ≤ D →
          |1 / 2 - ρ.re| ≤ |1 / 2 - ρ₀.re| := by
        intro ρ hnt hw
        have h := abs_le.mp hw
        exact hmaxS ρ ((hmemS ρ).mpr ⟨hnt, by linarith [h.1, hin.1], by linarith [h.2, hin.2]⟩)
      have hsep' : ∀ ρ : ℂ, IsNontrivialZero ρ → |ρ.im - ρ₀.im| ≤ D → ρ.im ≠ ρ₀.im →
          xmin ≤ |ρ.im - ρ₀.im| := fun ρ hnt hw hne' => hsep ρ₀ ρ h₀ hin.1 hin.2 hnt hw hne'
      set lam : ℝ := effectiveThreshold y0 xmin N Bmax D with hlam
      have hthr : effectiveThreshold y0 xmin N (constB ρ₀.im) D ≤ lam :=
        effectiveThreshold_mono_B N hy0 (hB ρ₀.im hin.1 hin.2)
      have hneg := effective_gaussian_dominance h₀ hy0 hbig hD hx hmax hsep'
        (hN ρ₀.im hin.1 hin.2) hthr
      have hnn := hpos ρ₀.im hin.1 hin.2 lam le_rfl
      linarith
    · right
      refine ⟨ρ₀, h₀, h₀1, h₀2, ?_, hbig, ?_⟩
      · by_contra hcon
        obtain ⟨h1, h2⟩ := not_or.mp hcon
        exact hin ⟨not_lt.mp h1, not_lt.mp h2⟩
      · intro ρ' hnt h1 h2
        exact hmaxS ρ' ((hmemS ρ').mpr ⟨hnt, h1, h2⟩)
  · left
    intro ρ hnt h1 h2
    have := hmaxS ρ ((hmemS ρ).mpr ⟨hnt, h1, h2⟩)
    have hbig' := not_le.mp hbig
    linarith

/-- The window count is bounded by the cumulative local count over (c - D - 1, c + D]
(Zeta23.Ncount), the quantity the local zero count certifies. -/
lemma windowCount_le_Ncount (c D : ℝ) :
    ∑ ρ ∈ zeroWindow c D, WeilExplicit.zeroMult ρ ≤ Zeta23.Ncount (c - D - 1) (c + D) := by
  classical
  have hfin : (zerosIn (c - D - 1) (c + D)).Finite := by
    refine (zetaSeam.finite_window (c - D - 1) (c + D)).subset ?_
    rintro ρ ⟨hnt, h1, h2⟩
    exact ⟨hnt, h1, h2⟩
  unfold Zeta23.Ncount
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hsub : zeroWindow c D ⊆ hfin.toFinset := by
    intro ρ hρ
    obtain ⟨hnt, hw⟩ := mem_zeroWindow.mp hρ
    rw [Set.Finite.mem_toFinset]
    have h := abs_le.mp hw
    exact ⟨hnt, by linarith [h.1], by linarith [h.2]⟩
  calc ∑ ρ ∈ zeroWindow c D, WeilExplicit.zeroMult ρ
      = ∑ ρ ∈ zeroWindow c D, Zeta23.zeroMult ρ :=
        Finset.sum_congr rfl fun ρ hρ =>
          RvMBridge4.zeroMult_eq_mult (mem_zeroWindow.mp hρ).1
    _ ≤ ∑ ρ ∈ hfin.toFinset, Zeta23.zeroMult ρ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.zero_le _

end RvMBridge14
