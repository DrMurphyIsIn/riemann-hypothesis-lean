/-
  E6Bridge15 -- the WEIL-TO-LI dictionary, convergence half (2026-09-21; rh campaign node
  RH_bl_explicit_formula = B7, the Bombieri-Lagarias explicit formula on Li's test class).

  Vocabulary: the BombieriLagarias block of missions/rh/lean/Statements/RHDefs.lean is mirrored
  VERBATIM below (namespace RvMBridge15.BombieriLagarias; only Mathlib names).  The node is

      bl_explicit_formula (n) (hn : 0 < n) :
        Tendsto (liZeroSum n) atTop (nhds (archSide n + finiteSide n)),

  liZeroSum n T = Sum_{0 < Re rho < 1, |Im rho| <= T} m(rho) (1 - (1 - 1/rho)^n) with the E8
  divisor multiplicity m = WeilExplicit.zeroMult.

  PROVED HERE (kernel-checked, no `sorry`): the CONVERGENCE half.  For every n the symmetric window
  sums converge,
      liZeroSum_tendsto (n) : Tendsto (liZeroSum n) atTop (nhds (liLimit n)),
      liLimit n := Sum'_rho m(rho) Re (1 - (1 - 1/rho)^n)     (absolutely convergent),
  and the window sums are REAL.  The argument is the one the design memo calls forced:
    (A) the divisor is conjugation-symmetric, m(conj rho) = m(rho)
        (Zeta23.analyticOrderAt_zeta_conj + Mathlib riemannZeta_conj);
    (B) the window {0 < Re < 1, |Im| <= T} is conjugation-closed and the kernel satisfies
        K_n(conj rho) = conj (K_n rho), so reindexing by conjugation shows every window sum equals
        the window sum of the PAIRED family m(rho) Re K_n(rho) (and is real);
    (C) the paired family is absolutely summable over ALL rho : C: on a nontrivial zero with
        |Im rho| >= 1, |Re K_n(rho)| <= 2^n / |rho|^2 <= (9/4) 2^n / (1 + |gamma_rho|^2) (binomial
        expansion; the j = 1 term Re(1/rho) = Re rho / |rho|^2 is where the pairing pays), and
        the local-count majorant summable_mult_div_one_add_normSq of the prelude RvMBridgeGauss does the rest; the
        finitely many zeros with |Im rho| < 1 (Zeta23 zetaSeam.finite_window) are absorbed;
    (D) Tannery (tendsto_tsum_of_dominated_convergence) passes the indicator sums to the limit.
  The UNPAIRED family m(rho) K_n(rho) is NOT summable (terms ~ n/(i gamma)); nothing here claims
  it is: the pairing is exactly why the symmetric order converges.

  NOT PROVED: the VALUE half, liLimit n = archSide n + finiteSide n (Bombieri-Lagarias 1999,
  Theorem 2).  It needs the Hadamard / xi'/xi partial-fraction data at s = 1 (the symmetric power
  sums Sum_rho rho^{-j} in terms of the Laurent coefficients eta_{j-1} and the digamma tower at
  1/2), which is not in Zeta23 (its partial fraction, WeilEF.zeta_logDeriv_partial_fraction, is
  Landau's LOCAL form with an unpinned O(log t) remainder).  It is carried as the single named
  obligation LiValue below (def : Prop, never a `sorry`); bl_explicit_formula_of consumes it.

  ALSO PROVED (finite-grade dictionary content): the forward half of Li's criterion on this
  island's vocabulary, rh_implies_liLimit_nonneg : RiemannHypothesis -> 0 <= Re (liLimit n),
  and rh_implies_liZeroSum_nonneg for every window: on the line |1 - 1/rho| = 1, so every paired
  term m(rho) (1 - Re w^n) with |w| = 1 is nonnegative.  Li's criterion CONVERSE (lambda_n >= 0
  for all n implies RH) is NOT on this island (the corpus's li_criterion_rh_iff lives on the
  v4.34 li_positivity island) and is not claimed.

  conjecture1_proved = False.  Nothing here says anything about whether RH holds.
-/
import E6Bridge6

open Zeta23 Complex MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace RvMBridge15
open WeilExplicit

/-! ## 0. The registry vocabulary, mirrored verbatim (RHDefs.lean, namespace BombieriLagarias). -/

namespace BombieriLagarias

/-- Li's kernel `1 - (1 - 1/ρ)^n`; `λ_n = Σ_ρ liKernel n ρ` in the symmetric order. -/
noncomputable def liKernel (n : ℕ) (ρ : ℂ) : ℂ := 1 - (1 - 1 / ρ) ^ n

/-- The symmetric partial zero sum: strip zeros with `|Im ρ| ≤ T`, weight
    `WeilExplicit.zeroMult` (the E8 / RvMCount divisor).  `finsum` is 0 on infinite support, so
    the definition is total; finiteness of every window is a theorem. -/
noncomputable def liZeroSum (n : ℕ) (T : ℝ) : ℂ :=
  ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
    (WeilExplicit.zeroMult ρ : ℂ) * liKernel n ρ

/-- The archimedean side `S_∞(n) = 1 - (n/2)(γ + log π + 2 log 2)
    + Σ_{j=2}^n (-1)^j C(n,j) (1 - 2^{-j}) ζ(j)` (Bombieri-Lagarias 1999, Thm 2). -/
noncomputable def archSide (n : ℕ) : ℂ :=
  1 - ((n : ℂ) / 2) * ((Real.eulerMascheroniConstant : ℂ) + (Real.log Real.pi : ℂ)
      + 2 * (Real.log 2 : ℂ))
    + ∑ j ∈ Finset.Icc 2 n,
        (-1 : ℂ) ^ j * (n.choose j : ℂ) * (1 - 1 / (2 : ℂ) ^ j) * riemannZeta (j : ℂ)

/-- `-ζ'/ζ(s) - 1/(s - 1)`, extended at `s = 1` by its limit `-γ`. -/
noncomputable def zetaLogDerivReg : ℂ → ℂ :=
  Function.update (fun s : ℂ => -logDeriv riemannZeta s - 1 / (s - 1)) 1
    (-(Real.eulerMascheroniConstant : ℂ))

/-- The Laurent constants `η_j`: `-ζ'/ζ(s) - 1/(s-1) = Σ_j η_j (s-1)^j`, `η_0 = -γ`. -/
noncomputable def eta (j : ℕ) : ℂ := iteratedDeriv j zetaLogDerivReg 1 / (j.factorial : ℂ)

/-- The finite part `S_f(n) = -Σ_{j=1}^n C(n,j) η_{j-1}` (Bombieri-Lagarias 1999, Thm 2). -/
noncomputable def finiteSide (n : ℕ) : ℂ :=
  -∑ j ∈ Finset.Icc 1 n, (n.choose j : ℂ) * eta (j - 1)

end BombieriLagarias

open BombieriLagarias

/-! ## A. The divisor is conjugation-symmetric. -/

lemma isNontrivialZero_conj {ρ : ℂ} (h : IsNontrivialZero ρ) : IsNontrivialZero (conj ρ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [_root_.riemannZeta_conj, h.1, map_zero]
  · rw [Complex.conj_re]; exact h.2.1
  · rw [Complex.conj_re]; exact h.2.2

lemma isNontrivialZero_conj_iff (ρ : ℂ) : IsNontrivialZero (conj ρ) ↔ IsNontrivialZero ρ :=
  ⟨fun h => by simpa using isNontrivialZero_conj h, isNontrivialZero_conj⟩

/-- m(conj rho) = m(rho) for every rho : C. -/
theorem zeroMult_conj (ρ : ℂ) : WeilExplicit.zeroMult (conj ρ) = WeilExplicit.zeroMult ρ := by
  by_cases h : IsNontrivialZero ρ
  · have h' := isNontrivialZero_conj h
    rw [RvMBridge4.zeroMult_eq_of_strip h'.2.1 h'.2.2, RvMBridge4.zeroMult_eq_of_strip h.2.1 h.2.2]
    unfold Zeta23.zeroMult
    have hne : ρ ≠ 1 := fun h1 => by
      have := h.2.2
      rw [h1, Complex.one_re] at this
      exact lt_irrefl _ this
    rw [Zeta23.analyticOrderAt_zeta_conj hne]
  · have h' : ¬ IsNontrivialZero (conj ρ) := fun h' => h ((isNontrivialZero_conj_iff ρ).mp h')
    rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial h,
      RvMBridge4.zeroMult_eq_zero_of_not_nontrivial h']

/-! ## B. Windows, their finiteness, and the pairing. -/

/-- The symmetric window {0 < Re rho < 1, |Im rho| <= T}. -/
def windowSet (T : ℝ) : Set ℂ := {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}

lemma mem_windowSet {T : ℝ} {ρ : ℂ} :
    ρ ∈ windowSet T ↔ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T := Iff.rfl

lemma conj_mem_windowSet {T : ℝ} {ρ : ℂ} : conj ρ ∈ windowSet T ↔ ρ ∈ windowSet T := by
  simp only [mem_windowSet, Complex.conj_re, Complex.conj_im, abs_neg]

/-- The nontrivial zeros in a symmetric window form a finite set (Zeta23 zetaSeam.finite_window). -/
lemma finite_zeros_window (T : ℝ) :
    ({ρ : ℂ | IsNontrivialZero ρ} ∩ {ρ : ℂ | |ρ.im| ≤ T}).Finite := by
  refine (zetaSeam.finite_window (-T - 1) T).subset ?_
  rintro ρ ⟨hnt, hw⟩
  have hw' : |ρ.im| ≤ T := hw
  have h := abs_le.mp hw'
  exact ⟨hnt, by linarith [h.1], h.2⟩

/-- The conjugation as an involutive equivalence of C. -/
def conjEquiv : ℂ ≃ ℂ where
  toFun := conj
  invFun := conj
  left_inv := Complex.conj_conj
  right_inv := Complex.conj_conj

/-- Li's kernel commutes with conjugation. -/
lemma liKernel_conj (n : ℕ) (ρ : ℂ) : liKernel n (conj ρ) = conj (liKernel n ρ) := by
  unfold liKernel
  simp only [map_sub, map_one, map_pow, map_div₀]

/-- The paired (real) family: m(rho) Re K_n(rho), as a complex number. -/
def liPaired (n : ℕ) (ρ : ℂ) : ℂ :=
  (WeilExplicit.zeroMult ρ : ℂ) * ((liKernel n ρ).re : ℂ)

/-- The limit of the symmetric window sums (a genuine absolutely convergent sum, section C). -/
def liLimit (n : ℕ) : ℂ := ∑' ρ : ℂ, liPaired n ρ

/-- The unpaired family, supported on the nontrivial zeros. -/
def liTerm (n : ℕ) (ρ : ℂ) : ℂ := (WeilExplicit.zeroMult ρ : ℂ) * liKernel n ρ

lemma liTerm_eq_zero_of_not_nontrivial {n : ℕ} {ρ : ℂ} (h : ¬ IsNontrivialZero ρ) :
    liTerm n ρ = 0 := by
  unfold liTerm
  rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial h]
  simp

lemma liPaired_eq_zero_of_not_nontrivial {n : ℕ} {ρ : ℂ} (h : ¬ IsNontrivialZero ρ) :
    liPaired n ρ = 0 := by
  unfold liPaired
  rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial h]
  simp

lemma liTerm_conj (n : ℕ) (ρ : ℂ) : liTerm n (conj ρ) = conj (liTerm n ρ) := by
  unfold liTerm
  rw [zeroMult_conj, liKernel_conj, map_mul, Complex.conj_natCast]

/-- The support of the window family is finite. -/
lemma windowSupport_finite (n : ℕ) (T : ℝ) :
    (windowSet T ∩ Function.support (liTerm n)).Finite := by
  refine (finite_zeros_window T).subset ?_
  rintro ρ ⟨hw, hs⟩
  refine ⟨?_, hw.2.2⟩
  by_contra hnt
  exact hs (liTerm_eq_zero_of_not_nontrivial hnt)

/-- The window sum as a tsum of the indicator family. -/
lemma liZeroSum_eq_tsum_indicator (n : ℕ) (T : ℝ) :
    liZeroSum n T = ∑' ρ : ℂ, (windowSet T).indicator (liTerm n) ρ := by
  unfold liZeroSum
  have hfin := windowSupport_finite n T
  change ∑ᶠ ρ ∈ windowSet T, liTerm n ρ = _
  rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ hfin]
  rw [tsum_eq_sum (s := hfin.toFinset)]
  · refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [Set.Finite.mem_toFinset] at hρ
    rw [Set.indicator_of_mem hρ.1]
  · intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    by_cases hw : ρ ∈ windowSet T
    · rw [Set.indicator_of_mem hw]
      by_contra hne
      exact hρ ⟨hw, hne⟩
    · exact Set.indicator_of_notMem hw _

lemma indicator_liTerm_conj (n : ℕ) (T : ℝ) (ρ : ℂ) :
    (windowSet T).indicator (liTerm n) (conj ρ) = conj ((windowSet T).indicator (liTerm n) ρ) := by
  by_cases hw : ρ ∈ windowSet T
  · rw [Set.indicator_of_mem hw, Set.indicator_of_mem (conj_mem_windowSet.mpr hw), liTerm_conj]
  · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem (fun h => hw (conj_mem_windowSet.mp h)),
      map_zero]

lemma summable_indicator_liTerm (n : ℕ) (T : ℝ) :
    Summable ((windowSet T).indicator (liTerm n)) := by
  refine summable_of_ne_finset_zero (s := (windowSupport_finite n T).toFinset) fun ρ hρ => ?_
  rw [Set.Finite.mem_toFinset] at hρ
  by_cases hw : ρ ∈ windowSet T
  · rw [Set.indicator_of_mem hw]
    by_contra hne
    exact hρ ⟨hw, hne⟩
  · exact Set.indicator_of_notMem hw _

/-- THE PAIRING: every symmetric window sum equals the window sum of the paired family. -/
theorem liZeroSum_eq_tsum_paired (n : ℕ) (T : ℝ) :
    liZeroSum n T = ∑' ρ : ℂ, (windowSet T).indicator (liPaired n) ρ := by
  rw [liZeroSum_eq_tsum_indicator]
  set F := (windowSet T).indicator (liTerm n) with hF
  have hsum : Summable F := summable_indicator_liTerm n T
  -- reindex by conjugation
  have hconj : ∑' ρ : ℂ, F ρ = ∑' ρ : ℂ, conj (F ρ) := by
    calc ∑' ρ : ℂ, F ρ = ∑' ρ : ℂ, F (conjEquiv ρ) := (conjEquiv.tsum_eq F).symm
      _ = ∑' ρ : ℂ, conj (F ρ) := by
          congr 1
          funext ρ
          exact indicator_liTerm_conj n T ρ
  have hsum' : Summable (fun ρ => conj (F ρ)) := by
    have := (conjEquiv.summable_iff (f := F)).mpr hsum
    refine this.congr fun ρ => ?_
    exact indicator_liTerm_conj n T ρ
  have h2 : (2 : ℂ) * ∑' ρ : ℂ, F ρ = ∑' ρ : ℂ, (F ρ + conj (F ρ)) := by
    rw [hsum.tsum_add hsum', ← hconj]
    ring
  have h3 : ∀ ρ, F ρ + conj (F ρ) = 2 * (windowSet T).indicator (liPaired n) ρ := by
    intro ρ
    rw [Complex.add_conj]
    by_cases hw : ρ ∈ windowSet T
    · rw [hF, Set.indicator_of_mem hw, Set.indicator_of_mem hw]
      unfold liTerm liPaired
      rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
      push_cast
      ring
    · rw [hF, Set.indicator_of_notMem hw, Set.indicator_of_notMem hw]
      simp
  simp_rw [h3] at h2
  rw [tsum_mul_left] at h2
  exact mul_left_cancel₀ two_ne_zero h2

/-- The symmetric window sums are real. -/
theorem liZeroSum_im (n : ℕ) (T : ℝ) : (liZeroSum n T).im = 0 := by
  rw [liZeroSum_eq_tsum_paired]
  have : ∀ ρ, (windowSet T).indicator (liPaired n) ρ
      = (((windowSet T).indicator (fun ρ => (WeilExplicit.zeroMult ρ : ℝ) * (liKernel n ρ).re) ρ : ℝ) : ℂ) := by
    intro ρ
    by_cases hw : ρ ∈ windowSet T
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw]
      unfold liPaired
      push_cast
      ring
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw]
      simp
  simp_rw [this]
  rw [← Complex.ofReal_tsum, Complex.ofReal_im]

/-! ## C. The paired family is absolutely summable. -/

/-- The binomial expansion K_n(rho) = -Sum_{m<n} C(n,m+1) (-1/rho)^(m+1). -/
lemma liKernel_eq_sum (n : ℕ) (ρ : ℂ) :
    liKernel n ρ = -∑ m ∈ Finset.range n, (n.choose (m + 1) : ℂ) * (-1 / ρ) ^ (m + 1) := by
  unfold liKernel
  have h : (1 - 1 / ρ) = (-1 / ρ) + 1 := by ring
  rw [h, add_pow, Finset.sum_range_succ']
  simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one]
  rw [show ∀ S : ℂ, 1 - (S + 1) = -S from fun S => by ring]
  congr 1
  exact Finset.sum_congr rfl fun m _ => by ring

lemma sum_choose_succ_le (n : ℕ) : (∑ m ∈ Finset.range n, (n.choose (m + 1) : ℝ)) ≤ 2 ^ n := by
  have h := Nat.sum_range_choose n
  rw [Finset.sum_range_succ', Nat.choose_zero_right] at h
  have h' : ∑ m ∈ Finset.range n, n.choose (m + 1) ≤ 2 ^ n := by omega
  exact_mod_cast h'

/-- On the strip, at distance >= 1 from 0, |Re K_n(rho)| <= 2^n / |rho|^2: the j = 1 term is
Re(1/rho) = Re rho / |rho|^2 (this is where the pairing pays) and the others are O(|rho|^-2). -/
lemma abs_re_liKernel_le {n : ℕ} {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hρ : 1 ≤ ‖ρ‖) :
    |(liKernel n ρ).re| ≤ 2 ^ n / Complex.normSq ρ := by
  have hns : 0 < Complex.normSq ρ := by
    rw [Complex.normSq_eq_norm_sq]; positivity
  have hterm : ∀ m ∈ Finset.range n,
      |((n.choose (m + 1) : ℂ) * (-1 / ρ) ^ (m + 1)).re|
        ≤ (n.choose (m + 1) : ℝ) * (1 / Complex.normSq ρ) := by
    intro m _
    rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, abs_mul,
      Nat.abs_cast]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [zero_add, pow_one, neg_div, one_div, Complex.neg_re, Complex.inv_re, abs_neg,
        abs_of_nonneg (div_nonneg h0.le hns.le)]
      exact div_le_div_of_nonneg_right h1.le hns.le
    · calc |((-1 / ρ) ^ (m + 1)).re| ≤ ‖(-1 / ρ) ^ (m + 1)‖ := Complex.abs_re_le_norm _
        _ = (1 / ‖ρ‖) ^ (m + 1) := by
            rw [norm_pow, norm_div, norm_neg, norm_one]
        _ ≤ (1 / ‖ρ‖) ^ 2 := by
            apply pow_le_pow_of_le_one (by positivity)
            · rw [div_le_one (by positivity)]; exact hρ
            · omega
        _ = 1 / Complex.normSq ρ := by
            rw [Complex.normSq_eq_norm_sq, div_pow, one_pow]
  rw [liKernel_eq_sum, Complex.neg_re, abs_neg, Complex.re_sum]
  calc |∑ m ∈ Finset.range n, ((n.choose (m + 1) : ℂ) * (-1 / ρ) ^ (m + 1)).re|
      ≤ ∑ m ∈ Finset.range n, |((n.choose (m + 1) : ℂ) * (-1 / ρ) ^ (m + 1)).re| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.range n, (n.choose (m + 1) : ℝ) * (1 / Complex.normSq ρ) :=
        Finset.sum_le_sum hterm
    _ = (∑ m ∈ Finset.range n, (n.choose (m + 1) : ℝ)) * (1 / Complex.normSq ρ) := by
        rw [Finset.sum_mul]
    _ ≤ 2 ^ n * (1 / Complex.normSq ρ) :=
        mul_le_mul_of_nonneg_right (sum_choose_succ_le n) (by positivity)
    _ = 2 ^ n / Complex.normSq ρ := by ring

lemma liPaired_re (n : ℕ) (ρ : ℂ) :
    (liPaired n ρ).re = (WeilExplicit.zeroMult ρ : ℝ) * (liKernel n ρ).re := by
  unfold liPaired
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]

lemma liPaired_im (n : ℕ) (ρ : ℂ) : (liPaired n ρ).im = 0 := by
  unfold liPaired
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_im]

lemma norm_liPaired (n : ℕ) (ρ : ℂ) :
    ‖liPaired n ρ‖ = (WeilExplicit.zeroMult ρ : ℝ) * |(liKernel n ρ).re| := by
  unfold liPaired
  rw [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]

/-- The local-count majorant constant for K_n. -/
def liC (n : ℕ) : ℝ := 9 / 4 * 2 ^ n

/-- On a nontrivial zero with |Im rho| >= 1 the paired term is bounded by the local-count majorant. -/
lemma norm_liPaired_le_majorant {n : ℕ} {ρ : ℂ} (h : IsNontrivialZero ρ) (him : 1 ≤ |ρ.im|) :
    ‖liPaired n ρ‖ ≤ (WeilExplicit.zeroMult ρ : ℝ) * (liC n / (1 + Complex.normSq (gammaOf ρ))) := by
  rw [norm_liPaired]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have hρ : 1 ≤ ‖ρ‖ := him.trans (Complex.abs_im_le_norm ρ)
  have hK := abs_re_liKernel_le (n := n) h.2.1 h.2.2 hρ
  refine hK.trans ?_
  have hns : Complex.normSq ρ = ρ.re ^ 2 + ρ.im ^ 2 := by
    rw [Complex.normSq_apply]; ring
  have hγ : Complex.normSq (gammaOf ρ) = ρ.im ^ 2 + (1 / 2 - ρ.re) ^ 2 := by
    rw [Complex.normSq_apply, Zeta23.WeilEF.gammaOf_re, Zeta23.WeilEF.gammaOf_im]; ring
  have him2 : 1 ≤ ρ.im ^ 2 := by
    have := sq_abs ρ.im
    nlinarith [abs_nonneg ρ.im]
  have hre := h.2.1
  have hre1 := h.2.2
  unfold liC
  rw [div_le_div_iff₀ (by rw [hns]; positivity) (by linarith [Complex.normSq_nonneg (gammaOf ρ)])]
  rw [hns, hγ]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]

/-- The nontrivial zeros with |Im rho| < 1 are finitely many. -/
lemma finite_zeros_small : ({ρ : ℂ | IsNontrivialZero ρ} ∩ {ρ : ℂ | |ρ.im| < 1}).Finite :=
  (finite_zeros_window 1).subset fun ρ ⟨h1, h2⟩ => ⟨h1, show |ρ.im| ≤ 1 from le_of_lt h2⟩

/-- The summable majorant: the finitely many small-ordinate terms plus the local-count majorant. -/
def liBound (n : ℕ) (ρ : ℂ) : ℝ :=
  ({ρ : ℂ | IsNontrivialZero ρ} ∩ {ρ : ℂ | |ρ.im| < 1}).indicator (fun ρ => ‖liPaired n ρ‖) ρ
    + (WeilExplicit.zeroMult ρ : ℝ) * (liC n / (1 + Complex.normSq (gammaOf ρ)))

lemma summable_liBound (n : ℕ) : Summable (liBound n) := by
  unfold liBound
  refine Summable.add ?_ (RvMBridgeGauss.summable_mult_div_one_add_normSq (liC n))
  refine summable_of_ne_finset_zero (s := finite_zeros_small.toFinset) fun ρ hρ => ?_
  rw [Set.Finite.mem_toFinset] at hρ
  exact Set.indicator_of_notMem hρ _

lemma norm_liPaired_le (n : ℕ) (ρ : ℂ) : ‖liPaired n ρ‖ ≤ liBound n ρ := by
  unfold liBound
  have hpos : 0 ≤ (WeilExplicit.zeroMult ρ : ℝ) * (liC n / (1 + Complex.normSq (gammaOf ρ))) := by
    have := Complex.normSq_nonneg (gammaOf ρ)
    unfold liC
    positivity
  by_cases h : IsNontrivialZero ρ
  · by_cases him : |ρ.im| < 1
    · rw [Set.indicator_of_mem (show ρ ∈ {ρ : ℂ | IsNontrivialZero ρ} ∩ {ρ : ℂ | |ρ.im| < 1}
        from ⟨h, him⟩)]
      linarith
    · rw [Set.indicator_of_notMem (fun hm => him hm.2), zero_add]
      exact norm_liPaired_le_majorant h (not_lt.mp him)
  · rw [liPaired_eq_zero_of_not_nontrivial h, norm_zero]
    have : 0 ≤ ({ρ : ℂ | IsNontrivialZero ρ} ∩ {ρ : ℂ | |ρ.im| < 1}).indicator
        (fun ρ => ‖liPaired n ρ‖) ρ := Set.indicator_nonneg (fun _ _ => norm_nonneg _) _
    linarith

/-- The paired family is absolutely summable over all rho : C. -/
theorem summable_liPaired (n : ℕ) : Summable (liPaired n) :=
  Summable.of_norm_bounded (summable_liBound n) (norm_liPaired_le n)

/-! ## D. Convergence of the symmetric window sums (Tannery). -/

/-- **The convergence half of B7.**  For every n the symmetric window sums converge to liLimit n. -/
theorem liZeroSum_tendsto (n : ℕ) : Tendsto (liZeroSum n) atTop (𝓝 (liLimit n)) := by
  have hfun : liZeroSum n = fun T => ∑' ρ : ℂ, (windowSet T).indicator (liPaired n) ρ :=
    funext (liZeroSum_eq_tsum_paired n)
  rw [hfun]
  unfold liLimit
  refine tendsto_tsum_of_dominated_convergence (summable_liBound n) ?_
    (Filter.Eventually.of_forall fun T ρ => ?_)
  · intro ρ
    by_cases hs : 0 < ρ.re ∧ ρ.re < 1
    · apply tendsto_const_nhds.congr'
      rw [Filter.EventuallyEq, Filter.eventually_atTop]
      exact ⟨|ρ.im|, fun T hT =>
        (Set.indicator_of_mem (show ρ ∈ windowSet T from ⟨hs.1, hs.2, hT⟩) _).symm⟩
    · have h0 : liPaired n ρ = 0 := liPaired_eq_zero_of_not_nontrivial (fun h => hs h.2)
      have hi : ∀ T, (windowSet T).indicator (liPaired n) ρ = 0 :=
        fun T => Set.indicator_of_notMem (fun h => hs ⟨h.1, h.2.1⟩) _
      simp only [hi, h0]
      exact tendsto_const_nhds
  · exact (norm_indicator_le_norm_self _ _).trans (norm_liPaired_le n ρ)

/-! ## E. The value half as ONE named obligation, and the forward half of Li's criterion. -/

/-- **Obligation (Bombieri-Lagarias 1999, Theorem 2; the value half of B7).**  The absolutely
convergent paired sum equals the closed form: Sum_rho m(rho) Re (1 - (1 - 1/rho)^n) =
S_inf(n) + S_f(n).  Content: the Hadamard / xi'/xi partial fraction at s = 1, i.e. the symmetric
power sums Sum_rho rho^{-j} (j = 1..n) in terms of the Laurent coefficients eta_{j-1} and the
digamma tower at 1/2.  Not in Zeta23 (whose partial fraction is Landau's local form).  Stated for
0 < n; at n = 0 both sides are computable (0 vs 1) and the node excludes it. -/
def LiValue (n : ℕ) : Prop := liLimit n = BombieriLagarias.archSide n + finiteSide n

/-- The node RH_bl_explicit_formula, verbatim, modulo LiValue n. -/
theorem bl_explicit_formula_of {n : ℕ} (_hn : 0 < n) (h : LiValue n) :
    Tendsto (liZeroSum n) atTop (𝓝 (BombieriLagarias.archSide n + finiteSide n)) := by
  rw [← h]
  exact liZeroSum_tendsto n

/-- On the line, |1 - 1/rho| = 1. -/
lemma norm_one_sub_inv_of_on_line {ρ : ℂ} (hre : ρ.re = 1 / 2) (hρ : ρ ≠ 0) :
    ‖1 - 1 / ρ‖ = 1 := by
  have h : 1 - 1 / ρ = (ρ - 1) / ρ := by field_simp
  rw [h, norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hρ)]
  rw [Complex.norm_eq_sqrt_sq_add_sq, Complex.norm_eq_sqrt_sq_add_sq, Complex.sub_re,
    Complex.sub_im, Complex.one_re, Complex.one_im, hre]
  congr 1
  ring

/-- Under RH every paired term has nonnegative real part (Li's computation). -/
lemma liPaired_re_nonneg_of_rh (hRH : RiemannHypothesis) (n : ℕ) (ρ : ℂ) :
    0 ≤ (liPaired n ρ).re := by
  by_cases h : IsNontrivialZero ρ
  · rw [liPaired_re]
    refine mul_nonneg (Nat.cast_nonneg _) ?_
    have hre : ρ.re = 1 / 2 := Zeta23.RH_implies_on_line hRH h
    have hρ : ρ ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hre; norm_num at hre
    unfold liKernel
    rw [Complex.sub_re, Complex.one_re, sub_nonneg]
    calc ((1 - 1 / ρ) ^ n).re ≤ ‖(1 - 1 / ρ) ^ n‖ := Complex.re_le_norm _
      _ = 1 := by rw [norm_pow, norm_one_sub_inv_of_on_line hre hρ, one_pow]
  · rw [liPaired_eq_zero_of_not_nontrivial h, Complex.zero_re]

/-- Forward half of Li's criterion, window form: under RH every symmetric window sum is >= 0. -/
theorem rh_implies_liZeroSum_re_nonneg (hRH : RiemannHypothesis) (n : ℕ) (T : ℝ) :
    0 ≤ (liZeroSum n T).re := by
  rw [liZeroSum_eq_tsum_paired]
  have hsum : Summable ((windowSet T).indicator (liPaired n)) :=
    (summable_liPaired n).indicator _
  rw [Complex.re_tsum hsum]
  refine tsum_nonneg fun ρ => ?_
  by_cases hw : ρ ∈ windowSet T
  · rw [Set.indicator_of_mem hw]; exact liPaired_re_nonneg_of_rh hRH n ρ
  · rw [Set.indicator_of_notMem hw, Complex.zero_re]

/-- Forward half of Li's criterion, limit form: under RH, Re (liLimit n) >= 0 for every n. -/
theorem rh_implies_liLimit_re_nonneg (hRH : RiemannHypothesis) (n : ℕ) : 0 ≤ (liLimit n).re := by
  unfold liLimit
  rw [Complex.re_tsum (summable_liPaired n)]
  exact tsum_nonneg fun ρ => liPaired_re_nonneg_of_rh hRH n ρ

end RvMBridge15
