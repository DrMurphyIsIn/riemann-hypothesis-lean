/-
  KWin2_Split -- the Zhu frequency split of the Weil form on windows PAST the prime-free boundary,
  in the sector form consumed by the KWin2 certificate (rvm_bridge island, 2026-09-24).

  conjecture1_proved = False.  (Finite-window Weil positivity is not RH; not Connes-Consani, whose
  theorem is for the pole-free class; cf. PR #604.)

  THE COMB.  For log 2 < 2L <= log 3 the prime comb of the Weil symbol is the single term n = 2:
      weilSymbol L t = Psi t - c2 cos(t log 2),   c2 = 2 Lambda(2)/sqrt 2 = sqrt 2 log 2,
  (`weilSymbol_eq_two`), and combMass L = c2 (`combMass_eq_two`).  Nothing is thrown away: the comb
  stays inside the symbol on [0, T] and is bounded by its mass only beyond T (Zhu's envelope step).

  PROVED HERE (`Q_ge_Rb`): for a real test v of parity par, smooth, compactly supported in [-L, L]
  with 0 <= L <= l = P.ell, 15/4 <= T and beta0 <= betaStar L T,
      Rb P (weilSymbol L) par v v <= Re weilForm (autocorr v),
  from Zhu eq. (2) (`symbol_representation_ofReal`, ZhuSymbol, valid for every L), the sector
  transform and pole functional on [-l, l], Plancherel, evenness of |F|^2 and of the symbol, and
  weilSymbol L t >= betaStar L T >= beta0 for t >= T (`weilSymbol_ge_betaStar`, ZhuSplit).
  No `sorry`.
-/
import KWin2_Tail
import KWin_Window

open Real MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace KWin2
open KWin (Tr Pl ip phiF poleF continuous_Tr epsR phiF_neg paperFT_ofReal_line norm_sq_line
  weilKernel_zero_ofReal exp_moment_parity integral_odd_eq_zero continuous_v compact_v integrable_v_mul
  plancherel_ofReal integrable_line_sq integrable_line_sq_mul_psi Psi
  eq_zero_of_tsupport_subset_Icc_left' eq_zero_of_tsupport_subset_Icc_right')
open RvMBridge11 RvMBridgeZhu WeilExplicit RvMBridge4 RvMBridge5 WeilWindow

variable (P : KPar)

/-! ## A. The Weil symbol on windows whose comb is {2}. -/

/-- The comb weight of n = 2: `2 Lambda(2) / sqrt 2`. -/
def c2 : ℝ := 2 * ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2

lemma c2_eq : c2 = 2 * Real.log 2 / Real.sqrt 2 := by
  unfold c2
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num

lemma c2_nonneg : 0 ≤ c2 := by
  rw [c2_eq]; have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); positivity

/-- The comb term vanishes except at n = 2 when log 2 < 2L <= log 3. -/
lemma comb_term_eq {L : ℝ} (hL2 : 2 * L ≤ Real.log 3) (t : ℝ) (n : ℕ) (hn : n ≠ 2) :
    (if Real.log n < 2 * L then
      2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * Real.cos (t * Real.log n) else 0) = 0 := by
  split_ifs with h
  · rcases Nat.lt_or_ge n 3 with h3 | h3
    · interval_cases n
      · simp
      · simp [ArithmeticFunction.vonMangoldt_apply_one]
      · exact absurd rfl hn
    · have : Real.log 3 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast h3)
      linarith
  · rfl

theorem comb_eq_two {L : ℝ} (hL1 : Real.log 2 < 2 * L) (hL2 : 2 * L ≤ Real.log 3) (t : ℝ) :
    (∑' n : ℕ, if Real.log n < 2 * L then
        2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * Real.cos (t * Real.log n) else 0)
      = c2 * Real.cos (t * Real.log 2) := by
  rw [tsum_eq_single 2 (fun n hn => comb_term_eq hL2 t n hn)]
  have h : Real.log ((2 : ℕ) : ℝ) < 2 * L := by push_cast; exact hL1
  rw [if_pos h]
  unfold c2
  push_cast
  ring

theorem combMass_eq_two {L : ℝ} (hL1 : Real.log 2 < 2 * L) (hL2 : 2 * L ≤ Real.log 3) :
    combMass L = c2 := by
  unfold combMass
  have hz : ∀ n : ℕ, n ≠ 2 → (if Real.log n < 2 * L then
      2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n else 0) = 0 := by
    intro n hn
    have := comb_term_eq hL2 0 n hn
    split_ifs at this ⊢ with h
    · simpa using this
    · rfl
  rw [tsum_eq_single 2 hz]
  have h : Real.log ((2 : ℕ) : ℝ) < 2 * L := by push_cast; exact hL1
  rw [if_pos h]
  unfold c2
  push_cast
  ring

/-- **The Weil symbol with the n = 2 comb.** -/
theorem weilSymbol_eq_two {L : ℝ} (hL1 : Real.log 2 < 2 * L) (hL2 : 2 * L ≤ Real.log 3) (t : ℝ) :
    weilSymbol L t = Psi t - c2 * Real.cos (t * Real.log 2) := by
  unfold weilSymbol
  rw [comb_eq_two hL1 hL2 t]
  unfold Psi
  rfl

lemma continuous_weilSymbol_two {L : ℝ} (hL1 : Real.log 2 < 2 * L) (hL2 : 2 * L ≤ Real.log 3) :
    Continuous (weilSymbol L) := by
  have e : weilSymbol L = fun t => Psi t - c2 * Real.cos (t * Real.log 2) :=
    funext (weilSymbol_eq_two hL1 hL2)
  rw [e]
  have := KWin.continuous_Psi
  fun_prop

lemma weilSymbol_two_neg {L : ℝ} (hL1 : Real.log 2 < 2 * L) (hL2 : 2 * L ≤ Real.log 3) (t : ℝ) :
    weilSymbol L (-t) = weilSymbol L t := by
  rw [weilSymbol_eq_two hL1 hL2, weilSymbol_eq_two hL1 hL2]
  unfold Psi
  rw [RvMBridge30.psiR_neg, neg_mul, Real.cos_neg]

/-! ## B. Support and the conversion to [-l, l]. -/

lemma v_zero_outside {v : ℝ → ℝ} (hf : IsWeilTest (fun u => (v u : ℂ))) {L l : ℝ} (hLl : L ≤ l)
    (hsupp : tsupport (fun u => (v u : ℂ)) ⊆ Icc (-L) L) {x : ℝ} (hx : x ∉ Ioc (-l) l) : v x = 0 := by
  have hc : Continuous (fun u => (v u : ℂ)) := hf.1.continuous
  rw [mem_Ioc, not_and_or] at hx
  rcases hx with h | h
  · have h1 : (fun u => (v u : ℂ)) x = 0 :=
      eq_zero_of_tsupport_subset_Icc_left' hc hsupp (by linarith [not_lt.mp h])
    simpa using h1
  · have h1 : (fun u => (v u : ℂ)) x = 0 :=
      eq_zero_of_tsupport_subset_Icc_right' hc hsupp (by linarith [not_le.mp h])
    simpa using h1

lemma integral_eq_interval' {v : ℝ → ℝ} (hf : IsWeilTest (fun u => (v u : ℂ))) {L l : ℝ} (hl : 0 < l)
    (hLl : L ≤ l) (hsupp : tsupport (fun u => (v u : ℂ)) ⊆ Icc (-L) L) (w : ℝ → ℝ) :
    ∫ x, v x * w x = ∫ x in (-l)..l, v x * w x := by
  rw [intervalIntegral.integral_of_le (by linarith)]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
  rw [v_zero_outside hf hLl hsupp hx, zero_mul]

/-! ## C. The transform on the line and the pole term. -/

/-- On the line, `|F(t)|^2` is the square of the sector transform on `[-l, l]`. -/
lemma norm_sq_line_sector' {v : ℝ → ℝ} {par : ℕ} (hpar : par = 0 ∨ par = 1)
    (hf : IsWeilTest (fun u => (v u : ℂ))) (hev : ∀ u, v (-u) = epsR par * v u) {L l : ℝ} (hl : 0 < l)
    (hLl : L ≤ l) (hsupp : tsupport (fun u => (v u : ℂ)) ⊆ Icc (-L) L) (t : ℝ) :
    ‖weilKernel (fun u => (v u : ℂ)) (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2 = (Tr l par v t) ^ 2 := by
  rw [norm_sq_line hf]
  unfold Tr
  rw [← integral_eq_interval' hf hl hLl hsupp]
  rcases hpar with h | h <;> subst h
  · have hs : ∫ u, v u * Real.sin (t * u) = 0 := integral_odd_eq_zero fun u => by
      have h1 := hev u
      simp only [epsR, if_true, one_mul] at h1
      rw [h1, mul_neg, Real.sin_neg]; ring
    rw [hs]
    simp [phiF]
  · have hc : ∫ u, v u * Real.cos (t * u) = 0 := integral_odd_eq_zero fun u => by
      have h1 := hev u
      simp only [epsR, one_ne_zero, if_false] at h1
      rw [h1, mul_neg, Real.cos_neg]; ring
    rw [hc]
    simp [phiF]

/-- The pole term: `|F(i/2)|^2` is the square of the sector pole functional on `[-l, l]`. -/
lemma K0_sq' {v : ℝ → ℝ} {par : ℕ} (hpar : par = 0 ∨ par = 1)
    (hf : IsWeilTest (fun u => (v u : ℂ))) (hev : ∀ u, v (-u) = epsR par * v u) {L l : ℝ} (hl : 0 < l)
    (hLl : L ≤ l) (hsupp : tsupport (fun u => (v u : ℂ)) ⊆ Icc (-L) L) :
    ‖weilKernel (fun u => (v u : ℂ)) 0‖ ^ 2 = (Pl l par v) ^ 2 := by
  rw [weilKernel_zero_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hE := exp_moment_parity hev
  have hPl : Pl l par v = ∫ u, v u * poleF par u := (integral_eq_interval' hf hl hLl hsupp _).symm
  have hi1 : Integrable (fun u => v u * Real.exp (u / 2)) := integrable_v_mul hf (by fun_prop)
  have hi2 : Integrable (fun u => v u * Real.exp (-(u / 2))) := integrable_v_mul hf (by fun_prop)
  rw [hPl]
  rcases hpar with h | h <;> subst h
  · have e : (fun u => v u * poleF 0 u)
        = fun u => (1 / 2 : ℝ) * (v u * Real.exp (u / 2) + v u * Real.exp (-(u / 2))) := by
      funext u; simp only [poleF, if_true, Real.cosh_eq]; ring
    rw [e, integral_const_mul, integral_add hi1 hi2]
    simp only [epsR, if_true, one_mul] at hE
    rw [hE]
    ring
  · have e : (fun u => v u * poleF 1 u)
        = fun u => (1 / 2 : ℝ) * (v u * Real.exp (u / 2) - v u * Real.exp (-(u / 2))) := by
      funext u; simp only [poleF, one_ne_zero, if_false, Real.sinh_eq]; ring
    rw [e, integral_const_mul, integral_sub hi1 hi2]
    simp only [epsR, one_ne_zero, if_false] at hE
    rw [hE]
    ring

/-! ## D. The split. -/

/-- The half-line split of an even integrand at `T` against an even symbol bounded below by `β`
beyond `T`. -/
theorem split_line' {F sym : ℝ → ℝ} {T β : ℝ} (hT : 0 ≤ T) (hFi : Integrable F)
    (hFSi : Integrable fun t => F t * sym t) (hF0 : ∀ t, 0 ≤ F t) (hFe : ∀ t, F (-t) = F t)
    (hSe : ∀ t, sym (-t) = sym t) (hSβ : ∀ t, T < t → β ≤ sym t) :
    (1 / Real.pi) * (∫ t in (0 : ℝ)..T, (sym t - β) * F t) + β * ((1 / (2 * Real.pi)) * ∫ t, F t)
      ≤ (1 / (2 * Real.pi)) * ∫ t, F t * sym t := by
  have hpi := Real.pi_pos
  have habs1 : ∫ t, F t * sym t = 2 * ∫ t in Ioi (0 : ℝ), F t * sym t := by
    rw [← integral_comp_abs (f := fun t => F t * sym t)]
    congr 1; funext t
    rcases le_or_gt 0 t with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, hFe, hSe]
  have habs2 : ∫ t, F t = 2 * ∫ t in Ioi (0 : ℝ), F t := by
    rw [← integral_comp_abs (f := F)]
    congr 1; funext t
    rcases le_or_gt 0 t with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, hFe]
  have hU : Ioc (0 : ℝ) T ∪ Ioi T = Ioi 0 := Ioc_union_Ioi_eq_Ioi hT
  have hD : Disjoint (Ioc (0 : ℝ) T) (Ioi T) := by
    rw [Set.disjoint_left]; intro x hx hx'; exact absurd hx.2 (not_le.mpr hx')
  have hs1 : ∫ t in Ioi (0 : ℝ), F t * sym t
      = (∫ t in Ioc (0 : ℝ) T, F t * sym t) + ∫ t in Ioi T, F t * sym t := by
    rw [← hU, setIntegral_union hD measurableSet_Ioi hFSi.integrableOn hFSi.integrableOn]
  have hs2 : ∫ t in Ioi (0 : ℝ), F t
      = (∫ t in Ioc (0 : ℝ) T, F t) + ∫ t in Ioi T, F t := by
    rw [← hU, setIntegral_union hD measurableSet_Ioi hFi.integrableOn hFi.integrableOn]
  have hmono : β * ∫ t in Ioi T, F t ≤ ∫ t in Ioi T, F t * sym t := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hFi.integrableOn.const_mul _) hFSi.integrableOn measurableSet_Ioi
      fun t ht => ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hSβ t ht) (hF0 t)
  have hIoc : ∫ t in (0 : ℝ)..T, (sym t - β) * F t
      = (∫ t in Ioc (0 : ℝ) T, F t * sym t) - β * ∫ t in Ioc (0 : ℝ) T, F t := by
    rw [intervalIntegral.integral_of_le hT, ← integral_const_mul,
      ← integral_sub hFSi.integrableOn (hFi.integrableOn.const_mul _)]
    congr 1; funext t; ring
  rw [hIoc, habs1, habs2, hs1, hs2]
  have e : (1 / Real.pi) = 2 * (1 / (2 * Real.pi)) := by field_simp
  rw [e]
  have hc : 0 < 1 / (2 * Real.pi) := by positivity
  nlinarith [hmono]

/-- **The split**: `Rb P (weilSymbol L) par v v <= Q(v)` on the window, for `log 2 < 2L <= log 3`. -/
theorem Q_ge_Rb (hpc : parCheck P = true) {L : ℝ} (hL1 : Real.log 2 < 2 * L)
    (hL2 : 2 * L ≤ Real.log 3) (hLl : L ≤ lR P) (hT : 15 / 4 ≤ TR P)
    (hβ : b0R P ≤ betaStar L (TR P)) {v : ℝ → ℝ} {par : ℕ} (hpar : par = 0 ∨ par = 1)
    (hf : IsWeilTest (fun u => (v u : ℂ))) (hev : ∀ u, v (-u) = epsR par * v u)
    (hsupp : tsupport (fun u => (v u : ℂ)) ⊆ Icc (-L) L) :
    Rb P (weilSymbol L) par v v ≤ (WeilForm.weilForm (WeilForm.autocorr (fun u => (v u : ℂ)))).re := by
  have hl := lR_pos P hpc
  have hε : epsR par * epsR par = 1 := by unfold epsR; split_ifs <;> norm_num
  rw [symbol_representation_ofReal hε hf hev hsupp]
  set F : ℝ → ℝ := fun r => ‖weilKernel (fun u => (v u : ℂ)) (1 / 2 + (r : ℂ) * Complex.I)‖ ^ 2
    with hF
  have hFT : ∀ t, F t = (Tr (lR P) par v t) ^ 2 := fun t =>
    norm_sq_line_sector' hpar hf hev hl hLl hsupp t
  have hFc : Continuous F := by
    have : F = fun t => (Tr (lR P) par v t) ^ 2 := funext hFT
    rw [this]
    exact (continuous_Tr (lR P) par (continuous_v hf)).pow 2
  have hFi : Integrable F := integrable_line_sq hf
  have hFpsi := integrable_line_sq_mul_psi hf
  have hFcos : Integrable fun t => F t * Real.cos (t * Real.log 2) := by
    have h := hFi.bdd_mul (c := 1)
      (by fun_prop : Continuous fun r : ℝ => Real.cos (r * Real.log 2)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun r => by
        rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
    exact h.congr (Filter.Eventually.of_forall fun r => mul_comm _ _)
  have hFSi : Integrable fun t => F t * weilSymbol L t := by
    have e : (fun t => F t * weilSymbol L t)
        = fun t => (F t * psiR t - F t * Real.log Real.pi) - c2 * (F t * Real.cos (t * Real.log 2)) := by
      funext t; rw [weilSymbol_eq_two hL1 hL2]; unfold Psi; ring
    rw [e]
    exact (hFpsi.sub (hFi.mul_const _)).sub (hFcos.const_mul _)
  have hF0 : ∀ t, 0 ≤ F t := fun t => by rw [hF]; positivity
  have hTneg : ∀ t, Tr (lR P) par v (-t) = (if par = 0 then (1 : ℝ) else -1) * Tr (lR P) par v t := by
    intro t
    unfold Tr
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    rw [show -t * x = -(t * x) by ring, phiF_neg par hpar]
    ring
  have hFe : ∀ t, F (-t) = F t := by
    intro t
    rw [hFT, hFT, hTneg, mul_pow]
    split_ifs <;> norm_num
  have hSβ : ∀ t, TR P < t → b0R P ≤ weilSymbol L t := fun t ht =>
    hβ.trans (weilSymbol_ge_betaStar hT ht.le)
  have hsplit := split_line' (TR_pos P hpc).le hFi hFSi hF0 hFe (weilSymbol_two_neg hL1 hL2) hSβ
  have hplan := plancherel_ofReal hf
  have hip : ip (lR P) v v = ∫ x, v x ^ 2 := by
    unfold ip
    rw [← integral_eq_interval' hf hl hLl hsupp]
    congr 1; funext x; ring
  have hpole := K0_sq' hpar hf hev hl hLl hsupp
  unfold Rb
  rw [hpole, hip, hplan]
  have e2 : (fun t => (weilSymbol L t - b0R P) * (Tr (lR P) par v t * Tr (lR P) par v t))
      = fun t => (weilSymbol L t - b0R P) * F t := by funext t; rw [hFT]; ring
  rw [e2]
  have e3 : (fun r : ℝ => ‖weilKernel (fun u => (v u : ℂ)) (1 / 2 + (r : ℂ) * Complex.I)‖ ^ 2) = F := rfl
  rw [e3]
  have e4 : (fun t : ℝ => F t * weilSymbol L t) = fun t => F t * weilSymbol L t := rfl
  nlinarith [hsplit]

end KWin2

end
