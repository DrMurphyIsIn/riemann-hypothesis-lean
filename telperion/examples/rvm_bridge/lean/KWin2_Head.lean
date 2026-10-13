/-
  KWin2_Head -- the head inequality of the window certificate, parametric in the window and ABSTRACT
  in the symbol (rvm_bridge island, 2026-09-24).

  conjecture1_proved = False.  (Finite-window Weil positivity is not RH; not Connes-Consani, whose
  theorem is for the pole-free class; cf. PR #604.)

  THE FORM.  For a KPar P, a symbol `sym : ℝ → ℝ`, a sector par (0 even / 1 odd, eps = +1 / -1) and
  continuous f, g,
      Rb P sym par f g = 2 eps Pl f Pl g + beta0 int_{-l}^{l} f g
                         + (1/pi) int_0^T (sym(t) - beta0) Tr f t Tr g t dt,
  l = P.ell, T = P.T.  KWin2_Split shows Q(v) >= Rb P (weilSymbol L) par v v on the window
  (sym = the Weil symbol WITH the prime comb).  The only facts about `sym` used here are the four
  fields of `SymHyp`: continuity, |sym - beta0| <= S0 on [0, T], the piecewise minorant
  wpoly_i - combPoly <= sym (KWin2_Minorant supplies it for the Weil symbol), and cosh(l/2) <= Cp.

  PROVED HERE (`head_floor`): for the head polynomials h = sum_{k<N} a_k (x/l)^(2k+par),
      pi (Rb h h - lam int h^2) >= sum_{j,k} a_j a_k headEntry_{jk} >= 0
  whenever tailCond evaluates to true and the head matrix is PSD (`HeadPSD`, from the kernel's
  exact LDL^T certificate psdCert or the rounded one psdCertR, KWin2_Round).  The same
  chain as KWin_Head (Taylor truncations with errors <= Econst, exact moments of the minorant, now
  including the comb moments int_0^T combPoly t^q).  No `sorry`.
-/
import KWin2_Minorant
import KWin2_Round
import KWin_Head

open Real Finset MeasureTheory intervalIntegral

noncomputable section

namespace KWin2
open KWin (Tr Pl ip mo A1 phiF poleF continuous_Tr Tr_sub_le Pl_sub_le abs_Tr_le abs_Pl_le A1_nonneg
  A1_sq_le continuous_phiF continuous_poleF psdCert psdCert_sound mget mget_map_range getD_map_range
  piLoQ piHiQ piEQ epsQ pi_gt_Q pi_lt_Q epsR quad_outer quad_hankel)

variable (P : KPar)

/-! ## A. The form. -/

def lR : ℝ := ((P.ell : ℚ) : ℝ)
def TR : ℝ := ((P.T : ℚ) : ℝ)
def b0R : ℝ := ((P.beta0 : ℚ) : ℝ)

lemma lR_pos (hpc : parCheck P = true) : 0 < lR P := by
  unfold lR; exact_mod_cast (parCheck_sound P hpc).1

lemma lR_half_le (hpc : parCheck P = true) : lR P / 2 ≤ 1 := by
  have h : ((P.ell : ℚ) : ℝ) ≤ 2 := by exact_mod_cast (parCheck_sound P hpc).2.1
  unfold lR; linarith

lemma TR_pos (hpc : parCheck P = true) : 0 < TR P := by
  unfold TR; exact_mod_cast (parCheck_sound P hpc).2.2.1

lemma S0_nonneg (hpc : parCheck P = true) : (0 : ℝ) ≤ ((P.S0 : ℚ) : ℝ) := by
  exact_mod_cast (parCheck_sound P hpc).2.2.2.1

lemma Cp_nonneg (hpc : parCheck P = true) : (0 : ℝ) ≤ ((P.Cp : ℚ) : ℝ) := by
  exact_mod_cast (parCheck_sound P hpc).2.2.2.2.1

lemma Econst_nonneg (hpc : parCheck P = true) : (0 : ℝ) ≤ ((P.Econst : ℚ) : ℝ) := by
  exact_mod_cast (parCheck_sound P hpc).2.2.2.2.2.1

/-- The split form `R(f, g)` of the Weil form on the window, for the symbol `sym`. -/
def Rb (sym : ℝ → ℝ) (par : ℕ) (f g : ℝ → ℝ) : ℝ :=
  2 * epsR par * Pl (lR P) par f * Pl (lR P) par g + b0R P * ip (lR P) f g
    + (1 / Real.pi) * ∫ t in (0 : ℝ)..(TR P), (sym t - b0R P) * (Tr (lR P) par f t * Tr (lR P) par g t)

/-- The analytic hypotheses on the symbol used by the head and the tail. -/
structure SymHyp (sym : ℝ → ℝ) : Prop where
  cont : Continuous sym
  bound : ∀ t, 0 ≤ t → t ≤ TR P → |sym t - b0R P| ≤ ((P.S0 : ℚ) : ℝ)
  minor : ∀ i < nPc P, ∀ t, ((brk P i : ℚ) : ℝ) ≤ t → t ≤ ((brk P (i + 1) : ℚ) : ℝ) →
    wpoly P i t - combPoly P t ≤ sym t
  cosh : Real.cosh (lR P / 2) ≤ ((P.Cp : ℚ) : ℝ)

/-- The head polynomials. -/
def hfun (par N : ℕ) (a : ℕ → ℝ) (x : ℝ) : ℝ := ∑ k ∈ range N, a k * (x / lR P) ^ (2 * k + par)

lemma continuous_hfun (par N : ℕ) (a : ℕ → ℝ) : Continuous (hfun P par N a) := by
  unfold hfun; fun_prop

/-! ## B. Moments of the head polynomials. -/

lemma int_pow_div_even (hpc : parCheck P = true) (n : ℕ) :
    ∫ x in (-lR P)..(lR P), (x / lR P) ^ (2 * n) = 2 * lR P / (2 * n + 1) := by
  have hl := lR_pos P hpc
  have h := intervalIntegral.integral_comp_div (a := -lR P) (b := lR P)
    (fun x : ℝ => x ^ (2 * n)) hl.ne'
  rw [h, integral_pow, smul_eq_mul, neg_div, div_self hl.ne']
  have e : (-1 : ℝ) ^ (2 * n + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
  rw [e]
  push_cast
  field_simp
  ring

lemma mo_hfun (hpc : parCheck P = true) (par N : ℕ) (a : ℕ → ℝ) (m : ℕ) :
    mo (lR P) (hfun P par N a) (2 * m + par) = ∑ k ∈ range N, a k * ((Gm P par k m : ℚ) : ℝ) := by
  unfold mo hfun
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum fun k _ => Continuous.intervalIntegrable (by fun_prop) _ _]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : ∀ x : ℝ, a k * (x / lR P) ^ (2 * k + par) * (x / lR P) ^ (2 * m + par)
      = a k * (x / lR P) ^ (2 * (k + m + par)) := by
    intro x
    rw [mul_assoc, ← pow_add]
    congr 2
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, int_pow_div_even P hpc]
  unfold Gm lR
  push_cast
  ring

lemma ip_hfun_left (par N : ℕ) (a : ℕ → ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    ip (lR P) (hfun P par N a) g = ∑ k ∈ range N, a k * mo (lR P) g (2 * k + par) := by
  unfold ip hfun mo
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum fun k _ => Continuous.intervalIntegrable (by fun_prop) _ _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext x
  ring

lemma Gm_symm (par j k : ℕ) : Gm P par j k = Gm P par k j := by
  unfold Gm; ring

lemma ip_hfun_self (hpc : parCheck P = true) (par N : ℕ) (a : ℕ → ℝ) :
    ip (lR P) (hfun P par N a) (hfun P par N a)
      = ∑ j ∈ range N, ∑ k ∈ range N, a j * a k * ((Gm P par j k : ℚ) : ℝ) := by
  rw [ip_hfun_left P par N a (continuous_hfun P par N a)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mo_hfun P hpc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Gm_symm P par k j]
  ring

/-! ## C. The quadratic form of the certified matrix. -/

/-- The certified quadratic form, expanded. -/
lemma quad_headEntry {par N : ℕ} (lam : ℚ) (a : ℕ → ℝ) :
    ∑ j ∈ range N, ∑ k ∈ range N, a j * a k * ((headEntry P par N lam j k : ℚ) : ℝ)
      = 2 * ((piEQ par : ℚ) : ℝ) * ((epsQ par : ℚ) : ℝ)
          * (∑ j ∈ range N, a j * ((pv P par j : ℚ) : ℝ)) ^ 2
        + ((diagc P lam : ℚ) : ℝ) * ∑ j ∈ range N, ∑ k ∈ range N, a j * a k * ((Gm P par j k : ℚ) : ℝ)
        + ∑ m ∈ range P.Mt, ∑ m' ∈ range P.Mt, (((momList P par).getD (m + m') 0 : ℚ) : ℝ)
            * (∑ j ∈ range N, ((Bm P par m j : ℚ) : ℝ) * a j)
            * (∑ k ∈ range N, ((Bm P par m' k : ℚ) : ℝ) * a k) := by
  have hentry : ∀ j ∈ range N, ∀ k ∈ range N, ((headEntry P par N lam j k : ℚ) : ℝ)
      = 2 * ((piEQ par : ℚ) : ℝ) * ((epsQ par : ℚ) : ℝ) * ((pv P par j : ℚ) : ℝ) * ((pv P par k : ℚ) : ℝ)
        + ((diagc P lam : ℚ) : ℝ) * ((Gm P par j k : ℚ) : ℝ)
        + ∑ m ∈ range P.Mt, ((Bm P par m j : ℚ) : ℝ) * ∑ m' ∈ range P.Mt,
            (((momList P par).getD (m + m') 0 : ℚ) : ℝ) * ((Bm P par m' k : ℚ) : ℝ) := by
    intro j _ k hk
    unfold headEntry
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun m hm => ?_
    congr 1
    unfold WBmat
    rw [getD_map_range _ _ (Finset.mem_range.mp hm)]
    unfold WBrow
    rw [getD_map_range _ _ (Finset.mem_range.mp hk)]
    push_cast
    rfl
  rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => by rw [hentry j hj k hk]]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [quad_outer N a (fun j => ((pv P par j : ℚ) : ℝ)) (2 * ((piEQ par : ℚ) : ℝ) * ((epsQ par : ℚ) : ℝ)),
    quad_hankel N P.Mt a (fun m j => ((Bm P par m j : ℚ) : ℝ))
      (fun s => (((momList P par).getD s 0 : ℚ) : ℝ))]
  congr 1
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ## D. The pole term. -/

lemma pole_sq_bound (hpc : parCheck P = true) {par : ℕ} (hpar : par = 0 ∨ par = 1) {Pv Pt A dP : ℝ}
    (hA : 0 ≤ A) (hdP : 0 ≤ dP) (h1 : |Pv - Pt| ≤ dP * A) (h2 : |Pv| ≤ ((P.Cp : ℚ) : ℝ) * A) :
    2 * ((piEQ par : ℚ) : ℝ) * ((epsQ par : ℚ) : ℝ) * Pt ^ 2
      - 2 * ((piHiQ : ℚ) : ℝ) * (dP * (2 * ((P.Cp : ℚ) : ℝ) + dP)) * A ^ 2
      ≤ 2 * Real.pi * epsR par * Pv ^ 2 := by
  have hlo := pi_gt_Q
  have hhi := pi_lt_Q
  have hCp := Cp_nonneg P hpc
  have hd : |Pv ^ 2 - Pt ^ 2| ≤ dP * (2 * ((P.Cp : ℚ) : ℝ) + dP) * A ^ 2 := by
    have hPt : |Pt| ≤ (((P.Cp : ℚ) : ℝ) + dP) * A := by
      have := abs_sub_abs_le_abs_sub Pt Pv
      rw [abs_sub_comm] at this
      nlinarith [abs_nonneg Pv]
    rw [sq_sub_sq, abs_mul]
    have h3 : |Pv + Pt| ≤ (2 * ((P.Cp : ℚ) : ℝ) + dP) * A := by
      refine (abs_add_le _ _).trans ?_
      nlinarith
    calc |Pv + Pt| * |Pv - Pt| ≤ ((2 * ((P.Cp : ℚ) : ℝ) + dP) * A) * (dP * A) :=
          mul_le_mul h3 h1 (abs_nonneg _) (by positivity)
      _ = dP * (2 * ((P.Cp : ℚ) : ℝ) + dP) * A ^ 2 := by ring
  have hE : 0 ≤ dP * (2 * ((P.Cp : ℚ) : ℝ) + dP) * A ^ 2 := by positivity
  rw [abs_le] at hd
  have hpi0 : 0 < Real.pi := Real.pi_pos
  rcases hpar with h | h <;> subst h
  · simp only [piEQ, epsQ, epsR, if_true]
    push_cast
    have hPt2 : 0 ≤ Pt ^ 2 := sq_nonneg _
    nlinarith
  · simp only [piEQ, epsQ, epsR, one_ne_zero, if_false]
    push_cast
    have hPt2 : 0 ≤ Pt ^ 2 := sq_nonneg _
    nlinarith

/-! ## E. The transform term. -/

/-- The transform-truncation error weight `eps_M(t) = 2 (t l)^n / n!`. -/
def epsW (n : ℕ) (t : ℝ) : ℝ := 2 * (t * lR P) ^ n / (n.factorial : ℝ)

lemma continuous_epsW (n : ℕ) : Continuous (epsW P n) := by unfold epsW; fun_prop

lemma epsW_nonneg (hpc : parCheck P = true) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ epsW P n t := by
  unfold epsW; have := lR_pos P hpc; positivity

lemma int_epsW (n : ℕ) :
    ∫ t in (0 : ℝ)..(TR P), epsW P n t
      = 2 * lR P ^ n * TR P ^ (n + 1) / ((n + 1 : ℝ) * (n.factorial : ℝ)) := by
  unfold epsW
  have e : (fun t : ℝ => 2 * (t * lR P) ^ n / (n.factorial : ℝ))
      = fun t => (2 * lR P ^ n / (n.factorial : ℝ)) * t ^ n := by
    funext t; rw [mul_pow]; ring
  rw [e, intervalIntegral.integral_const_mul, integral_pow]
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  field_simp
  ring

lemma int_epsW_sq (n : ℕ) :
    ∫ t in (0 : ℝ)..(TR P), epsW P n t ^ 2
      = 4 * lR P ^ (2 * n) * TR P ^ (2 * n + 1) / ((2 * n + 1 : ℝ) * (n.factorial : ℝ) ^ 2) := by
  unfold epsW
  have e : (fun t : ℝ => (2 * (t * lR P) ^ n / (n.factorial : ℝ)) ^ 2)
      = fun t => (4 * lR P ^ (2 * n) / (n.factorial : ℝ) ^ 2) * t ^ (2 * n) := by
    funext t; ring
  rw [e, intervalIntegral.integral_const_mul, integral_pow]
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  push_cast
  field_simp
  ring

/-- `int_0^T (sym - beta0) F^2 >= int_0^T (sym - beta0) G^2 - S0 (2 I1 + I2) A^2` when
`|F - G| <= eps_n A` and `|F| <= A` on `[0, T]`. -/
lemma int_sq_perturb (hpc : parCheck P = true) {sym : ℝ → ℝ} (hs : SymHyp P sym) {F G : ℝ → ℝ}
    (hF : Continuous F) (hG : Continuous G) {A : ℝ} (hA : 0 ≤ A) (n : ℕ)
    (h1 : ∀ t ∈ Set.Icc (0 : ℝ) (TR P), |F t - G t| ≤ epsW P n t * A)
    (h2 : ∀ t ∈ Set.Icc (0 : ℝ) (TR P), |F t| ≤ A) :
    (∫ t in (0 : ℝ)..(TR P), (sym t - b0R P) * G t ^ 2)
      - ((P.S0 : ℚ) : ℝ) * (2 * (∫ t in (0 : ℝ)..(TR P), epsW P n t)
          + ∫ t in (0 : ℝ)..(TR P), epsW P n t ^ 2) * A ^ 2
      ≤ ∫ t in (0 : ℝ)..(TR P), (sym t - b0R P) * F t ^ 2 := by
  have hT := (TR_pos P hpc).le
  have hS0 := S0_nonneg P hpc
  have hsc := hs.cont
  have hcP : Continuous fun t => sym t - b0R P := hsc.sub continuous_const
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) (TR P), (sym t - b0R P) * G t ^ 2
      - ((P.S0 : ℚ) : ℝ) * (2 * epsW P n t + epsW P n t ^ 2) * A ^ 2 ≤ (sym t - b0R P) * F t ^ 2 := by
    intro t ht
    have hS := hs.bound t ht.1 ht.2
    have he := epsW_nonneg P hpc n ht.1
    have hd : |F t ^ 2 - G t ^ 2| ≤ epsW P n t * (2 + epsW P n t) * A ^ 2 := by
      rw [sq_sub_sq, abs_mul]
      have hFG := h1 t ht
      have hFt := h2 t ht
      have hsum : |F t + G t| ≤ (2 + epsW P n t) * A := by
        have : |G t| ≤ |F t| + |F t - G t| := by
          have := abs_sub_abs_le_abs_sub (F t) (G t)
          have := abs_sub_abs_le_abs_sub (G t) (F t)
          rw [abs_sub_comm (G t)] at this
          linarith
        refine (abs_add_le _ _).trans ?_
        nlinarith
      calc |F t + G t| * |F t - G t| ≤ ((2 + epsW P n t) * A) * (epsW P n t * A) :=
            mul_le_mul hsum hFG (abs_nonneg _) (by positivity)
        _ = epsW P n t * (2 + epsW P n t) * A ^ 2 := by ring
    have hprod : |(sym t - b0R P) * (F t ^ 2 - G t ^ 2)|
        ≤ ((P.S0 : ℚ) : ℝ) * (epsW P n t * (2 + epsW P n t) * A ^ 2) := by
      rw [abs_mul]
      exact mul_le_mul hS hd (abs_nonneg _) hS0
    have := neg_abs_le ((sym t - b0R P) * (F t ^ 2 - G t ^ 2))
    nlinarith
  have hce := continuous_epsW P n
  have hint1 : IntervalIntegrable (fun t => (sym t - b0R P) * G t ^ 2
      - ((P.S0 : ℚ) : ℝ) * (2 * epsW P n t + epsW P n t ^ 2) * A ^ 2) volume 0 (TR P) :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hint2 : IntervalIntegrable (fun t => (sym t - b0R P) * F t ^ 2) volume 0 (TR P) :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hmono := intervalIntegral.integral_mono_on hT hint1 hint2 hpt
  rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)] at hmono
  have e1 : ∫ t in (0 : ℝ)..(TR P), ((P.S0 : ℚ) : ℝ) * (2 * epsW P n t + epsW P n t ^ 2) * A ^ 2
      = ((P.S0 : ℚ) : ℝ) * (2 * (∫ t in (0 : ℝ)..(TR P), epsW P n t)
          + ∫ t in (0 : ℝ)..(TR P), epsW P n t ^ 2) * A ^ 2 := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_const_mul]
  rw [e1] at hmono
  exact hmono

/-! ## F. The moments of the minorant. -/

lemma int_wpoly_mom {i : ℕ} (q : ℕ) :
    ∫ t in ((brk P i : ℚ) : ℝ)..((brk P (i + 1) : ℚ) : ℝ), (wpoly P i t - b0R P) * t ^ q
      = ((momPiece P i q : ℚ) : ℝ) := by
  unfold wpoly momPiece b0R
  have e : (fun t : ℝ => (∑ p ∈ range (P.Dmax + 1), (((wpList P i).getD p 0 : ℚ) : ℝ) * t ^ p
        - ((P.beta0 : ℚ) : ℝ)) * t ^ q)
      = fun t => ∑ p ∈ range (P.Dmax + 1), (((wpList P i).getD p 0 : ℚ) : ℝ) * t ^ (p + q)
        - ((P.beta0 : ℚ) : ℝ) * t ^ q := by
    funext t
    rw [sub_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [pow_add]; ring
  rw [e, intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_finsetSum fun p _ => Continuous.intervalIntegrable (by fun_prop) _ _,
    intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  congr 1
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_pow]
    push_cast
    ring
  · ring

lemma int_comb_mom (q : ℕ) :
    ∫ t in (0 : ℝ)..(TR P), combPoly P t * t ^ q = ((momComb P q : ℚ) : ℝ) := by
  unfold combPoly momComb TR
  have e : (fun t : ℝ => (∑ p ∈ range (2 * P.Mc + 1), (((combList P).getD p 0 : ℚ) : ℝ) * t ^ p) * t ^ q)
      = fun t => ∑ p ∈ range (2 * P.Mc + 1), (((combList P).getD p 0 : ℚ) : ℝ) * t ^ (p + q) := by
    funext t
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [pow_add]; ring
  rw [e, intervalIntegral.integral_finsetSum fun p _ => Continuous.intervalIntegrable (by fun_prop) _ _]
  push_cast
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  ring

/-- `int_0^T (sym - beta0) (sum_m c_m t^(2m+par))^2 >= sum_{m,m'} W_{m+m'} c_m c_m'`. -/
theorem moment_floor {sym : ℝ → ℝ} (hs : SymHyp P sym) (hb : brkCheck P = true) (par : ℕ)
    (c : ℕ → ℝ) :
    ∑ m ∈ range P.Mt, ∑ m' ∈ range P.Mt, (((momList P par).getD (m + m') 0 : ℚ) : ℝ) * c m * c m'
      ≤ ∫ t in (0 : ℝ)..(TR P), (sym t - b0R P) * (∑ m ∈ range P.Mt, c m * t ^ (2 * m + par)) ^ 2 := by
  set pt : ℝ → ℝ := fun t => ∑ m ∈ range P.Mt, c m * t ^ (2 * m + par) with hpt
  have hptc : Continuous pt := by rw [hpt]; fun_prop
  show _ ≤ ∫ t in (0 : ℝ)..(TR P), (sym t - b0R P) * pt t ^ 2
  have hsc := hs.cont
  obtain ⟨hb0, hbT, _⟩ := brkCheck_sound P hb
  have hbrk0 : ((brk P 0 : ℚ) : ℝ) = 0 := by rw [hb0]; simp
  have hbrkT : ((brk P (nPc P) : ℚ) : ℝ) = TR P := by rw [hbT]; rfl
  have hsplit : ∀ F : ℝ → ℝ, Continuous F →
      ∑ i ∈ range (nPc P), ∫ t in ((brk P i : ℚ) : ℝ)..((brk P (i + 1) : ℚ) : ℝ), F t
        = ∫ t in (0 : ℝ)..(TR P), F t := by
    intro F hF
    rw [intervalIntegral.sum_integral_adjacent_intervals (a := fun i => ((brk P i : ℚ) : ℝ))
      fun k _ => hF.intervalIntegrable _ _]
    rw [hbrk0, hbrkT]
  rw [← hsplit (fun t => (sym t - b0R P) * pt t ^ 2)
    ((hsc.sub continuous_const).mul (hptc.pow 2))]
  have hcw : ∀ i, Continuous fun t => wpoly P i t - combPoly P t - b0R P := by
    intro i; unfold wpoly combPoly; fun_prop
  -- on each piece sym >= wpoly - combPoly
  have hpiece : ∀ i ∈ range (nPc P),
      ∫ t in ((brk P i : ℚ) : ℝ)..((brk P (i + 1) : ℚ) : ℝ), (wpoly P i t - combPoly P t - b0R P) * pt t ^ 2
        ≤ ∫ t in ((brk P i : ℚ) : ℝ)..((brk P (i + 1) : ℚ) : ℝ), (sym t - b0R P) * pt t ^ 2 := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hle : ((brk P i : ℚ) : ℝ) ≤ ((brk P (i + 1) : ℚ) : ℝ) := by exact_mod_cast brk_le_succ P hb hi'
    apply intervalIntegral.integral_mono_on hle
    · exact Continuous.intervalIntegrable ((hcw i).mul (hptc.pow 2)) _ _
    · exact Continuous.intervalIntegrable ((hsc.sub continuous_const).mul (hptc.pow 2)) _ _
    · intro t ht
      exact mul_le_mul_of_nonneg_right (by linarith [hs.minor i hi' t ht.1 ht.2]) (sq_nonneg _)
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum hpiece)
  -- split off the comb, which is global
  have hsplit2 : ∀ i ∈ range (nPc P),
      ∫ t in ((brk P i : ℚ) : ℝ)..((brk P (i + 1) : ℚ) : ℝ), (wpoly P i t - combPoly P t - b0R P) * pt t ^ 2
        = (∫ t in ((brk P i : ℚ) : ℝ)..((brk P (i + 1) : ℚ) : ℝ), (wpoly P i t - b0R P) * pt t ^ 2)
          - ∫ t in ((brk P i : ℚ) : ℝ)..((brk P (i + 1) : ℚ) : ℝ), combPoly P t * pt t ^ 2 := by
    intro i _
    have hc1 : Continuous fun t => (wpoly P i t - b0R P) * pt t ^ 2 := by
      have : Continuous fun t => wpoly P i t - b0R P := by unfold wpoly; fun_prop
      exact this.mul (hptc.pow 2)
    have hc2 : Continuous fun t => combPoly P t * pt t ^ 2 := by
      have : Continuous fun t => combPoly P t := by unfold combPoly; fun_prop
      exact this.mul (hptc.pow 2)
    rw [← intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
    congr 1; funext t; ring
  rw [Finset.sum_congr rfl hsplit2, Finset.sum_sub_distrib]
  have hcombc : Continuous fun t => combPoly P t * pt t ^ 2 := by
    have : Continuous fun t => combPoly P t := by unfold combPoly; fun_prop
    exact this.mul (hptc.pow 2)
  rw [hsplit _ hcombc]
  -- expand the squares and integrate the monomials
  have hexp : ∀ i ∈ range (nPc P),
      ∫ t in ((brk P i : ℚ) : ℝ)..((brk P (i + 1) : ℚ) : ℝ), (wpoly P i t - b0R P) * pt t ^ 2
        = ∑ m ∈ range P.Mt, ∑ m' ∈ range P.Mt,
            c m * c m' * ((momPiece P i (2 * (m + m') + 2 * par) : ℚ) : ℝ) := by
    intro i _
    have e : (fun t : ℝ => (wpoly P i t - b0R P) * pt t ^ 2)
        = fun t => ∑ m ∈ range P.Mt, ∑ m' ∈ range P.Mt,
            c m * c m' * ((wpoly P i t - b0R P) * t ^ (2 * (m + m') + 2 * par)) := by
      funext t
      rw [hpt, sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m' _ => ?_
      have : t ^ (2 * (m + m') + 2 * par) = t ^ (2 * m + par) * t ^ (2 * m' + par) := by
        rw [← pow_add]; congr 1; ring
      rw [this]; ring
    have hcw' : Continuous fun t => wpoly P i t - b0R P := by unfold wpoly; fun_prop
    rw [e, intervalIntegral.integral_finsetSum fun m _ => Continuous.intervalIntegrable
      (continuous_finsetSum _ fun m' _ => by fun_prop) _ _]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [intervalIntegral.integral_finsetSum fun m' _ => Continuous.intervalIntegrable (by fun_prop) _ _]
    refine Finset.sum_congr rfl fun m' _ => ?_
    rw [intervalIntegral.integral_const_mul, int_wpoly_mom]
  have hexpc : ∫ t in (0 : ℝ)..(TR P), combPoly P t * pt t ^ 2
      = ∑ m ∈ range P.Mt, ∑ m' ∈ range P.Mt,
          c m * c m' * ((momComb P (2 * (m + m') + 2 * par) : ℚ) : ℝ) := by
    have e : (fun t : ℝ => combPoly P t * pt t ^ 2)
        = fun t => ∑ m ∈ range P.Mt, ∑ m' ∈ range P.Mt,
            c m * c m' * (combPoly P t * t ^ (2 * (m + m') + 2 * par)) := by
      funext t
      rw [hpt, sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m' _ => ?_
      have : t ^ (2 * (m + m') + 2 * par) = t ^ (2 * m + par) * t ^ (2 * m' + par) := by
        rw [← pow_add]; congr 1; ring
      rw [this]; ring
    have hcc : Continuous fun t => combPoly P t := by unfold combPoly; fun_prop
    rw [e, intervalIntegral.integral_finsetSum fun m _ => Continuous.intervalIntegrable
      (continuous_finsetSum _ fun m' _ => by fun_prop) _ _]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [intervalIntegral.integral_finsetSum fun m' _ => Continuous.intervalIntegrable (by fun_prop) _ _]
    refine Finset.sum_congr rfl fun m' _ => ?_
    rw [intervalIntegral.integral_const_mul, int_comb_mom]
  rw [Finset.sum_congr rfl hexp, hexpc]
  conv_rhs => rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  conv_rhs => rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m' hm' => ?_
  have hs' : m + m' < 2 * P.Mt := by
    have := Finset.mem_range.mp hm; have := Finset.mem_range.mp hm'; omega
  unfold momList
  rw [getD_map_range _ _ hs']
  unfold mom
  push_cast
  rw [sub_mul, sub_mul, Finset.sum_mul, Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · ring

/-! ## G. The head floor. -/

theorem head_floor {sym : ℝ → ℝ} (hs : SymHyp P sym) (hpc : parCheck P = true)
    (hb : brkCheck P = true) {par N : ℕ} (hpar : par = 0 ∨ par = 1) {lam : ℚ}
    (htail : tailCond P par N lam = true) (hcert : HeadPSD (headMat P par N lam) N)
    (a : ℕ → ℝ) :
    (lam : ℝ) * ip (lR P) (hfun P par N a) (hfun P par N a) ≤ Rb P sym par (hfun P par N a) (hfun P par N a) := by
  obtain ⟨_, _, _, hE, hlam, _, hM, _⟩ := tailCond_sound P htail
  set h := hfun P par N a with hh
  have hc : Continuous h := continuous_hfun P par N a
  have hl := lR_pos P hpc
  set X := ip (lR P) h h with hX
  set A := A1 (lR P) h with hA
  have hA0 : 0 ≤ A := A1_nonneg hl.le h
  have hA2 : A ^ 2 ≤ 2 * lR P * X := by
    have := A1_sq_le hl hc
    rw [hX]
    unfold ip
    have e : (fun x => h x ^ 2) = fun x => h x * h x := by funext x; ring
    rw [e] at this
    exact this
  have hX0 : 0 ≤ X := by
    rw [hX]; unfold ip
    exact intervalIntegral.integral_nonneg (by linarith) fun x _ => mul_self_nonneg _
  -- the pole term
  set Pt := ∑ k ∈ range N, a k * ((pv P par k : ℚ) : ℝ) with hPt
  set dP : ℝ := 2 * (lR P / 2) ^ (2 * P.Mp + par) / ((2 * P.Mp + par).factorial : ℝ) with hdP
  have hdP0 : 0 ≤ dP := by rw [hdP]; positivity
  have hPt_eq : ∑ m ∈ range P.Mp, (lR P / 2) ^ (2 * m + par) / ((2 * m + par).factorial : ℝ)
      * mo (lR P) h (2 * m + par) = Pt := by
    rw [hPt, hh]
    simp_rw [mo_hfun P hpc, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold pv
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Gm_symm P par k m]
    unfold lR
    ring
  have hP1 : |Pl (lR P) par h - Pt| ≤ dP * A := by
    have hM0 : 0 < 2 * P.Mp + par := by have := (parCheck_sound P hpc).2.2.2.2.2.2.2; omega
    have := Pl_sub_le hl (lR_half_le P hpc) hpar (M := P.Mp) hM0 hc
    rw [hPt_eq] at this
    rw [hdP]; exact this
  have hP2 : |Pl (lR P) par h| ≤ ((P.Cp : ℚ) : ℝ) * A := by
    have h1 := abs_Pl_le hl par hc
    exact h1.trans (mul_le_mul_of_nonneg_right hs.cosh hA0)
  have hpole := pole_sq_bound P hpc hpar hA0 hdP0 hP1 hP2
  -- the transform term
  set c : ℕ → ℝ := fun m => ∑ k ∈ range N, ((Bm P par m k : ℚ) : ℝ) * a k with hcdef
  set pt : ℝ → ℝ := fun t => ∑ m ∈ range P.Mt, c m * t ^ (2 * m + par) with hpt
  have hptc : Continuous pt := by rw [hpt]; fun_prop
  have hpt_eq : ∀ t, ∑ m ∈ range P.Mt, (-1) ^ m * (t * lR P) ^ (2 * m + par)
      / ((2 * m + par).factorial : ℝ) * mo (lR P) h (2 * m + par) = pt t := by
    intro t
    rw [hpt]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hcdef, hh, mo_hfun P hpc]
    simp only
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Gm_symm P par k m]
    unfold Bm
    push_cast
    rw [mul_pow]
    unfold lR
    ring
  have hT1 : ∀ t ∈ Set.Icc (0 : ℝ) (TR P), |Tr (lR P) par h t - pt t| ≤ epsW P (2 * P.Mt + par) t * A := by
    intro t ht
    have htl : t * lR P ≤ (2 * P.Mt + par + 1) / 2 := by
      have h1 : t * lR P ≤ TR P * lR P := mul_le_mul_of_nonneg_right ht.2 hl.le
      have h2 := (Rat.cast_le (K := ℝ)).mpr hM
      push_cast at h2
      have e : TR P * lR P = ((P.T : ℚ) : ℝ) * ((P.ell : ℚ) : ℝ) := rfl
      linarith
    have := Tr_sub_le hl hpar hc ht.1 htl
    rw [hpt_eq] at this
    unfold epsW
    exact this
  have hT2 : ∀ t ∈ Set.Icc (0 : ℝ) (TR P), |Tr (lR P) par h t| ≤ A := fun t _ => abs_Tr_le hl par hc t
  have hint := int_sq_perturb P hpc hs (continuous_Tr (lR P) par hc) hptc hA0 (2 * P.Mt + par) hT1 hT2
  have hmom := moment_floor P hs hb par c
  -- the error constant
  have hEle : 2 * ((piHiQ : ℚ) : ℝ) * (dP * (2 * ((P.Cp : ℚ) : ℝ) + dP))
      + ((P.S0 : ℚ) : ℝ) * (2 * (∫ t in (0 : ℝ)..(TR P), epsW P (2 * P.Mt + par) t)
        + ∫ t in (0 : ℝ)..(TR P), epsW P (2 * P.Mt + par) t ^ 2) ≤ ((P.Econst : ℚ) : ℝ) := by
    rw [int_epsW, int_epsW_sq]
    have h1 : ((Ehead P par : ℚ) : ℝ) ≤ ((P.Econst : ℚ) : ℝ) := by exact_mod_cast hE
    refine le_trans (le_of_eq ?_) h1
    unfold Ehead
    rw [hdP]
    unfold lR TR
    push_cast
    ring
  -- the quadratic form
  have hquad := quad_headEntry P (par := par) (N := N) lam a
  have hGX : ∑ j ∈ range N, ∑ k ∈ range N, a j * a k * ((Gm P par j k : ℚ) : ℝ) = X := by
    rw [hX, hh, ip_hfun_self P hpc]
  rw [hGX] at hquad
  have hWc : ∑ m ∈ range P.Mt, ∑ m' ∈ range P.Mt, (((momList P par).getD (m + m') 0 : ℚ) : ℝ)
        * (∑ j ∈ range N, ((Bm P par m j : ℚ) : ℝ) * a j) * (∑ k ∈ range N, ((Bm P par m' k : ℚ) : ℝ) * a k)
      = ∑ m ∈ range P.Mt, ∑ m' ∈ range P.Mt, (((momList P par).getD (m + m') 0 : ℚ) : ℝ) * c m * c m' := rfl
  rw [hWc] at hquad
  have hpsd := hcert a
  have hmat : ∑ j ∈ range N, ∑ k ∈ range N, a j * a k * ((mget (headMat P par N lam) j k : ℚ) : ℝ)
      = ∑ j ∈ range N, ∑ k ∈ range N, a j * a k * ((headEntry P par N lam j k : ℚ) : ℝ) := by
    refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => ?_
    unfold headMat
    rw [mget_map_range _ (Finset.mem_range.mp hj) (Finset.mem_range.mp hk)]
  rw [hmat, hquad] at hpsd
  -- assemble
  have hpi := Real.pi_pos
  have hlo := pi_gt_Q
  have hbl : (lam : ℝ) < b0R P := by unfold b0R; exact_mod_cast hlam
  have hdiag : ((diagc P lam : ℚ) : ℝ)
      = ((piLoQ : ℚ) : ℝ) * (b0R P - lam) - 2 * lR P * ((P.Econst : ℚ) : ℝ) := by
    unfold diagc b0R lR; push_cast; ring
  rw [hdiag] at hpsd
  have hRb : Real.pi * (Rb P sym par h h - (lam : ℝ) * X)
      = 2 * Real.pi * epsR par * (Pl (lR P) par h) ^ 2 + Real.pi * (b0R P - lam) * X
        + ∫ t in (0 : ℝ)..(TR P), (sym t - b0R P) * (Tr (lR P) par h t) ^ 2 := by
    unfold Rb
    rw [← hX]
    have e : (fun t => (sym t - b0R P) * (Tr (lR P) par h t * Tr (lR P) par h t))
        = fun t => (sym t - b0R P) * (Tr (lR P) par h t) ^ 2 := by funext t; ring
    rw [e]
    field_simp
    ring
  have hfin : 0 ≤ Real.pi * (Rb P sym par h h - (lam : ℝ) * X) := by
    rw [hRb]
    have hEc := Econst_nonneg P hpc
    have h1 : ((piLoQ : ℚ) : ℝ) * (b0R P - lam) * X ≤ Real.pi * (b0R P - lam) * X :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlo.le (by linarith)) hX0
    have h2 : ((P.S0 : ℚ) : ℝ) * (2 * (∫ t in (0 : ℝ)..(TR P), epsW P (2 * P.Mt + par) t)
        + ∫ t in (0 : ℝ)..(TR P), epsW P (2 * P.Mt + par) t ^ 2) * A ^ 2
          + 2 * ((piHiQ : ℚ) : ℝ) * (dP * (2 * ((P.Cp : ℚ) : ℝ) + dP)) * A ^ 2
        ≤ ((P.Econst : ℚ) : ℝ) * (2 * lR P * X) := by
      have := mul_le_mul hEle hA2 (sq_nonneg A) hEc
      nlinarith
    nlinarith
  have := (mul_nonneg_iff_of_pos_left hpi).mp hfin
  linarith

end KWin2

end
