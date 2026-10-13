/-
  KWin_Head -- the head inequality of the prime-free window certificate (rvm_bridge island,
  2026-09-24).

  conjecture1_proved = False.  (Finite-window Weil positivity is not RH; PR #604: the 1.3e-3
  full-class margin at this window is zero content; not Connes-Consani, whose theorem is for the
  pole-free class.)

  THE FORM.  For a sector par (0 even / 1 odd, eps = +1 / -1) and continuous f, g,
      Rb par f g = 2 eps Pl f Pl g + beta0 int_{-l}^{l} f g
                   + (1/pi) int_0^20 (Psi(t) - beta0) Tr f t Tr g t dt,
  with l = 26/75, Tr f t = int_{-l}^{l} f(x) phiF(t x) (cosine / sine transform), Pl f =
  int f cosh(x/2) (resp. sinh(x/2)).  KWin_Split shows Q(v) >= Rb par v v (Zhu split at T = 20).

  PROVED HERE (`head_floor`): for the head polynomials h = sum_{k<N} a_k (x/l)^(2k+par),
      pi (Rb h h - lam int h^2) >= sum_{j,k} a_j a_k headEntry_{jk},
  where headEntry is the exact-rational matrix of KWin_Data whose kernel LDL^T certificate
  (KWin_Cert) makes the right side >= 0; hence Rb h h >= lam int h^2.  The inequality chain:
  pole and transform Taylor truncations (KWin_Taylor; errors Ehead <= 1e-6 absorbed through
  (int |h|)^2 <= 2 l int h^2), Psi >= w_i on every piece (KWin_Minorant), and exact polynomial
  moments of (w_i - beta0) t^q (integral_pow).  No `sorry`.
-/
import KWin_Minorant
import KWin_Taylor

open Real Finset MeasureTheory intervalIntegral

noncomputable section

namespace KWin
open RvMBridge11

/-! ## A. The form. -/

def ellR : ℝ := ((ellQ : ℚ) : ℝ)
lemma ellR_eq : ellR = 26 / 75 := by unfold ellR ellQ; push_cast; norm_num
lemma ellR_pos : 0 < ellR := by rw [ellR_eq]; norm_num

def epsR (par : ℕ) : ℝ := if par = 0 then 1 else -1
def beta0R : ℝ := ((beta0Q : ℚ) : ℝ)

/-- The split form `R(f, g)` of the Weil form on the window (KWin_Split: `Q(v) >= Rb v v`). -/
def Rb (par : ℕ) (f g : ℝ → ℝ) : ℝ :=
  2 * epsR par * Pl ellR par f * Pl ellR par g + beta0R * ip ellR f g
    + (1 / Real.pi) * ∫ t in (0 : ℝ)..20, (Psi t - beta0R) * (Tr ellR par f t * Tr ellR par g t)

/-- The head polynomials. -/
def hfun (par N : ℕ) (a : ℕ → ℝ) (x : ℝ) : ℝ := ∑ k ∈ range N, a k * (x / ellR) ^ (2 * k + par)

lemma continuous_hfun (par N : ℕ) (a : ℕ → ℝ) : Continuous (hfun par N a) := by
  unfold hfun; fun_prop

lemma continuous_Psi : Continuous Psi := by
  unfold Psi; exact continuous_psiR.sub continuous_const

/-! ## B. Moments of the head polynomials. -/

lemma int_pow_div_even (n : ℕ) :
    ∫ x in (-ellR)..ellR, (x / ellR) ^ (2 * n) = 2 * ellR / (2 * n + 1) := by
  have hl := ellR_pos
  have h := intervalIntegral.integral_comp_div (a := -ellR) (b := ellR)
    (fun x : ℝ => x ^ (2 * n)) hl.ne'
  rw [h, integral_pow, smul_eq_mul, neg_div, div_self hl.ne']
  have e : (-1 : ℝ) ^ (2 * n + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
  rw [e]
  push_cast
  field_simp
  ring

lemma mo_hfun (par N : ℕ) (a : ℕ → ℝ) (m : ℕ) :
    mo ellR (hfun par N a) (2 * m + par) = ∑ k ∈ range N, a k * ((Gm par k m : ℚ) : ℝ) := by
  unfold mo hfun
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum fun k _ => Continuous.intervalIntegrable (by fun_prop) _ _]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : ∀ x : ℝ, a k * (x / ellR) ^ (2 * k + par) * (x / ellR) ^ (2 * m + par)
      = a k * (x / ellR) ^ (2 * (k + m + par)) := by
    intro x
    rw [mul_assoc, ← pow_add]
    congr 2
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, int_pow_div_even]
  unfold Gm ellR
  push_cast
  ring

lemma ip_hfun_left (par N : ℕ) (a : ℕ → ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    ip ellR (hfun par N a) g = ∑ k ∈ range N, a k * mo ellR g (2 * k + par) := by
  unfold ip hfun mo
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum fun k _ => Continuous.intervalIntegrable (by fun_prop) _ _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext x
  ring

lemma Gm_symm (par j k : ℕ) : Gm par j k = Gm par k j := by
  unfold Gm; ring

lemma ip_hfun_self (par N : ℕ) (a : ℕ → ℝ) :
    ip ellR (hfun par N a) (hfun par N a)
      = ∑ j ∈ range N, ∑ k ∈ range N, a j * a k * ((Gm par j k : ℚ) : ℝ) := by
  rw [ip_hfun_left par N a (continuous_hfun par N a)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mo_hfun, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Gm_symm par k j]
  ring

/-! ## C. The quadratic form of the certified matrix. -/

lemma quad_outer (N : ℕ) (a u : ℕ → ℝ) (C : ℝ) :
    ∑ j ∈ range N, ∑ k ∈ range N, a j * a k * (C * u j * u k)
      = C * (∑ j ∈ range N, a j * u j) ^ 2 := by
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma quad_hankel (N M : ℕ) (a : ℕ → ℝ) (B : ℕ → ℕ → ℝ) (W : ℕ → ℝ) :
    ∑ j ∈ range N, ∑ k ∈ range N, a j * a k * ∑ m ∈ range M, B m j * ∑ m' ∈ range M, W (m + m') * B m' k
      = ∑ m ∈ range M, ∑ m' ∈ range M,
          W (m + m') * (∑ j ∈ range N, B m j * a j) * (∑ k ∈ range N, B m' k * a k) := by
  have hF : ∀ j k, a j * a k * ∑ m ∈ range M, B m j * ∑ m' ∈ range M, W (m + m') * B m' k
      = ∑ m ∈ range M, ∑ m' ∈ range M, a j * a k * B m j * W (m + m') * B m' k := by
    intro j k
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    ring
  simp_rw [hF]
  conv_lhs => enter [2, j]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  conv_lhs => enter [2, j]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The certified quadratic form, expanded. -/
lemma quad_headEntry {par N : ℕ} (lam : ℚ) (a : ℕ → ℝ) :
    ∑ j ∈ range N, ∑ k ∈ range N, a j * a k * ((headEntry par N lam j k : ℚ) : ℝ)
      = 2 * ((piEQ par : ℚ) : ℝ) * ((epsQ par : ℚ) : ℝ)
          * (∑ j ∈ range N, a j * ((pv par j : ℚ) : ℝ)) ^ 2
        + ((diagc lam : ℚ) : ℝ) * ∑ j ∈ range N, ∑ k ∈ range N, a j * a k * ((Gm par j k : ℚ) : ℝ)
        + ∑ m ∈ range Mt, ∑ m' ∈ range Mt, (((momList par).getD (m + m') 0 : ℚ) : ℝ)
            * (∑ j ∈ range N, ((Bm par m j : ℚ) : ℝ) * a j)
            * (∑ k ∈ range N, ((Bm par m' k : ℚ) : ℝ) * a k) := by
  have hentry : ∀ j ∈ range N, ∀ k ∈ range N, ((headEntry par N lam j k : ℚ) : ℝ)
      = 2 * ((piEQ par : ℚ) : ℝ) * ((epsQ par : ℚ) : ℝ) * ((pv par j : ℚ) : ℝ) * ((pv par k : ℚ) : ℝ)
        + ((diagc lam : ℚ) : ℝ) * ((Gm par j k : ℚ) : ℝ)
        + ∑ m ∈ range Mt, ((Bm par m j : ℚ) : ℝ) * ∑ m' ∈ range Mt,
            (((momList par).getD (m + m') 0 : ℚ) : ℝ) * ((Bm par m' k : ℚ) : ℝ) := by
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
  rw [quad_outer N a (fun j => ((pv par j : ℚ) : ℝ)) (2 * ((piEQ par : ℚ) : ℝ) * ((epsQ par : ℚ) : ℝ)),
    quad_hankel N Mt a (fun m j => ((Bm par m j : ℚ) : ℝ)) (fun s => (((momList par).getD s 0 : ℚ) : ℝ))]
  congr 1
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ## D. The pole term. -/

lemma pole_sq_bound {par : ℕ} (hpar : par = 0 ∨ par = 1) {P Pt A dP : ℝ} (hA : 0 ≤ A)
    (hdP : 0 ≤ dP) (h1 : |P - Pt| ≤ dP * A) (h2 : |P| ≤ ((CpQ : ℚ) : ℝ) * A) :
    2 * ((piEQ par : ℚ) : ℝ) * ((epsQ par : ℚ) : ℝ) * Pt ^ 2
      - 2 * ((piHiQ : ℚ) : ℝ) * (dP * (2 * ((CpQ : ℚ) : ℝ) + dP)) * A ^ 2
      ≤ 2 * Real.pi * epsR par * P ^ 2 := by
  have hlo := pi_gt_Q
  have hhi := pi_lt_Q
  have hCp : (0 : ℝ) ≤ ((CpQ : ℚ) : ℝ) := by unfold CpQ; push_cast; norm_num
  have hd : |P ^ 2 - Pt ^ 2| ≤ dP * (2 * ((CpQ : ℚ) : ℝ) + dP) * A ^ 2 := by
    have hPt : |Pt| ≤ (((CpQ : ℚ) : ℝ) + dP) * A := by
      have := abs_sub_abs_le_abs_sub Pt P
      rw [abs_sub_comm] at this
      nlinarith [abs_nonneg P]
    rw [sq_sub_sq, abs_mul]
    have h3 : |P + Pt| ≤ (2 * ((CpQ : ℚ) : ℝ) + dP) * A := by
      refine (abs_add_le _ _).trans ?_
      nlinarith
    calc |P + Pt| * |P - Pt| ≤ ((2 * ((CpQ : ℚ) : ℝ) + dP) * A) * (dP * A) :=
          mul_le_mul h3 h1 (abs_nonneg _) (by positivity)
      _ = dP * (2 * ((CpQ : ℚ) : ℝ) + dP) * A ^ 2 := by ring
  have hE : 0 ≤ dP * (2 * ((CpQ : ℚ) : ℝ) + dP) * A ^ 2 := by positivity
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
def epsW (n : ℕ) (t : ℝ) : ℝ := 2 * (t * ellR) ^ n / (n.factorial : ℝ)

lemma continuous_epsW (n : ℕ) : Continuous (epsW n) := by unfold epsW; fun_prop

lemma epsW_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ epsW n t := by
  unfold epsW; have := ellR_pos; positivity

lemma int_epsW (n : ℕ) :
    ∫ t in (0 : ℝ)..20, epsW n t
      = 2 * ellR ^ n * 20 ^ (n + 1) / ((n + 1 : ℝ) * (n.factorial : ℝ)) := by
  unfold epsW
  have e : (fun t : ℝ => 2 * (t * ellR) ^ n / (n.factorial : ℝ))
      = fun t => (2 * ellR ^ n / (n.factorial : ℝ)) * t ^ n := by
    funext t; rw [mul_pow]; ring
  rw [e, intervalIntegral.integral_const_mul, integral_pow]
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  field_simp
  ring

lemma int_epsW_sq (n : ℕ) :
    ∫ t in (0 : ℝ)..20, epsW n t ^ 2
      = 4 * ellR ^ (2 * n) * 20 ^ (2 * n + 1) / ((2 * n + 1 : ℝ) * (n.factorial : ℝ) ^ 2) := by
  unfold epsW
  have e : (fun t : ℝ => (2 * (t * ellR) ^ n / (n.factorial : ℝ)) ^ 2)
      = fun t => (4 * ellR ^ (2 * n) / (n.factorial : ℝ) ^ 2) * t ^ (2 * n) := by
    funext t; ring
  rw [e, intervalIntegral.integral_const_mul, integral_pow]
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  push_cast
  field_simp
  ring

/-- `int_0^20 (Psi - beta0) F^2 >= int_0^20 (Psi - beta0) G^2 - S0 (2 I1 + I2) A^2` when
`|F - G| <= eps_n A` and `|F| <= A` on `[0, 20]`. -/
lemma int_sq_perturb {F G : ℝ → ℝ} (hF : Continuous F) (hG : Continuous G) {A : ℝ} (hA : 0 ≤ A)
    (n : ℕ) (h1 : ∀ t ∈ Set.Icc (0 : ℝ) 20, |F t - G t| ≤ epsW n t * A)
    (h2 : ∀ t ∈ Set.Icc (0 : ℝ) 20, |F t| ≤ A) :
    (∫ t in (0 : ℝ)..20, (Psi t - beta0R) * G t ^ 2)
      - ((S0Q : ℚ) : ℝ) * (2 * (∫ t in (0 : ℝ)..20, epsW n t) + ∫ t in (0 : ℝ)..20, epsW n t ^ 2) * A ^ 2
      ≤ ∫ t in (0 : ℝ)..20, (Psi t - beta0R) * F t ^ 2 := by
  have hcP : Continuous fun t => Psi t - beta0R := continuous_Psi.sub continuous_const
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 20, (Psi t - beta0R) * G t ^ 2
      - ((S0Q : ℚ) : ℝ) * (2 * epsW n t + epsW n t ^ 2) * A ^ 2 ≤ (Psi t - beta0R) * F t ^ 2 := by
    intro t ht
    have hS := abs_Psi_sub_beta0_le ht.1 ht.2
    have he := epsW_nonneg n ht.1
    have hd : |F t ^ 2 - G t ^ 2| ≤ epsW n t * (2 + epsW n t) * A ^ 2 := by
      rw [sq_sub_sq, abs_mul]
      have hFG := h1 t ht
      have hFt := h2 t ht
      have hsum : |F t + G t| ≤ (2 + epsW n t) * A := by
        have : |G t| ≤ |F t| + |F t - G t| := by
          have := abs_sub_abs_le_abs_sub (F t) (G t)
          have := abs_sub_abs_le_abs_sub (G t) (F t)
          rw [abs_sub_comm (G t)] at this
          linarith
        refine (abs_add_le _ _).trans ?_
        nlinarith
      calc |F t + G t| * |F t - G t| ≤ ((2 + epsW n t) * A) * (epsW n t * A) :=
            mul_le_mul hsum hFG (abs_nonneg _) (by positivity)
        _ = epsW n t * (2 + epsW n t) * A ^ 2 := by ring
    have hprod : |(Psi t - beta0R) * (F t ^ 2 - G t ^ 2)|
        ≤ ((S0Q : ℚ) : ℝ) * (epsW n t * (2 + epsW n t) * A ^ 2) := by
      rw [abs_mul]
      exact mul_le_mul hS hd (abs_nonneg _) (by unfold S0Q; push_cast; norm_num)
    have := neg_abs_le ((Psi t - beta0R) * (F t ^ 2 - G t ^ 2))
    nlinarith
  have hint1 : IntervalIntegrable (fun t => (Psi t - beta0R) * G t ^ 2
      - ((S0Q : ℚ) : ℝ) * (2 * epsW n t + epsW n t ^ 2) * A ^ 2) volume 0 20 :=
    Continuous.intervalIntegrable (by have := continuous_epsW n; fun_prop) _ _
  have hint2 : IntervalIntegrable (fun t => (Psi t - beta0R) * F t ^ 2) volume 0 20 :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 20) hint1 hint2 hpt
  have hce := continuous_epsW n
  rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)] at hmono
  have e1 : ∫ t in (0 : ℝ)..20, ((S0Q : ℚ) : ℝ) * (2 * epsW n t + epsW n t ^ 2) * A ^ 2
      = ((S0Q : ℚ) : ℝ) * (2 * (∫ t in (0 : ℝ)..20, epsW n t) + ∫ t in (0 : ℝ)..20, epsW n t ^ 2)
        * A ^ 2 := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_const_mul]
  rw [e1] at hmono
  exact hmono

/-! ## F. The moments of the minorant. -/

lemma int_wpoly_mom {i : ℕ} (q : ℕ) :
    ∫ t in ((brk i : ℚ) : ℝ)..((brk (i + 1) : ℚ) : ℝ), (wpoly i t - beta0R) * t ^ q
      = ((momPiece i q : ℚ) : ℝ) := by
  unfold wpoly momPiece beta0R
  have e : (fun t : ℝ => (∑ p ∈ range (Dmax + 1), (((wpList i).getD p 0 : ℚ) : ℝ) * t ^ p
        - ((beta0Q : ℚ) : ℝ)) * t ^ q)
      = fun t => ∑ p ∈ range (Dmax + 1), (((wpList i).getD p 0 : ℚ) : ℝ) * t ^ (p + q)
        - ((beta0Q : ℚ) : ℝ) * t ^ q := by
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

/-- `int_0^20 (Psi - beta0) (sum_m c_m t^(2m+par))^2 >= sum_{m,m'} W_{m+m'} c_m c_m'`. -/
theorem moment_floor (par : ℕ) (c : ℕ → ℝ) :
    ∑ m ∈ range Mt, ∑ m' ∈ range Mt, (((momList par).getD (m + m') 0 : ℚ) : ℝ) * c m * c m'
      ≤ ∫ t in (0 : ℝ)..20, (Psi t - beta0R) * (∑ m ∈ range Mt, c m * t ^ (2 * m + par)) ^ 2 := by
  set pt : ℝ → ℝ := fun t => ∑ m ∈ range Mt, c m * t ^ (2 * m + par) with hpt
  have hptc : Continuous pt := by rw [hpt]; fun_prop
  show _ ≤ ∫ t in (0 : ℝ)..20, (Psi t - beta0R) * pt t ^ 2
  -- split [0, 20] into the pieces
  have hbrk0 : ((brk 0 : ℚ) : ℝ) = 0 := by simp [brk]
  have hbrk7 : ((brk nPc : ℚ) : ℝ) = 20 := by simp [brk, nPc]
  have hsplit : ∀ F : ℝ → ℝ, Continuous F →
      ∑ i ∈ range nPc, ∫ t in ((brk i : ℚ) : ℝ)..((brk (i + 1) : ℚ) : ℝ), F t
        = ∫ t in (0 : ℝ)..20, F t := by
    intro F hF
    rw [intervalIntegral.sum_integral_adjacent_intervals (a := fun i => ((brk i : ℚ) : ℝ))
      fun k _ => hF.intervalIntegrable _ _]
    rw [hbrk0, hbrk7]
  rw [← hsplit (fun t => (Psi t - beta0R) * pt t ^ 2)
    ((continuous_Psi.sub continuous_const).mul (hptc.pow 2))]
  -- on each piece Psi >= w_i
  have hpiece : ∀ i ∈ range nPc,
      ∫ t in ((brk i : ℚ) : ℝ)..((brk (i + 1) : ℚ) : ℝ), (wpoly i t - beta0R) * pt t ^ 2
        ≤ ∫ t in ((brk i : ℚ) : ℝ)..((brk (i + 1) : ℚ) : ℝ), (Psi t - beta0R) * pt t ^ 2 := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hle : ((brk i : ℚ) : ℝ) ≤ ((brk (i + 1) : ℚ) : ℝ) := by exact_mod_cast brk_le_succ hi'
    apply intervalIntegral.integral_mono_on hle
    · exact Continuous.intervalIntegrable (by unfold wpoly; fun_prop) _ _
    · exact Continuous.intervalIntegrable ((continuous_Psi.sub continuous_const).mul (hptc.pow 2)) _ _
    · intro t ht
      exact mul_le_mul_of_nonneg_right (by linarith [wpoly_le_Psi hi' ht.1 ht.2]) (sq_nonneg _)
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum hpiece)
  -- expand the square and integrate the monomials
  have hexp : ∀ i ∈ range nPc,
      ∫ t in ((brk i : ℚ) : ℝ)..((brk (i + 1) : ℚ) : ℝ), (wpoly i t - beta0R) * pt t ^ 2
        = ∑ m ∈ range Mt, ∑ m' ∈ range Mt, c m * c m' * ((momPiece i (2 * (m + m') + 2 * par) : ℚ) : ℝ) := by
    intro i _
    have e : (fun t : ℝ => (wpoly i t - beta0R) * pt t ^ 2)
        = fun t => ∑ m ∈ range Mt, ∑ m' ∈ range Mt,
            c m * c m' * ((wpoly i t - beta0R) * t ^ (2 * (m + m') + 2 * par)) := by
      funext t
      rw [hpt, sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m' _ => ?_
      have : t ^ (2 * (m + m') + 2 * par) = t ^ (2 * m + par) * t ^ (2 * m' + par) := by
        rw [← pow_add]; congr 1; ring
      rw [this]; ring
    have hcw : Continuous fun t => wpoly i t - beta0R := by unfold wpoly; fun_prop
    rw [e, intervalIntegral.integral_finsetSum fun m _ => Continuous.intervalIntegrable
      (continuous_finsetSum _ fun m' _ => by fun_prop) _ _]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [intervalIntegral.integral_finsetSum fun m' _ => Continuous.intervalIntegrable (by fun_prop) _ _]
    refine Finset.sum_congr rfl fun m' _ => ?_
    rw [intervalIntegral.integral_const_mul, int_wpoly_mom]
  rw [Finset.sum_congr rfl hexp]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m' hm' => ?_
  have hs : m + m' < 2 * Mt := by
    have := Finset.mem_range.mp hm; have := Finset.mem_range.mp hm'; omega
  unfold momList
  rw [getD_map_range _ _ hs]
  unfold mom
  push_cast
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ## G. The head floor. -/

theorem head_floor {par N : ℕ} (hpar : par = 0 ∨ par = 1) {lam : ℚ}
    (htail : tailCond par N lam = true) (hcert : psdCert (headMat par N lam) N = true)
    (a : ℕ → ℝ) :
    (lam : ℝ) * ip ellR (hfun par N a) (hfun par N a) ≤ Rb par (hfun par N a) (hfun par N a) := by
  obtain ⟨_, _, _, hE, hlam, _, hM⟩ := tailCond_sound htail
  set h := hfun par N a with hh
  have hc : Continuous h := continuous_hfun par N a
  have hl := ellR_pos
  set X := ip ellR h h with hX
  set A := A1 ellR h with hA
  have hA0 : 0 ≤ A := A1_nonneg hl.le h
  have hA2 : A ^ 2 ≤ 2 * ellR * X := by
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
  set Pt := ∑ k ∈ range N, a k * ((pv par k : ℚ) : ℝ) with hPt
  set dP : ℝ := 2 * (ellR / 2) ^ (2 * Mp + par) / ((2 * Mp + par).factorial : ℝ) with hdP
  have hdP0 : 0 ≤ dP := by rw [hdP]; positivity
  have hPt_eq : ∑ m ∈ range Mp, (ellR / 2) ^ (2 * m + par) / ((2 * m + par).factorial : ℝ)
      * mo ellR h (2 * m + par) = Pt := by
    rw [hPt, hh]
    simp_rw [mo_hfun, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold pv
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Gm_symm par k m]
    unfold ellR
    ring
  have hP1 : |Pl ellR par h - Pt| ≤ dP * A := by
    have := Pl_sub_le hl (by rw [ellR_eq]; norm_num) hpar (M := Mp) (by unfold Mp; omega) hc
    rw [hPt_eq] at this
    rw [hdP]; exact this
  have hP2 : |Pl ellR par h| ≤ ((CpQ : ℚ) : ℝ) * A := by
    have h1 := abs_Pl_le hl par hc
    have h2 := cosh_half_ell_le
    rw [← ellR] at h2
    exact h1.trans (mul_le_mul_of_nonneg_right h2 hA0)
  have hpole := pole_sq_bound hpar hA0 hdP0 hP1 hP2
  -- the transform term
  set c : ℕ → ℝ := fun m => ∑ k ∈ range N, ((Bm par m k : ℚ) : ℝ) * a k with hcdef
  set pt : ℝ → ℝ := fun t => ∑ m ∈ range Mt, c m * t ^ (2 * m + par) with hpt
  have hptc : Continuous pt := by rw [hpt]; fun_prop
  have hpt_eq : ∀ t, ∑ m ∈ range Mt, (-1) ^ m * (t * ellR) ^ (2 * m + par)
      / ((2 * m + par).factorial : ℝ) * mo ellR h (2 * m + par) = pt t := by
    intro t
    rw [hpt]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hcdef, hh, mo_hfun]
    simp only
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Gm_symm par k m]
    unfold Bm
    push_cast
    rw [mul_pow]
    unfold ellR
    ring
  have hT1 : ∀ t ∈ Set.Icc (0 : ℝ) 20, |Tr ellR par h t - pt t| ≤ epsW (2 * Mt + par) t * A := by
    intro t ht
    have htl : t * ellR ≤ (2 * Mt + par + 1) / 2 := by
      have h1 : t * ellR ≤ 20 * ellR := mul_le_mul_of_nonneg_right ht.2 hl.le
      have h2 := (Rat.cast_le (K := ℝ)).mpr hM
      unfold TQ at h2
      push_cast at h2
      have e : (20 : ℝ) * ellR = (20 : ℝ) * ((ellQ : ℚ) : ℝ) := rfl
      linarith
    have := Tr_sub_le hl hpar hc ht.1 htl
    rw [hpt_eq] at this
    unfold epsW
    exact this
  have hT2 : ∀ t ∈ Set.Icc (0 : ℝ) 20, |Tr ellR par h t| ≤ A := fun t _ => abs_Tr_le hl par hc t
  have hint := int_sq_perturb (continuous_Tr ellR par hc) hptc hA0 (2 * Mt + par) hT1 hT2
  have hmom := moment_floor par c
  -- the error constant
  have hEle : 2 * ((piHiQ : ℚ) : ℝ) * (dP * (2 * ((CpQ : ℚ) : ℝ) + dP))
      + ((S0Q : ℚ) : ℝ) * (2 * (∫ t in (0 : ℝ)..20, epsW (2 * Mt + par) t)
        + ∫ t in (0 : ℝ)..20, epsW (2 * Mt + par) t ^ 2) ≤ ((Econst : ℚ) : ℝ) := by
    rw [int_epsW, int_epsW_sq]
    have h1 : ((Ehead par : ℚ) : ℝ) ≤ ((Econst : ℚ) : ℝ) := by exact_mod_cast hE
    refine le_trans (le_of_eq ?_) h1
    unfold Ehead
    rw [hdP]
    unfold ellR TQ
    push_cast
    ring
  -- the quadratic form
  have hquad := quad_headEntry (par := par) (N := N) lam a
  have hGX : ∑ j ∈ range N, ∑ k ∈ range N, a j * a k * ((Gm par j k : ℚ) : ℝ) = X := by
    rw [hX, hh, ip_hfun_self]
  rw [hGX] at hquad
  have hWc : ∑ m ∈ range Mt, ∑ m' ∈ range Mt, (((momList par).getD (m + m') 0 : ℚ) : ℝ)
        * (∑ j ∈ range N, ((Bm par m j : ℚ) : ℝ) * a j) * (∑ k ∈ range N, ((Bm par m' k : ℚ) : ℝ) * a k)
      = ∑ m ∈ range Mt, ∑ m' ∈ range Mt, (((momList par).getD (m + m') 0 : ℚ) : ℝ) * c m * c m' := rfl
  rw [hWc] at hquad
  have hpsd := psdCert_sound hcert a
  have hmat : ∑ j ∈ range N, ∑ k ∈ range N, a j * a k * ((mget (headMat par N lam) j k : ℚ) : ℝ)
      = ∑ j ∈ range N, ∑ k ∈ range N, a j * a k * ((headEntry par N lam j k : ℚ) : ℝ) := by
    refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => ?_
    unfold headMat
    rw [mget_map_range _ (Finset.mem_range.mp hj) (Finset.mem_range.mp hk)]
  rw [hmat, hquad] at hpsd
  -- assemble
  have hpi := Real.pi_pos
  have hlo := pi_gt_Q
  have hbl : (lam : ℝ) < beta0R := by unfold beta0R; exact_mod_cast hlam
  have hdiag : ((diagc lam : ℚ) : ℝ) = ((piLoQ : ℚ) : ℝ) * (beta0R - lam) - 2 * ellR * ((Econst : ℚ) : ℝ) := by
    unfold diagc beta0R ellR; push_cast; ring
  rw [hdiag] at hpsd
  have hRb : Real.pi * (Rb par h h - (lam : ℝ) * X)
      = 2 * Real.pi * epsR par * (Pl ellR par h) ^ 2 + Real.pi * (beta0R - lam) * X
        + ∫ t in (0 : ℝ)..20, (Psi t - beta0R) * (Tr ellR par h t) ^ 2 := by
    unfold Rb
    rw [← hX]
    have e : (fun t => (Psi t - beta0R) * (Tr ellR par h t * Tr ellR par h t))
        = fun t => (Psi t - beta0R) * (Tr ellR par h t) ^ 2 := by funext t; ring
    rw [e]
    field_simp
    ring
  have hfin : 0 ≤ Real.pi * (Rb par h h - (lam : ℝ) * X) := by
    rw [hRb]
    have hEc : 0 ≤ ((Econst : ℚ) : ℝ) := by unfold Econst; positivity
    have h1 : ((piLoQ : ℚ) : ℝ) * (beta0R - lam) * X ≤ Real.pi * (beta0R - lam) * X :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlo.le (by linarith)) hX0
    have h2 : ((S0Q : ℚ) : ℝ) * (2 * (∫ t in (0 : ℝ)..20, epsW (2 * Mt + par) t)
        + ∫ t in (0 : ℝ)..20, epsW (2 * Mt + par) t ^ 2) * A ^ 2
          + 2 * ((piHiQ : ℚ) : ℝ) * (dP * (2 * ((CpQ : ℚ) : ℝ) + dP)) * A ^ 2
        ≤ ((Econst : ℚ) : ℝ) * (2 * ellR * X) := by
      have := mul_le_mul hEle hA2 (sq_nonneg A) hEc
      nlinarith
    nlinarith
  have := (mul_nonneg_iff_of_pos_left hpi).mp hfin
  linarith

end KWin

end
